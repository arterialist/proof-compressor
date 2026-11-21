"""Scalable graph topology analysis: iterative Tarjan SCC, CHK dominators, DAG flow, and bottlenecks."""

from __future__ import annotations

import json
import math
import random
import sqlite3
from array import array
from collections import defaultdict, deque
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

from proof_compressor.schema import connect_db, get_meta, set_meta

_THM_KINDS = frozenset({"theorem", "lemma"})
_DEF_KINDS = frozenset({"def", "abbrev", "structure", "class", "inductive"})

_KIND_WEIGHTS = {
    "theorem": 1.0,
    "lemma": 1.0,
    "def": 0.75,
    "structure": 0.80,
    "class": 0.80,
    "inductive": 0.80,
    "abbrev": 0.65,
    "axiom": 0.55,
    "opaque": 0.50,
    "constant": 0.50,
    "instance": 0.15,
    "other": 0.25,
}


@dataclass
class TopologyReport:
    """Topology metrics, bottleneck pillars, high-centrality definitions, and backbone DAG."""

    node_count: int = 0
    edge_count: int = 0
    scc_count: int = 0
    nontrivial_scc_count: int = 0
    largest_scc_size: int = 0
    max_dominator_depth: int = 0
    exact_flow_mode: bool = True

    top_bottlenecks: list[dict[str, Any]] = field(default_factory=list)
    top_definitions: list[dict[str, Any]] = field(default_factory=list)
    backbone_nodes: list[dict[str, Any]] = field(default_factory=list)
    backbone_edges: list[dict[str, Any]] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _open_db(db: sqlite3.Connection | str | Path) -> tuple[sqlite3.Connection, bool]:
    if isinstance(db, sqlite3.Connection):
        return db, False
    return connect_db(db), True


def build_csr(
    n: int,
    edges: list[tuple[int, int]],
) -> tuple[array, array, array, array]:
    """Build forward and reverse Compressed Sparse Row (CSR) adjacency arrays."""
    out_deg = array("I", [0]) * n
    in_deg = array("I", [0]) * n
    for u, v in edges:
        out_deg[u] += 1
        in_deg[v] += 1

    out_offsets = array("I", [0]) * (n + 1)
    in_offsets = array("I", [0]) * (n + 1)
    acc_out = 0
    acc_in = 0
    for i in range(n):
        out_offsets[i] = acc_out
        acc_out += out_deg[i]
        in_offsets[i] = acc_in
        acc_in += in_deg[i]
    out_offsets[n] = acc_out
    in_offsets[n] = acc_in

    out_targets = array("I", [0]) * acc_out
    in_targets = array("I", [0]) * acc_in
    out_cursor = array("I", out_offsets[:-1])
    in_cursor = array("I", in_offsets[:-1])

    for u, v in edges:
        pos = out_cursor[u]
        out_targets[pos] = v
        out_cursor[u] = pos + 1

        pos_in = in_cursor[v]
        in_targets[pos_in] = u
        in_cursor[v] = pos_in + 1

    return out_offsets, out_targets, in_offsets, in_targets


def tarjan_scc_iterative(
    n: int,
    out_offsets: array,
    out_targets: array,
) -> tuple[array, int]:
    """Iterative Tarjan strongly connected components algorithm.

    Returns `(scc_id, num_sccs)` where `scc_id` is in reverse topological order:
    for every condensed DAG edge `scc(u) -> scc(v)` with `scc(u) != scc(v)`,
    `scc(u) > scc(v)`.
    """
    index = array("i", [-1]) * n
    lowlink = array("i", [0]) * n
    on_stack = bytearray(n)
    scc_id = array("i", [-1]) * n

    tarjan_stack: list[int] = []
    # Explicit DFS stack stores (node, edge_cursor)
    call_stack: list[tuple[int, int]] = []

    next_index = 0
    next_scc = 0

    for start in range(n):
        if index[start] != -1:
            continue

        index[start] = next_index
        lowlink[start] = next_index
        next_index += 1
        tarjan_stack.append(start)
        on_stack[start] = 1
        call_stack.append((start, out_offsets[start]))

        while call_stack:
            u, pos = call_stack[-1]
            end = out_offsets[u + 1]
            if pos < end:
                v = out_targets[pos]
                call_stack[-1] = (u, pos + 1)
                if index[v] == -1:
                    index[v] = next_index
                    lowlink[v] = next_index
                    next_index += 1
                    tarjan_stack.append(v)
                    on_stack[v] = 1
                    call_stack.append((v, out_offsets[v]))
                elif on_stack[v]:
                    if index[v] < lowlink[u]:
                        lowlink[u] = index[v]
            else:
                call_stack.pop()
                if lowlink[u] == index[u]:
                    cid = next_scc
                    next_scc += 1
                    while True:
                        w = tarjan_stack.pop()
                        on_stack[w] = 0
                        scc_id[w] = cid
                        if w == u:
                            break
                if call_stack:
                    parent = call_stack[-1][0]
                    if lowlink[u] < lowlink[parent]:
                        lowlink[parent] = lowlink[u]

    return scc_id, next_scc


def compute_dominators_chk(
    n: int,
    root_indices: list[int],
    out_offsets: array,
    out_targets: array,
    in_offsets: array,
    in_targets: array,
    node_loc: array,
) -> tuple[array, array, array, array]:
    """Iterative Cooper-Harvey-Kennedy dominator tree from virtual super-root S = n.

    Returns `(idom, dom_depth, dom_count, dom_loc)` of length `n` (excluding S).
    `idom[u] == n` means `u` is directly dominated by the virtual super-root.
    """
    super_root = n
    # Build super-root outgoing list: explicit roots plus any zero-in-degree nodes
    # so disconnected reachable components also join the dominator tree cleanly.
    sr_set: set[int] = set(root_indices)
    for i in range(n):
        if in_offsets[i] == in_offsets[i + 1]:
            sr_set.add(i)
    if not sr_set and n > 0:
        sr_set.add(0)

    sr_targets = sorted(sr_set)

    # Iterative DFS from super_root to compute postorder -> reverse postorder (RPO)
    visited = bytearray(n + 1)
    postorder: list[int] = []

    def _dfs_from(seed: int) -> None:
        visited[seed] = 1
        if seed == super_root:
            stack: list[tuple[int, int]] = [(super_root, 0)]
        else:
            stack = [(seed, out_offsets[seed])]

        while stack:
            u, pos = stack[-1]
            if u == super_root:
                if pos < len(sr_targets):
                    v = sr_targets[pos]
                    stack[-1] = (u, pos + 1)
                    if not visited[v]:
                        visited[v] = 1
                        stack.append((v, out_offsets[v]))
                else:
                    stack.pop()
                    postorder.append(u)
            else:
                end = out_offsets[u + 1]
                if pos < end:
                    v = out_targets[pos]
                    stack[-1] = (u, pos + 1)
                    if not visited[v]:
                        visited[v] = 1
                        stack.append((v, out_offsets[v]))
                else:
                    stack.pop()
                    postorder.append(u)

    _dfs_from(super_root)

    # Any cycle with no external entry (not reached from sr_targets) gets attached to super_root
    extra_sr: list[int] = []
    for i in range(n):
        if not visited[i]:
            extra_sr.append(i)
            sr_set.add(i)
            _dfs_from(i)
    if extra_sr:
        # Ensure super_root sits last in postorder (i.e. rpo_num == 0)
        postorder = [x for x in postorder if x != super_root]
        postorder.append(super_root)

    rpo_nodes = postorder[::-1]
    rpo_num = array("i", [-1]) * (n + 1)
    for idx, node in enumerate(rpo_nodes):
        rpo_num[node] = idx

    idom = array("i", [-1]) * (n + 1)
    idom[super_root] = super_root

    # Cooper-Harvey-Kennedy iterative fixed-point computation
    changed = True
    while changed:
        changed = False
        for u in rpo_nodes:
            if u == super_root:
                continue
            new_idom = -1
            if u in sr_set:
                new_idom = super_root
            start = in_offsets[u]
            end = in_offsets[u + 1]
            for pos in range(start, end):
                p = in_targets[pos]
                if idom[p] == -1:
                    continue
                if new_idom == -1:
                    new_idom = p
                else:
                    f1 = p
                    f2 = new_idom
                    while f1 != f2:
                        while rpo_num[f1] > rpo_num[f2]:
                            f1 = idom[f1]
                        while rpo_num[f2] > rpo_num[f1]:
                            f2 = idom[f2]
                    new_idom = f1
            if new_idom != -1 and idom[u] != new_idom:
                idom[u] = new_idom
                changed = True

    # Build dominator tree children and compute exact depth + dominated subtree weights
    dom_children: list[list[int]] = [[] for _ in range(n + 1)]
    for u in range(n):
        p = idom[u]
        if p >= 0:
            dom_children[p].append(u)

    dom_depth = array("i", [0]) * n
    bfs_order: list[int] = []
    q: deque[tuple[int, int]] = deque([(super_root, 0)])
    while q:
        u, d = q.popleft()
        if u != super_root:
            dom_depth[u] = d
            bfs_order.append(u)
        for ch in dom_children[u]:
            q.append((ch, d + 1))

    dom_count = array("I", [1]) * n
    dom_loc = array("Q", [0]) * n
    for u in range(n):
        dom_loc[u] = node_loc[u]

    for u in reversed(bfs_order):
        p = idom[u]
        if 0 <= p < n:
            dom_count[p] += dom_count[u]
            dom_loc[p] += dom_loc[u]

    return idom[:n], dom_depth, dom_count, dom_loc


def _build_condensed_dag(
    n: int,
    num_sccs: int,
    scc_id: array,
    out_offsets: array,
    out_targets: array,
) -> tuple[list[list[int]], list[list[int]]]:
    """Build deduplicated forward and reverse adjacency lists on the SCC DAG."""
    dag_out_sets: list[set[int]] = [set() for _ in range(num_sccs)]
    for u in range(n):
        cu = scc_id[u]
        start = out_offsets[u]
        end = out_offsets[u + 1]
        for pos in range(start, end):
            cv = scc_id[out_targets[pos]]
            if cu != cv:
                dag_out_sets[cu].add(cv)

    dag_out: list[list[int]] = [list(s) for s in dag_out_sets]
    dag_in: list[list[int]] = [[] for _ in range(num_sccs)]
    for cu, nbs in enumerate(dag_out):
        for cv in nbs:
            dag_in[cv].append(cu)
    return dag_out, dag_in


def compute_dag_flow(
    num_sccs: int,
    dag_out: list[list[int]],
    dag_in: list[list[int]],
    scc_size: array,
    scc_loc: array,
    *,
    exact_threshold: int = 2500,
    sketch_bits: int = 256,
) -> tuple[array, array, array, bool]:
    """Compute descendant count, descendant LOC, and ancestor count per SCC.

    Uses 100% exact bitsets when `num_sccs <= exact_threshold`, and deterministic
    bit-parallel landmark sketches (256-bit Python ints) for 500k+ node DAGs.
    Recall Tarjan SCC IDs satisfy `cu > cv` for every edge `cu -> cv`.
    """
    desc_count = array("I", [0]) * num_sccs
    desc_loc = array("Q", [0]) * num_sccs
    anc_count = array("I", [0]) * num_sccs

    if num_sccs == 0:
        return desc_count, desc_loc, anc_count, True

    if num_sccs <= exact_threshold:
        # Exact bottom-up reachability bitmasks
        dmasks = [1 << c for c in range(num_sccs)]
        for c in range(num_sccs):
            m = dmasks[c]
            for nb in dag_out[c]:
                m |= dmasks[nb]
            dmasks[c] = m
            # Sum exact size and LOC over set bits
            cnt = 0
            loc = 0
            tmp = m
            while tmp:
                lsb = tmp & -tmp
                bit = lsb.bit_length() - 1
                cnt += scc_size[bit]
                loc += scc_loc[bit]
                tmp ^= lsb
            desc_count[c] = cnt
            desc_loc[c] = loc

        # Exact top-down ancestor bitmasks
        amasks = [1 << c for c in range(num_sccs)]
        for c in range(num_sccs - 1, -1, -1):
            m = amasks[c]
            for p in dag_in[c]:
                m |= amasks[p]
            amasks[c] = m
            cnt = 0
            tmp = m
            while tmp:
                lsb = tmp & -tmp
                bit = lsb.bit_length() - 1
                cnt += scc_size[bit]
                tmp ^= lsb
            anc_count[c] = cnt

        return desc_count, desc_loc, anc_count, True

    # Scalable bit-parallel landmark estimation for large DAGs (500k+ nodes)
    rng = random.Random(42)
    total_nodes = sum(scc_size)
    total_loc = sum(scc_loc)

    # Build cumulative weights for O(log C) weighted landmark sampling
    cum_nodes: list[int] = []
    acc = 0
    for sz in scc_size:
        acc += sz
        cum_nodes.append(acc)

    cum_loc: list[int] = []
    acc_l = 0
    for lc in scc_loc:
        acc_l += lc
        cum_loc.append(acc_l)

    import bisect

    def _sample_masks(cum: list[int], total: int) -> list[int]:
        masks = [0] * num_sccs
        if total <= 0:
            return masks
        for bit in range(sketch_bits):
            r = rng.randint(1, total)
            idx = bisect.bisect_left(cum, r)
            if idx >= num_sccs:
                idx = num_sccs - 1
            masks[idx] |= 1 << bit
        return masks

    # Descendant LOC sketch (bottom-up)
    dloc_masks = _sample_masks(cum_loc, total_loc)
    for c in range(num_sccs):
        m = dloc_masks[c]
        for nb in dag_out[c]:
            m |= dloc_masks[nb]
        dloc_masks[c] = m
        est = int(round(total_loc * m.bit_count() / sketch_bits))
        desc_loc[c] = max(scc_loc[c], est)
    del dloc_masks

    # Descendant node count sketch (bottom-up)
    dcnt_masks = _sample_masks(cum_nodes, total_nodes)
    for c in range(num_sccs):
        m = dcnt_masks[c]
        for nb in dag_out[c]:
            m |= dcnt_masks[nb]
        dcnt_masks[c] = m
        est = int(round(total_nodes * m.bit_count() / sketch_bits))
        desc_count[c] = max(scc_size[c], est)
    del dcnt_masks

    # Ancestor node count sketch (top-down)
    acnt_masks = _sample_masks(cum_nodes, total_nodes)
    for c in range(num_sccs - 1, -1, -1):
        m = acnt_masks[c]
        for p in dag_in[c]:
            m |= acnt_masks[p]
        acnt_masks[c] = m
        est = int(round(total_nodes * m.bit_count() / sketch_bits))
        anc_count[c] = max(scc_size[c], est)
    del acnt_masks

    return desc_count, desc_loc, anc_count, False


def transitive_reduction(
    nodes: list[int],
    reach: dict[int, set[int]],
) -> list[tuple[int, int]]:
    """Compute exact transitive reduction of a small DAG given reachability sets.

    `reach[u]` is the set of nodes `v != u` strictly reachable from `u`.
    Edge `(u, v)` is kept iff no intermediate `w` exists with `w in reach[u]` and `v in reach[w]`.
    """
    reduced: list[tuple[int, int]] = []
    for u in nodes:
        ru = reach.get(u, set())
        for v in sorted(ru):
            is_transitive = False
            for w in ru:
                if w != v and v in reach.get(w, ()):
                    is_transitive = True
                    break
            if not is_transitive:
                reduced.append((u, v))
    return reduced


def compute_backbone_dag(
    pillar_indices: list[int],
    num_sccs: int,
    scc_id: array,
    dag_out: list[list[int]],
) -> list[tuple[int, int]]:
    """Extract exact induced reachability among pillar nodes and return transitive reduction."""
    if len(pillar_indices) <= 1:
        return []

    # Map each pillar to a bit position
    k = len(pillar_indices)
    scc_to_bits: dict[int, int] = defaultdict(int)
    for bit, idx in enumerate(pillar_indices):
        scc_to_bits[scc_id[idx]] |= 1 << bit

    # Single bottom-up bit-parallel pass on the condensed DAG
    reach_bits = [0] * num_sccs
    for c in range(num_sccs):
        m = scc_to_bits.get(c, 0)
        for nb in dag_out[c]:
            m |= reach_bits[nb]
        reach_bits[c] = m

    reach: dict[int, set[int]] = {}
    for i, u in enumerate(pillar_indices):
        cu = scc_id[u]
        m = reach_bits[cu]
        targets: set[int] = set()
        for j, v in enumerate(pillar_indices):
            if i == j:
                continue
            # Strictly acyclic between distinct SCCs (cu > cv guaranteed in Tarjan order)
            if scc_id[v] != cu and ((m >> j) & 1):
                targets.add(v)
        reach[u] = targets

    return transitive_reduction(pillar_indices, reach)


def analyze_topology(
    db: sqlite3.Connection | str | Path,
    *,
    top_k: int = 25,
    reachable_only: bool = True,
    exact_flow_threshold: int = 2500,
    batch_size: int = 50_000,
) -> TopologyReport:
    """Compute SCCs, dominators, DAG flow, bottleneck scores, and backbone transitive reduction."""
    conn, should_close = _open_db(db)
    try:
        cur = conn.cursor()

        has_reachable = False
        if reachable_only:
            row = cur.execute(
                "SELECT 1 FROM metrics WHERE reachable = 1 LIMIT 1"
            ).fetchone()
            has_reachable = row is not None

        if reachable_only and has_reachable:
            decl_sql = (
                "SELECT d.id, d.name, d.short_name, d.module_id, d.kind, d.type_sig, "
                "d.body_loc, d.is_bookkeeping, COALESCE(mo.path, '') "
                "FROM declarations d "
                "JOIN metrics m ON m.decl_id = d.id "
                "LEFT JOIN modules mo ON mo.id = d.module_id "
                "WHERE m.reachable = 1 AND d.is_mathlib = 0 "
                "ORDER BY d.id"
            )
        else:
            decl_sql = (
                "SELECT d.id, d.name, d.short_name, d.module_id, d.kind, d.type_sig, "
                "d.body_loc, d.is_bookkeeping, COALESCE(mo.path, '') "
                "FROM declarations d "
                "LEFT JOIN modules mo ON mo.id = d.module_id "
                "WHERE d.is_mathlib = 0 "
                "ORDER BY d.id"
            )

        idx_to_id = array("I")
        id_to_idx: dict[int, int] = {}
        names: list[str] = []
        short_names: list[str] = []
        mod_paths: list[str] = []
        kinds: list[str] = []
        sig_lens = array("I")
        sig_previews: list[str] = []
        node_loc = array("I")
        is_bk = bytearray()

        for (
            did,
            name,
            short_name,
            _mid,
            kind,
            type_sig,
            body_loc,
            bk,
            mpath,
        ) in cur.execute(decl_sql):
            idx = len(idx_to_id)
            did_i = int(did)
            idx_to_id.append(did_i)
            id_to_idx[did_i] = idx
            names.append(name or "")
            short_names.append(short_name or "")
            mod_paths.append(mpath or "")
            kinds.append((kind or "").lower())
            ts = type_sig or ""
            sig_lens.append(len(ts))
            sig_previews.append(ts[:240])
            node_loc.append(max(1, int(body_loc or 0)))
            is_bk.append(1 if bk else 0)

        n = len(idx_to_id)
        if n == 0:
            report = TopologyReport()
            set_meta(conn, "analysis_topology_stats", json.dumps(report.to_dict()))
            set_meta(conn, "analysis_backbone_edges", json.dumps([]))
            conn.commit()
            return report

        # Load deduplicated edges restricted to our dense node set (O(1) dedup via PK order)
        edges: list[tuple[int, int]] = []
        prev_src = -1
        prev_dst = -1
        for src_id, dst_id in cur.execute(
            "SELECT src_id, dst_id FROM edges ORDER BY src_id, dst_id"
        ):
            if src_id == dst_id or (src_id == prev_src and dst_id == prev_dst):
                continue
            prev_src = src_id
            prev_dst = dst_id
            u = id_to_idx.get(src_id)
            if u is None:
                continue
            v = id_to_idx.get(dst_id)
            if v is None:
                continue
            edges.append((u, v))

        out_offsets, out_targets, in_offsets, in_targets = build_csr(n, edges)
        edge_count = len(edges)
        del edges

        # 1. Iterative Tarjan SCC
        scc_id, num_sccs = tarjan_scc_iterative(n, out_offsets, out_targets)

        scc_size = array("I", [0]) * num_sccs
        scc_loc = array("Q", [0]) * num_sccs
        for u in range(n):
            c = scc_id[u]
            scc_size[c] += 1
            scc_loc[c] += node_loc[u]

        nontrivial_sccs = sum(1 for sz in scc_size if sz > 1)
        largest_scc = max(scc_size) if num_sccs > 0 else 0

        # 2. Condensed SCC DAG & flow estimation
        dag_out, dag_in = _build_condensed_dag(n, num_sccs, scc_id, out_offsets, out_targets)
        desc_count, desc_loc, anc_count, exact_mode = compute_dag_flow(
            num_sccs,
            dag_out,
            dag_in,
            scc_size,
            scc_loc,
            exact_threshold=exact_flow_threshold,
        )

        # 3. Resolve root indices from meta (or fallback to zero-in-degree nodes)
        root_indices: list[int] = []
        roots_raw = get_meta(conn, "analysis_roots")
        if roots_raw:
            try:
                for item in json.loads(roots_raw):
                    rid = item.get("id") if isinstance(item, dict) else item
                    if rid in id_to_idx:
                        root_indices.append(id_to_idx[rid])
            except Exception:
                pass
        root_set = set(root_indices)

        # 4. Iterative Cooper-Harvey-Kennedy dominator tree
        _idom, dom_depth, dom_count, dom_loc = compute_dominators_chk(
            n,
            root_indices,
            out_offsets,
            out_targets,
            in_offsets,
            in_targets,
            node_loc,
        )

        # 5. Compute bottleneck_score & definition centrality
        scores = array("d", [0.0]) * n
        def_centrality = array("d", [0.0]) * n

        for u in range(n):
            c = scc_id[u]
            in_d = in_offsets[u + 1] - in_offsets[u]
            out_d = out_offsets[u + 1] - out_offsets[u]
            d_loc = float(dom_loc[u])
            ds_loc = float(desc_loc[c])
            an_cnt = float(anc_count[c])
            b_loc = float(node_loc[u])

            # Interface narrowness: concise type signatures score higher
            slen = max(20, sig_lens[u])
            narrowness = 1.0 / math.log2(slen + 16.0)

            encapsulation = math.log1p(d_loc)
            flow = math.log1p(ds_loc) * math.log1p(an_cnt)

            k_w = _KIND_WEIGHTS.get(kinds[u], 0.3)
            bk_w = 0.05 if is_bk[u] else 1.0

            # Boost genuine structural pillars that encapsulate downstream work or bridge flow
            pillar_bonus = 1.0
            if dom_count[u] > 1:
                pillar_bonus += 0.45
            if in_d >= 2 and out_d >= 2:
                pillar_bonus += 0.25
            if u in root_set:
                pillar_bonus += 0.35

            score = bk_w * k_w * narrowness * (0.55 * encapsulation + 0.45 * flow) * pillar_bonus
            scores[u] = round(score, 6)

            if kinds[u] in _DEF_KINDS and not is_bk[u]:
                def_centrality[u] = round(
                    narrowness
                    * (math.log1p(in_d * 4.0) + 0.6 * math.log1p(an_cnt) + 0.4 * math.log1p(d_loc)),
                    6,
                )

        # 6. Persist metrics in fast batches
        upsert_sql = (
            "INSERT INTO metrics "
            "(decl_id, reachable, in_degree, out_degree, scc_id, dominator_depth, bottleneck_score) "
            "VALUES (?, 1, ?, ?, ?, ?, ?) "
            "ON CONFLICT(decl_id) DO UPDATE SET "
            "in_degree = excluded.in_degree, "
            "out_degree = excluded.out_degree, "
            "scc_id = excluded.scc_id, "
            "dominator_depth = excluded.dominator_depth, "
            "bottleneck_score = excluded.bottleneck_score"
        )
        batch: list[tuple[int, int, int, int, int, float]] = []
        for u in range(n):
            batch.append(
                (
                    int(idx_to_id[u]),
                    int(in_offsets[u + 1] - in_offsets[u]),
                    int(out_offsets[u + 1] - out_offsets[u]),
                    int(scc_id[u]),
                    int(dom_depth[u]),
                    float(scores[u]),
                )
            )
            if len(batch) >= batch_size:
                conn.executemany(upsert_sql, batch)
                batch.clear()
        if batch:
            conn.executemany(upsert_sql, batch)
            batch.clear()

        def _node_record(u: int) -> dict[str, Any]:
            c = scc_id[u]
            return {
                "decl_id": int(idx_to_id[u]),
                "name": names[u],
                "short_name": short_names[u],
                "kind": kinds[u],
                "module": mod_paths[u],
                "body_loc": int(node_loc[u]),
                "in_degree": int(in_offsets[u + 1] - in_offsets[u]),
                "out_degree": int(out_offsets[u + 1] - out_offsets[u]),
                "scc_id": int(c),
                "dominator_depth": int(dom_depth[u]),
                "dominated_count": int(dom_count[u]),
                "dominated_loc": int(dom_loc[u]),
                "descendant_count": int(desc_count[c]),
                "descendant_loc": int(desc_loc[c]),
                "ancestor_count": int(anc_count[c]),
                "bottleneck_score": float(scores[u]),
                "is_root": u in root_set,
                "type_sig_preview": sig_previews[u],
            }

        # Top-K bottleneck theorems/lemmas (non-bookkeeping first)
        thm_cands = [u for u in range(n) if kinds[u] in _THM_KINDS and not is_bk[u]]
        if not thm_cands:
            thm_cands = [u for u in range(n) if not is_bk[u]] or list(range(n))
        thm_cands.sort(key=lambda u: (-scores[u], -dom_loc[u], names[u]))
        top_thm_indices = thm_cands[:top_k]

        # Top-K high-centrality definitions
        def_cands = [u for u in range(n) if kinds[u] in _DEF_KINDS and not is_bk[u]]
        def_cands.sort(key=lambda u: (-def_centrality[u], -(in_offsets[u + 1] - in_offsets[u]), names[u]))
        top_def_indices = def_cands[:top_k]

        # Build backbone DAG: roots (up to 10) + top bottlenecks (deduplicated)
        pillar_indices: list[int] = []
        seen_p: set[int] = set()
        for r in root_indices[:10]:
            if r not in seen_p:
                seen_p.add(r)
                pillar_indices.append(r)
        for u in top_thm_indices:
            if u not in seen_p:
                seen_p.add(u)
                pillar_indices.append(u)

        reduced_edges = compute_backbone_dag(pillar_indices, num_sccs, scc_id, dag_out)

        backbone_nodes = [_node_record(u) for u in pillar_indices]
        backbone_edges = [
            {
                "src_id": int(idx_to_id[u]),
                "src_name": names[u],
                "dst_id": int(idx_to_id[v]),
                "dst_name": names[v],
            }
            for u, v in reduced_edges
        ]

        top_defs_records = []
        for u in top_def_indices:
            rec = _node_record(u)
            rec["centrality"] = float(def_centrality[u])
            top_defs_records.append(rec)

        report = TopologyReport(
            node_count=n,
            edge_count=edge_count,
            scc_count=num_sccs,
            nontrivial_scc_count=nontrivial_sccs,
            largest_scc_size=int(largest_scc),
            max_dominator_depth=int(max(dom_depth)) if n > 0 else 0,
            exact_flow_mode=exact_mode,
            top_bottlenecks=[_node_record(u) for u in top_thm_indices],
            top_definitions=top_defs_records,
            backbone_nodes=backbone_nodes,
            backbone_edges=backbone_edges,
        )

        set_meta(conn, "analysis_topology_stats", json.dumps(report.to_dict()))
        set_meta(conn, "analysis_backbone_edges", json.dumps(backbone_edges))
        conn.commit()
        return report
    finally:
        if should_close:
            conn.close()
