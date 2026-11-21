import Lean
import Lean.Util.CollectAxioms

open Lean Meta

namespace ExtractDag

private def coreRoots : Array Name :=
  #[`Init, `Std, `Lean, `Mathlib, `Batteries, `Qq, `Aesop, `ProofWidgets, `ImportGraph, `Lake]

private def isMathlibOrCoreName (n : Name) : Bool :=
  coreRoots.contains n.getRoot

private def getModuleName (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx =>
    if h : idx.toNat < env.header.moduleNames.size then
      (env.header.moduleNames[idx.toNat]'h).toString
    else
      ""
  | none =>
    if env.contains n then env.header.mainModule.toString else ""

private def isMathlibOrCore (env : Environment) (n : Name) : Bool :=
  let modStr := getModuleName env n
  if !modStr.isEmpty then
    let modRoot := Name.mkSimple (modStr.splitOn "." |>.headD "")
    if coreRoots.contains modRoot then true else isMathlibOrCoreName n
  else
    isMathlibOrCoreName n

private def constKindString : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

/-- Count unique subexpressions (DAG size) iteratively to handle heavily shared proof terms fast. -/
private def exprDagSize (root : Expr) (maxNodes : Nat := 250000) : Nat := Id.run do
  let mut visited : Std.HashSet Expr := {}
  let mut stack : Array Expr := #[root]
  while !stack.isEmpty && visited.size < maxNodes do
    let e := stack.back!
    stack := stack.pop
    if visited.contains e then
      continue
    visited := visited.insert e
    match e with
    | .app f a =>
      stack := stack.push f
      stack := stack.push a
    | .lam _ t b _ =>
      stack := stack.push t
      stack := stack.push b
    | .forallE _ t b _ =>
      stack := stack.push t
      stack := stack.push b
    | .letE _ t v b _ =>
      stack := stack.push t
      stack := stack.push v
      stack := stack.push b
    | .mdata _ b =>
      stack := stack.push b
    | .proj _ _ s =>
      stack := stack.push s
    | _ => pure ()
  return visited.size

private def dedupNames (arr : Array Name) (selfName : Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out : Array Name := #[]
  for n in arr do
    if n != selfName && !seen.contains n then
      seen := seen.insert n
      out := out.push n
  return out

private def prettyType (env : Environment) (e : Expr) : IO String := do
  let coreCtx : Core.Context := {
    fileName := "<extract_dag>"
    fileMap := default
  }
  let coreState : Core.State := { env := env }
  let metaM : MetaM String := do
    let fmt ← Meta.ppExpr e
    return fmt.pretty 100
  match ← (metaM.run' {} {}).toIO coreCtx coreState |>.toBaseIO with
  | .ok (s, _) => return s
  | .error _ => return toString e

private def collectAxiomNames (env : Environment) (n : Name) : IO (Array Name) := do
  let coreCtx : Core.Context := {
    fileName := "<extract_dag>"
    fileMap := default
  }
  let coreState : Core.State := { env := env }
  let act : CoreM (Array Name) := Lean.collectAxioms n
  match ← act.toIO coreCtx coreState |>.toBaseIO with
  | .ok (axs, _) => return axs
  | .error _ => return #[]

private def findDoc (env : Environment) (n : Name) : IO (Option String) := do
  match ← (Lean.findDocString? env n).toBaseIO with
  | .ok doc => return doc
  | .error _ => return none

private def constValue? : ConstantInfo → Option Expr
  | .thmInfo v    => some v.value
  | .defnInfo v   => some v.value
  | .opaqueInfo v => some v.value
  | _             => none

private def buildRecordJson (env : Environment) (n : Name) (cinfo : ConstantInfo) : IO Json := do
  let modName := getModuleName env n
  let mathlib := isMathlibOrCore env n
  let kindStr := constKindString cinfo
  let typeStr ← prettyType env cinfo.type
  let typeDeps := dedupNames cinfo.type.getUsedConstants n
  let (valDeps, proofSize) :=
    match constValue? cinfo with
    | some v => (dedupNames v.getUsedConstants n, exprDagSize v)
    | none   => (#[], 0)
  let axioms ← collectAxiomNames env n
  let doc? ← findDoc env n
  let mut fields : List (String × Json) := [
    ("name", Json.str n.toString),
    ("module", Json.str modName),
    ("kind", Json.str kindStr),
    ("type", Json.str typeStr),
    ("proof_term_size", Json.num proofSize),
    ("is_mathlib", Json.bool mathlib),
    ("axioms", Json.arr (axioms.map (fun a => Json.str a.toString))),
    ("type_deps", Json.arr (typeDeps.map (fun d => Json.str d.toString))),
    ("value_deps", Json.arr (valDeps.map (fun d => Json.str d.toString)))
  ]
  if let some d := doc? then
    fields := fields ++ [("docstring", Json.str d)]
  return Json.mkObj fields

private def parseName (s : String) : Name :=
  (s.splitOn ".").foldl (fun acc seg => Name.str acc seg) Name.anonymous

/-- Built-in mini theorems for `--self-test` verification without external Mathlib. -/
def demoHelper (n : Nat) : Nat := n + 0

theorem demoHelper_eq (n : Nat) : demoHelper n = n := by
  simp [demoHelper]

/-- Self-test target theorem exercising type, value, and helper dependencies. -/
theorem demoTheorem (a b : Nat) : demoHelper a + demoHelper b = a + b := by
  rw [demoHelper_eq, demoHelper_eq]

private structure Config where
  modules : Array Name := #[]
  roots : Array Name := #[]
  outPath : Option String := none
  includeMathlib : Bool := false
  selfTest : Bool := false

private def parseArgs (args : List String) : Except String Config :=
  go args {}
where
  go : List String → Config → Except String Config
    | [], cfg => .ok cfg
    | "--module" :: m :: rest, cfg =>
      go rest { cfg with modules := cfg.modules.push (parseName m) }
    | "--root" :: r :: rest, cfg =>
      go rest { cfg with roots := cfg.roots.push (parseName r) }
    | "--out" :: p :: rest, cfg =>
      go rest { cfg with outPath := some p }
    | "--include-mathlib" :: rest, cfg =>
      go rest { cfg with includeMathlib := true }
    | "--self-test" :: rest, cfg =>
      go rest { cfg with selfTest := true }
    | "-h" :: _, _ | "--help" :: _, _ =>
      .error "usage"
    | flag :: _, _ =>
      .error s!"Unknown or incomplete argument: {flag}"

private def usage : String :=
  "Usage: extract_dag --module <Mod> [--module <Mod2> ...] --root <Const> [--root <Const2> ...] [--out <file.jsonl>] [--include-mathlib] [--self-test]"

def runExtraction (cfg : Config) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let modules := if cfg.selfTest && cfg.modules.isEmpty then #[`ExtractDag] else cfg.modules
  let roots := if cfg.selfTest && cfg.roots.isEmpty then #[`ExtractDag.demoTheorem] else cfg.roots

  if modules.isEmpty || roots.isEmpty then
    IO.eprintln usage
    return 1

  let imports : Array Import := modules.map (fun m => { module := m })
  let env ← Lean.importModules imports {} (trustLevel := 1024)

  let mut visited : Std.HashSet Name := {}
  let mut queue : Array Name := roots
  let mut lines : Array String := #[]
  let mut qIdx : Nat := 0

  while qIdx < queue.size do
    let n := queue[qIdx]!
    qIdx := qIdx + 1
    if visited.contains n then
      continue
    visited := visited.insert n

    match env.find? n with
    | none =>
      IO.eprintln s!"[extract_dag] warning: constant not found in environment: {n}"
    | some cinfo =>
      let recJson ← buildRecordJson env n cinfo
      lines := lines.push recJson.compress

      let stopHere := (!cfg.includeMathlib) && isMathlibOrCore env n && !roots.contains n
      if !stopHere then
        for d in cinfo.type.getUsedConstants do
          if !visited.contains d then
            queue := queue.push d
        if let some v := constValue? cinfo then
          for d in v.getUsedConstants do
            if !visited.contains d then
              queue := queue.push d

  let payload := String.intercalate "\n" lines.toList ++ (if lines.isEmpty then "" else "\n")
  match cfg.outPath with
  | none | some "-" =>
    IO.print payload
  | some path =>
    IO.FS.writeFile ⟨path⟩ payload
    IO.eprintln s!"[extract_dag] wrote {lines.size} declarations to {path}"
  return 0

end ExtractDag

def main (args : List String) : IO UInt32 := do
  match ExtractDag.parseArgs args with
  | .error "usage" =>
    IO.println ExtractDag.usage
    return 0
  | .error msg =>
    IO.eprintln s!"Error: {msg}"
    IO.eprintln ExtractDag.usage
    return 1
  | .ok cfg =>
    ExtractDag.runExtraction cfg
