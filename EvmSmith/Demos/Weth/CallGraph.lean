import Lean
import EvmSmith.Demos.Weth.Solvency

/-!
# Call-graph extractor for `weth_solvency_invariant`

Walks the proof term of `EvmSmith.Weth.weth_solvency_invariant` and
emits a mermaid `graph TD` block to stdout. Edges are filtered to
**theorems / axioms only**, declared in our framework / Weth modules
(`EvmYul.Frame`, `EvmSmith.Demos.Weth`, `EvmSmith.Lemmas`). The upstream
EVM semantics, Mathlib, Batteries, match-elaborator artifacts, and
plain definitions are pruned away — what's left is the proof's
mathematical dependency tree.

Run with `lake exe weth-call-graph > /tmp/graph.md`, then inspect or
splice the mermaid block into `REPORT_WETH.md`.
-/

open Lean

namespace EvmSmith.Weth.CallGraph

/-- Module-name allowlist: keep an edge `caller → callee` only when
`callee` is declared in one of our framework modules. -/
private def keepModule (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "EvmYul.Frame" ||
  s.startsWith "EvmSmith.Demos.Weth" ||
  s.startsWith "EvmSmith.Lemmas"

private def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.allImportedModuleNames[idx.toNat]?

/-- Names ending in compiler-generated suffixes (match elaborator,
equation compiler, structure projections, recursors). Skipped. -/
private def isAutogen (n : Name) : Bool :=
  let s := n.toString
  s.endsWith ".rec" ||
  s.endsWith ".recOn" ||
  s.endsWith ".casesOn" ||
  s.endsWith ".noConfusion" ||
  s.endsWith ".sizeOf_spec" ||
  -- match_N, _eq_N, _splitter, _proof_N, _unsafe_rec, _hyg_N, etc.
  (s.splitOn "." |>.any fun part =>
    part.startsWith "match_" ||
    part.startsWith "_eq_" ||
    part.startsWith "_splitter" ||
    part.startsWith "_proof_" ||
    part.startsWith "_unsafe_rec" ||
    part.endsWith "_splitter")

/-- Keep only theorems and axioms — not definitions, structure projections,
inductive constructors, etc. The proof tree we want to display is the
*mathematical* dependency tree. -/
private def isTheoremLike (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _)    => true
  | some (.axiomInfo _)  => true
  | _                    => false

/-- Theorem-or-axiom that lives in one of our framework modules and
isn't compiler-generated. Nodes we want to *display* in the graph. -/
private def isShownNode (env : Environment) (n : Name) : Bool :=
  !isAutogen n &&
  isTheoremLike env n &&
  (match moduleOf? env n with
   | some m => keepModule m
   | none   => false)

/-- Direct constant dependencies of `n`'s proof / value term. -/
private def depsOf (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | some ci =>
    match ci.value? with
    | some v => v.getUsedConstantsAsSet
    | none   => {}
  | none => {}

/-- Compute the set of *theorem* descendants reachable from `start`
through any chain of constants (skipping over non-theorem nodes like
definitions, structure projections, match elaborator artifacts). -/
private partial def reachableTheorems
    (env : Environment) (start : Name) : NameSet := Id.run do
  let mut found : NameSet := {}
  let mut visited : NameSet := {}
  let mut queue : Array Name := #[start]
  while h : queue.size > 0 do
    let n := queue.back
    queue := queue.pop
    if visited.contains n then continue
    visited := visited.insert n
    for d in depsOf env n do
      if isShownNode env d then
        found := found.insert d
        -- Don't recurse — `collectEdges`'s outer loop handles each
        -- theorem's own descendants.
      else if !visited.contains d then
        queue := queue.push d
  return found

/-- Build the edge list, bounded by depth (BFS). For each theorem
reachable from `root` within `maxDepth` levels, draw direct edges to
its theorem descendants (skipping intermediate non-theorem nodes).
A node at depth = `maxDepth` is included but its children are not. -/
private partial def collectEdges
    (env : Environment) (root : Name) (maxDepth : Nat) :
    Array (Name × Name) := Id.run do
  let mut edges : Array (Name × Name) := #[]
  let mut visited : NameSet := {}
  -- Queue of (node, depth-from-root). Iterate FIFO for true BFS.
  let mut queue : Array (Name × Nat) := #[(root, 0)]
  while h : queue.size > 0 do
    let (n, depth) := queue[0]!
    queue := queue.eraseIdx 0
    if visited.contains n then continue
    visited := visited.insert n
    if depth ≥ maxDepth then continue
    let children := reachableTheorems env n
    for d in children do
      edges := edges.push (n, d)
      if !visited.contains d then
        queue := queue.push (d, depth + 1)
  return edges

/-- Strip Lean's `_private.<module>.<hash>.` mangling from a name's
string form, leaving the user-visible name. -/
private def stripPrivate (s : String) : String :=
  if s.startsWith "_private." then
    -- Drop "_private." prefix, then drop the next "<module>.<hash>."
    -- segments. Lean's mangling is `_private.<Module.Path>.<N>.<Real.Name>`
    -- where `<N>` is a digit; strip up through the first all-digit segment.
    let after := s.drop "_private.".length
    let parts := after.splitOn "."
    let rec go : List String → List String
      | [] => []
      | x :: xs =>
        if x.all Char.isDigit then xs
        else go xs
    ".".intercalate (go parts)
  else s

/-- Mermaid-safe id: replace dots with underscores. -/
private def mermaidId (n : Name) : String :=
  (stripPrivate n.toString).replace "." "_"

/-- Short label: the last component of the (de-privated) name. -/
private def shortLabel (n : Name) : String :=
  let s := stripPrivate n.toString
  let parts := s.splitOn "."
  parts.getLast!

/-- Group prefix for colouring: which module bucket a constant belongs to. -/
private def bucket (env : Environment) (n : Name) : String :=
  match moduleOf? env n with
  | some m =>
    let s := m.toString
    if s.startsWith "EvmSmith.Demos.Weth" then "weth"
    else if s.startsWith "EvmYul.Frame" then "frame"
    else if s.startsWith "EvmSmith.Lemmas" then "lemma"
    else "other"
  | none => "other"

/-- Emit the mermaid graph to stdout, BFS-bounded by `maxDepth`. -/
def emit (env : Environment) (root : Name) (maxDepth : Nat := 4) : IO Unit := do
  let edges := collectEdges env root maxDepth
  let nodes := ((#[root] ++ edges.flatMap fun (a, b) => #[a, b])).toList.eraseDups
  IO.println "```mermaid"
  IO.println "graph TD"
  -- Node declarations with labels (shortened) + class assignment.
  for n in nodes do
    IO.println s!"  {mermaidId n}[\"{shortLabel n}\"]:::{bucket env n}"
  -- Edges.
  for (a, b) in edges do
    IO.println s!"  {mermaidId a} --> {mermaidId b}"
  -- Classes for visual grouping.
  IO.println "  classDef weth fill:#e3f2fd,stroke:#1565c0;"
  IO.println "  classDef frame fill:#fff3e0,stroke:#ef6c00;"
  IO.println "  classDef lemma fill:#f3e5f5,stroke:#6a1b9a;"
  IO.println "  classDef other fill:#eeeeee,stroke:#616161;"
  IO.println "```"

end EvmSmith.Weth.CallGraph

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `EvmSmith.Demos.Weth.Solvency }]
    Options.empty
    (loadExts := true)
  -- Usage: weth-call-graph [<root-name>] [<max-depth>]
  let root : Name :=
    match args with
    | s :: _ => s.toName
    | []     => `EvmSmith.Weth.weth_solvency_invariant
  let maxDepth : Nat :=
    match args with
    | _ :: d :: _ => d.toNat?.getD 4
    | _           => 4
  EvmSmith.Weth.CallGraph.emit env root maxDepth
