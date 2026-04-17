import EvmSmith.Framework
import EvmSmith.Demos.Add3.Program

/-!
# IO demos — shows the framework in action

Each `demo*` prints an expected result to stdout. `EvmSmith/Demos/Main.lean`
calls them all from `main`, so `lake exe evm-smith` is the one-command
smoke test.
-/

namespace EvmSmith
open EvmYul EvmYul.EVM

/-- ADD: 3 + 4 = 7 on top of stack. -/
def demoAdd : IO Unit := do
  let pre  := mkState (stack := [UInt256.ofNat 3, UInt256.ofNat 4])
  let post := runOp .ADD pre
  IO.println s!"ADD: top = {topOf post}"

/-- PUSH1 42 onto empty stack. -/
def demoPush : IO Unit := do
  let pre  := mkState (stack := [])
  let post := runOp (.Push .PUSH1) pre (arg := some (UInt256.ofNat 42, 1))
  IO.println s!"PUSH1 42: top = {topOf post}"

/-- DUP1 duplicates the top. -/
def demoDup : IO Unit := do
  let pre  := mkState (stack := [UInt256.ofNat 7, UInt256.ofNat 8])
  let post := runOp .DUP1 pre
  let printedStack :=
    match stackOf post with
    | some s => toString (s.map UInt256.toNat)
    | none   => "<error>"
  IO.println s!"DUP1: stack = {printedStack}"

/-- Parity between the pure `runOp` (via `EvmYul.step`) and the full
    `runOpFull` (via `EVM.step`). They must agree on `.stack`. -/
def demoParity : IO Unit := do
  let pre := mkState (stack := [UInt256.ofNat 3, UInt256.ofNat 4])
  let a := (runOp .ADD pre).toOption.map (·.stack.map UInt256.toNat)
  let b := (runOpFull .ADD pre).toOption.map (·.stack.map UInt256.toNat)
  IO.println s!"parity: runOp stack = {a}"
  IO.println s!"parity: runOpFull stack = {b}"
  IO.println s!"parity stacks match? {a == b}"

/-- End-to-end demo of the `add3` bytecode: construct 96-byte calldata
    from three UInt256 values, run the full program (ADD prefix + MSTORE +
    RETURN), and check the returned 32 bytes decode to `a + b + c`. -/
def demoAdd3 : IO Unit := do
  let run (a b c : Nat) : IO Unit := do
    let av := UInt256.ofNat a
    let bv := UInt256.ofNat b
    let cv := UInt256.ofNat c
    let cd := av.toByteArray ++ bv.toByteArray ++ cv.toByteArray
    let s0 := withCalldata (mkState []) cd
    match runSeq Add3.program s0 with
    | .ok s =>
        let returned := (uInt256OfByteArray s.H_return).toNat
        let ok := returned == a + b + c
        IO.println s!"add3({a}, {b}, {c}) → {returned} (expected {a + b + c}, ok? {ok})"
    | .error e =>
        IO.println s!"add3({a}, {b}, {c}) → error {repr e}"
  run 1 2 3
  run 10 20 30
  run 100 200 300
  run 0 0 0

end EvmSmith
