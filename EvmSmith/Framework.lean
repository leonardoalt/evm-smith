import EvmYul.EVM.Semantics
import EvmYul.Semantics

/-!
# EvmSmith — a framework for AI-generated EVM bytecode and safety proofs

This module is the thin core of the framework. It gives you:

* `mkState` — build a fresh `EVM.State` with an initial stack.
* `withCalldata` — set the calldata on any state.
* `runOp` / `runOpFull` — execute a single opcode (pure-semantics / full driver).
* `Program`, `runSeq` — sequence multiple opcodes.
* `topOf`, `stackOf` — small lenses for inspecting a post-state.

The intended use: write an EVM bytecode program as a `Program` value, run it
against an `EVM.State` to demonstrate behavior, and state/prove safety
properties against the upstream semantics from `NethermindEth/EVMYulLean`.
See `EvmSmith/Add3.lean` + `EvmSmith/Add3Proofs.lean` for a worked example.
-/

namespace EvmSmith
open EvmYul EVM

/-- A fresh `EVM.State` with the given initial stack; everything else defaulted. -/
def mkState (stack : Stack UInt256 := []) : EVM.State :=
  { (default : EVM.State) with stack := stack }

/-- Set the calldata on an `EVM.State`. -/
def withCalldata (s : EVM.State) (cd : ByteArray) : EVM.State :=
  { s with toState :=
    { s.toState with executionEnv :=
      { s.toState.executionEnv with calldata := cd } } }

/-- Run one EVM opcode on a state using the pure semantics layer (`EvmYul.step`).
    No fuel, no gas, no `execLength` bump. Post-state differs from pre-state only
    in `stack` and `pc` (and per-opcode effects). -/
def runOp (op : Operation .EVM) (s : EVM.State)
    (arg : Option (UInt256 × Nat) := .none) :
    Except EVM.ExecutionException EVM.State :=
  EvmYul.step op arg s

/-- Run one EVM opcode through the full driver (`EVM.step`) with `fuel := 1`,
    `gasCost := 0`. Produces the same `.stack` / `.pc` as `runOp` but also bumps
    `execLength` and deducts 0 from `gasAvailable`. -/
def runOpFull (op : Operation .EVM) (s : EVM.State)
    (arg : Option (UInt256 × Nat) := .none) :
    Except EVM.ExecutionException EVM.State :=
  EVM.step (fuel := 1) (gasCost := 0) (instr := .some (op, arg)) s

/-- Top of the stack of a post-state, if present. -/
def topOf : Except EVM.ExecutionException EVM.State → Option UInt256
  | .ok s => s.stack.head?
  | .error _ => .none

/-- Stack of a post-state, if present. -/
def stackOf : Except EVM.ExecutionException EVM.State → Option (Stack UInt256)
  | .ok s => some s.stack
  | .error _ => none

/-- A program is a sequence of `(opcode, optional push-arg)` pairs. -/
abbrev Program := List (Operation .EVM × Option (UInt256 × Nat))

/-- Execute a `Program` by stepping via `runOp`, threading state through `Except`. -/
def runSeq : Program → EVM.State → Except EVM.ExecutionException EVM.State
  | [], s => .ok s
  | (op, arg) :: rest, s => do
      let s' ← runOp op s arg
      runSeq rest s'

end EvmSmith
