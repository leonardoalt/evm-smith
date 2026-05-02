import EvmYul.EVM.Semantics
import EvmYul.Semantics

/-!
# EvmSmith — a framework for AI-generated EVM bytecode and safety proofs

This module is the thin core of the framework. It gives you:

* `mkState` — build a fresh `EVM.State` with an initial stack.
* `withCalldata` — set the calldata on any state.
* `withSelfAccount` — install a default account at `codeOwner` so
  SSTORE has a target (without it SSTORE silently no-ops).
* `runOp` / `runOpFull` — execute a single opcode (pure-semantics / full driver).
* `Program`, `runSeq` — sequence multiple opcodes.
* `topOf`, `stackOf` — small lenses for inspecting a post-state.
* `addressSlot`, `storageAt` — helpers for inspecting account storage
  (matches the EVM's "empty = 0" convention).

The intended use: write an EVM bytecode program as a `Program` value, run it
against an `EVM.State` to demonstrate behavior, and state/prove safety
properties against the upstream semantics from `NethermindEth/EVMYulLean`.
See `EvmSmith/Demos/Add3/` for a single-block worked example;
`EvmSmith/Demos/Register/` and `EvmSmith/Demos/Weth/` for full
cross-transaction proofs via the EVMYulLean Frame library.
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

/-- Insert a default `Account` at `s.executionEnv.codeOwner`. SSTORE
    short-circuits to a no-op when its codeOwner has no entry in
    `accountMap` (`lookupAccount Iₐ |>.option self ...`), so executing
    storage-writing programs from a fresh `mkState` requires this. -/
def withSelfAccount (s : EVM.State) : EVM.State :=
  { s with accountMap := s.accountMap.insert s.executionEnv.codeOwner default }

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

/-- An EVM account address used as a storage key — mapped to the
    `UInt256` slot index matching what `CALLER` pushes onto the stack
    (zero-extension of the 20-byte address to 32 bytes). -/
def addressSlot (a : AccountAddress) : UInt256 := UInt256.ofNat a.val

/-- `storageAt s a slot` returns the value at `slot` in `a`'s storage,
    or `⟨0⟩` if the account doesn't exist / the slot is unset. Matches
    the EVM's "empty = 0" convention; consistent with
    `Account.updateStorage`'s erase-on-zero behaviour so that
    `findD` gives 0 for both "absent slot" and "slot explicitly 0". -/
def storageAt (s : EVM.State) (a : AccountAddress) (slot : UInt256) : UInt256 :=
  (s.accountMap.find? a).elim ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)

/-- A program is a sequence of `(opcode, optional push-arg)` pairs. -/
abbrev Program := List (Operation .EVM × Option (UInt256 × Nat))

/-- Execute a `Program` by stepping via `runOp`, threading state through `Except`. -/
def runSeq : Program → EVM.State → Except EVM.ExecutionException EVM.State
  | [], s => .ok s
  | (op, arg) :: rest, s => do
      let s' ← runOp op s arg
      runSeq rest s'

end EvmSmith
