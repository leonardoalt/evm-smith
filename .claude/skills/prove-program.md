---
name: prove-program
description: Prove correctness of an EVM bytecode program in the evm-smith repo. Writes `EvmSmith/Demos/<Name>/Proofs.lean` that chains the per-opcode step lemmas from `EvmSmith.Lemmas` via `runSeq_cons_ok` into a single end-to-end theorem about the program's effect on the stack. Use after the `add-program` skill.
---

# Proving a program correct

The proof pattern in this repo (see `EvmSmith/Demos/Add3/Proofs.lean`):

1. Take a hypothetical initial state `s0 : EVM.State` plus assumptions
   about what it contains (stack empty, calldata readable, storage set,
   etc.).
2. Use per-opcode step lemmas from `EvmSmith.Lemmas` to compute the
   post-state of each opcode as a named `have`.
3. Chain them via `runSeq_cons_ok` to collapse the program-level
   `runSeq` call into a single equation.
4. Normalise the final state shape (arithmetic simplifications,
   `Except.map` peeling, `Option.some` unwrapping) and close.

## Skeleton

```lean
import EvmSmith.Lemmas
import EvmSmith.Demos.<Name>.Program

/-! # Correctness of the <name> program

    Statement of what we prove and (crucially) what we DON'T — e.g. any
    byte-level claims about `H_return` cannot be proved because
    `ffi.ByteArray.zeroes` is opaque. Be explicit.
-/

namespace EvmSmith.<Name>Proofs
open EvmYul EvmYul.EVM EvmSmith

theorem program_correct
    (s0 : EVM.State)
    -- ... parameters (symbolic inputs): a b c : UInt256, etc.
    (hs : s0.stack = [])
    -- ... hypotheses about calldata / storage / memory:
    -- (h0 : EvmYul.State.calldataload s0.toState (UInt256.ofNat 0) = a)
    -- ...
    : (runSeq <Name>.program s0).map (·.stack.head?)
        = .ok (some <expected>) := by
  -- Normalise s0 so the step lemmas apply:
  have hs0 : s0 = { s0 with stack := [], pc := s0.pc } := by
    cases s0; cases hs; rfl

  -- One `have` per opcode, computing its post-state.
  have e1 : runOp <opcode> <state> <arg> = .ok <post-state> := by
    rw [hs0]; exact <lemma from EvmSmith.Lemmas> …
  have e2 : runOp <opcode> <post1> <arg> = .ok <post2> := by
    rw [runOp_calldataload]; simp [<hypothesis>]
  -- … continue …

  -- Chain them:
  show (runSeq <Name>.program s0).map _ = _
  simp only [<Name>.program]
  rw [runSeq_cons_ok _ _ _ _ _ e1]
  rw [runSeq_cons_ok _ _ _ _ _ e2]
  -- …

  -- Peel the final result:
  simp only [runSeq, Except.map, List.head?]

  -- Arithmetic cleanup (e.g. c + (b + a) = a + b + c):
  -- congr 1; congr 1; unfold UInt256.add; congr 1; abel_nf

end EvmSmith.<Name>Proofs
```

## Mechanics that trip people up

- **The per-opcode lemmas require concrete stack shape.** They're
  stated as `runOp <op> { s with stack := <cons pattern>, pc := <pc> }
  = …`. Your `have` equations must match this literally — use the
  `hs0 : s0 = { s0 with stack := [], pc := s0.pc }` rewrite so `s0`'s
  shape is literally `{ s with stack := [], pc := … }` for the first
  step. After that, every step produces a state in the right shape
  because the lemmas output structure-update syntax.
- **`toState` is preserved by stack/pc updates.** The `toState_update`
  simp lemma (in `EvmSmith.Lemmas`, tagged `@[simp]`) ensures
  `{ s0 with stack := …, pc := … }.toState = s0.toState`, so
  calldata/storage hypotheses about `s0.toState` continue to apply
  after every step.
- **`runSeq` uses do-notation that `simp` struggles to iota-reduce**
  through. Use `runSeq_cons_ok` (the fusion lemma) instead — it's
  specifically written to sidestep that.
- **Byte-level round-trips go through opaque FFI.** `MSTORE` + `RETURN`
  writes `val.toByteArray` to memory then reads it back via
  `readWithPadding`. Both halves call `ffi.ByteArray.zeroes`, an
  `opaque` declaration. You cannot prove `H_return = val.toByteArray`
  without axiomatising the FFI. Prove the stack-level property
  instead. See `EvmSmith/Demos/Add3/Proofs.lean` for the canonical
  statement of this limitation.

## Storage-using programs

If the program uses `SSTORE` / `SLOAD` / `MSTORE` / `MLOAD`, the post-state
has mutated fields other than stack/pc. Some patterns worth knowing:

- **`hacct` precondition.** `SSTORE` is a silent no-op if the code owner
  account doesn't exist in `accountMap` (see `EvmYul/StateOps.lean:159 —
  lookupAccount Iₐ |>.option self ...`). Any theorem about what `SSTORE`
  wrote needs `hacct : s0.accountMap.find? s0.executionEnv.codeOwner =
  some acc` as a hypothesis. The Foundry test harness satisfies this
  trivially by calling `vm.etch` on the code-owner address.

- **Prefer account-level statements over slot-level.** For storage
  programs, a theorem like
  "`(postState s0 x).accountMap.find? codeOwner = some
  (acc.updateStorage sender x)`" is **cleanly provable** with the
  existing Batteries API (via `sstore_accountMap` from
  `EvmSmith.Lemmas` + `find?_insert_of_eq`). A surface-level restatement
  "`storageAt postState codeOwner (addressSlot sender) = x`" requires
  `Std.LawfulOrd UInt256` (not registered anywhere) plus RBMap `erase`
  lemmas (missing from Batteries). Stick to account-level claims unless
  you're prepared to prove the infrastructure; see
  `.claude/batteries-wishlist.md` for what's needed upstream.

- **`storageAt` helper** in `EvmSmith/Framework.lean` gives a safe
  `.find? a |>.elim ⟨0⟩ (·.storage.findD k ⟨0⟩)` lookup that matches
  the EVM's "absent key = 0" convention and the `Account.updateStorage`
  "writing 0 erases the slot" quirk in one go.

- **Substate frame is deliberately excluded.** `SSTORE` mutates
  `substate.refundBalance` and `substate.accessedStorageKeys`. Frame
  theorems should state themselves over `accountMap` only and note
  that substate *does* change, so no one accidentally strengthens the
  theorem to `sf.toState = s0.toState`.

- **See the worked example** at `EvmSmith/Demos/Register/Proofs.lean`
  for the full pattern.

## Minimum-hypotheses principle

A theorem about `postState s0 x` (a pure definition) typically doesn't
need the runtime hypotheses `s0.stack = []` or the calldata hypothesis.
Only the theorem that connects `runSeq program s0` to `postState s0 x`
needs those. Drop unused hypotheses from theorem signatures — if you
find yourself writing `let _ := hs` to silence unused-variable
warnings, the hypothesis shouldn't be there in the first place.

## What to prove

Good targets for program safety theorems:

1. **Functional correctness** — "given inputs with these properties,
   the stack top / memory / storage after the program is `f(inputs)`".
   This is the headline theorem.
2. **Error-freeness** — "given these preconditions, the program does
   not error out." Often falls out as a side-effect of proving (1).
3. **Invariants** — "for every intermediate state, stack size stays
   bounded / storage slot X is never written / PC stays in range."
4. **Peephole equivalence** — "this sequence of opcodes produces the
   same stack effect as this simpler sequence." The soundness
   statement for a compiler optimization. See `push_push_add_peephole`
   in `EvmSmith/Demos/DemoProofs.lean`.

## If the proof doesn't close

See the `debug-proof` skill for common failure modes
(whnf timeout, match not reducing, calldata hypotheses not firing,
etc.).
