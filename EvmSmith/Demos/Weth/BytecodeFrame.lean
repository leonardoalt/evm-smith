import EvmYul.Frame
import EvmSmith.Demos.Weth.Invariant
import EvmSmith.Lemmas.RBMapSum

/-!
# Weth — bytecode-specific Ξ preservation (B2 / §2.x)

This file is the Weth analogue of Register's `BytecodeFrame.lean`. It
collects the Weth-specific lemmas needed to discharge the Ξ closure
obligations consumed by `ΞPreservesInvariantAtC_of_Reachable_general`
(§H.2's entry point) for Weth's bytecode.

§2.3a: `weth_caller_ne_C` (state-local form).

§2.3 + §2.4: the `WethTrace` predicate enumerating Weth's reachable PCs
and the bytecode walk `WethTrace_step_preserves` proving the predicate
is closed under `EVM.step`. -/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame

/-! ## §2.3a — `weth_caller_ne_C` (state-local form)

Per the plan: when Weth's withdraw block reaches the CALL site at
PC 72, the recipient is `AccountAddress.ofUInt256 stack[1]`, i.e.
the value pushed by the CALLER opcode at PC 70.

CALLER pushes `(.ofNat ∘ Fin.val ∘ ExecutionEnv.source)` (see
`EvmYul.Semantics`'s CALLER arm). Round-tripping through
`AccountAddress.ofUInt256` recovers the original sender (since
`AccountAddress.size = 2^160 < 2^256 = UInt256.size`, the embedding
is injective and the round-trip is the identity).

The §H.2 CALL-arm closure obligation requires `recipient ≠ C`.
Combined with the round-trip identity, this reduces to
`s.executionEnv.sender ≠ C` — a hypothesis the consumer
(`weth_solvency_invariant`'s outer wrapper) discharges from the
boundary hypothesis `C ≠ S_T` and the (future) trace-shape induction
that no Weth bytecode path produces a direct `C → C` call.

For now, the §2.3a deliverable is the state-local fact: given that
`stack[1]?` is `some` of a UInt256 that round-trips back to
`s.executionEnv.sender`, the recipient address differs from `C`. -/

/-- **§2.3a structural lemma.** State-local form: if the executionEnv's
sender differs from `C` and `stack[1]?` is `some senderAsUInt256` such
that `AccountAddress.ofUInt256 senderAsUInt256 = sender`, then the
recipient address (`AccountAddress.ofUInt256` of `stack[1]?.getD ⟨0⟩`)
is also `≠ C`.

This is the form that doesn't depend on the (not-yet-defined)
`WethTrace` predicate. Once §2.3 lands, the bytecode-walk consumer
will discharge the `hStack` hypothesis from the trace-shape invariant
that PC 70's CALLER push leaves the sender at `stack[1]?`. -/
theorem weth_caller_ne_C
    (C : AccountAddress) (s : EVM.State)
    (hOuter_ne : s.executionEnv.sender ≠ C)
    (hStack : ∃ x, s.stack[1]? = some x ∧
                   AccountAddress.ofUInt256 x = s.executionEnv.sender) :
    AccountAddress.ofUInt256 (s.stack[1]?.getD ⟨0⟩) ≠ C := by
  obtain ⟨x, hSome, hRound⟩ := hStack
  -- Reduce `getD` of `some x`.
  rw [hSome]
  -- Goal: AccountAddress.ofUInt256 ((some x).getD ⟨0⟩) ≠ C, i.e.
  -- AccountAddress.ofUInt256 x ≠ C. Use the round-trip identity.
  rw [Option.getD_some]
  rw [hRound]
  exact hOuter_ne

/-! ## §2.3 — `WethTrace` predicate

A state `s` is **Weth-traced** at `C` when:
* `C = s.executionEnv.codeOwner`,
* `s.executionEnv.code = bytecode`,
* its `(pc, stack-length)` lies on one of Weth's enumerated valid
  execution states (per the bytecode walk).

Each disjunct lists the PC and the stack length at that PC. JUMPI
branches are enumerated as separate disjuncts (per Plan §3.4 / MI-7).

The "halt" disjuncts at PC 41 (deposit STOP), PC 79 (withdraw STOP),
PC 32* (post-31-REVERT halt), and PC 86 (post-85-REVERT halt) are the
fixed/terminal PCs the X loop never iterates from; STOP keeps the PC
the same (see `step_STOP_at_pc`), REVERT advances by 1 to the
post-REVERT halt PC. The X loop catches REVERT/STOP and exits, so
these states are never re-fed to step, but the closure proof still
must show the post-step state lies in *some* `WethTrace` disjunct.

Note on PC 32: it appears twice — once as the post-REVERT halt with
empty stack (post-31-REVERT) and once as the deposit JUMPDEST entry
with the dispatch selector still on the stack (taken-branch from
PC 16 JUMPI). The two are distinguished by stack length. -/
private def WethTrace (C : AccountAddress) (s : EVM.State) : Prop :=
  C = s.executionEnv.codeOwner ∧
  s.executionEnv.code = bytecode ∧
  -- Dispatch block (PCs 0..31).
  ((s.pc.toNat = 0  ∧ s.stack.length = 0) ∨
   (s.pc.toNat = 2  ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 3  ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 5  ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 6  ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 7  ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 12 ∧ s.stack.length = 3) ∨
   (s.pc.toNat = 13 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 16 ∧ s.stack.length = 3 ∧ s.stack[0]? = some depositLbl) ∨
   (s.pc.toNat = 17 ∧ s.stack.length = 1) ∨   -- JUMPI not-taken
   (s.pc.toNat = 22 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 23 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 26 ∧ s.stack.length = 2 ∧ s.stack[0]? = some withdrawLbl) ∨
   (s.pc.toNat = 27 ∧ s.stack.length = 0) ∨   -- JUMPI not-taken (revert path)
   (s.pc.toNat = 29 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 31 ∧ s.stack.length = 2) ∨
  -- Deposit block (PCs 32..41), entered from PC 16 JUMPI taken.
   (s.pc.toNat = 32 ∧ s.stack.length = 0) ∨   -- post-PC-31-REVERT halt sink
   (s.pc.toNat = 32 ∧ s.stack.length = 1) ∨   -- JUMPDEST entry (selector still)
   (s.pc.toNat = 33 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 34 ∧ s.stack.length = 0) ∨
   (s.pc.toNat = 35 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 36 ∧ s.stack.length = 2 ∧ s.stack[0]? = s.stack[1]?) ∨
   (s.pc.toNat = 37 ∧ s.stack.length = 2 ∧
     ∃ slot oldVal : UInt256,
       s.stack = oldVal :: slot :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot))) ∨
   (s.pc.toNat = 38 ∧ s.stack.length = 3 ∧
     ∃ slot oldVal v : UInt256,
       s.stack = v :: oldVal :: slot :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot))) ∨
   (s.pc.toNat = 39 ∧ s.stack.length = 2 ∧
     ∃ slot oldVal newVal : UInt256,
       s.stack = newVal :: slot :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot))) ∨
   (s.pc.toNat = 40 ∧ s.stack.length = 2 ∧
     ∃ slot oldVal newVal : UInt256,
       s.stack = slot :: newVal :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot))) ∨
   (s.pc.toNat = 41 ∧ s.stack.length = 0) ∨   -- post-SSTORE; STOP next
  -- Withdraw block prefix (PCs 42..60), entered from PC 26 JUMPI taken.
   (s.pc.toNat = 42 ∧ s.stack.length = 0) ∨   -- JUMPDEST
   (s.pc.toNat = 43 ∧ s.stack.length = 0) ∨
   (s.pc.toNat = 45 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 46 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 47 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 48 ∧ s.stack.length = 3 ∧ s.stack[0]? = s.stack[1]?) ∨
   (s.pc.toNat = 49 ∧ s.stack.length = 3 ∧
     ∃ slot oldVal x : UInt256,
       s.stack = oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot))) ∨
   (s.pc.toNat = 50 ∧ s.stack.length = 4 ∧
     ∃ slot oldVal x : UInt256,
       s.stack = x :: oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot))) ∨
   (s.pc.toNat = 51 ∧ s.stack.length = 5 ∧
     ∃ slot oldVal x : UInt256,
       s.stack = oldVal :: x :: oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot))) ∨
   (s.pc.toNat = 52 ∧ s.stack.length = 4 ∧
     ∃ slot oldVal x : UInt256,
       s.stack = UInt256.lt oldVal x :: oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot))) ∨
   (s.pc.toNat = 55 ∧ s.stack.length = 5 ∧
     ∃ slot oldVal x : UInt256,
       s.stack = revertLbl :: UInt256.lt oldVal x :: oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot))) ∨
   (s.pc.toNat = 56 ∧ s.stack.length = 3 ∧
     ∃ slot oldVal x : UInt256,
       s.stack = oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)) ∧
       x.toNat ≤ oldVal.toNat) ∨   -- JUMPI not-taken; LT result was 0 ⇒ x ≤ oldVal
   (s.pc.toNat = 57 ∧ s.stack.length = 4 ∧
     ∃ slot oldVal x : UInt256,
       s.stack = x :: oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)) ∧
       x.toNat ≤ oldVal.toNat) ∨
   (s.pc.toNat = 58 ∧ s.stack.length = 4 ∧
     ∃ slot oldVal x : UInt256,
       s.stack = oldVal :: x :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)) ∧
       x.toNat ≤ oldVal.toNat) ∨
   (s.pc.toNat = 59 ∧ s.stack.length = 3 ∧
     ∃ slot oldVal x : UInt256,
       s.stack = UInt256.sub oldVal x :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)) ∧
       x.toNat ≤ oldVal.toNat) ∨
   (s.pc.toNat = 60 ∧ s.stack.length = 3 ∧
     ∃ slot oldVal x : UInt256,
       s.stack = slot :: UInt256.sub oldVal x :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)) ∧
       x.toNat ≤ oldVal.toNat) ∨
     -- pre-SSTORE [slot; newVal; x]; the cascade exposes
     -- (slot, oldVal=SLOAD slot at C, x=withdrawal amount) with the
     -- bound x ≤ oldVal established by the LT-not-taken at PC 55.
     -- newVal = UInt256.sub oldVal x is the post-SUB result (balance −
     -- x). The cascade is threaded forward from PC 49's SLOAD-strong
     -- result through PCs 49..59 walks.
  -- Withdraw block CALL setup (PCs 61..79).
   -- The post-SSTORE slack is threaded forward from PC 60 (pre-SSTORE
   -- WethInvFr `storageSum ≤ balanceOf` plus the SSTORE-replace law,
   -- using the fact that x ≤ oldVal at PC 60). At every PC in
   -- {61, 63, 65, 67, 69, 70, 71, 72}, the bottom-of-stack residual
   -- `x` (the withdrawal amount) satisfies the slack.
   (s.pc.toNat = 61 ∧ s.stack.length = 1 ∧
     ∃ x : UInt256, s.stack[0]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C) ∨
   (s.pc.toNat = 63 ∧ s.stack.length = 2 ∧
     ∃ x : UInt256, s.stack[1]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C) ∨
   (s.pc.toNat = 65 ∧ s.stack.length = 3 ∧
     ∃ x : UInt256, s.stack[2]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C) ∨
   (s.pc.toNat = 67 ∧ s.stack.length = 4 ∧
     ∃ x : UInt256, s.stack[3]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C) ∨
   (s.pc.toNat = 69 ∧ s.stack.length = 5 ∧
     ∃ x : UInt256, s.stack[4]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C) ∨
   (s.pc.toNat = 70 ∧ s.stack.length = 6 ∧
     ∃ x : UInt256, s.stack[0]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C) ∨
   (s.pc.toNat = 71 ∧ s.stack.length = 7 ∧
     ∃ x : UInt256, s.stack[1]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C) ∨
   (s.pc.toNat = 72 ∧ s.stack.length = 8 ∧
     ∃ x : UInt256, s.stack[2]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C) ∨   -- pre-CALL: gas, to, val=x, ao, as, ro, rs, x
   (s.pc.toNat = 73 ∧ s.stack.length = 2) ∨   -- post-CALL: success, x
   (s.pc.toNat = 74 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 77 ∧ s.stack.length = 3 ∧ s.stack[0]? = some revertLbl) ∨
   (s.pc.toNat = 78 ∧ s.stack.length = 1) ∨   -- JUMPI not-taken
   (s.pc.toNat = 79 ∧ s.stack.length = 0) ∨   -- post-POP; STOP next
  -- Revert tail (PCs 80..85). Two entry shapes at PC=80:
  --   length=3: from PC 55 JUMPI taken (revert-from-LT path).
  --   length=1: from PC 77 JUMPI taken (revert-from-CALL-fail path).
  -- The downstream PUSH1/PUSH1/REVERT chain accumulates length+2 to
  -- length+0 (REVERT pops 2). Both lengths drain to PC=85 with the
  -- same minimum-2-pop requirement; we list both shapes through PC 85.
   (s.pc.toNat = 80 ∧ s.stack.length = 3) ∨
   (s.pc.toNat = 80 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 81 ∧ s.stack.length = 3) ∨
   (s.pc.toNat = 81 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 83 ∧ s.stack.length = 4) ∨
   (s.pc.toNat = 83 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 85 ∧ s.stack.length = 5) ∨
   (s.pc.toNat = 85 ∧ s.stack.length = 3))

/-! ## Decode lemmas: each Weth PC's decoded instruction

`native_decide`-discharged. The PCs map per `Program.lean`'s comment
table. Note PC 31, 85 (REVERT), PC 7, 17 (PUSH4), PC 43, 61, 63, 65,
67, 81, 83 (PUSH1), PC 13, 23, 52, 74 (PUSH2). -/

private theorem decode_bytecode_at_0 :
    decode bytecode (UInt256.ofNat 0)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by native_decide

private theorem decode_bytecode_at_2 :
    decode bytecode (UInt256.ofNat 2)
      = some (.CALLDATALOAD, none) := by native_decide

private theorem decode_bytecode_at_3 :
    decode bytecode (UInt256.ofNat 3)
      = some (.Push .PUSH1, some (UInt256.ofNat 0xe0, 1)) := by native_decide

private theorem decode_bytecode_at_5 :
    decode bytecode (UInt256.ofNat 5) = some (.SHR, none) := by native_decide

private theorem decode_bytecode_at_6 :
    decode bytecode (UInt256.ofNat 6) = some (.DUP1, none) := by native_decide

private theorem decode_bytecode_at_7 :
    decode bytecode (UInt256.ofNat 7)
      = some (.Push .PUSH4, some (depositSelector, 4)) := by native_decide

private theorem decode_bytecode_at_12 :
    decode bytecode (UInt256.ofNat 12) = some (.EQ, none) := by native_decide

private theorem decode_bytecode_at_13 :
    decode bytecode (UInt256.ofNat 13)
      = some (.Push .PUSH2, some (depositLbl, 2)) := by native_decide

private theorem decode_bytecode_at_16 :
    decode bytecode (UInt256.ofNat 16) = some (.JUMPI, none) := by native_decide

private theorem decode_bytecode_at_17 :
    decode bytecode (UInt256.ofNat 17)
      = some (.Push .PUSH4, some (withdrawSelector, 4)) := by native_decide

private theorem decode_bytecode_at_22 :
    decode bytecode (UInt256.ofNat 22) = some (.EQ, none) := by native_decide

private theorem decode_bytecode_at_23 :
    decode bytecode (UInt256.ofNat 23)
      = some (.Push .PUSH2, some (withdrawLbl, 2)) := by native_decide

private theorem decode_bytecode_at_26 :
    decode bytecode (UInt256.ofNat 26) = some (.JUMPI, none) := by native_decide

private theorem decode_bytecode_at_27 :
    decode bytecode (UInt256.ofNat 27)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by native_decide

private theorem decode_bytecode_at_29 :
    decode bytecode (UInt256.ofNat 29)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by native_decide

private theorem decode_bytecode_at_31 :
    decode bytecode (UInt256.ofNat 31) = some (.REVERT, none) := by native_decide

private theorem decode_bytecode_at_32 :
    decode bytecode (UInt256.ofNat 32) = some (.JUMPDEST, none) := by native_decide

private theorem decode_bytecode_at_33 :
    decode bytecode (UInt256.ofNat 33) = some (.POP, none) := by native_decide

private theorem decode_bytecode_at_34 :
    decode bytecode (UInt256.ofNat 34) = some (.CALLER, none) := by native_decide

private theorem decode_bytecode_at_35 :
    decode bytecode (UInt256.ofNat 35) = some (.DUP1, none) := by native_decide

private theorem decode_bytecode_at_36 :
    decode bytecode (UInt256.ofNat 36) = some (.SLOAD, none) := by native_decide

private theorem decode_bytecode_at_37 :
    decode bytecode (UInt256.ofNat 37) = some (.CALLVALUE, none) := by native_decide

private theorem decode_bytecode_at_38 :
    decode bytecode (UInt256.ofNat 38) = some (.ADD, none) := by native_decide

private theorem decode_bytecode_at_39 :
    decode bytecode (UInt256.ofNat 39) = some (.SWAP1, none) := by native_decide

private theorem decode_bytecode_at_40 :
    decode bytecode (UInt256.ofNat 40) = some (.SSTORE, none) := by native_decide

private theorem decode_bytecode_at_41 :
    decode bytecode (UInt256.ofNat 41) = some (.STOP, none) := by native_decide

private theorem decode_bytecode_at_42 :
    decode bytecode (UInt256.ofNat 42) = some (.JUMPDEST, none) := by native_decide

private theorem decode_bytecode_at_43 :
    decode bytecode (UInt256.ofNat 43)
      = some (.Push .PUSH1, some (UInt256.ofNat 4, 1)) := by native_decide

private theorem decode_bytecode_at_45 :
    decode bytecode (UInt256.ofNat 45) = some (.CALLDATALOAD, none) := by native_decide

private theorem decode_bytecode_at_46 :
    decode bytecode (UInt256.ofNat 46) = some (.CALLER, none) := by native_decide

private theorem decode_bytecode_at_47 :
    decode bytecode (UInt256.ofNat 47) = some (.DUP1, none) := by native_decide

private theorem decode_bytecode_at_48 :
    decode bytecode (UInt256.ofNat 48) = some (.SLOAD, none) := by native_decide

private theorem decode_bytecode_at_49 :
    decode bytecode (UInt256.ofNat 49) = some (.DUP3, none) := by native_decide

private theorem decode_bytecode_at_50 :
    decode bytecode (UInt256.ofNat 50) = some (.DUP2, none) := by native_decide

private theorem decode_bytecode_at_51 :
    decode bytecode (UInt256.ofNat 51) = some (.LT, none) := by native_decide

private theorem decode_bytecode_at_52 :
    decode bytecode (UInt256.ofNat 52)
      = some (.Push .PUSH2, some (revertLbl, 2)) := by native_decide

private theorem decode_bytecode_at_55 :
    decode bytecode (UInt256.ofNat 55) = some (.JUMPI, none) := by native_decide

private theorem decode_bytecode_at_56 :
    decode bytecode (UInt256.ofNat 56) = some (.DUP3, none) := by native_decide

private theorem decode_bytecode_at_57 :
    decode bytecode (UInt256.ofNat 57) = some (.SWAP1, none) := by native_decide

private theorem decode_bytecode_at_58 :
    decode bytecode (UInt256.ofNat 58) = some (.SUB, none) := by native_decide

private theorem decode_bytecode_at_59 :
    decode bytecode (UInt256.ofNat 59) = some (.SWAP1, none) := by native_decide

private theorem decode_bytecode_at_60 :
    decode bytecode (UInt256.ofNat 60) = some (.SSTORE, none) := by native_decide

private theorem decode_bytecode_at_61 :
    decode bytecode (UInt256.ofNat 61)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by native_decide

private theorem decode_bytecode_at_63 :
    decode bytecode (UInt256.ofNat 63)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by native_decide

private theorem decode_bytecode_at_65 :
    decode bytecode (UInt256.ofNat 65)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by native_decide

private theorem decode_bytecode_at_67 :
    decode bytecode (UInt256.ofNat 67)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by native_decide

private theorem decode_bytecode_at_69 :
    decode bytecode (UInt256.ofNat 69) = some (.DUP5, none) := by native_decide

private theorem decode_bytecode_at_70 :
    decode bytecode (UInt256.ofNat 70) = some (.CALLER, none) := by native_decide

private theorem decode_bytecode_at_71 :
    decode bytecode (UInt256.ofNat 71) = some (.GAS, none) := by native_decide

private theorem decode_bytecode_at_72 :
    decode bytecode (UInt256.ofNat 72) = some (.CALL, none) := by native_decide

private theorem decode_bytecode_at_73 :
    decode bytecode (UInt256.ofNat 73) = some (.ISZERO, none) := by native_decide

private theorem decode_bytecode_at_74 :
    decode bytecode (UInt256.ofNat 74)
      = some (.Push .PUSH2, some (revertLbl, 2)) := by native_decide

private theorem decode_bytecode_at_77 :
    decode bytecode (UInt256.ofNat 77) = some (.JUMPI, none) := by native_decide

private theorem decode_bytecode_at_78 :
    decode bytecode (UInt256.ofNat 78) = some (.POP, none) := by native_decide

private theorem decode_bytecode_at_79 :
    decode bytecode (UInt256.ofNat 79) = some (.STOP, none) := by native_decide

private theorem decode_bytecode_at_80 :
    decode bytecode (UInt256.ofNat 80) = some (.JUMPDEST, none) := by native_decide

private theorem decode_bytecode_at_81 :
    decode bytecode (UInt256.ofNat 81)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by native_decide

private theorem decode_bytecode_at_83 :
    decode bytecode (UInt256.ofNat 83)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by native_decide

private theorem decode_bytecode_at_85 :
    decode bytecode (UInt256.ofNat 85) = some (.REVERT, none) := by native_decide

/-! ## Withdraw cascade helper predicate

The withdraw block (PCs 42..60) computes `storage[sender] := storage[sender] - x`,
guarded by an LT-not-taken at PC 55 ensuring `x ≤ storage[sender]`. To
discharge `WethPC60CascadeFacts`, the trace at PCs 48..60 needs to
expose:

* the `slot` (sender) on which the SLOAD/SSTORE operates,
* the `oldVal := lookupAccount.option ⟨0⟩ (lookupStorage k=slot)`
  that PC 48's SLOAD-strong wrapper pushes (this collapses to
  `acc.storage.findD slot ⟨0⟩` when `find? C = some acc`),
* the `x` (the requested withdraw amount, originally on the stack),
* the bound `x.toNat ≤ oldVal.toNat` (established at PC 55 JUMPI
  not-taken from PC 51's `LT(oldVal, x) = 0` result),
* the SUB equation `newVal = oldVal - x` (established at PC 58).

`WithdrawCascadeAt s C slot oldVal x` captures the find?/findD/bound
invariants common to PCs 48..60 (the SUB equation is added at PC 58
and threaded through PCs 59, 60 separately). The conjunction of
`WithdrawCascadeAt` with the SUB equation gives the data needed to
discharge `WethPC60CascadeFacts` from the trace. -/

/-- The withdraw cascade's per-state invariant at slot `slot`:
* `s.accountMap.find? C = some acc`, and
* `acc.storage.findD slot ⟨0⟩ = oldVal`, and
* `x.toNat ≤ oldVal.toNat`.

This is the data that PC 48's SLOAD-strong (case-split on `find? C`)
+ PC 51's LT-strong + PC 55's JUMPI-not-taken jointly establish, and
that PCs 56..60 preserve through the non-storage-touching ops. -/
private def WithdrawCascadeAt (s : EVM.State) (C : AccountAddress)
    (slot oldVal x : UInt256) : Prop :=
  ∃ acc : Account .EVM,
    s.accountMap.find? C = some acc ∧
    acc.storage.findD slot ⟨0⟩ = oldVal ∧
    x.toNat ≤ oldVal.toNat

/-! ## Local PC-walk wrapper for SWAP1

`EvmYul.Frame.PcWalk` doesn't expose a `step_SWAP1_at_pc` wrapper, but
Weth's bytecode uses SWAP1 at PCs 39, 57, 59. We mirror the standard
pattern: align `op`/`arg` from `hFetch`+`hDecode` and apply the
underlying `step_SWAP1_shape`. -/

private theorem step_SWAP1_at_pc_local {code : ByteArray} {N : ℕ}
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (expArg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hCode : s.executionEnv.code = code)
    (hpc : s.pc = UInt256.ofNat N)
    (hDecode : decode code (UInt256.ofNat N) = some (.SWAP1, expArg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = hd2 :: hd1 :: tl ∧
    s'.executionEnv = s.executionEnv := by
  have hDec : decode s.executionEnv.code s.pc = some (.SWAP1, expArg) := by
    rw [hCode, hpc]; exact hDecode
  obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
  subst hOp; subst hArg
  exact step_SWAP1_shape s s' f' cost arg hd1 hd2 tl hStk hStep

/-! ## Helpers

`pc_eq_ofNat_of_toNat` lifts the `s.pc.toNat = n` hypothesis into
`s.pc = UInt256.ofNat n` for `n < 256` (every Weth PC fits). -/

/-- A trace state `s` always has `s.pc` equal to `UInt256.ofNat n` for
its declared `n` (since `pc.toNat = n` and `n < 256 < UInt256.size`). -/
private theorem pc_eq_ofNat_of_toNat
    (s : EVM.State) (n : ℕ) (hn : n < 256)
    (h : s.pc.toNat = n) :
    s.pc = UInt256.ofNat n :=
  EvmYul.Frame.pc_eq_ofNat_of_toNat s n (by unfold UInt256.size; omega) h

/-- For nats `a, b < UInt256.size` whose sum is also `< UInt256.size`,
the toNat of `UInt256.ofNat a + UInt256.ofNat b` equals `a + b`. -/
private theorem ofNat_add_ofNat_toNat
    (a b : ℕ) (ha : a < UInt256.size) (hb : b < UInt256.size)
    (hab : a + b < UInt256.size) :
    (UInt256.ofNat a + UInt256.ofNat b).toNat = a + b := by
  show (UInt256.ofNat a + UInt256.ofNat b).val.val = a + b
  rw [show (UInt256.ofNat a + UInt256.ofNat b).val
        = (UInt256.ofNat a).val + (UInt256.ofNat b).val from rfl,
      Fin.val_add,
      show (UInt256.ofNat a).val.val = a from Nat.mod_eq_of_lt ha,
      show (UInt256.ofNat b).val.val = b from Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt hab

/-- Convenience wrapper: for `a, b < 256` (always true for Weth's PCs), the
toNat of the sum is `a + b` provided `a + b < 256`. -/
private theorem ofNat_add_ofNat_toNat_lt256
    (a b : ℕ) (_ha : a < 256 := by decide) (_hb : b < 256 := by decide)
    (_hab : a + b < 256 := by decide) :
    (UInt256.ofNat a + UInt256.ofNat b).toNat = a + b :=
  ofNat_add_ofNat_toNat a b
    (by unfold UInt256.size; omega) (by unfold UInt256.size; omega)
    (by unfold UInt256.size; omega)

/-! ## Closure obligations: Z, decodeSome -/

/-- Z (gas-only update) preserves `WethTrace`. -/
private theorem WethTrace_Z_preserves
    (C : AccountAddress) (s : EVM.State) (g : UInt256)
    (h : WethTrace C s) :
    WethTrace C { s with gasAvailable := g } := h

/-- Each reachable state has decode = some pair. -/
private theorem WethTrace_decodeSome
    (C : AccountAddress) (s : EVM.State)
    (h : WethTrace C s) :
    ∃ pair, decode s.executionEnv.code s.pc = some pair := by
  obtain ⟨_, hCode, hPC⟩ := h
  rw [hCode]
  -- 64 disjuncts; PCs 16, 26, 55, 77 carry a stack[0]? witness so are
  -- 3-conjunct (need ⟨hpc, _, _⟩); PC 60 carries a `True` placeholder
  -- (for future cascade-fact threading) so is also 3-conjunct. PCs 61, 63,
  -- 65, 67, 69, 70, 71, 72 carry slack witnesses (`x + storageSum ≤ balanceOf`).
  -- The rest are 2-conjunct. PCs 80, 81, 83, 85 each appear twice (different
  -- stack lengths from PC 55/77 entry); both are 2-conjunct.
  rcases hPC with
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩
  all_goals (rw [pc_eq_ofNat_of_toNat s _ (by decide) hpc])
  exacts [⟨_, decode_bytecode_at_0⟩, ⟨_, decode_bytecode_at_2⟩,
          ⟨_, decode_bytecode_at_3⟩, ⟨_, decode_bytecode_at_5⟩,
          ⟨_, decode_bytecode_at_6⟩, ⟨_, decode_bytecode_at_7⟩,
          ⟨_, decode_bytecode_at_12⟩, ⟨_, decode_bytecode_at_13⟩,
          ⟨_, decode_bytecode_at_16⟩, ⟨_, decode_bytecode_at_17⟩,
          ⟨_, decode_bytecode_at_22⟩, ⟨_, decode_bytecode_at_23⟩,
          ⟨_, decode_bytecode_at_26⟩, ⟨_, decode_bytecode_at_27⟩,
          ⟨_, decode_bytecode_at_29⟩, ⟨_, decode_bytecode_at_31⟩,
          ⟨_, decode_bytecode_at_32⟩, ⟨_, decode_bytecode_at_32⟩,
          ⟨_, decode_bytecode_at_33⟩,
          ⟨_, decode_bytecode_at_34⟩, ⟨_, decode_bytecode_at_35⟩,
          ⟨_, decode_bytecode_at_36⟩, ⟨_, decode_bytecode_at_37⟩,
          ⟨_, decode_bytecode_at_38⟩, ⟨_, decode_bytecode_at_39⟩,
          ⟨_, decode_bytecode_at_40⟩, ⟨_, decode_bytecode_at_41⟩,
          ⟨_, decode_bytecode_at_42⟩, ⟨_, decode_bytecode_at_43⟩,
          ⟨_, decode_bytecode_at_45⟩, ⟨_, decode_bytecode_at_46⟩,
          ⟨_, decode_bytecode_at_47⟩, ⟨_, decode_bytecode_at_48⟩,
          ⟨_, decode_bytecode_at_49⟩, ⟨_, decode_bytecode_at_50⟩,
          ⟨_, decode_bytecode_at_51⟩, ⟨_, decode_bytecode_at_52⟩,
          ⟨_, decode_bytecode_at_55⟩, ⟨_, decode_bytecode_at_56⟩,
          ⟨_, decode_bytecode_at_57⟩, ⟨_, decode_bytecode_at_58⟩,
          ⟨_, decode_bytecode_at_59⟩, ⟨_, decode_bytecode_at_60⟩,
          ⟨_, decode_bytecode_at_61⟩, ⟨_, decode_bytecode_at_63⟩,
          ⟨_, decode_bytecode_at_65⟩, ⟨_, decode_bytecode_at_67⟩,
          ⟨_, decode_bytecode_at_69⟩, ⟨_, decode_bytecode_at_70⟩,
          ⟨_, decode_bytecode_at_71⟩, ⟨_, decode_bytecode_at_72⟩,
          ⟨_, decode_bytecode_at_73⟩, ⟨_, decode_bytecode_at_74⟩,
          ⟨_, decode_bytecode_at_77⟩, ⟨_, decode_bytecode_at_78⟩,
          ⟨_, decode_bytecode_at_79⟩, ⟨_, decode_bytecode_at_80⟩,
          ⟨_, decode_bytecode_at_80⟩, ⟨_, decode_bytecode_at_81⟩,
          ⟨_, decode_bytecode_at_81⟩, ⟨_, decode_bytecode_at_83⟩,
          ⟨_, decode_bytecode_at_83⟩, ⟨_, decode_bytecode_at_85⟩,
          ⟨_, decode_bytecode_at_85⟩]

/-! ## Per-PC step lemmas

Each per-PC `WethTrace_step_at_N` lemma fixes the pre-state at PC=N
(via the corresponding disjunct of `WethTrace`) and shows the post-step
state inhabits `WethTrace` (typically the next-PC disjunct in the
trace).

These per-PC artifacts are usable building blocks for the full
aggregate `WethTrace_step_preserves` theorem (which is required by
`ΞPreservesInvariantAtC_of_Reachable_general`'s `hReach_step` slot).
The PC=85 REVERT case is a known gap: its post-state has PC=86 with
`decode bytecode 86 = none`, so the post-state cannot inhabit
`WethTrace` (which carries `decodeSome` as a closure obligation).
The remaining ~58 PCs each close cleanly. -/

/-- Short alias for the smart-constructor body reused across all
per-PC lemmas. -/
private theorem mk_wethTrace_aux
    {C : AccountAddress} {s s' : EVM.State}
    (hCO : C = s.executionEnv.codeOwner)
    (hCode : s.executionEnv.code = bytecode)
    (hEE' : s'.executionEnv = s.executionEnv)
    (hPC :
      ((s'.pc.toNat = 0  ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 2  ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 3  ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 5  ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 6  ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 7  ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 12 ∧ s'.stack.length = 3) ∨
       (s'.pc.toNat = 13 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 16 ∧ s'.stack.length = 3 ∧ s'.stack[0]? = some depositLbl) ∨
       (s'.pc.toNat = 17 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 22 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 23 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 26 ∧ s'.stack.length = 2 ∧ s'.stack[0]? = some withdrawLbl) ∨
       (s'.pc.toNat = 27 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 29 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 31 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 32 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 32 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 33 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 34 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 35 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 36 ∧ s'.stack.length = 2 ∧ s'.stack[0]? = s'.stack[1]?) ∨
       (s'.pc.toNat = 37 ∧ s'.stack.length = 2 ∧
         ∃ slot oldVal : UInt256,
           s'.stack = oldVal :: slot :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot))) ∨
       (s'.pc.toNat = 38 ∧ s'.stack.length = 3 ∧
         ∃ slot oldVal v : UInt256,
           s'.stack = v :: oldVal :: slot :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot))) ∨
       (s'.pc.toNat = 39 ∧ s'.stack.length = 2 ∧
         ∃ slot oldVal newVal : UInt256,
           s'.stack = newVal :: slot :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot))) ∨
       (s'.pc.toNat = 40 ∧ s'.stack.length = 2 ∧
         ∃ slot oldVal newVal : UInt256,
           s'.stack = slot :: newVal :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot))) ∨
       (s'.pc.toNat = 41 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 42 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 43 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 45 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 46 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 47 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 48 ∧ s'.stack.length = 3 ∧ s'.stack[0]? = s'.stack[1]?) ∨
       (s'.pc.toNat = 49 ∧ s'.stack.length = 3 ∧
         ∃ slot oldVal x : UInt256,
           s'.stack = oldVal :: slot :: x :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot))) ∨
       (s'.pc.toNat = 50 ∧ s'.stack.length = 4 ∧
         ∃ slot oldVal x : UInt256,
           s'.stack = x :: oldVal :: slot :: x :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot))) ∨
       (s'.pc.toNat = 51 ∧ s'.stack.length = 5 ∧
         ∃ slot oldVal x : UInt256,
           s'.stack = oldVal :: x :: oldVal :: slot :: x :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot))) ∨
       (s'.pc.toNat = 52 ∧ s'.stack.length = 4 ∧
         ∃ slot oldVal x : UInt256,
           s'.stack = UInt256.lt oldVal x :: oldVal :: slot :: x :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot))) ∨
       (s'.pc.toNat = 55 ∧ s'.stack.length = 5 ∧
         ∃ slot oldVal x : UInt256,
           s'.stack = revertLbl :: UInt256.lt oldVal x :: oldVal :: slot :: x :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot))) ∨
       (s'.pc.toNat = 56 ∧ s'.stack.length = 3 ∧
         ∃ slot oldVal x : UInt256,
           s'.stack = oldVal :: slot :: x :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot)) ∧
           x.toNat ≤ oldVal.toNat) ∨
       (s'.pc.toNat = 57 ∧ s'.stack.length = 4 ∧
         ∃ slot oldVal x : UInt256,
           s'.stack = x :: oldVal :: slot :: x :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot)) ∧
           x.toNat ≤ oldVal.toNat) ∨
       (s'.pc.toNat = 58 ∧ s'.stack.length = 4 ∧
         ∃ slot oldVal x : UInt256,
           s'.stack = oldVal :: x :: slot :: x :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot)) ∧
           x.toNat ≤ oldVal.toNat) ∨
       (s'.pc.toNat = 59 ∧ s'.stack.length = 3 ∧
         ∃ slot oldVal x : UInt256,
           s'.stack = UInt256.sub oldVal x :: slot :: x :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot)) ∧
           x.toNat ≤ oldVal.toNat) ∨
       (s'.pc.toNat = 60 ∧ s'.stack.length = 3 ∧
         ∃ slot oldVal x : UInt256,
           s'.stack = slot :: UInt256.sub oldVal x :: x :: [] ∧
           oldVal = (s'.accountMap.find? C).option ⟨0⟩
                      (Account.lookupStorage (k := slot)) ∧
           x.toNat ≤ oldVal.toNat) ∨
       (s'.pc.toNat = 61 ∧ s'.stack.length = 1 ∧
         ∃ x : UInt256, s'.stack[0]? = some x ∧
           x.toNat + storageSum s'.accountMap C ≤ balanceOf s'.accountMap C) ∨
       (s'.pc.toNat = 63 ∧ s'.stack.length = 2 ∧
         ∃ x : UInt256, s'.stack[1]? = some x ∧
           x.toNat + storageSum s'.accountMap C ≤ balanceOf s'.accountMap C) ∨
       (s'.pc.toNat = 65 ∧ s'.stack.length = 3 ∧
         ∃ x : UInt256, s'.stack[2]? = some x ∧
           x.toNat + storageSum s'.accountMap C ≤ balanceOf s'.accountMap C) ∨
       (s'.pc.toNat = 67 ∧ s'.stack.length = 4 ∧
         ∃ x : UInt256, s'.stack[3]? = some x ∧
           x.toNat + storageSum s'.accountMap C ≤ balanceOf s'.accountMap C) ∨
       (s'.pc.toNat = 69 ∧ s'.stack.length = 5 ∧
         ∃ x : UInt256, s'.stack[4]? = some x ∧
           x.toNat + storageSum s'.accountMap C ≤ balanceOf s'.accountMap C) ∨
       (s'.pc.toNat = 70 ∧ s'.stack.length = 6 ∧
         ∃ x : UInt256, s'.stack[0]? = some x ∧
           x.toNat + storageSum s'.accountMap C ≤ balanceOf s'.accountMap C) ∨
       (s'.pc.toNat = 71 ∧ s'.stack.length = 7 ∧
         ∃ x : UInt256, s'.stack[1]? = some x ∧
           x.toNat + storageSum s'.accountMap C ≤ balanceOf s'.accountMap C) ∨
       (s'.pc.toNat = 72 ∧ s'.stack.length = 8 ∧
         ∃ x : UInt256, s'.stack[2]? = some x ∧
           x.toNat + storageSum s'.accountMap C ≤ balanceOf s'.accountMap C) ∨
       (s'.pc.toNat = 73 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 74 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 77 ∧ s'.stack.length = 3 ∧ s'.stack[0]? = some revertLbl) ∨
       (s'.pc.toNat = 78 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 79 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 80 ∧ s'.stack.length = 3) ∨
       (s'.pc.toNat = 80 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 81 ∧ s'.stack.length = 3) ∨
       (s'.pc.toNat = 81 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 83 ∧ s'.stack.length = 4) ∨
       (s'.pc.toNat = 83 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 85 ∧ s'.stack.length = 5) ∨
       (s'.pc.toNat = 85 ∧ s'.stack.length = 3))) :
    WethTrace C s' :=
  ⟨by rw [hEE']; exact hCO, by rw [hEE']; exact hCode, hPC⟩

/-! ### PC 0 — `PUSH1 0` -/

private theorem WethTrace_step_at_0
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 0) (hLen : s.stack.length = 0)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 0 := pc_eq_ofNat_of_toNat s 0 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_0 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  right; left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 0 2
  · rw [hStk']
    show List.length (UInt256.ofNat 0 :: s.stack) = 1
    simp [hLen]

/-! ### PC 2 — `CALLDATALOAD` -/

private theorem WethTrace_step_at_2
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 2) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 2 := pc_eq_ofNat_of_toNat s 2 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: tl, hLen2 =>
    have hLenTl : tl.length = 0 := by
      have h1 : (hd :: tl).length = 1 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_CALLDATALOAD_at_pc s s' f' cost op arg _ hd tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_2 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 2 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 2 1
    · rw [hStk']; show (v :: tl).length = 1; simp [hLenTl]

/-! ### PC 3 — `PUSH1 0xe0` -/

private theorem WethTrace_step_at_3
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 3) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 3 := pc_eq_ofNat_of_toNat s 3 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_3 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 3 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 3 2
  · rw [hStk']
    show List.length (UInt256.ofNat 0xe0 :: s.stack) = 2
    simp [hLen]

/-! ### PC 5 — `SHR` -/

private theorem WethTrace_step_at_5
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 5) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 5 := pc_eq_ofNat_of_toNat s 5 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: tl, hLen2 =>
    have hLenTl : tl.length = 0 := by
      have h1 : (hd1 :: hd2 :: tl).length = 2 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_SHR_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_5 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 4 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 5 1
    · rw [hStk']; show (v :: tl).length = 1; simp [hLenTl]

/-! ### PC 6 — `DUP1` -/

private theorem WethTrace_step_at_6
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 6) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 6 := pc_eq_ofNat_of_toNat s 6 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: tl, hLen2 =>
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_DUP1_at_pc s s' f' cost op arg _ hd tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_6 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 5 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 6 1
    · rw [hStk']; show (hd :: s.stack).length = 2; simp [hLen]

/-! ### PC 7 — `PUSH4 depositSelector` -/

private theorem WethTrace_step_at_7
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 7) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 7 := pc_eq_ofNat_of_toNat s 7 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH_at_pc s s' f' cost op arg .PUSH4 (by decide) depositSelector 4
      hFetch hCode hpcEq decode_bytecode_at_7 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 6 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 7 5
  · rw [hStk']
    show List.length (depositSelector :: s.stack) = 3
    simp [hLen]

/-! ### PC 12 — `EQ` (deposit selector match) -/

private theorem WethTrace_step_at_12
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 12) (hLen : s.stack.length = 3)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 12 := pc_eq_ofNat_of_toNat s 12 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: tl, hLen2 =>
    have hLenTl : tl.length = 1 := by
      have h1 : (hd1 :: hd2 :: tl).length = 3 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_EQ_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_12 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 7 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 12 1
    · rw [hStk']; show (v :: tl).length = 2; simp [hLenTl]

/-! ### PC 13 — `PUSH2 depositLbl` -/

private theorem WethTrace_step_at_13
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 13) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 13 := pc_eq_ofNat_of_toNat s 13 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH_at_pc s s' f' cost op arg .PUSH2 (by decide) depositLbl 2
      hFetch hCode hpcEq decode_bytecode_at_13 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 8 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 13 3
  · rw [hStk']; show List.length (depositLbl :: s.stack) = 3; simp [hLen]
  · rw [hStk']
    show (depositLbl :: s.stack)[0]? = some depositLbl
    rfl

/-! ### PC 16 — `JUMPI` (deposit dispatch)

Both branches fire: fall-through to PC 17 if EQ flag = 0, taken-branch
to PC 32 (deposit JUMPDEST) if EQ flag ≠ 0. The taken-branch's
destination is `depositLbl = 32`, which the trace pins via
`stack[0]? = some depositLbl` at PC 16. -/

private theorem WethTrace_step_at_16
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 16) (hLen : s.stack.length = 3)
    (hStk0 : s.stack[0]? = some depositLbl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 16 := pc_eq_ofNat_of_toNat s 16 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: tl, hLen2 =>
    have hLenTl : tl.length = 1 := by
      have h1 : (hd1 :: hd2 :: tl).length = 3 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    have hd1_eq : hd1 = depositLbl := by
      have : (hd1 :: hd2 :: tl)[0]? = some depositLbl := by rw [← hStk_eq]; exact hStk0
      simpa using this
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_JUMPI_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_16 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    -- Bool case-analysis on `hd2 != ⟨0⟩`. UInt256's BEq is derived from
    -- Fin so it's lawful, but rather than invoke that we just split on
    -- the Bool.
    cases hb : (hd2 != ⟨0⟩) with
    | true =>
      -- Taken-branch: post-pc = hd1 = depositLbl = 32.
      iterate 17 right
      left
      refine ⟨?_, ?_⟩
      · rw [hPC']
        simp only [hb, ↓reduceIte]
        rw [hd1_eq]; show depositLbl.toNat = 32; rfl
      · rw [hStk']; exact hLenTl
    | false =>
      -- Fall-through: post-pc = s.pc + 1 = 17.
      iterate 9 right
      left
      refine ⟨?_, ?_⟩
      · rw [hPC']
        simp only [hb, Bool.false_eq_true, if_false]
        rw [hpcEq]
        exact ofNat_add_ofNat_toNat_lt256 16 1
      · rw [hStk']; exact hLenTl

/-! ### PC 17 — `PUSH4 withdrawSelector` -/

private theorem WethTrace_step_at_17
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 17) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 17 := pc_eq_ofNat_of_toNat s 17 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH_at_pc s s' f' cost op arg .PUSH4 (by decide) withdrawSelector 4
      hFetch hCode hpcEq decode_bytecode_at_17 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 10 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 17 5
  · rw [hStk']; show List.length (withdrawSelector :: s.stack) = 2; simp [hLen]

/-! ### PC 22 — `EQ` (withdraw selector match) -/

private theorem WethTrace_step_at_22
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 22) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 22 := pc_eq_ofNat_of_toNat s 22 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: tl, hLen2 =>
    have hLenTl : tl.length = 0 := by
      have h1 : (hd1 :: hd2 :: tl).length = 2 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_EQ_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_22 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 11 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 22 1
    · rw [hStk']; show (v :: tl).length = 1; simp [hLenTl]

/-! ### PC 23 — `PUSH2 withdrawLbl` -/

private theorem WethTrace_step_at_23
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 23) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 23 := pc_eq_ofNat_of_toNat s 23 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH_at_pc s s' f' cost op arg .PUSH2 (by decide) withdrawLbl 2
      hFetch hCode hpcEq decode_bytecode_at_23 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 12 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 23 3
  · rw [hStk']; show List.length (withdrawLbl :: s.stack) = 2; simp [hLen]
  · rw [hStk']
    show (withdrawLbl :: s.stack)[0]? = some withdrawLbl
    rfl

/-! ### PC 26 — `JUMPI` (withdraw dispatch) -/

private theorem WethTrace_step_at_26
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 26) (hLen : s.stack.length = 2)
    (hStk0 : s.stack[0]? = some withdrawLbl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 26 := pc_eq_ofNat_of_toNat s 26 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: tl, hLen2 =>
    have hLenTl : tl.length = 0 := by
      have h1 : (hd1 :: hd2 :: tl).length = 2 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    have hd1_eq : hd1 = withdrawLbl := by
      have : (hd1 :: hd2 :: tl)[0]? = some withdrawLbl := by
        rw [← hStk_eq]; exact hStk0
      simpa using this
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_JUMPI_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_26 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    cases hb : (hd2 != ⟨0⟩) with
    | true =>
      -- Taken-branch: post-pc = hd1 = withdrawLbl = 42 (withdraw JUMPDEST).
      iterate 27 right
      left
      refine ⟨?_, ?_⟩
      · rw [hPC']
        simp only [hb, if_true]
        rw [hd1_eq]; show withdrawLbl.toNat = 42; rfl
      · rw [hStk']; exact hLenTl
    | false =>
      -- Fall-through: post-pc = 27.
      iterate 13 right
      left
      refine ⟨?_, ?_⟩
      · rw [hPC']
        simp only [hb, Bool.false_eq_true, if_false]
        rw [hpcEq]
        exact ofNat_add_ofNat_toNat_lt256 26 1
      · rw [hStk']; exact hLenTl

/-! ### PC 27 — `PUSH1 0` (revert path setup) -/

private theorem WethTrace_step_at_27
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 27) (hLen : s.stack.length = 0)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 27 := pc_eq_ofNat_of_toNat s 27 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_27 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 14 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 27 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 1; simp [hLen]

/-! ### PC 29 — `PUSH1 0` (revert path setup) -/

private theorem WethTrace_step_at_29
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 29) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 29 := pc_eq_ofNat_of_toNat s 29 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_29 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 15 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 29 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 2; simp [hLen]

/-! ### PC 31 — `REVERT` (no-selector-match)

Post-REVERT pc = 32, stack = []. Lands in the PC=32 length=0 halt-sink
disjunct (the X loop catches REVERT and exits, but the post-step state
must still inhabit some `WethTrace` disjunct for the closure). -/

private theorem WethTrace_step_at_31
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 31) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 31 := pc_eq_ofNat_of_toNat s 31 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: tl, hLen2 =>
    have hLenTl : tl.length = 0 := by
      have h1 : (hd1 :: hd2 :: tl).length = 2 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_REVERT_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_31 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    -- Lands in the 17th disjunct (PC=32 length=0).
    iterate 16 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 31 1
    · rw [hStk']; exact hLenTl

/-! ### PC 32 — `JUMPDEST` (deposit JUMPDEST entry, length=1)

Note: only the length=1 case is walked. The length=0 disjunct is the
post-PC-31-REVERT halt sink — X has already exited so this state is
never re-stepped. The aggregate `WethTrace_step_preserves` would also
need a length=0 case; left as a known gap. -/

private theorem WethTrace_step_at_32
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 32) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 32 := pc_eq_ofNat_of_toNat s 32 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_JUMPDEST_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_32 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 18 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 32 1
  · rw [hStk']; exact hLen

/-! ### PC 33 — `POP` (deposit: pop selector) -/

private theorem WethTrace_step_at_33
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 33) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 33 := pc_eq_ofNat_of_toNat s 33 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: tl, hLen2 =>
    have hLenTl : tl.length = 0 := by
      have h1 : (hd :: tl).length = 1 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_POP_at_pc s s' f' cost op arg _ hd tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_33 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 19 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 33 1
    · rw [hStk']; exact hLenTl

/-! ### PC 34 — `CALLER` (deposit: push sender) -/

private theorem WethTrace_step_at_34
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 34) (hLen : s.stack.length = 0)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 34 := pc_eq_ofNat_of_toNat s 34 (by decide) hpc
  obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
    step_CALLER_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_34 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 20 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 34 1
  · rw [hStk']; show (v :: s.stack).length = 1; simp [hLen]

/-! ### PC 35 — `DUP1` (deposit: duplicate sender) -/

private theorem WethTrace_step_at_35
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 35) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 35 := pc_eq_ofNat_of_toNat s 35 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: tl, hLen2 =>
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_DUP1_at_pc s s' f' cost op arg _ hd tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_35 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 21 right
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 35 1
    · rw [hStk']; show (hd :: s.stack).length = 2; simp [hLen]
    · -- DUP1 invariant: post-state's top two stack elements are equal.
      rw [hStk', hStk_eq]; rfl

/-! ### PC 36 — `SLOAD` (deposit: load balance) -/

private theorem WethTrace_step_at_36
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 36) (hLen : s.stack.length = 2)
    (hStk01 : s.stack[0]? = s.stack[1]?)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 36 := pc_eq_ofNat_of_toNat s 36 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: t1 :: [], _ =>
    -- DUP1 invariant: stack[0] = stack[1] pre-SLOAD, so the slot
    -- popped by SLOAD also lives at the new top's tail head.
    have hHd_eq_t1 : hd = t1 := by
      have h0 : s.stack[0]? = some hd := by rw [hStk_eq]; rfl
      have h1 : s.stack[1]? = some t1 := by rw [hStk_eq]; rfl
      rw [h0] at hStk01
      rw [h1] at hStk01
      exact Option.some.inj hStk01
    -- Use the strong wrapper: exposes the pushed value as the
    -- storage lookup at the contract's own address.
    obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
      step_SLOAD_at_pc_strong s s' f' cost op arg _ hd (t1 :: []) hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_36 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 22 right
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 36 1
    · rw [hStk']; rfl
    · refine ⟨t1,
              (s.lookupAccount s.executionEnv.codeOwner).option ⟨0⟩
                (Account.lookupStorage (k := hd)), ?_, ?_⟩
      · -- Goal: s'.stack = oldVal :: slot :: [].
        rw [hStk']
      · -- Goal: oldVal = (s'.accountMap.find? C).option ⟨0⟩ (lookupStorage slot).
        rw [hHd_eq_t1, show s'.accountMap = s.accountMap from hAcc', hCO]
        rfl

/-! ### PC 37 — `CALLVALUE` (deposit: push msg.value) -/

private theorem WethTrace_step_at_37
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 37) (hLen : s.stack.length = 2)
    (hCascade37 : ∃ slot oldVal : UInt256,
       s.stack = oldVal :: slot :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 37 := pc_eq_ofNat_of_toNat s 37 (by decide) hpc
  obtain ⟨slot, oldVal, hStk_eq, hOldVal⟩ := hCascade37
  obtain ⟨hPC', ⟨v, hStk'⟩, hEE', hAcc'⟩ :=
    step_CALLVALUE_at_pc_strong s s' f' cost op arg _
      hFetch hCode hpcEq decode_bytecode_at_37 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 23 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 37 1
  · rw [hStk']; show (v :: s.stack).length = 3; simp [hLen]
  · refine ⟨slot, oldVal, v, ?_, ?_⟩
    · rw [hStk', hStk_eq]
    · rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### PC 38 — `ADD` (deposit: balance + msg.value) -/

private theorem WethTrace_step_at_38
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 38) (hLen : s.stack.length = 3)
    (hCascade38 : ∃ slot oldVal v : UInt256,
       s.stack = v :: oldVal :: slot :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 38 := pc_eq_ofNat_of_toNat s 38 (by decide) hpc
  obtain ⟨slot, oldVal, v, hStk_eq, hOldVal⟩ := hCascade38
  obtain ⟨hPC', ⟨w, hStk'⟩, hEE', hAcc'⟩ :=
    step_ADD_at_pc_strong s s' f' cost op arg _ v oldVal (slot :: []) hStk_eq
      hFetch hCode hpcEq decode_bytecode_at_38 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 24 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 38 1
  · rw [hStk']; rfl
  · refine ⟨slot, oldVal, w, ?_, ?_⟩
    · rw [hStk']
    · rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### PC 39 — `SWAP1` (deposit: swap newBalance and sender) -/

private theorem WethTrace_step_at_39
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 39) (hLen : s.stack.length = 2)
    (hCascade39 : ∃ slot oldVal newVal : UInt256,
       s.stack = newVal :: slot :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 39 := pc_eq_ofNat_of_toNat s 39 (by decide) hpc
  obtain ⟨slot, oldVal, newVal, hStk_eq, hOldVal⟩ := hCascade39
  obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
    step_SWAP1_at_pc_strong s s' f' cost op arg _ newVal slot [] hStk_eq
      hFetch hCode hpcEq decode_bytecode_at_39 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 25 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 39 1
  · rw [hStk']; rfl
  · refine ⟨slot, oldVal, newVal, ?_, ?_⟩
    · rw [hStk']
    · rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### Closed-form post-state `accountMap` shape for an EVM SSTORE step

Used by the per-PC SSTORE walks (PCs 40, 60) to thread cascade-fact
data forward through the SSTORE post-state. -/

/-- Closed-form post-state `accountMap` shape for an EVM SSTORE step
at the codeOwner. The two popped values `(slot, newVal)` index the
storage update: post-state's accountMap inserts `acc.updateStorage
slot newVal` at the codeOwner. -/
private theorem step_SSTORE_accountMap
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (slot newVal : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = slot :: newVal :: tl)
    (acc : Account .EVM)
    (h_find : s.accountMap.find? s.executionEnv.codeOwner = some acc)
    (hStep : EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s') :
    s'.accountMap
      = s.accountMap.insert s.executionEnv.codeOwner
          (acc.updateStorage slot newVal) := by
  -- Reduce EVM.step to the binaryStateOp dispatch.
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryStateOp EVM.binaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  -- Reduce: s' = ({ s with toState := State.sstore s.toState ... }).replaceStackAndIncrPC tl.
  -- Its `.accountMap` is the inserted-storage map.
  simp only [accountMap_replaceStackAndIncrPC]
  show (EvmYul.State.sstore s.toState slot newVal).accountMap
       = s.accountMap.insert s.executionEnv.codeOwner
           (acc.updateStorage slot newVal)
  unfold EvmYul.State.sstore
  simp only [EvmYul.State.lookupAccount, h_find, Option.option]
  -- The remaining transformation: setAccount + addAccessedStorageKey + substate.refundBalance.
  -- All but setAccount preserve accountMap.
  rfl

/-! ### PC 40 — `SSTORE` (deposit: write storage[sender]) -/

private theorem WethTrace_step_at_40
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 40) (hLen : s.stack.length = 2)
    (_hCascade40 : ∃ slot oldVal newVal : UInt256,
       s.stack = slot :: newVal :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 40 := pc_eq_ofNat_of_toNat s 40 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: tl, hLen2 =>
    have hLenTl : tl.length = 0 := by
      have h1 : (hd1 :: hd2 :: tl).length = 2 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_SSTORE_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_40 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 26 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 40 1
    · rw [hStk']; exact hLenTl

/-! ### PC 41 — `STOP` (deposit success)

STOP keeps pc the same and preserves stack — fixed point at PC=41
length=0. -/

private theorem WethTrace_step_at_41
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 41) (hLen : s.stack.length = 0)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 41 := pc_eq_ofNat_of_toNat s 41 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_STOP_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_41 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 26 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC']; exact hpc
  · rw [hStk']; exact hLen

/-! ### PC 42 — `JUMPDEST` (withdraw entry) -/

private theorem WethTrace_step_at_42
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 42) (hLen : s.stack.length = 0)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 42 := pc_eq_ofNat_of_toNat s 42 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_JUMPDEST_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_42 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 28 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 42 1
  · rw [hStk']; exact hLen

/-! ### PC 43 — `PUSH1 4` (withdraw: calldata offset for `x`) -/

private theorem WethTrace_step_at_43
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 43) (hLen : s.stack.length = 0)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 43 := pc_eq_ofNat_of_toNat s 43 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_43 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 29 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 43 2
  · rw [hStk']; show List.length (UInt256.ofNat 4 :: s.stack) = 1; simp [hLen]

/-! ### PC 45 — `CALLDATALOAD` (withdraw: load `x`) -/

private theorem WethTrace_step_at_45
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 45) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 45 := pc_eq_ofNat_of_toNat s 45 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: tl, hLen2 =>
    have hLenTl : tl.length = 0 := by
      have h1 : (hd :: tl).length = 1 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_CALLDATALOAD_at_pc s s' f' cost op arg _ hd tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_45 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 30 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 45 1
    · rw [hStk']; show (v :: tl).length = 1; simp [hLenTl]

/-! ### PC 46 — `CALLER` (withdraw: push sender) -/

private theorem WethTrace_step_at_46
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 46) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 46 := pc_eq_ofNat_of_toNat s 46 (by decide) hpc
  obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
    step_CALLER_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_46 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 31 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 46 1
  · rw [hStk']; show (v :: s.stack).length = 2; simp [hLen]

/-! ### PC 47 — `DUP1` (withdraw: duplicate sender) -/

private theorem WethTrace_step_at_47
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 47) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 47 := pc_eq_ofNat_of_toNat s 47 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: tl, hLen2 =>
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_DUP1_at_pc s s' f' cost op arg _ hd tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_47 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 32 right
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 47 1
    · rw [hStk']; show (hd :: s.stack).length = 3; simp [hLen]
    · -- DUP1 invariant: post-state's top two stack elements are equal.
      rw [hStk', hStk_eq]; rfl

/-! ### PC 48 — `SLOAD` (withdraw: load balance) -/

private theorem WethTrace_step_at_48
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 48) (hLen : s.stack.length = 3)
    (hStk01 : s.stack[0]? = s.stack[1]?)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 48 := pc_eq_ofNat_of_toNat s 48 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: t1 :: t2 :: [], _ =>
    -- DUP1 invariant: stack[0] = stack[1] pre-SLOAD, so the slot
    -- popped by SLOAD also lives at the new top's stack[1].
    have hHd_eq_t1 : hd = t1 := by
      have h0 : s.stack[0]? = some hd := by rw [hStk_eq]; rfl
      have h1 : s.stack[1]? = some t1 := by rw [hStk_eq]; rfl
      rw [h0] at hStk01
      rw [h1] at hStk01
      exact Option.some.inj hStk01
    -- Use the strong wrapper: exposes the pushed value as the
    -- storage lookup at the contract's address.
    obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
      step_SLOAD_at_pc_strong s s' f' cost op arg _ hd (t1 :: t2 :: []) hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_48 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 33 right
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 48 1
    · rw [hStk']; rfl
    · refine ⟨t1,
              (s.lookupAccount s.executionEnv.codeOwner).option ⟨0⟩
                (Account.lookupStorage (k := hd)),
              t2, ?_, ?_⟩
      · -- Goal: s'.stack = oldVal :: slot :: x :: [].
        rw [hStk']
      · -- Goal: oldVal = (s'.accountMap.find? C).option ⟨0⟩ (lookupStorage slot).
        rw [hHd_eq_t1, show s'.accountMap = s.accountMap from hAcc', hCO]
        rfl

/-! ### PC 49 — `DUP3` (withdraw: duplicate `x` to top) -/

private theorem WethTrace_step_at_49
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 49) (hLen : s.stack.length = 3)
    (hCascade49 : ∃ slot oldVal x : UInt256,
       s.stack = oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 49 := pc_eq_ofNat_of_toNat s 49 (by decide) hpc
  obtain ⟨slot, oldVal, x, hStk_eq, hOldVal⟩ := hCascade49
  obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
    step_DUP3_at_pc_strong s s' f' cost op arg _ oldVal slot x [] hStk_eq
      hFetch hCode hpcEq decode_bytecode_at_49 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 34 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 49 1
  · rw [hStk']; show (x :: s.stack).length = 4; simp [hLen]
  · refine ⟨slot, oldVal, x, ?_, ?_⟩
    · -- Goal: s'.stack = x :: oldVal :: slot :: x :: [].
      rw [hStk', hStk_eq]
    · -- Goal: oldVal = (s'.accountMap.find? C).option ⟨0⟩ (lookupStorage slot).
      rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### PC 50 — `DUP2` (withdraw: duplicate balance) -/

private theorem WethTrace_step_at_50
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 50) (hLen : s.stack.length = 4)
    (hCascade50 : ∃ slot oldVal x : UInt256,
       s.stack = x :: oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 50 := pc_eq_ofNat_of_toNat s 50 (by decide) hpc
  obtain ⟨slot, oldVal, x, hStk_eq, hOldVal⟩ := hCascade50
  obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
    step_DUP2_at_pc_strong s s' f' cost op arg _ x oldVal (slot :: x :: []) hStk_eq
      hFetch hCode hpcEq decode_bytecode_at_50 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 35 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 50 1
  · rw [hStk']; show (oldVal :: s.stack).length = 5; simp [hLen]
  · refine ⟨slot, oldVal, x, ?_, ?_⟩
    · rw [hStk', hStk_eq]
    · rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### PC 51 — `LT` (withdraw: balance < x) -/

private theorem WethTrace_step_at_51
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 51) (hLen : s.stack.length = 5)
    (hCascade51 : ∃ slot oldVal x : UInt256,
       s.stack = oldVal :: x :: oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 51 := pc_eq_ofNat_of_toNat s 51 (by decide) hpc
  obtain ⟨slot, oldVal, x, hStk_eq, hOldVal⟩ := hCascade51
  obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
    step_LT_at_pc_strong s s' f' cost op arg _ oldVal x
      (oldVal :: slot :: x :: []) hStk_eq
      hFetch hCode hpcEq decode_bytecode_at_51 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 36 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 51 1
  · rw [hStk']; rfl
  · refine ⟨slot, oldVal, x, ?_, ?_⟩
    · rw [hStk']
    · rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### PC 52 — `PUSH2 revertLbl` (withdraw: revert dest setup) -/

private theorem WethTrace_step_at_52
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 52) (hLen : s.stack.length = 4)
    (hCascade52 : ∃ slot oldVal x : UInt256,
       s.stack = UInt256.lt oldVal x :: oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 52 := pc_eq_ofNat_of_toNat s 52 (by decide) hpc
  obtain ⟨slot, oldVal, x, hStk_eq, hOldVal⟩ := hCascade52
  obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
    step_PUSH_at_pc_strong s s' f' cost op arg .PUSH2 (by decide) revertLbl 2
      hFetch hCode hpcEq decode_bytecode_at_52 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 37 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 52 3
  · rw [hStk']; show List.length (revertLbl :: s.stack) = 5; simp [hLen]
  · refine ⟨slot, oldVal, x, ?_, ?_⟩
    · rw [hStk', hStk_eq]
    · rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### PC 55 — `JUMPI` (withdraw: revert if balance < x) -/

private theorem WethTrace_step_at_55
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 55) (hLen : s.stack.length = 5)
    (hCascade55 : ∃ slot oldVal x : UInt256,
       s.stack = revertLbl :: UInt256.lt oldVal x :: oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)))
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 55 := pc_eq_ofNat_of_toNat s 55 (by decide) hpc
  obtain ⟨slot, oldVal, x, hStk_eq, hOldVal⟩ := hCascade55
  obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
    step_JUMPI_at_pc_strong s s' f' cost op arg _ revertLbl (UInt256.lt oldVal x)
      (oldVal :: slot :: x :: []) hStk_eq
      hFetch hCode hpcEq decode_bytecode_at_55 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  cases hb : (UInt256.lt oldVal x != ⟨0⟩) with
  | true =>
    -- Taken-branch: post-pc = revertLbl = 80, post-stack length 3.
    iterate 56 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC']
      simp only [hb, if_true]
      show revertLbl.toNat = 80; rfl
    · rw [hStk']; rfl
  | false =>
    -- Fall-through: post-pc = 56, post-stack length 3, with bound x ≤ oldVal.
    iterate 38 right
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [hPC']
      simp only [hb, Bool.false_eq_true, if_false]
      rw [hpcEq]
      exact ofNat_add_ofNat_toNat_lt256 55 1
    · rw [hStk']; rfl
    · refine ⟨slot, oldVal, x, ?_, ?_, ?_⟩
      · rw [hStk']
      · rw [show s'.accountMap = s.accountMap from hAcc']
        exact hOldVal
      · -- Goal: x.toNat ≤ oldVal.toNat. From `LT oldVal x = 0` (JUMPI not-taken).
        -- The cases on `lt`: either `oldVal < x` (then lt = ⟨1⟩, JUMPI takes the branch ≠ this case),
        -- or `¬ (oldVal < x)` (then lt = ⟨0⟩, JUMPI not-taken — our case — gives the bound).
        unfold UInt256.lt UInt256.fromBool at hb
        by_cases h_lt : oldVal < x
        · -- Case oldVal < x: fromBool true = ⟨1⟩ ≠ ⟨0⟩ ⇒ != = true, contradicts hb=false.
          exfalso
          simp only [h_lt, decide_true, Bool.toUInt256] at hb
          exact Bool.noConfusion hb
        · -- Case ¬(oldVal < x): hence x.val ≤ oldVal.val.
          show x.val ≤ oldVal.val
          exact Nat.le_of_not_lt h_lt

/-! ### PC 56 — `DUP3` (withdraw: duplicate `x` for SUB) -/

private theorem WethTrace_step_at_56
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 56) (hLen : s.stack.length = 3)
    (hCascade56 : ∃ slot oldVal x : UInt256,
       s.stack = oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)) ∧
       x.toNat ≤ oldVal.toNat)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 56 := pc_eq_ofNat_of_toNat s 56 (by decide) hpc
  obtain ⟨slot, oldVal, x, hStk_eq, hOldVal, hBound⟩ := hCascade56
  obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
    step_DUP3_at_pc_strong s s' f' cost op arg _ oldVal slot x [] hStk_eq
      hFetch hCode hpcEq decode_bytecode_at_56 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 39 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 56 1
  · rw [hStk']; show (x :: s.stack).length = 4; simp [hLen]
  · refine ⟨slot, oldVal, x, ?_, ?_, hBound⟩
    · rw [hStk', hStk_eq]
    · rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### PC 57 — `SWAP1` (withdraw: align balance and x for SUB) -/

private theorem WethTrace_step_at_57
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 57) (hLen : s.stack.length = 4)
    (hCascade57 : ∃ slot oldVal x : UInt256,
       s.stack = x :: oldVal :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)) ∧
       x.toNat ≤ oldVal.toNat)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 57 := pc_eq_ofNat_of_toNat s 57 (by decide) hpc
  obtain ⟨slot, oldVal, x, hStk_eq, hOldVal, hBound⟩ := hCascade57
  obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
    step_SWAP1_at_pc_strong s s' f' cost op arg _ x oldVal (slot :: x :: []) hStk_eq
      hFetch hCode hpcEq decode_bytecode_at_57 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 40 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 57 1
  · rw [hStk']; rfl
  · refine ⟨slot, oldVal, x, ?_, ?_, hBound⟩
    · rw [hStk']
    · rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### PC 58 — `SUB` (withdraw: balance - x = newBalance) -/

private theorem WethTrace_step_at_58
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 58) (hLen : s.stack.length = 4)
    (hCascade58 : ∃ slot oldVal x : UInt256,
       s.stack = oldVal :: x :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)) ∧
       x.toNat ≤ oldVal.toNat)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 58 := pc_eq_ofNat_of_toNat s 58 (by decide) hpc
  obtain ⟨slot, oldVal, x, hStk_eq, hOldVal, hBound⟩ := hCascade58
  obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
    step_SUB_at_pc_strong s s' f' cost op arg _ oldVal x (slot :: x :: []) hStk_eq
      hFetch hCode hpcEq decode_bytecode_at_58 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 41 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 58 1
  · rw [hStk']; rfl
  · refine ⟨slot, oldVal, x, ?_, ?_, hBound⟩
    · rw [hStk']
    · rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### PC 59 — `SWAP1` (withdraw: align newBalance and sender for SSTORE) -/

private theorem WethTrace_step_at_59
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 59) (hLen : s.stack.length = 3)
    (hCascade59 : ∃ slot oldVal x : UInt256,
       s.stack = UInt256.sub oldVal x :: slot :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)) ∧
       x.toNat ≤ oldVal.toNat)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 59 := pc_eq_ofNat_of_toNat s 59 (by decide) hpc
  obtain ⟨slot, oldVal, x, hStk_eq, hOldVal, hBound⟩ := hCascade59
  obtain ⟨hPC', hStk', hEE', hAcc'⟩ :=
    step_SWAP1_at_pc_strong s s' f' cost op arg _
      (UInt256.sub oldVal x) slot (x :: []) hStk_eq
      hFetch hCode hpcEq decode_bytecode_at_59 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 42 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 59 1
  · rw [hStk']; rfl
  · refine ⟨slot, oldVal, x, ?_, ?_, hBound⟩
    · rw [hStk']
    · rw [show s'.accountMap = s.accountMap from hAcc']
      exact hOldVal

/-! ### PC 60 — `SSTORE` (withdraw: write decremented `storage[sender]`)

This is the central state-update step in withdraw: writes
`storage[sender] = balance − x` where `x` is the requested withdraw
amount. The §2.5 combined-step lemma will use the trace shape at PC 60
+ PC 72 to track `Δstorage[C]_{addressSlot CALLER} = −x` for the
solvency invariant. -/

private theorem WethTrace_step_at_60
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 60) (hLen : s.stack.length = 3)
    (hCascade60 : ∃ slot oldVal x : UInt256,
       s.stack = slot :: UInt256.sub oldVal x :: x :: [] ∧
       oldVal = (s.accountMap.find? C).option ⟨0⟩
                  (Account.lookupStorage (k := slot)) ∧
       x.toNat ≤ oldVal.toNat)
    (hAcc : accountPresentAt s.accountMap C)
    (hInv : WethInvFr s.accountMap C)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 60 := pc_eq_ofNat_of_toNat s 60 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: tl, hLen2 =>
    have hLenTl : tl.length = 1 := by
      have h1 : (hd1 :: hd2 :: tl).length = 3 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_SSTORE_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_60 hStep
    -- Extract the cascade: slot, oldVal, x.
    obtain ⟨slot, oldVal, x, hStkCas, hOldVal, hBound⟩ := hCascade60
    -- Combine hStk_eq : s.stack = hd1 :: hd2 :: tl
    -- with hStkCas : s.stack = slot :: (oldVal - x) :: x :: [] to identify
    -- hd1 = slot, hd2 = oldVal - x, tl = [x].
    have hStkEq2 : (hd1 :: hd2 :: tl) = slot :: UInt256.sub oldVal x :: x :: [] := by
      rw [← hStk_eq]; exact hStkCas
    have hd1_eq : hd1 = slot := by injection hStkEq2
    have hd2_eq : hd2 = UInt256.sub oldVal x := by
      injection hStkEq2 with _ h; injection h
    have tl_eq : tl = x :: [] := by
      injection hStkEq2 with _ h; injection h
    -- σ has C.
    obtain ⟨acc, h_find⟩ := hAcc
    -- Convert oldVal to acc.storage.findD slot ⟨0⟩ via h_find.
    have h_findD : acc.storage.findD slot ⟨0⟩ = oldVal := by
      rw [h_find] at hOldVal
      show acc.storage.findD slot ⟨0⟩ = oldVal
      rw [hOldVal]
      rfl
    -- Bound: (oldVal - x).toNat ≤ oldVal.toNat.
    have h_subVal : (UInt256.sub oldVal x).toNat ≤ oldVal.toNat := by
      have hSub_eq : UInt256.sub oldVal x = oldVal - x := rfl
      rw [hSub_eq, UInt256_sub_toNat_of_le _ _ hBound]
      exact Nat.sub_le _ _
    -- Post-state accountMap shape via step_SSTORE_accountMap.
    have h_find_CO : s.accountMap.find? s.executionEnv.codeOwner = some acc := by
      rw [← hCO]; exact h_find
    -- Align `op` to `.SSTORE` via the decode lemma.
    have hDec_at_pc : decode s.executionEnv.code s.pc
        = some (.StackMemFlow .SSTORE, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_60
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec_at_pc hFetch
    subst hOp
    have h_am : s'.accountMap
        = s.accountMap.insert s.executionEnv.codeOwner
            (acc.updateStorage slot (UInt256.sub oldVal x)) := by
      have hStk_pre : s.stack = slot :: UInt256.sub oldVal x :: tl := by
        rw [hStk_eq, hd1_eq, hd2_eq]
      exact step_SSTORE_accountMap s s' f' cost arg slot (UInt256.sub oldVal x) tl
        hStk_pre acc h_find_CO hStep
    -- balanceOf preserved: storage-only update doesn't touch balance.
    have h_bal_eq :
        balanceOf s'.accountMap C = balanceOf s.accountMap C := by
      rw [h_am, ← hCO]
      apply balanceOf_insert_preserve_of_eq s.accountMap C acc _ h_find
      exact Account_updateStorage_balance _ _ _
    -- storageSum bound depending on slot existence.
    have h_storageSum_le :
        x.toNat + storageSum s'.accountMap C ≤ storageSum s.accountMap C := by
      rw [h_am, ← hCO]
      -- Case-split on acc.storage.find? slot.
      cases h_slot : acc.storage.find? slot with
      | some oldVal' =>
        -- findD = oldVal' = oldVal.
        have hOldEq : oldVal' = oldVal := by
          have hh : acc.storage.findD slot ⟨0⟩ = oldVal' := by
            unfold Batteries.RBMap.findD
            rw [h_slot]; rfl
          rw [hh] at h_findD; exact h_findD
        -- Sub-case: (oldVal - x) = 0 (erase) vs ≠ 0 (replace).
        by_cases h_newZero : (UInt256.sub oldVal x == default) = true
        · -- Erase.
          have h_newVal_eq : UInt256.sub oldVal x = (⟨0⟩ : UInt256) := by
            have h_newZero' : ((UInt256.sub oldVal x).val == (default : UInt256).val) = true := h_newZero
            have h1 : (UInt256.sub oldVal x).val = (default : UInt256).val :=
              of_decide_eq_true h_newZero'
            have h_def_val : (default : UInt256).val = (0 : Fin UInt256.size) := rfl
            rw [h_def_val] at h1
            -- h1 : (UInt256.sub oldVal x).val = 0.
            apply UInt256.mk.injEq _ _ |>.mpr
            exact h1
          rw [h_newVal_eq]
          -- Use storageSum_sstore_erase_eq with oldVal'.
          have h_delta := storageSum_sstore_erase_eq s.accountMap C slot oldVal'
                            acc h_find h_slot
          -- h_delta : storageSum (insert ...) C + oldVal'.toNat = storageSum s.accountMap C
          -- From h_newVal_eq: oldVal - x = 0 ⇒ since x ≤ oldVal, oldVal = x.
          have h_xeq : oldVal.toNat = x.toNat := by
            have h_subzero : (UInt256.sub oldVal x).toNat = 0 := by
              rw [h_newVal_eq]; rfl
            have hSub_eq : UInt256.sub oldVal x = oldVal - x := rfl
            rw [hSub_eq, UInt256_sub_toNat_of_le _ _ hBound] at h_subzero
            omega
          have h_xeq' : oldVal'.toNat = x.toNat := by rw [hOldEq]; exact h_xeq
          omega
        · -- Replace.
          have hNonZero : (UInt256.sub oldVal x == default) = false := by
            cases hh : (UInt256.sub oldVal x == default) with
            | true => exact absurd hh h_newZero
            | false => rfl
          have h_delta := storageSum_sstore_replace_eq s.accountMap C slot
                            (UInt256.sub oldVal x) oldVal' hNonZero
                            acc h_find h_slot
          -- h_delta : storageSum_post + oldVal'.toNat = storageSum_pre + (oldVal - x).toNat.
          -- (oldVal - x).toNat = oldVal.toNat - x.toNat (since x ≤ oldVal).
          have h_subToNat : (UInt256.sub oldVal x).toNat = oldVal.toNat - x.toNat := by
            have hSub_eq : UInt256.sub oldVal x = oldVal - x := rfl
            rw [hSub_eq, UInt256_sub_toNat_of_le _ _ hBound]
          -- x.toNat ≤ oldVal'.toNat (= oldVal.toNat).
          have h_x_le : x.toNat ≤ oldVal'.toNat := by rw [hOldEq]; exact hBound
          -- oldVal'.toNat ≤ storageSum_pre.
          have h_old_ge : oldVal'.toNat ≤ storageSum s.accountMap C := by
            apply storageSum_old_le s.accountMap C slot oldVal'
            rw [h_find]; simp [h_slot]
          have hOldEq' : oldVal'.toNat = oldVal.toNat := by rw [hOldEq]
          omega
      | none =>
        -- findD = ⟨0⟩, so oldVal = ⟨0⟩, x ≤ 0 ⇒ x = 0.
        have hOldZero : oldVal = (⟨0⟩ : UInt256) := by
          have hh : acc.storage.findD slot ⟨0⟩ = (⟨0⟩ : UInt256) := by
            unfold Batteries.RBMap.findD
            rw [h_slot]; rfl
          rw [hh] at h_findD; exact h_findD.symm
        have hBound' : x.toNat ≤ 0 := by
          have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
          rw [hOldZero, h0] at hBound; exact hBound
        have hx_zero : x.toNat = 0 := Nat.le_zero.mp hBound'
        -- x = 0 forces 0 + storageSum_post ≤ storageSum_pre.
        rw [hx_zero, Nat.zero_add]
        -- storageSum_post ≤ storageSum_pre via _findD lemma.
        exact storageSum_sstore_replace_eq_findD s.accountMap C slot
          (UInt256.sub oldVal x) oldVal acc h_find h_findD h_subVal
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 43 right
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 60 1
    · rw [hStk']; exact hLenTl
    · -- Slack: x + storageSum s'.accountMap C ≤ balanceOf s'.accountMap C.
      refine ⟨x, ?_, ?_⟩
      · -- s'.stack[0]? = some x: s'.stack = tl = [x].
        rw [hStk', tl_eq]; rfl
      · rw [h_bal_eq]; exact Nat.le_trans h_storageSum_le hInv

/-! ### PC 61 — `PUSH1 0` (withdraw: CALL retSize) -/

private theorem WethTrace_step_at_61
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 61) (hLen : s.stack.length = 1)
    (hSlack61 : ∃ x : UInt256, s.stack[0]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 61 := pc_eq_ofNat_of_toNat s 61 (by decide) hpc
  obtain ⟨hPC', hStk', hEE', hAM⟩ :=
    step_PUSH1_at_pc_strong s s' f' cost op arg _
      hFetch hCode hpcEq decode_bytecode_at_61 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 44 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 61 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 2; simp [hLen]
  · -- Slack: x at s'.stack[1] = s.stack[0] (after PUSH1 0 push).
    obtain ⟨x, hStk0, hSlack⟩ := hSlack61
    refine ⟨x, ?_, ?_⟩
    · -- s'.stack = ⟨0⟩ :: s.stack, so s'.stack[1] = s.stack[0] = some x.
      rw [hStk']
      show (UInt256.ofNat 0 :: s.stack)[1]? = some x
      simp [hStk0]
    · rw [hAM]; exact hSlack

/-! ### PC 63 — `PUSH1 0` (withdraw: CALL retOff) -/

private theorem WethTrace_step_at_63
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 63) (hLen : s.stack.length = 2)
    (hSlack63 : ∃ x : UInt256, s.stack[1]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 63 := pc_eq_ofNat_of_toNat s 63 (by decide) hpc
  obtain ⟨hPC', hStk', hEE', hAM⟩ :=
    step_PUSH1_at_pc_strong s s' f' cost op arg _
      hFetch hCode hpcEq decode_bytecode_at_63 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 45 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 63 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 3; simp [hLen]
  · obtain ⟨x, hStk1, hSlack⟩ := hSlack63
    refine ⟨x, ?_, ?_⟩
    · rw [hStk']
      show (UInt256.ofNat 0 :: s.stack)[2]? = some x
      simp [hStk1]
    · rw [hAM]; exact hSlack

/-! ### PC 65 — `PUSH1 0` (withdraw: CALL argsSize) -/

private theorem WethTrace_step_at_65
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 65) (hLen : s.stack.length = 3)
    (hSlack65 : ∃ x : UInt256, s.stack[2]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 65 := pc_eq_ofNat_of_toNat s 65 (by decide) hpc
  obtain ⟨hPC', hStk', hEE', hAM⟩ :=
    step_PUSH1_at_pc_strong s s' f' cost op arg _
      hFetch hCode hpcEq decode_bytecode_at_65 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 46 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 65 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 4; simp [hLen]
  · obtain ⟨x, hStk2, hSlack⟩ := hSlack65
    refine ⟨x, ?_, ?_⟩
    · rw [hStk']
      show (UInt256.ofNat 0 :: s.stack)[3]? = some x
      simp [hStk2]
    · rw [hAM]; exact hSlack

/-! ### PC 67 — `PUSH1 0` (withdraw: CALL argsOff) -/

private theorem WethTrace_step_at_67
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 67) (hLen : s.stack.length = 4)
    (hSlack67 : ∃ x : UInt256, s.stack[3]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 67 := pc_eq_ofNat_of_toNat s 67 (by decide) hpc
  obtain ⟨hPC', hStk', hEE', hAM⟩ :=
    step_PUSH1_at_pc_strong s s' f' cost op arg _
      hFetch hCode hpcEq decode_bytecode_at_67 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 47 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 67 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 5; simp [hLen]
  · obtain ⟨x, hStk3, hSlack⟩ := hSlack67
    refine ⟨x, ?_, ?_⟩
    · rw [hStk']
      show (UInt256.ofNat 0 :: s.stack)[4]? = some x
      simp [hStk3]
    · rw [hAM]; exact hSlack

/-! ### PC 69 — `DUP5` (withdraw: copy `x` as CALL value) -/

private theorem WethTrace_step_at_69
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 69) (hLen : s.stack.length = 5)
    (hSlack69 : ∃ x : UInt256, s.stack[4]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 69 := pc_eq_ofNat_of_toNat s 69 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: tl, hLen2 =>
    obtain ⟨hPC', hStk', hEE', hAM⟩ :=
      step_DUP5_at_pc_strong s s' f' cost op arg _ hd1 hd2 hd3 hd4 hd5 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_69 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 48 right
    left
    refine ⟨?_, ?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 69 1
    · rw [hStk']; show (hd5 :: s.stack).length = 6; simp [hLen]
    · obtain ⟨x, hStk4, hSlack⟩ := hSlack69
      -- s.stack = hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: tl, so s.stack[4]? = some hd5.
      have hd5_eq : hd5 = x := by
        have : s.stack[4]? = some hd5 := by
          rw [hStk_eq]; rfl
        rw [this] at hStk4
        injection hStk4
      refine ⟨x, ?_, ?_⟩
      · -- s'.stack = hd5 :: s.stack, so s'.stack[0]? = some hd5 = some x.
        rw [hStk', ← hd5_eq]; rfl
      · rw [hAM]; exact hSlack

/-! ### PC 70 — `CALLER` (withdraw: push recipient = sender) -/

private theorem WethTrace_step_at_70
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 70) (hLen : s.stack.length = 6)
    (hSlack70 : ∃ x : UInt256, s.stack[0]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 70 := pc_eq_ofNat_of_toNat s 70 (by decide) hpc
  obtain ⟨hPC', ⟨v, hStk'⟩, hEE', hAM⟩ :=
    step_CALLER_at_pc_strong s s' f' cost op arg _
      hFetch hCode hpcEq decode_bytecode_at_70 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 49 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 70 1
  · rw [hStk']; show (v :: s.stack).length = 7; simp [hLen]
  · obtain ⟨x, hStk0, hSlack⟩ := hSlack70
    refine ⟨x, ?_, ?_⟩
    · -- s'.stack = v :: s.stack, so s'.stack[1]? = s.stack[0]? = some x.
      rw [hStk']
      show (v :: s.stack)[1]? = some x
      simp [hStk0]
    · rw [hAM]; exact hSlack

/-! ### PC 71 — `GAS` (withdraw: push remaining gas as CALL gas) -/

private theorem WethTrace_step_at_71
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 71) (hLen : s.stack.length = 7)
    (hSlack71 : ∃ x : UInt256, s.stack[1]? = some x ∧
       x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 71 := pc_eq_ofNat_of_toNat s 71 (by decide) hpc
  obtain ⟨hPC', ⟨v, hStk'⟩, hEE', hAM⟩ :=
    step_GAS_at_pc_strong s s' f' cost op arg _
      hFetch hCode hpcEq decode_bytecode_at_71 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 50 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 71 1
  · rw [hStk']; show (v :: s.stack).length = 8; simp [hLen]
  · obtain ⟨x, hStk1, hSlack⟩ := hSlack71
    refine ⟨x, ?_, ?_⟩
    · -- s'.stack = v :: s.stack, so s'.stack[2]? = s.stack[1]? = some x.
      rw [hStk']
      show (v :: s.stack)[2]? = some x
      simp [hStk1]
    · rw [hAM]; exact hSlack

/-! ### PC 72 — `CALL` (withdraw: external transfer)

The recursive Ξ entry. At step level CALL just pops 7 and pushes 1
(the success flag). The post-state has stack length 2: success + the
trailing `x` left over from the [..., x] residual after the SSTORE
prefix (since CALL pops 7 from the 8-deep stack [gas, to, val, ao,
as, ro, rs, x]). -/

private theorem WethTrace_step_at_72
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 72) (hLen : s.stack.length = 8)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 72 := pc_eq_ofNat_of_toNat s 72 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: hd7 :: tl, hLen2 =>
    have hLenTl : tl.length = 1 := by
      have h1 : (hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: hd7 :: tl).length = 8 := by
        rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_CALL_at_pc s s' f' cost op arg _ hd1 hd2 hd3 hd4 hd5 hd6 hd7 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_72 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 51 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 72 1
    · rw [hStk']; show (v :: tl).length = 2; simp [hLenTl]

/-! ### PC 73 — `ISZERO` (withdraw: check CALL success flag) -/

private theorem WethTrace_step_at_73
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 73) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 73 := pc_eq_ofNat_of_toNat s 73 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: tl, hLen2 =>
    have hLenTl : tl.length = 1 := by
      have h1 : (hd :: tl).length = 2 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_ISZERO_at_pc s s' f' cost op arg _ hd tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_73 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 52 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 73 1
    · rw [hStk']; show (v :: tl).length = 2; simp [hLenTl]

/-! ### PC 74 — `PUSH2 revertLbl` (withdraw: revert dest for CALL-fail) -/

private theorem WethTrace_step_at_74
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 74) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 74 := pc_eq_ofNat_of_toNat s 74 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH_at_pc s s' f' cost op arg .PUSH2 (by decide) revertLbl 2
      hFetch hCode hpcEq decode_bytecode_at_74 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 53 right
  left
  refine ⟨?_, ?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 74 3
  · rw [hStk']; show List.length (revertLbl :: s.stack) = 3; simp [hLen]
  · rw [hStk']
    show (revertLbl :: s.stack)[0]? = some revertLbl
    rfl

/-! ### PC 77 — `JUMPI` (withdraw: revert if CALL failed) -/

private theorem WethTrace_step_at_77
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 77) (hLen : s.stack.length = 3)
    (hStk0 : s.stack[0]? = some revertLbl)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 77 := pc_eq_ofNat_of_toNat s 77 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: tl, hLen2 =>
    have hLenTl : tl.length = 1 := by
      have h1 : (hd1 :: hd2 :: tl).length = 3 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    have hd1_eq : hd1 = revertLbl := by
      have : (hd1 :: hd2 :: tl)[0]? = some revertLbl := by
        rw [← hStk_eq]; exact hStk0
      simpa using this
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_JUMPI_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_77 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    cases hb : (hd2 != ⟨0⟩) with
    | true =>
      -- Taken-branch: post-pc = revertLbl = 80, post-stack length 1.
      -- Lands in the PC=80 length=1 disjunct (position 57).
      iterate 57 right
      left
      refine ⟨?_, ?_⟩
      · rw [hPC']
        simp only [hb, if_true]
        rw [hd1_eq]; show revertLbl.toNat = 80; rfl
      · rw [hStk']; exact hLenTl
    | false =>
      -- Fall-through: post-pc = 78, post-stack length 1.
      iterate 54 right
      left
      refine ⟨?_, ?_⟩
      · rw [hPC']
        simp only [hb, Bool.false_eq_true, if_false]
        rw [hpcEq]
        exact ofNat_add_ofNat_toNat_lt256 77 1
      · rw [hStk']; exact hLenTl

/-! ### PC 78 — `POP` (withdraw success: pop `x`) -/

private theorem WethTrace_step_at_78
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 78) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 78 := pc_eq_ofNat_of_toNat s 78 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: tl, hLen2 =>
    have hLenTl : tl.length = 0 := by
      have h1 : (hd :: tl).length = 1 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_POP_at_pc s s' f' cost op arg _ hd tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_78 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 55 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 78 1
    · rw [hStk']; exact hLenTl

/-! ### PC 79 — `STOP` (withdraw success) -/

private theorem WethTrace_step_at_79
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 79) (hLen : s.stack.length = 0)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 79 := pc_eq_ofNat_of_toNat s 79 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_STOP_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_79 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 55 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC']; exact hpc
  · rw [hStk']; exact hLen

/-! ### PC 80 — `JUMPDEST` (revert tail entry, two shapes)

Two entry stack lengths: 3 (from PC 55 JUMPI taken) or 1 (from PC 77
JUMPI taken). Each preserves stack and lands at PC=81 with the same
length. -/

private theorem WethTrace_step_at_80_len3
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 80) (hLen : s.stack.length = 3)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 80 := pc_eq_ofNat_of_toNat s 80 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_JUMPDEST_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_80 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  -- PC=81 length=3 is at position 58.
  iterate 58 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 80 1
  · rw [hStk']; exact hLen

private theorem WethTrace_step_at_80_len1
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 80) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 80 := pc_eq_ofNat_of_toNat s 80 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_JUMPDEST_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_80 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  -- PC=81 length=1 is at position 59.
  iterate 59 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 80 1
  · rw [hStk']; exact hLen

/-! ### PC 81 — `PUSH1 0` (revert tail, two shapes) -/

private theorem WethTrace_step_at_81_len3
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 81) (hLen : s.stack.length = 3)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 81 := pc_eq_ofNat_of_toNat s 81 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_81 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  -- PC=83 length=4 is at position 60.
  iterate 60 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 81 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 4; simp [hLen]

private theorem WethTrace_step_at_81_len1
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 81) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 81 := pc_eq_ofNat_of_toNat s 81 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_81 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  -- PC=83 length=2 is at position 61.
  iterate 61 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 81 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 2; simp [hLen]

/-! ### PC 83 — `PUSH1 0` (revert tail, two shapes) -/

private theorem WethTrace_step_at_83_len4
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 83) (hLen : s.stack.length = 4)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 83 := pc_eq_ofNat_of_toNat s 83 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_83 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  -- PC=85 length=5 is at position 62.
  iterate 62 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 83 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 5; simp [hLen]

private theorem WethTrace_step_at_83_len2
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 83) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 83 := pc_eq_ofNat_of_toNat s 83 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_83 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  -- PC=85 length=3 is at position 63 (last disjunct).
  iterate 63 right
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 83 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 3; simp [hLen]

/-! ## Closure obligation: initial state

Mirrors Register's `RegisterTrace_initial`: the initial Weth-execution
state (pc = 0, empty stack) lies in `WethTrace`, given the
deployment-pinned code-identity witness `DeployedAtC`. -/

/-- **Weth-context code-identity hypothesis.**

`DeployedAtC C` asserts that any `ExecutionEnv` with `codeOwner = C`
runs Weth's bytecode. Real-world tx contexts satisfy this when:

  * Weth's genesis deployment installed this exact 86-byte code at `C`.
  * Weth's own bytecode contains no `CREATE`/`CREATE2` opcode, so no
    nested frame can overwrite code at `C`.
  * The boundary hypothesis enforced by the consumer (`weth_solvency_invariant`)
    excludes nested `CREATE`/`CREATE2` from any other contract producing
    address `C`.
  * Weth's bytecode contains no `SELFDESTRUCT`, so `C`'s account is
    never erased (which would otherwise reset its code to empty).

Mirror of Register's `DeployedAtC` predicate. -/
def DeployedAtC (C : AccountAddress) : Prop :=
  ∀ I : ExecutionEnv .EVM, I.codeOwner = C → I.code = bytecode

/-- An initial Weth-execution state is `WethTrace`, given the
deployment-pinned code-identity witness. -/
private theorem WethTrace_initial
    (C : AccountAddress)
    (hDeployed : DeployedAtC C)
    (cA : Batteries.RBSet AccountAddress compare)
    (gbh : BlockHeader) (bs : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM)
    (hCO : I.codeOwner = C) :
    WethTrace C
      { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          gasAvailable := g
          blocks := bs
          genesisBlockHeader := gbh } := by
  have hCode : I.code = bytecode := hDeployed I hCO
  refine ⟨hCO.symm, hCode, ?_⟩
  -- Initial state has pc = 0 and empty stack.
  left
  refine ⟨?_, ?_⟩
  · show (⟨0⟩ : UInt256).toNat = 0
    decide
  · show ([] : Stack UInt256).length = 0
    rfl

/-! ## SSTORE-step `WethInvFr` preservation helpers

These lift the `Frame.storageSum_sstore_*_eq` delta laws into clean
`WethInvFr` preservation lemmas under the SSTORE post-state shape.

The "monotone-decrement" form (PC 60) is fully closed-form: when
`newVal.toNat ≤ oldVal.toNat`, the post-storageSum at `C` does not
exceed the pre-storageSum (by `storageSum_sstore_replace_eq` /
`_erase_eq`), and `sstore` preserves `balanceOf`, so `WethInvFr` is
preserved verbatim.

The "increment" form (PC 40) needs additional slack from the trace
shape (the at-`C` Ξ pre-credit of `msg.value`). It's omitted here;
the `WethSStorePreserves` consumer handles it via per-state
hypotheses. -/

/-- `WethInvFr` is preserved by an SSTORE-replace at `C` whose new
value is bounded above by the old value at the slot. The pre-state
balance is unchanged (sstore doesn't touch balance), so the
storageSum decrease translates verbatim to invariant preservation. -/
theorem WethInvFr_of_sstore_replace_decr
    (σ : AccountMap .EVM) (C : AccountAddress)
    (slot newVal oldVal : UInt256)
    (h_newVal : (newVal == default) = false)
    (acc : Account .EVM)
    (h_find : σ.find? C = some acc)
    (h_old : acc.storage.find? slot = some oldVal)
    (h_le  : newVal.toNat ≤ oldVal.toNat)
    (hInv : WethInvFr σ C) :
    WethInvFr (σ.insert C (acc.updateStorage slot newVal)) C := by
  unfold WethInvFr at *
  -- balanceOf is preserved by storage-only updates at `C`.
  have h_bal_eq :
      balanceOf (σ.insert C (acc.updateStorage slot newVal)) C
        = balanceOf σ C := by
    apply balanceOf_insert_preserve_of_eq σ C acc _ h_find
    exact Account_updateStorage_balance _ _ _
  rw [h_bal_eq]
  -- storageSum delta: new + oldVal = old + newVal ⇒ new = old + newVal − oldVal
  -- Since newVal ≤ oldVal, the RHS (in ℕ-truncated subtraction) is ≤ old.
  have h_delta := storageSum_sstore_replace_eq σ C slot newVal oldVal h_newVal
                    acc h_find h_old
  -- h_delta : new + oldVal.toNat = old + newVal.toNat.
  have hnew_le_old : storageSum (σ.insert C (acc.updateStorage slot newVal)) C
                       ≤ storageSum σ C := by
    omega
  exact Nat.le_trans hnew_le_old hInv

/-- `WethInvFr` is preserved by an SSTORE-erase at `C` (equivalently,
SSTORE with `newVal = 0`). The post-storageSum drops by exactly the
slot's old value, so it does not exceed the pre-storageSum. -/
theorem WethInvFr_of_sstore_erase
    (σ : AccountMap .EVM) (C : AccountAddress) (slot oldVal : UInt256)
    (acc : Account .EVM)
    (h_find : σ.find? C = some acc)
    (h_old : acc.storage.find? slot = some oldVal)
    (hInv : WethInvFr σ C) :
    WethInvFr (σ.insert C (acc.updateStorage slot ⟨0⟩)) C := by
  unfold WethInvFr at *
  have h_bal_eq :
      balanceOf (σ.insert C (acc.updateStorage slot ⟨0⟩)) C
        = balanceOf σ C := by
    apply balanceOf_insert_preserve_of_eq σ C acc _ h_find
    exact Account_updateStorage_balance _ _ _
  rw [h_bal_eq]
  have h_delta := storageSum_sstore_erase_eq σ C slot oldVal acc h_find h_old
  -- h_delta : new + oldVal.toNat = old.
  have hnew_le_old : storageSum (σ.insert C (acc.updateStorage slot ⟨0⟩)) C
                       ≤ storageSum σ C := by
    omega
  exact Nat.le_trans hnew_le_old hInv

/-! ### Closed-form bridge: EVM SSTORE-step → `WethInvFr` preservation

The two `WethInvFr_of_sstore_*` lemmas above operate on
`σ.insert C (acc.updateStorage slot newVal)` — the post-state shape
of `EvmYul.State.sstore`. To use them on the output of `EVM.step`,
we need to bridge `s'.accountMap` (EVM step's output) to that shape.

`step_SSTORE_accountMap` does exactly that: given the EVM SSTORE
step + the pre-state stack shape `(slot :: newVal :: tl)` and the
`s.accountMap.find? C = some acc` lookup, the post-state's
`accountMap` is `s.accountMap.insert C (acc.updateStorage slot
newVal)`. (Defined earlier, before the per-PC walks, so the PC 60
walk can use it to thread the post-SSTORE slack.) -/

/-- **Closed-form decrement bridge.** Given an EVM SSTORE step at
the codeOwner with stack `(slot :: newVal :: tl)` where the slot's
pre-storage value is `oldVal` and `newVal ≤ oldVal` (and `newVal ≠ 0`),
the post-state preserves `WethInvFr`. -/
theorem WethInvFr_step_SSTORE_at_C_replace_decr
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (slot newVal oldVal : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = slot :: newVal :: tl)
    (hCO : C = s.executionEnv.codeOwner)
    (acc : Account .EVM)
    (h_find : s.accountMap.find? C = some acc)
    (h_old : acc.storage.find? slot = some oldVal)
    (h_le  : newVal.toNat ≤ oldVal.toNat)
    (h_newVal_ne_zero : (newVal == default) = false)
    (hInv : WethInvFr s.accountMap C)
    (hStep : EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s') :
    WethInvFr s'.accountMap C := by
  have h_find_CO : s.accountMap.find? s.executionEnv.codeOwner = some acc := by
    rw [← hCO]; exact h_find
  have h_am := step_SSTORE_accountMap s s' f' cost arg slot newVal tl hStk acc h_find_CO hStep
  rw [h_am, ← hCO]
  exact WethInvFr_of_sstore_replace_decr s.accountMap C slot newVal oldVal
    h_newVal_ne_zero acc h_find h_old h_le hInv

/-- **Closed-form replace bridge with explicit slack.** Given an EVM
SSTORE step at the codeOwner with stack `(slot :: newVal :: tl)`,
slot pre-value `oldVal`, and the slack hypothesis
`storageSum σ C - oldVal.toNat + newVal.toNat ≤ balanceOf σ C`, the
post-state preserves `WethInvFr`.

Used for the PC 40 (deposit) increment case: `newVal > oldVal` is
allowed, but the at-`C` Θ-pre-credit slack covers the increment.
The slack hypothesis is the cascade-fact the deposit-side trace
extension would establish (Θ pre-credits the at-`C` balance by
`msg.value`, which exactly equals the SSTORE delta `newVal − oldVal`). -/
theorem WethInvFr_of_sstore_replace_with_slack
    (σ : AccountMap .EVM) (C : AccountAddress)
    (slot newVal oldVal : UInt256)
    (h_newVal : (newVal == default) = false)
    (acc : Account .EVM)
    (h_find : σ.find? C = some acc)
    (h_old : acc.storage.find? slot = some oldVal)
    (h_slack : storageSum σ C - oldVal.toNat + newVal.toNat ≤ balanceOf σ C) :
    WethInvFr (σ.insert C (acc.updateStorage slot newVal)) C := by
  unfold WethInvFr
  -- balanceOf preserved.
  have h_bal_eq :
      balanceOf (σ.insert C (acc.updateStorage slot newVal)) C
        = balanceOf σ C := by
    apply balanceOf_insert_preserve_of_eq σ C acc _ h_find
    exact Account_updateStorage_balance _ _ _
  rw [h_bal_eq]
  -- storageSum delta: new + oldVal = old + newVal ⇒ new = old + newVal − oldVal.
  have h_delta := storageSum_sstore_replace_eq σ C slot newVal oldVal
                    h_newVal acc h_find h_old
  -- h_old_ge: oldVal.toNat ≤ storageSum σ C (slot is in the sum)
  have h_old_ge : oldVal.toNat ≤ storageSum σ C := by
    apply storageSum_old_le σ C slot oldVal
    rw [h_find]; simp [h_old]
  -- new = storageSum + newVal − oldVal (∈ ℕ since oldVal ≤ storageSum guarantees no truncation)
  have h_eq : storageSum (σ.insert C (acc.updateStorage slot newVal)) C
                = storageSum σ C - oldVal.toNat + newVal.toNat := by
    omega
  rw [h_eq]
  exact h_slack

/-- **Closed-form erase bridge.** Given an EVM SSTORE step at the
codeOwner with stack `(slot :: ⟨0⟩ :: tl)` where the slot's
pre-storage value is `oldVal`, the post-state preserves `WethInvFr`. -/
theorem WethInvFr_step_SSTORE_at_C_erase
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (slot oldVal : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = slot :: ⟨0⟩ :: tl)
    (hCO : C = s.executionEnv.codeOwner)
    (acc : Account .EVM)
    (h_find : s.accountMap.find? C = some acc)
    (h_old : acc.storage.find? slot = some oldVal)
    (hInv : WethInvFr s.accountMap C)
    (hStep : EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s') :
    WethInvFr s'.accountMap C := by
  have h_find_CO : s.accountMap.find? s.executionEnv.codeOwner = some acc := by
    rw [← hCO]; exact h_find
  have h_am := step_SSTORE_accountMap s s' f' cost arg slot ⟨0⟩ tl hStk acc h_find_CO hStep
  rw [h_am, ← hCO]
  exact WethInvFr_of_sstore_erase s.accountMap C slot oldVal acc h_find h_old hInv

/-- **Closed-form replace-with-slack bridge.** EVM-step version of
`WethInvFr_of_sstore_replace_with_slack`. -/
theorem WethInvFr_step_SSTORE_at_C_replace_with_slack
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (arg : Option (UInt256 × Nat))
    (slot newVal oldVal : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = slot :: newVal :: tl)
    (hCO : C = s.executionEnv.codeOwner)
    (acc : Account .EVM)
    (h_find : s.accountMap.find? C = some acc)
    (h_old : acc.storage.find? slot = some oldVal)
    (h_slack : storageSum s.accountMap C - oldVal.toNat + newVal.toNat
                 ≤ balanceOf s.accountMap C)
    (h_newVal_ne_zero : (newVal == default) = false)
    (_hInv : WethInvFr s.accountMap C)
    (hStep : EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s') :
    WethInvFr s'.accountMap C := by
  have h_find_CO : s.accountMap.find? s.executionEnv.codeOwner = some acc := by
    rw [← hCO]; exact h_find
  have h_am := step_SSTORE_accountMap s s' f' cost arg slot newVal tl hStk acc h_find_CO hStep
  rw [h_am, ← hCO]
  exact WethInvFr_of_sstore_replace_with_slack s.accountMap C slot newVal oldVal
    h_newVal_ne_zero acc h_find h_old h_slack

/-! ## §H.2 wiring — `bytecodePreservesInvariant`

Combines the per-PC walks and `WethTrace` predicate with three
structural Weth-bytecode hypotheses to derive
`ΞPreservesInvariantAtC C` via the framework's call-dispatch consumer
entry.

The three structural hypotheses are the **load-bearing pieces**:

* `WethStepClosure` — non-halt-op trace-closure: given a Weth-reachable
  state and a non-halt step, the post-state is Weth-reachable. The
  61 per-PC walks above (`WethTrace_step_at_*`) provide the
  ingredients; aggregating them is mechanical (~58 cases, each
  delegating to a per-PC lemma).
* `WethSStorePreserves` — per-state SSTORE preserves the relational
  invariant. At PC 60 (withdraw), the slot is decremented by `x` and
  the stored value `balance − x` ≤ pre-balance, so `storageSum`
  decreases ⇒ invariant preserved. At PC 40 (deposit), the slot is
  incremented by `msg.value`, but the at-C Ξ pre-state already had
  `msg.value` slack from Θ's pre-credit; threading this through
  `Reachable` requires extending the trace shape.
* `WethCallSlack` — per-state CALL slack precondition at PC 72.
  Slack-callback form (consumer of the framework's
  `_call_slack_dispatch` entry): given the seven popped CALL parameters
  and the residual stack tail, supply the three preconditions of
  `call_invariant_preserved` (no-wrap, sender funds, slack disjunction).
  The slack inequality `v.toNat + storageSum σ C ≤ balanceOf σ C` is
  threaded from PC 60's SSTORE-decrement fact; alternatively the
  recipient ≠ C disjunct discharges via `weth_caller_ne_C`. The IHs
  are threaded internally — the consumer never sees them.

The narrowing lemmas `WethReachable_sstore_pc` (PCs 40, 60) and
`WethReachable_call_pc` (PC 72) reduce per-state case analysis to
the single-PC discharge form. **The framework SSTORE-delta laws
(`storageSum_sstore_replace_eq`, `storageSum_sstore_erase_eq`) are
closed-form**, the **EVM-step bridges**
(`WethInvFr_step_SSTORE_at_C_replace_decr`, `_erase`,
`_replace_with_slack`) compose them with the SSTORE step shape, and
the **per-PC cascade-fact predicates**
(`WethPC{40,60,72}CascadeFacts`) capture the precise per-state
trace-cascade data the dischargers need. The closed-form glue lemmas
(`weth_sstore_preserves_pc60_from_cascade`,
`weth_sstore_preserves_pc40_from_cascade`,
`weth_sstore_preserves_from_cascades`,
`weth_call_slack_from_cascade`) compose these into the larger
`WethSStorePreserves` / `WethCallSlack` shapes.

The convenience entry `bytecodePreservesInvariant_from_cascades`
discharges `ΞPreservesInvariantAtC C` directly from the deployment
witness + the three per-PC cascade-fact predicates — this is what
`WethAssumptions` consumes via `pc40_cascade`, `pc60_cascade`,
`pc72_cascade`.

The **remaining work** to fully discharge `WethAssumptions`'s
cascade-fact predicates inside Lean is the **trace extension**:

  1. **PC 60 storage cascade**: the trace at PCs 48→60 needs to
     carry `(σ.find? C).bind (·.storage.find? slot) = some oldVal`
     through the 12 intermediate steps (PCs 49–59). PC 48's SLOAD
     establishes it; non-SSTORE steps preserve it.
  2. **PC 60 arithmetic cascade**: the trace at PCs 51→60 needs to
     carry `newVal.toNat ≤ oldVal.toNat`. PC 51's LT + PC 55's JUMPI
     not-taken establishes it; non-arithmetic steps preserve it.
  3. **PC 72 slack cascade**: the trace at PCs 60→72 needs to carry
     the post-SSTORE slack `μ₂.toNat + storageSum ≤ balanceOf` plus
     the recipient-as-sender witness from PC 70's CALLER. Both
     propagate through PCs 61–71.
  4. **PC 40 deposit cascade** (deferable): needs Θ-pre-credit slack
     `storageSum - oldVal + newVal ≤ balanceOf`. Threading requires
     lifting the at-`C` Ξ pre-state's β-credit through the trace.

Together with the deployment witness (`hDeployed`), these reduce
`ΞPreservesInvariantAtC C` to a closed-form Lean proof, eliminating
the need for the opaque `WethAssumptions.xi_inv` hypothesis. -/

/-- Refined reachability: `WethTrace C s` minus the post-PC-31-REVERT
halt sink (PC 32 length=0), plus account-presence at `C`, plus
`WethInvFr` (the relational solvency invariant at `C`). The X loop
never re-iterates through the halt sink (PC 31 = REVERT exits the X
loop), so dropping it from the reachable set still covers the
X-induction's needs while satisfying the framework's step closure for
non-halt ops. The third conjunct (`accountPresentAt s.accountMap C`)
makes `WethAccountAtC` derivable from `WethReachable` via projection.
The fourth conjunct (`WethInvFr s.accountMap C`) is the bytecode-level
solvency invariant carried alongside the trace, enabling cascade-fact
dischargers (e.g. for PC 72 CALL slack) to project the invariant
directly from `WethReachable`. -/
private def WethReachable (C : AccountAddress) (s : EVM.State) : Prop :=
  WethTrace C s ∧ ¬ (s.pc.toNat = 32 ∧ s.stack.length = 0) ∧
    accountPresentAt s.accountMap C ∧
    WethInvFr s.accountMap C

/-- `Z` (gas-only update) preserves `WethReachable`. -/
private theorem WethReachable_Z_preserves
    (C : AccountAddress) (s : EVM.State) (g : UInt256)
    (h : WethReachable C s) :
    WethReachable C { s with gasAvailable := g } := by
  obtain ⟨hTrace, hNot, hAcc, hInv⟩ := h
  refine ⟨WethTrace_Z_preserves C s g hTrace, hNot, ?_, ?_⟩
  -- Z preserves accountMap (only changes gasAvailable).
  · exact hAcc
  · exact hInv

/-- Each Weth-reachable state has decode-some at its `pc`. Delegates
to `WethTrace_decodeSome`. -/
private theorem WethReachable_decodeSome
    (C : AccountAddress) (s : EVM.State)
    (h : WethReachable C s) :
    ∃ pair, decode s.executionEnv.code s.pc = some pair :=
  WethTrace_decodeSome C s h.1

/-- The Weth-allowed op-set: strictly-preserves-accountMap, plus
`.CALL` (handled via `call_invariant_preserved`) and `.SSTORE`
(handled per-state by the consumer). All Weth-bytecode ops fall in
one of these classes. -/
private def WethOpAllowed (op : Operation .EVM) : Prop :=
  strictlyPreservesAccountMap op ∨ op = .CALL ∨ op = .StackMemFlow .SSTORE

/-- The op-allowed set's discharge to the framework's `hDischarge`
shape. (Definitional unfolding.) -/
private theorem WethOpAllowed_discharge :
    ∀ op', WethOpAllowed op' →
        strictlyPreservesAccountMap op' ∨ op' = .CALL ∨
        op' = .StackMemFlow .SSTORE :=
  fun _ h => h

/-- Helper: every op decoded at any Weth PC falls in `WethOpAllowed`.
This is the closed-form proof of the `WethOpReach` structural
hypothesis — given any reachable Weth state and the decoded op, the
op is in the allowed-set. Discharged by case-split on the
`WethTrace` disjunct + the per-PC decode lemmas + decidability of
`strictlyPreservesAccountMap` on concrete ops. -/
private theorem WethReachable_op_in_allowed
    (C : AccountAddress) (s : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (h : WethReachable C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg)) :
    WethOpAllowed op := by
  obtain ⟨⟨_, hCode, hPC⟩, _hNot, _, _⟩ := h
  unfold fetchInstr at hFetch
  rw [hCode] at hFetch
  rcases hPC with
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩
  all_goals (rw [pc_eq_ofNat_of_toNat s _ (by decide) hpc] at hFetch)
  all_goals
    simp only [decode_bytecode_at_0, decode_bytecode_at_2,
      decode_bytecode_at_3, decode_bytecode_at_5, decode_bytecode_at_6,
      decode_bytecode_at_7, decode_bytecode_at_12, decode_bytecode_at_13,
      decode_bytecode_at_16, decode_bytecode_at_17, decode_bytecode_at_22,
      decode_bytecode_at_23, decode_bytecode_at_26, decode_bytecode_at_27,
      decode_bytecode_at_29, decode_bytecode_at_31, decode_bytecode_at_32,
      decode_bytecode_at_33, decode_bytecode_at_34, decode_bytecode_at_35,
      decode_bytecode_at_36, decode_bytecode_at_37, decode_bytecode_at_38,
      decode_bytecode_at_39, decode_bytecode_at_40, decode_bytecode_at_41,
      decode_bytecode_at_42, decode_bytecode_at_43, decode_bytecode_at_45,
      decode_bytecode_at_46, decode_bytecode_at_47, decode_bytecode_at_48,
      decode_bytecode_at_49, decode_bytecode_at_50, decode_bytecode_at_51,
      decode_bytecode_at_52, decode_bytecode_at_55, decode_bytecode_at_56,
      decode_bytecode_at_57, decode_bytecode_at_58, decode_bytecode_at_59,
      decode_bytecode_at_60, decode_bytecode_at_61, decode_bytecode_at_63,
      decode_bytecode_at_65, decode_bytecode_at_67, decode_bytecode_at_69,
      decode_bytecode_at_70, decode_bytecode_at_71, decode_bytecode_at_72,
      decode_bytecode_at_73, decode_bytecode_at_74, decode_bytecode_at_77,
      decode_bytecode_at_78, decode_bytecode_at_79, decode_bytecode_at_80,
      decode_bytecode_at_81, decode_bytecode_at_83, decode_bytecode_at_85] at hFetch
  all_goals (simp only [Option.option] at hFetch)
  all_goals (
    injection hFetch with h1
    injection h1 with h1 _
    subst h1)
  -- 64 goals. Each goal is `WethOpAllowed (specific op)`. Three of the
  -- ops are CALL (PC 72) and SSTORE (PCs 40, 60); the rest are
  -- strictlyPreservesAccountMap. We can dispatch via tauto + decide.
  all_goals first
    | (right; right; rfl)         -- SSTORE
    | (right; left; rfl)           -- CALL
    | (left
       refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> intro hh <;>
         exact absurd hh (by decide))  -- strict (handled ∧ ¬SD ∧ ¬SSTORE ∧ ¬TSTORE)

/-- Every `WethOpAllowed` op is non-CREATE/CREATE2. Direct case-split:
strictlyPreservesAccountMap excludes CREATE/CREATE2 (`handledByEvmYulStep`'s
first two conjuncts), CALL ≠ CREATE, SSTORE ≠ CREATE. -/
private theorem WethOpAllowed_no_create
    (op : Operation .EVM) (h : WethOpAllowed op) :
    op ≠ .CREATE ∧ op ≠ .CREATE2 := by
  rcases h with hStrict | hCall | hSStore
  · exact ⟨hStrict.1.1, hStrict.1.2.1⟩
  · subst hCall
    exact ⟨by decide, by decide⟩
  · subst hSStore
    exact ⟨by decide, by decide⟩

/-- Direct discharge of the `hReach_no_create` framework hypothesis for
`WethReachable`: every Weth-reachable state has a non-CREATE/CREATE2
decoded op. Composes `WethReachable_op_in_allowed` with
`WethOpAllowed_no_create`. -/
theorem weth_no_create
    (C : AccountAddress) (s : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (h : WethReachable C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg)) :
    op ≠ .CREATE ∧ op ≠ .CREATE2 :=
  WethOpAllowed_no_create op (WethReachable_op_in_allowed C s op arg h hFetch)

/-- For any handled-strict op (`strictlyPreservesAccountMap`), `EVM.step`
preserves `WethInvFr`. Mirrors `EVM_step_handled_preserves_present`'s
bridging from `EVM.step` to `EvmYul.step`, then dispatches to
`EvmYul_step_preserves_WethInvFr_of_strict`. -/
private theorem EVM_step_strict_preserves_WethInvFr
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (C : AccountAddress) (f cost : ℕ)
    (s s' : EVM.State)
    (hStrict : strictlyPreservesAccountMap op)
    (hStep : EVM.step (f + 1) cost (some (op, arg)) s = .ok s')
    (hInv : WethInvFr s.accountMap C) :
    WethInvFr s'.accountMap C := by
  -- Bridge EVM.step → EvmYul.step at the handled-strict op.
  set s_pre : EVM.State :=
    { s with
        execLength := s.execLength + 1,
        gasAvailable := s.gasAvailable - UInt256.ofNat cost }
    with hs_pre_def
  have hAM : s_pre.accountMap = s.accountMap := rfl
  have hHandled : handledByEvmYulStep op := hStrict.1
  have hStep' : EvmYul.step op arg s_pre = .ok s' := by
    unfold EVM.step at hStep
    simp only [bind, Except.bind, pure, Except.pure] at hStep
    obtain ⟨hne1, hne2, hne3, hne4, hne5, hne6⟩ := hHandled
    cases op with
    | StopArith _ => exact hStep
    | CompBit _ => exact hStep
    | Keccak _ => exact hStep
    | Env _ => exact hStep
    | Block _ => exact hStep
    | StackMemFlow _ => exact hStep
    | Push _ => exact hStep
    | Dup _ => exact hStep
    | Exchange _ => exact hStep
    | Log _ => exact hStep
    | System o =>
      cases o with
      | CREATE => exact absurd rfl hne1
      | CALL => exact absurd rfl hne3
      | CALLCODE => exact absurd rfl hne4
      | RETURN => exact hStep
      | DELEGATECALL => exact absurd rfl hne5
      | CREATE2 => exact absurd rfl hne2
      | STATICCALL => exact absurd rfl hne6
      | REVERT => exact hStep
      | INVALID => exact hStep
      | SELFDESTRUCT => exact hStep
  have hInv_pre : WethInvFr s_pre.accountMap C := by
    rw [hAM]; exact hInv
  exact EvmYul_step_preserves_WethInvFr_of_strict op arg s_pre s' C hStrict
    hStep' hInv_pre

/-! ## Structural hypotheses (§H.2 closure for Weth's bytecode)

These three predicates capture the load-bearing per-state facts that
`bytecodePreservesInvariant` consumes from the bundle of per-PC walks
plus the bytecode-level slack reasoning. -/

/-- **Bytecode-level per-step `WethInvFr` preservation predicate.**
Every reachable non-halt step preserves `WethInvFr`. Used to thread the
fourth conjunct of `WethReachable` (`WethInvFr s.accountMap C`) through
`weth_step_closure`'s 61 per-PC walks.

Discharged in-Lean (modulo CALL) by `weth_inv_step_pres`:
* For strict ops (most PCs): closed-form via
  `EVM_step_strict_preserves_WethInvFr`.
* For SSTORE PCs (40, 60): closed-form via
  `weth_sstore_preserves_pc{40,60}_from_cascade` with cascade facts
  derived from σ-has-C (= `weth_account_at_C`) and the Θ-pre-credit
  `WethDepositPreCredit`.
* For CALL PC (72): delegated to a `WethCALLStepInvFr C` argument —
  the only branch needing the framework's strong-induction IHs (via
  `step_CALL_arm_at_C_slack_invariant`'s
  `ΞInvariantAtCFrame`/`ΞInvariantFrameAtC` slots), which are not
  exposed by the framework's `hReach_step` interface. -/
def WethStepInvFrPreserves (C : AccountAddress) : Prop :=
  ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ op arg,
    WethReachable C s →
    fetchInstr s.executionEnv s.pc = .ok (op, arg) →
    EVM.step (f' + 1) cost (some (op, arg)) s = .ok s' →
    op ≠ .RETURN → op ≠ .REVERT → op ≠ .STOP → op ≠ .SELFDESTRUCT →
    WethInvFr s'.accountMap C

/-- **Narrowed CALL-only step preservation predicate.** Like
`WethStepInvFrPreserves` but specialised to CALL — the only op for which
the per-step preservation needs the framework's strong-induction IHs
(via `step_CALL_arm_at_C_slack_invariant`'s `hAtCFrame`/`hFrame`).

This isolates the genuinely-non-derivable case from the trivially
derivable strict + SSTORE cases (handled inline by
`weth_inv_step_pres` below). -/
def WethCALLStepInvFr (C : AccountAddress) : Prop :=
  ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
    WethReachable C s →
    fetchInstr s.executionEnv s.pc = .ok (.CALL, arg) →
    EVM.step (f' + 1) cost (some (.CALL, arg)) s = .ok s' →
    WethInvFr s'.accountMap C

/-- Step closure of `WethReachable` under non-halt operations. The 61
per-PC walks (`WethTrace_step_at_*` above) provide the ingredients —
aggregating them into this aggregate is mechanical case-splitting.

The `hΞ : ΞPreservesAccountAt C` parameter is consumed by the walks
to propagate `accountPresentAt` (the third conjunct of
`WethReachable`) across each step via the framework's
`EVM_step_preserves_present_no_create`.

The `WethStepInvFrPreserves C` parameter discharges the fourth conjunct
(`WethInvFr s'.accountMap C`) per-step. -/
def WethStepClosure (C : AccountAddress) : Prop :=
  ΞPreservesAccountAt C →
  WethStepInvFrPreserves C →
  ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ op arg,
    WethReachable C s →
    fetchInstr s.executionEnv s.pc = .ok (op, arg) →
    EVM.step (f' + 1) cost (some (op, arg)) s = .ok s' →
    op ≠ .RETURN → op ≠ .REVERT → op ≠ .STOP → op ≠ .SELFDESTRUCT →
    WethReachable C s'

-- (`WethOpReach` removed: discharged in-Lean by
-- `WethReachable_op_in_allowed` above.)

/-! ### Helpers for the step-closure aggregate

Two helpers reduce the boilerplate inside `weth_step_closure`. Each per-PC
case yields `WethTrace s'` (via the matching `WethTrace_step_at_N`) plus
either `s'.pc.toNat ≠ 32` or `s'.stack.length ≠ 0` (from the per-PC step
shape). The two helpers project these into `WethReachable s'`. -/

private theorem WethReachable_of_WethTrace_pc_ne_32
    {C : AccountAddress} {s : EVM.State}
    (hAcc : accountPresentAt s.accountMap C)
    (hInv : WethInvFr s.accountMap C)
    (hT : WethTrace C s) (hpc_ne : s.pc.toNat ≠ 32) :
    WethReachable C s :=
  ⟨hT, fun ⟨h1, _⟩ => hpc_ne h1, hAcc, hInv⟩

private theorem WethReachable_of_WethTrace_len_ne_0
    {C : AccountAddress} {s : EVM.State}
    (hAcc : accountPresentAt s.accountMap C)
    (hInv : WethInvFr s.accountMap C)
    (hT : WethTrace C s) (hlen : s.stack.length ≠ 0) :
    WethReachable C s :=
  ⟨hT, fun ⟨_, h2⟩ => hlen h2, hAcc, hInv⟩

/-! ### PC-narrowing lemmas for SSTORE / CALL

The `WethSStorePreserves` and `WethCallSlack` predicates quantify over
all reachable states where `fetchInstr` returns SSTORE / CALL. By the
bytecode walk, the only such states are at PC 40 / 60 (SSTORE) and
PC 72 (CALL). These narrowing lemmas extract that fact in closed form
from the `WethReachable` predicate, providing a clean entry point for
future per-state dischargers (which must then case-split on PC 40 vs
PC 60 for SSTORE; PC 72 is the unique CALL site).

Both lemmas are pure case-analysis on `WethTrace`'s 64 disjuncts,
using the per-PC `decode_bytecode_at_*` lemmas to rule out non-SSTORE /
non-CALL PCs by op-mismatch in `fetchInstr`. -/

/-- A reachable Weth state with `fetchInstr` returning SSTORE has
`s.pc.toNat = 40 ∨ s.pc.toNat = 60`. Used by `WethSStorePreserves`
dischargers to narrow the case split to the two SSTORE PCs. -/
private theorem WethReachable_sstore_pc
    {C : AccountAddress} {s : EVM.State} {arg : Option (UInt256 × Nat)}
    (hR : WethReachable C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg)) :
    s.pc.toNat = 40 ∨ s.pc.toNat = 60 := by
  obtain ⟨⟨_, hCode, hPC⟩, _⟩ := hR
  unfold fetchInstr at hFetch
  rw [hCode] at hFetch
  rcases hPC with
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩
  -- Every disjunct rewrites the PC and the decoded op. SSTORE only at
  -- PCs 40 and 60. All other disjuncts produce a fetch-decoded op
  -- inequality (their op is not SSTORE), refuted by `injection`.
  case _ => -- PC 0
    rw [pc_eq_ofNat_of_toNat s 0 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_0] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 2
    rw [pc_eq_ofNat_of_toNat s 2 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_2] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 3
    rw [pc_eq_ofNat_of_toNat s 3 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_3] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 5
    rw [pc_eq_ofNat_of_toNat s 5 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_5] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 6
    rw [pc_eq_ofNat_of_toNat s 6 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_6] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 7
    rw [pc_eq_ofNat_of_toNat s 7 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_7] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 12
    rw [pc_eq_ofNat_of_toNat s 12 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_12] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 13
    rw [pc_eq_ofNat_of_toNat s 13 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_13] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 16
    rw [pc_eq_ofNat_of_toNat s 16 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_16] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 17
    rw [pc_eq_ofNat_of_toNat s 17 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_17] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 22
    rw [pc_eq_ofNat_of_toNat s 22 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_22] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 23
    rw [pc_eq_ofNat_of_toNat s 23 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_23] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 26
    rw [pc_eq_ofNat_of_toNat s 26 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_26] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 27
    rw [pc_eq_ofNat_of_toNat s 27 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_27] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 29
    rw [pc_eq_ofNat_of_toNat s 29 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_29] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 31 (REVERT)
    rw [pc_eq_ofNat_of_toNat s 31 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_31] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 32 length 0
    rw [pc_eq_ofNat_of_toNat s 32 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_32] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 32 length 1
    rw [pc_eq_ofNat_of_toNat s 32 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_32] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 33
    rw [pc_eq_ofNat_of_toNat s 33 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_33] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 34
    rw [pc_eq_ofNat_of_toNat s 34 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_34] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 35
    rw [pc_eq_ofNat_of_toNat s 35 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_35] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 36
    rw [pc_eq_ofNat_of_toNat s 36 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_36] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 37
    rw [pc_eq_ofNat_of_toNat s 37 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_37] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 38
    rw [pc_eq_ofNat_of_toNat s 38 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_38] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 39
    rw [pc_eq_ofNat_of_toNat s 39 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_39] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 40 (SSTORE)
    left; exact hpc
  case _ => -- PC 41 (STOP)
    rw [pc_eq_ofNat_of_toNat s 41 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_41] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 42
    rw [pc_eq_ofNat_of_toNat s 42 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_42] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 43
    rw [pc_eq_ofNat_of_toNat s 43 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_43] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 45
    rw [pc_eq_ofNat_of_toNat s 45 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_45] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 46
    rw [pc_eq_ofNat_of_toNat s 46 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_46] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 47
    rw [pc_eq_ofNat_of_toNat s 47 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_47] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 48
    rw [pc_eq_ofNat_of_toNat s 48 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_48] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 49
    rw [pc_eq_ofNat_of_toNat s 49 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_49] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 50
    rw [pc_eq_ofNat_of_toNat s 50 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_50] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 51
    rw [pc_eq_ofNat_of_toNat s 51 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_51] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 52
    rw [pc_eq_ofNat_of_toNat s 52 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_52] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 55
    rw [pc_eq_ofNat_of_toNat s 55 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_55] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 56
    rw [pc_eq_ofNat_of_toNat s 56 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_56] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 57
    rw [pc_eq_ofNat_of_toNat s 57 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_57] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 58
    rw [pc_eq_ofNat_of_toNat s 58 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_58] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 59
    rw [pc_eq_ofNat_of_toNat s 59 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_59] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 60 (SSTORE)
    right; exact hpc
  case _ => -- PC 61
    rw [pc_eq_ofNat_of_toNat s 61 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_61] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 63
    rw [pc_eq_ofNat_of_toNat s 63 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_63] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 65
    rw [pc_eq_ofNat_of_toNat s 65 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_65] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 67
    rw [pc_eq_ofNat_of_toNat s 67 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_67] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 69
    rw [pc_eq_ofNat_of_toNat s 69 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_69] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 70
    rw [pc_eq_ofNat_of_toNat s 70 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_70] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 71
    rw [pc_eq_ofNat_of_toNat s 71 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_71] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 72 (CALL)
    rw [pc_eq_ofNat_of_toNat s 72 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_72] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 73
    rw [pc_eq_ofNat_of_toNat s 73 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_73] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 74
    rw [pc_eq_ofNat_of_toNat s 74 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_74] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 77
    rw [pc_eq_ofNat_of_toNat s 77 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_77] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 78
    rw [pc_eq_ofNat_of_toNat s 78 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_78] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 79
    rw [pc_eq_ofNat_of_toNat s 79 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_79] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 80 length 3
    rw [pc_eq_ofNat_of_toNat s 80 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_80] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 80 length 1
    rw [pc_eq_ofNat_of_toNat s 80 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_80] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 81 length 3
    rw [pc_eq_ofNat_of_toNat s 81 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_81] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 81 length 1
    rw [pc_eq_ofNat_of_toNat s 81 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_81] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 83 length 4
    rw [pc_eq_ofNat_of_toNat s 83 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_83] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 83 length 2
    rw [pc_eq_ofNat_of_toNat s 83 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_83] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 85 length 5
    rw [pc_eq_ofNat_of_toNat s 85 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_85] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1
  case _ => -- PC 85 length 3
    rw [pc_eq_ofNat_of_toNat s 85 (by decide) hpc] at hFetch
    rw [decode_bytecode_at_85] at hFetch
    simp only [Option.option] at hFetch
    injection hFetch with h1
    injection h1 with h1 _
    cases h1

/-- A reachable Weth state with `fetchInstr` returning CALL has
`s.pc.toNat = 72`. Used by `WethCallSlack` dischargers to fix the
unique CALL site at PC 72. -/
private theorem WethReachable_call_pc
    {C : AccountAddress} {s : EVM.State} {arg : Option (UInt256 × Nat)}
    (hR : WethReachable C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (.CALL, arg)) :
    s.pc.toNat = 72 := by
  obtain ⟨⟨_, hCode, hPC⟩, _⟩ := hR
  unfold fetchInstr at hFetch
  rw [hCode] at hFetch
  rcases hPC with
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩
  -- Every disjunct rewrites the PC and the decoded op. CALL only at
  -- PC 72. All other disjuncts give a fetch-decoded op inequality.
  all_goals first
    | exact hpc
    | (rw [pc_eq_ofNat_of_toNat s _ (by decide) hpc] at hFetch
       first
       | rw [decode_bytecode_at_0] at hFetch
       | rw [decode_bytecode_at_2] at hFetch
       | rw [decode_bytecode_at_3] at hFetch
       | rw [decode_bytecode_at_5] at hFetch
       | rw [decode_bytecode_at_6] at hFetch
       | rw [decode_bytecode_at_7] at hFetch
       | rw [decode_bytecode_at_12] at hFetch
       | rw [decode_bytecode_at_13] at hFetch
       | rw [decode_bytecode_at_16] at hFetch
       | rw [decode_bytecode_at_17] at hFetch
       | rw [decode_bytecode_at_22] at hFetch
       | rw [decode_bytecode_at_23] at hFetch
       | rw [decode_bytecode_at_26] at hFetch
       | rw [decode_bytecode_at_27] at hFetch
       | rw [decode_bytecode_at_29] at hFetch
       | rw [decode_bytecode_at_31] at hFetch
       | rw [decode_bytecode_at_32] at hFetch
       | rw [decode_bytecode_at_33] at hFetch
       | rw [decode_bytecode_at_34] at hFetch
       | rw [decode_bytecode_at_35] at hFetch
       | rw [decode_bytecode_at_36] at hFetch
       | rw [decode_bytecode_at_37] at hFetch
       | rw [decode_bytecode_at_38] at hFetch
       | rw [decode_bytecode_at_39] at hFetch
       | rw [decode_bytecode_at_40] at hFetch
       | rw [decode_bytecode_at_41] at hFetch
       | rw [decode_bytecode_at_42] at hFetch
       | rw [decode_bytecode_at_43] at hFetch
       | rw [decode_bytecode_at_45] at hFetch
       | rw [decode_bytecode_at_46] at hFetch
       | rw [decode_bytecode_at_47] at hFetch
       | rw [decode_bytecode_at_48] at hFetch
       | rw [decode_bytecode_at_49] at hFetch
       | rw [decode_bytecode_at_50] at hFetch
       | rw [decode_bytecode_at_51] at hFetch
       | rw [decode_bytecode_at_52] at hFetch
       | rw [decode_bytecode_at_55] at hFetch
       | rw [decode_bytecode_at_56] at hFetch
       | rw [decode_bytecode_at_57] at hFetch
       | rw [decode_bytecode_at_58] at hFetch
       | rw [decode_bytecode_at_59] at hFetch
       | rw [decode_bytecode_at_60] at hFetch
       | rw [decode_bytecode_at_61] at hFetch
       | rw [decode_bytecode_at_63] at hFetch
       | rw [decode_bytecode_at_65] at hFetch
       | rw [decode_bytecode_at_67] at hFetch
       | rw [decode_bytecode_at_69] at hFetch
       | rw [decode_bytecode_at_70] at hFetch
       | rw [decode_bytecode_at_71] at hFetch
       | rw [decode_bytecode_at_73] at hFetch
       | rw [decode_bytecode_at_74] at hFetch
       | rw [decode_bytecode_at_77] at hFetch
       | rw [decode_bytecode_at_78] at hFetch
       | rw [decode_bytecode_at_79] at hFetch
       | rw [decode_bytecode_at_80] at hFetch
       | rw [decode_bytecode_at_81] at hFetch
       | rw [decode_bytecode_at_83] at hFetch
       | rw [decode_bytecode_at_85] at hFetch
       simp only [Option.option] at hFetch
       injection hFetch with h1
       injection h1 with h1 _
       cases h1)

/-- Per-state SSTORE invariant preservation. At every reachable SSTORE
state, the post-step `WethInvFr` holds. The two SSTORE PCs in Weth
are PC 40 (deposit, slot += msg.value) and PC 60 (withdraw, slot −=
x). PC 60 strictly decreases `storageSum`; PC 40 needs slack from
the Θ-pre-credit which propagates through the trace shape. -/
def WethSStorePreserves (C : AccountAddress) : Prop :=
  ∀ s s' : EVM.State, ∀ f' cost : ℕ, ∀ arg,
    WethReachable C s →
    StateWF s.accountMap →
    C = s.executionEnv.codeOwner →
    WethInvFr s.accountMap C →
    fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
    EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
    WethInvFr s'.accountMap C

/-! ### Conditional discharger for the PC 60 (withdraw decrement) SSTORE case

`WethSStorePreserves_PC60_of_storage_facts` is a closed-form proof of
the SSTORE invariant-preservation step at PC 60, conditional on the
storage facts that PC 60's bytecode walk establishes:

* the SSTORE pops `(slot, newVal)` where `slot` is the sender's slot
  and `newVal = old − x` (the decremented balance);
* the slot's pre-storage value is `oldVal`;
* `newVal.toNat ≤ oldVal.toNat` (from PC 51 LT + PC 55 JUMPI not-taken).

The §H.2 walk lands exactly on this shape; the missing piece for
in-Lean discharge is exposing these per-state facts in `WethReachable`
at PC 60 (see `SOLVENCY_PLAN.md`'s trace-extension roadmap).

Until trace extension lands, this lemma is the closed-form template
that the eventual discharger composes; it is ready-to-call once the
trace exposes the prerequisite facts. -/
theorem WethSStorePreserves_PC60_decr
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (arg : Option (UInt256 × Nat))
    (slot newVal oldVal : UInt256) (tl : Stack UInt256)
    (hCO : C = s.executionEnv.codeOwner)
    (hStk : s.stack = slot :: newVal :: tl)
    (acc : Account .EVM)
    (h_find : s.accountMap.find? C = some acc)
    (h_old : acc.storage.find? slot = some oldVal)
    (h_le : newVal.toNat ≤ oldVal.toNat)
    (h_newVal_ne_zero : (newVal == default) = false)
    (hInv : WethInvFr s.accountMap C)
    (hStep : EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s') :
    WethInvFr s'.accountMap C :=
  WethInvFr_step_SSTORE_at_C_replace_decr C s s' f' cost arg slot newVal oldVal tl
    hStk hCO acc h_find h_old h_le h_newVal_ne_zero hInv hStep

/-- Variant for the SSTORE-erase case (`newVal = 0`): closed-form
preservation at any reachable SSTORE step where the new value is
zero. Used by Weth (and any contract) for slot-clearing patterns. -/
theorem WethSStorePreserves_erase
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (arg : Option (UInt256 × Nat))
    (slot oldVal : UInt256) (tl : Stack UInt256)
    (hCO : C = s.executionEnv.codeOwner)
    (hStk : s.stack = slot :: ⟨0⟩ :: tl)
    (acc : Account .EVM)
    (h_find : s.accountMap.find? C = some acc)
    (h_old : acc.storage.find? slot = some oldVal)
    (hInv : WethInvFr s.accountMap C)
    (hStep : EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s') :
    WethInvFr s'.accountMap C :=
  WethInvFr_step_SSTORE_at_C_erase C s s' f' cost arg slot oldVal tl
    hStk hCO acc h_find h_old hInv hStep

/-! ### Narrower cascade-fact predicates for SSTORE / CALL discharge

The full `WethSStorePreserves` / `WethCallSlack` predicates ask the
caller to discharge the entire post-step invariant or full slack
disjunction at every reachable SSTORE/CALL state. With the closed-form
bridges (`WethSStorePreserves_PC60_decr`, `WethSStorePreserves_erase`,
the slack-callback's three preconditions), the discharge depends only
on a small set of **cascade-trace facts** at the trace level:

* **PC 60 (withdraw SSTORE)**: stack shape `[sender_uint, balance−x, x]`,
  storage[sender_uint] = some `balance`, and `(balance−x).toNat ≤ balance.toNat`.
* **PC 40 (deposit SSTORE)**: stack shape, storage value, plus the
  Θ-prefix slack `(balance + x).toNat ≤ acc.balance.toNat`.
* **PC 72 (CALL)**: stack shape `[gas, to, x, ao, as, ro, rs, x']` with
  `to = AccountAddress.ofUInt256 sender`, plus the post-PC-60 slack
  invariant `x.toNat + storageSum σ C ≤ balanceOf σ C`.

The lemmas below define the **narrower per-PC cascade-fact predicates**
and the **closed-form glue** showing they imply the larger
`WethSStorePreserves` / `WethCallSlack` shapes. With these in place,
dropping the bigger structural hypotheses reduces to discharging the
narrower cascade-fact predicates, which is exactly what trace
extension (PCs 48→60→72) would establish.

This is the **interface** the trace cascade lands against: the trace
cascade extension makes these narrower predicates true, and these
glue lemmas pipe that into the framework's `bytecodePreservesInvariant`. -/

/-- **PC 60 cascade fact predicate.** At every Weth-reachable state at
PC 60 (the withdraw SSTORE), the trace cascade exposes one of two
disjuncts:

* **decrement** — non-zero new value: stack `[slot, newVal, …]`,
  `s.accountMap.find? C = some acc`,
  `acc.storage.findD slot ⟨0⟩ = oldVal`,
  `newVal.toNat ≤ oldVal.toNat`, `(newVal == default) = false`.
* **erase** — zero new value: stack `[slot, ⟨0⟩, …]`,
  `s.accountMap.find? C = some acc`,
  `acc.storage.findD slot ⟨0⟩ = oldVal`.

The `findD slot ⟨0⟩` shape (rather than `find? slot = some _`) matches
EVM SSTORE-after-SLOAD semantics: SLOAD-of-missing returns `0`, and
the SLOAD-strong wrapper exposes the pushed value as exactly
`acc.storage.findD slot ⟨0⟩`. The downstream glue
(`weth_sstore_preserves_pc60_from_cascade`) case-splits on
`find? slot` to recover the underlying `find?`-form needed by the
storage-sum delta lemmas.

Discharged by extending the trace at PCs 48→60: PC 48's SLOAD
establishes the storage fact; PC 51's LT + PC 55's JUMPI not-taken
establishes the bound. -/
def WethPC60CascadeFacts (C : AccountAddress) : Prop :=
  ∀ s : EVM.State,
    WethReachable C s →
    s.pc.toNat = 60 →
    fetchInstr s.executionEnv s.pc =
      .ok (.StackMemFlow .SSTORE, none) →
    ∃ (slot : UInt256) (tl : Stack UInt256),
      ∃ (acc : Account .EVM) (oldVal : UInt256),
        s.accountMap.find? C = some acc ∧
        acc.storage.findD slot ⟨0⟩ = oldVal ∧
        ((∃ newVal,
            s.stack = slot :: newVal :: tl ∧
            newVal.toNat ≤ oldVal.toNat ∧
            (newVal == default) = false) ∨
         s.stack = slot :: ⟨0⟩ :: tl)

/-- Extract the PC 60 cascade witnesses from a Weth-reachable state at
PC 60. Discharged from the threaded WethTrace cascade (PCs 47..60). -/
private theorem WethReachable_pc60_cascade
    (C : AccountAddress) (s : EVM.State)
    (hR : WethReachable C s) (hPC60 : s.pc.toNat = 60) :
    ∃ slot oldVal x : UInt256,
      s.stack = slot :: UInt256.sub oldVal x :: x :: [] ∧
      oldVal = (s.accountMap.find? C).option ⟨0⟩
                 (Account.lookupStorage (k := slot)) ∧
      x.toNat ≤ oldVal.toNat := by
  obtain ⟨⟨_, _, hPC⟩, _⟩ := hR
  -- All 64 disjuncts named uniformly except PC 60's cascade.
  rcases hPC with
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, hCascade⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩
  -- PC 60's case has hCascade in scope; all others derive False from hpc + hPC60.
  all_goals first
    | exact hCascade
    | (exfalso; omega)

/-- σ-has-C invariant: every Weth-reachable state has σ.find? C = some _.

This is the **structural fact** that replaces the opaque
`WethPC60CascadeFacts` assumption. It is much narrower (only asserts
account presence, not full cascade-trace data) and is true because:

1. Λ enters Weth at C with σ[C] = some acc (framework guarantee).
2. Weth's bytecode has no SELFDESTRUCT.
3. SSTORE preserves account presence (it inserts/updates).
4. CALL preserves σ at the executing-frame address (Θ-preservation).

Bundled as a structural assumption to avoid threading σ-has-C through
all 61 walks of `weth_step_closure`. The eventual framework-level
discharger would expose a "Reachable preserves σ-at-codeOwner" helper. -/
def WethAccountAtC (C : AccountAddress) : Prop :=
  ∀ s : EVM.State, WethReachable C s →
    ∃ acc : Account .EVM, s.accountMap.find? C = some acc

/-- **`WethAccountAtC` is a theorem.** Discharged via the σ-has-C
conjunct in `WethReachable`'s definition. -/
theorem weth_account_at_C (C : AccountAddress) : WethAccountAtC C :=
  fun _ hR => hR.2.2.1

/-- **`WethPC60CascadeFacts` is a theorem given σ-has-C.** Discharges
the cascade fact predicate from the threaded WethTrace cascade plus a
narrow structural fact: every Weth-reachable state has σ.find? C =
some acc. The σ-has-C fact is true (Weth has no SELFDESTRUCT and Ξ
enters at C) but proving it uniformly across the trace requires
extending WethReachable's preservation; here we expose it as a hook. -/
theorem weth_pc60_cascade
    (C : AccountAddress)
    (hAccC : WethAccountAtC C) :
    WethPC60CascadeFacts C := by
  intro s hR hPC60 _hFetch
  obtain ⟨slot, oldVal, x, hStk_eq, hOldVal, hBound⟩ :=
    WethReachable_pc60_cascade C s hR hPC60
  obtain ⟨acc, h_find⟩ := hAccC s hR
  -- Convert oldVal to acc.storage.findD slot ⟨0⟩ via h_find.
  have h_findD : acc.storage.findD slot ⟨0⟩ = oldVal := by
    rw [h_find] at hOldVal
    -- hOldVal : oldVal = (some acc).option ⟨0⟩ (lookupStorage slot)
    --        = acc.storage.findD slot ⟨0⟩
    show acc.storage.findD slot ⟨0⟩ = oldVal
    rw [hOldVal]
    rfl
  -- newVal = sub oldVal x. Bound: x ≤ oldVal ⇒ (sub oldVal x).toNat ≤ oldVal.toNat.
  have h_subVal : (UInt256.sub oldVal x).toNat ≤ oldVal.toNat := by
    have hSub_eq : UInt256.sub oldVal x = oldVal - x := rfl
    rw [hSub_eq, UInt256_sub_toNat_of_le _ _ hBound]
    exact Nat.sub_le _ _
  refine ⟨slot, [x], acc, oldVal, h_find, h_findD, ?_⟩
  -- Case-split on newVal = 0 (erase) vs ≠ 0 (decrement).
  by_cases h_eq : UInt256.sub oldVal x = default
  · -- Erase arm: newVal = 0.
    right
    rw [h_eq] at hStk_eq
    exact hStk_eq
  · -- Decrement arm.
    left
    refine ⟨UInt256.sub oldVal x, hStk_eq, h_subVal, ?_⟩
    -- (UInt256.sub oldVal x == default) = false from h_eq.
    -- For UInt256 (deriving BEq from Fin), `(a == b) = false` ↔ a ≠ b.
    have hd : (UInt256.sub oldVal x).val ≠ (default : UInt256).val := fun h_val_eq =>
      h_eq (UInt256.mk.injEq _ _ |>.mpr h_val_eq)
    show ((UInt256.sub oldVal x).val == (default : UInt256).val) = false
    show (decide ((UInt256.sub oldVal x).val = (default : UInt256).val) : Bool) = false
    exact decide_eq_false hd

/-- **PC 40 cascade fact predicate.** At every Weth-reachable state at
PC 40 (the deposit SSTORE), the trace cascade exposes:

* stack shape `[slot, newVal, …]`,
* `s.accountMap.find? C = some acc`,
* `acc.storage.findD slot ⟨0⟩ = oldVal` (the `findD`-flavored shape
  matching SLOAD-strong; reduces to `find? slot = some oldVal` when
  the slot exists, and to `oldVal = ⟨0⟩` when it does not),
* the at-`C` Ξ-pre-state β-credit slack:
  `storageSum σ C - oldVal.toNat + newVal.toNat ≤ balanceOf σ C`,
  which combined with the SSTORE-replace law yields the post-step
  invariant.

Discharged by extending the trace at PCs 32→40 plus the Θ-pre-credit
slack tracked at the Ξ entry point. -/
def WethPC40CascadeFacts (C : AccountAddress) : Prop :=
  ∀ s : EVM.State,
    WethReachable C s →
    s.pc.toNat = 40 →
    fetchInstr s.executionEnv s.pc =
      .ok (.StackMemFlow .SSTORE, none) →
    ∃ (slot : UInt256) (tl : Stack UInt256),
      ∃ (acc : Account .EVM) (oldVal : UInt256),
        s.accountMap.find? C = some acc ∧
        acc.storage.findD slot ⟨0⟩ = oldVal ∧
        ((∃ newVal,
            s.stack = slot :: newVal :: tl ∧
            storageSum s.accountMap C - oldVal.toNat + newVal.toNat
              ≤ balanceOf s.accountMap C ∧
            (newVal == default) = false) ∨
         s.stack = slot :: ⟨0⟩ :: tl)

/-- **Bytecode-derivable cascade at PC 40 (deposit SSTORE).**

At every Weth-reachable PC 40 state, the stack and storage are in the
form expected by the deposit flow: stack = [sender, newBal, …] where
`sender = CALLER` (pushed at PC 34) and `newBal = SLOAD(sender) +
msg.value` (computed at PC 38 ADD).

The storage equation uses the **`findD slot ⟨0⟩`** shape (matching
SLOAD-strong's pushed-value semantics: SLOAD-of-missing returns `⟨0⟩`)
rather than a strict `find? slot = some oldVal` form. This matches
the cascade actually exposable from the WethTrace cascade threading at
PCs 36→40 (commit 14dd324) — the strict `find?` form would not be
derivable from bytecode walks for first-time depositors.

Discharged as `weth_deposit_cascade` theorem from the cascade thread.  -/
def WethDepositCascadeStruct (C : AccountAddress) : Prop :=
  ∀ s : EVM.State,
    WethReachable C s →
    s.pc.toNat = 40 →
    fetchInstr s.executionEnv s.pc =
      .ok (.StackMemFlow .SSTORE, none) →
    ∃ (slot : UInt256) (tl : Stack UInt256),
      ∃ (acc : Account .EVM) (oldVal : UInt256),
        s.accountMap.find? C = some acc ∧
        acc.storage.findD slot ⟨0⟩ = oldVal ∧
        (∃ newVal, s.stack = slot :: newVal :: tl)

/-- **Θ-pre-credit slack at PC 40 (deposit SSTORE).**

The genuinely-Υ-side fact: at PC 40, `storageSum σ C - oldVal +
newVal ≤ balanceOf σ C`. This encodes that Θ already credited
`msg.value` to C's balance before Ξ entered, so the post-SSTORE
storageSum (= old storageSum + msg.value) is bounded by the post-Θ
balance (= pre-Θ balance + msg.value).

**Cannot be derived from bytecode walks alone** — it lives in the
framework's outer Θ/Λ layer. Stays as a structural assumption.

The disjunction (decrement vs. erase) handles both newVal ≠ 0 (normal
deposit) and newVal = 0 (zero-deposit edge case, where the slack is
trivially the existing `storageSum - oldVal ≤ balanceOf` from the
pre-state invariant). -/
def WethDepositPreCredit (C : AccountAddress) : Prop :=
  ∀ s : EVM.State,
    WethReachable C s →
    s.pc.toNat = 40 →
    fetchInstr s.executionEnv s.pc =
      .ok (.StackMemFlow .SSTORE, none) →
    ∀ (slot : UInt256) (tl : Stack UInt256) (acc : Account .EVM)
      (oldVal : UInt256),
      s.accountMap.find? C = some acc →
      acc.storage.findD slot ⟨0⟩ = oldVal →
      ((∃ newVal,
          s.stack = slot :: newVal :: tl ∧
          storageSum s.accountMap C - oldVal.toNat + newVal.toNat
            ≤ balanceOf s.accountMap C ∧
          (newVal == default) = false) ∨
       s.stack = slot :: ⟨0⟩ :: tl)

/-- Extract the PC 40 cascade witnesses from a Weth-reachable state at
PC 40. Discharged from the threaded WethTrace cascade (PCs 36..40). -/
private theorem WethReachable_pc40_cascade
    (C : AccountAddress) (s : EVM.State)
    (hR : WethReachable C s) (hPC40 : s.pc.toNat = 40) :
    ∃ slot oldVal newVal : UInt256,
      s.stack = slot :: newVal :: [] ∧
      oldVal = (s.accountMap.find? C).option ⟨0⟩
                 (Account.lookupStorage (k := slot)) := by
  obtain ⟨⟨_, _, hPC⟩, _⟩ := hR
  -- PC 40 is the 26th disjunct (0-indexed 25). All other disjuncts derive
  -- False from hpc + hPC40.
  rcases hPC with
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, hCascade⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩
  all_goals first
    | exact hCascade
    | (exfalso; omega)

/-- **`WethDepositCascadeStruct` is a theorem.** Discharged from the
σ-has-C fact (`WethAccountAtC` — itself a theorem now) plus the
threaded WethTrace cascade at PCs 36..40. The cascade exposes the
storage equation in `findD`-flavored form (matching SLOAD-strong's
pushed-value semantics: `findD slot ⟨0⟩ = oldVal`); first-time
depositors carry `oldVal = ⟨0⟩` via this shape. -/
theorem weth_deposit_cascade
    (C : AccountAddress)
    (hAccC : WethAccountAtC C) :
    WethDepositCascadeStruct C := by
  intro s hR hPC40 _hFetch
  obtain ⟨slot, oldVal, newVal, hStk_eq, hOldVal⟩ :=
    WethReachable_pc40_cascade C s hR hPC40
  obtain ⟨acc, h_find⟩ := hAccC s hR
  -- Convert oldVal to acc.storage.findD slot ⟨0⟩ via h_find.
  have h_findD : acc.storage.findD slot ⟨0⟩ = oldVal := by
    rw [h_find] at hOldVal
    -- hOldVal : oldVal = (some acc).option ⟨0⟩ (lookupStorage slot)
    --        = acc.storage.findD slot ⟨0⟩
    show acc.storage.findD slot ⟨0⟩ = oldVal
    rw [hOldVal]
    rfl
  refine ⟨slot, [], acc, oldVal, h_find, h_findD, newVal, ?_⟩
  exact hStk_eq

/-- **`WethPC40CascadeFacts` is a theorem given the two narrower
structural facts.** -/
theorem weth_pc40_cascade
    (C : AccountAddress)
    (hCascade : WethDepositCascadeStruct C)
    (hPreCredit : WethDepositPreCredit C) :
    WethPC40CascadeFacts C := by
  intro s hR hPC40 hFetch
  obtain ⟨slot, tl, acc, oldVal, h_find, h_findSlot, _hStk⟩ :=
    hCascade s hR hPC40 hFetch
  refine ⟨slot, tl, acc, oldVal, h_find, h_findSlot, ?_⟩
  exact hPreCredit s hR hPC40 hFetch slot tl acc oldVal h_find h_findSlot

/-- **PC 60 SSTORE preservation from cascade facts.** Closed-form glue:
given the cascade facts at PC 60, every reachable SSTORE step at PC 60
preserves the invariant. Composes `WethReachable_sstore_pc` to fix the
PC, then dispatches between `_replace_decr` and `_erase` based on the
zero-check on `newVal`. -/
private theorem weth_sstore_preserves_pc60_from_cascade
    (C : AccountAddress) (hCascade : WethPC60CascadeFacts C) :
    ∀ (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat)),
      WethReachable C s →
      C = s.executionEnv.codeOwner →
      WethInvFr s.accountMap C →
      s.pc.toNat = 60 →
      fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
      EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
      WethInvFr s'.accountMap C := by
  intro s s' f' cost arg hR hCO hInv hPC60 hFetch hStep
  -- The decode at PC 60 is SSTORE with arg = none.
  have hFetchNone : fetchInstr s.executionEnv s.pc =
      .ok (.StackMemFlow .SSTORE, none) := by
    obtain ⟨⟨_, hCode, _⟩, _⟩ := hR
    have hpcEq : s.pc = UInt256.ofNat 60 :=
      pc_eq_ofNat_of_toNat s 60 (by decide) hPC60
    unfold fetchInstr
    rw [hCode, hpcEq, decode_bytecode_at_60]
    rfl
  -- The fetched arg matches the decode's none.
  have hArgNone : arg = none := by
    rw [hFetchNone] at hFetch
    injection hFetch with h1
    injection h1 with _ h2
    exact h2.symm
  subst hArgNone
  -- Pull the cascade facts (now `findD`-flavored).
  obtain ⟨slot, tl, acc, oldVal, h_find, h_findD, hCase⟩ :=
    hCascade s hR hPC60 hFetchNone
  -- Unify both arms (decrement / erase) into a single `newVal` with
  -- the bound `newVal.toNat ≤ oldVal.toNat`. Then route through the
  -- `findD`-flavored `≤`-bridge.
  obtain ⟨newVal, hStk, h_le⟩ : ∃ newVal,
      s.stack = slot :: newVal :: tl ∧ newVal.toNat ≤ oldVal.toNat := by
    cases hCase with
    | inl h =>
      obtain ⟨newVal, hStk, h_le, _⟩ := h
      exact ⟨newVal, hStk, h_le⟩
    | inr hStk =>
      refine ⟨⟨0⟩, hStk, ?_⟩
      show (⟨0⟩ : UInt256).toNat ≤ _; show 0 ≤ _; exact Nat.zero_le _
  -- Extract the post-state's accountMap shape via `step_SSTORE_accountMap`.
  have h_find_CO : s.accountMap.find? s.executionEnv.codeOwner = some acc := by
    rw [← hCO]; exact h_find
  have h_am := step_SSTORE_accountMap s s' f' cost none slot newVal tl hStk acc
    h_find_CO hStep
  rw [h_am, ← hCO]
  -- Goal: WethInvFr (s.accountMap.insert C (acc.updateStorage slot newVal)) C
  unfold WethInvFr at *
  -- balanceOf preserved (storage-only update).
  have h_bal_eq :
      balanceOf (s.accountMap.insert C (acc.updateStorage slot newVal)) C
        = balanceOf s.accountMap C := by
    apply balanceOf_insert_preserve_of_eq s.accountMap C acc _ h_find
    exact Account_updateStorage_balance _ _ _
  rw [h_bal_eq]
  -- storageSum bounded by the `findD`-flavored bridge.
  have h_storageSum_le :
      storageSum (s.accountMap.insert C (acc.updateStorage slot newVal)) C
        ≤ storageSum s.accountMap C :=
    storageSum_sstore_replace_eq_findD s.accountMap C slot newVal oldVal acc
      h_find h_findD h_le
  exact Nat.le_trans h_storageSum_le hInv

/-- **PC 40 SSTORE preservation from cascade facts.** Closed-form glue
for the deposit case. Uses the at-`C` Θ-pre-credit slack to bound the
post-SSTORE storageSum by the (preserved) balanceOf.

Handles the `findD`-flavored cascade fact: case-splits on
`find? slot` to recover the strict `find?`-form bridges in the
existing-slot case, and uses direct `storageSum`-delta reasoning in the
absent-slot case (first-time depositor). -/
private theorem weth_sstore_preserves_pc40_from_cascade
    (C : AccountAddress) (hCascade : WethPC40CascadeFacts C) :
    ∀ (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat)),
      WethReachable C s →
      C = s.executionEnv.codeOwner →
      WethInvFr s.accountMap C →
      s.pc.toNat = 40 →
      fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
      EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
      WethInvFr s'.accountMap C := by
  intro s s' f' cost arg hR hCO hInv hPC40 hFetch hStep
  have hFetchNone : fetchInstr s.executionEnv s.pc =
      .ok (.StackMemFlow .SSTORE, none) := by
    obtain ⟨⟨_, hCode, _⟩, _⟩ := hR
    have hpcEq : s.pc = UInt256.ofNat 40 :=
      pc_eq_ofNat_of_toNat s 40 (by decide) hPC40
    unfold fetchInstr
    rw [hCode, hpcEq, decode_bytecode_at_40]
    rfl
  have hArgNone : arg = none := by
    rw [hFetchNone] at hFetch
    injection hFetch with h1
    injection h1 with _ h2
    exact h2.symm
  subst hArgNone
  obtain ⟨slot, tl, acc, oldVal, h_find, h_findD, hCase⟩ :=
    hCascade s hR hPC40 hFetchNone
  -- Case-split on `find? slot` to recover the strict `find?` form.
  unfold Batteries.RBMap.findD at h_findD
  cases h_find_slot : acc.storage.find? slot with
  | some oldVal' =>
    -- Existing slot: use the strict-form bridges.
    rw [h_find_slot, Option.getD] at h_findD
    subst h_findD
    cases hCase with
    | inl h =>
      obtain ⟨newVal, hStk, h_slack, hNonZero⟩ := h
      exact WethInvFr_step_SSTORE_at_C_replace_with_slack C s s' f' cost none
        slot newVal oldVal' tl hStk hCO acc h_find h_find_slot h_slack hNonZero
        hInv hStep
    | inr hStk =>
      exact WethSStorePreserves_erase C s s' f' cost none slot oldVal' tl
        hCO hStk acc h_find h_find_slot hInv hStep
  | none =>
    -- Absent slot (first-time depositor): oldVal = ⟨0⟩, slot is being inserted.
    rw [h_find_slot, Option.getD] at h_findD
    subst h_findD
    have h_oldVal_toNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
    cases hCase with
    | inl h =>
      -- Decrement arm: slack = storageSum - 0 + newVal ≤ balanceOf, so
      -- storageSum + newVal ≤ balanceOf. Post-state inserts (slot, newVal),
      -- so storageSum_post = storageSum_pre + newVal.toNat.
      obtain ⟨newVal, hStk, h_slack, hNonZero⟩ := h
      have h_find_CO : s.accountMap.find? s.executionEnv.codeOwner = some acc := by
        rw [← hCO]; exact h_find
      have h_am := step_SSTORE_accountMap s s' f' cost none slot newVal tl hStk acc
        h_find_CO hStep
      rw [h_am, ← hCO]
      unfold WethInvFr at *
      -- balanceOf preserved.
      have h_bal_eq :
          balanceOf (s.accountMap.insert C (acc.updateStorage slot newVal)) C
            = balanceOf s.accountMap C := by
        apply balanceOf_insert_preserve_of_eq s.accountMap C acc _ h_find
        exact Account_updateStorage_balance _ _ _
      rw [h_bal_eq]
      -- storageSum_post: insert at C with updated storage where slot was absent.
      have h_post_storage :
          (acc.updateStorage slot newVal).storage = acc.storage.insert slot newVal := by
        unfold Account.updateStorage; simp [hNonZero]
      -- Need: storageSum (insert C ...) ≤ balanceOf σ C.
      -- Slack: storageSum σ C - 0 + newVal ≤ balanceOf σ C.
      rw [h_oldVal_toNat] at h_slack
      -- Show: storageSum (insert ...) ≤ storageSum σ C + newVal.toNat,
      -- which combined with h_slack gives the result.
      -- Use storageSum_sstore_replace_eq_findD with newVal ≤ ⟨0⟩? No, that
      -- requires the bound. Use the equation form via the existence-bridge.
      -- Strategy: prove storageSum_post = storageSum_pre + newVal.toNat directly.
      have h_post_eq :
          storageSum (s.accountMap.insert C (acc.updateStorage slot newVal)) C
            = storageSum s.accountMap C + newVal.toNat := by
        rw [storageSum_insert_at_C,
            storageSum_of_find?_some s.accountMap C acc h_find,
            h_post_storage]
        exact storageSum_storage_insert_absent_eq acc.storage slot newVal h_find_slot
      rw [h_post_eq]
      exact h_slack
    | inr hStk =>
      -- Erase arm: stack[1] = ⟨0⟩, but slot is absent. SSTORE-erase of absent
      -- slot is a no-op (storage unchanged). Invariant preserved.
      have h_find_CO : s.accountMap.find? s.executionEnv.codeOwner = some acc := by
        rw [← hCO]; exact h_find
      have h_am := step_SSTORE_accountMap s s' f' cost none slot ⟨0⟩ tl hStk acc
        h_find_CO hStep
      rw [h_am, ← hCO]
      unfold WethInvFr at *
      -- balanceOf preserved.
      have h_bal_eq :
          balanceOf (s.accountMap.insert C (acc.updateStorage slot ⟨0⟩)) C
            = balanceOf s.accountMap C := by
        apply balanceOf_insert_preserve_of_eq s.accountMap C acc _ h_find
        exact Account_updateStorage_balance _ _ _
      rw [h_bal_eq]
      -- Post-storage: erase of absent slot ⇒ storage preserved.
      have h_post_storage :
          (acc.updateStorage slot ⟨0⟩).storage = acc.storage.erase slot := by
        unfold Account.updateStorage
        have h0 : ((⟨0⟩ : UInt256) == default) = true := by decide
        simp [h0]
      have h_storage_preserved :
          storageSum (s.accountMap.insert C (acc.updateStorage slot ⟨0⟩)) C
            = storageSum s.accountMap C := by
        rw [storageSum_insert_at_C,
            storageSum_of_find?_some s.accountMap C acc h_find,
            h_post_storage]
        exact storageSum_storage_erase_eq_of_find?_none acc.storage slot h_find_slot
      rw [h_storage_preserved]
      exact hInv

/-- **Compose PC 40 + PC 60 cascade-fact predicates into the full
`WethSStorePreserves`.** Reduces the structural assumption to the
per-PC cascade predicates `WethPC40CascadeFacts` and
`WethPC60CascadeFacts`, plus the framework's narrowing
`WethReachable_sstore_pc`. -/
theorem weth_sstore_preserves_from_cascades
    (C : AccountAddress)
    (h40 : WethPC40CascadeFacts C)
    (h60 : WethPC60CascadeFacts C) :
    WethSStorePreserves C := by
  intro s s' f' cost arg hR _hWF hCO hInv hFetch hStep
  rcases WethReachable_sstore_pc hR hFetch with hPC40 | hPC60
  · exact weth_sstore_preserves_pc40_from_cascade C h40 s s' f' cost arg
      hR hCO hInv hPC40 hFetch hStep
  · exact weth_sstore_preserves_pc60_from_cascade C h60 s s' f' cost arg
      hR hCO hInv hPC60 hFetch hStep

/-- Per-state CALL slack precondition at PC 72. Slack-callback form:
given the seven popped CALL parameters and the residual stack tail,
supply the three preconditions of `call_invariant_preserved`:
* `no-wrap`: recipient balance + value < UInt256.size,
* `funds`: sender funds cover value (or value = 0),
* `slack`: at-`C` debit safety (recipient ≠ C ∨ value = 0 ∨
  value + storageSum σ C ≤ balanceOf σ C).

The slack inequality at PC 72 follows from PC 60's SSTORE-decrement
fact (the slot was decremented by `x` which is exactly the CALL value),
combined with `WethInvFr` (storageSum ≤ balanceOf). The recipient ≠ C
disjunct is satisfied by `weth_caller_ne_C` (the recipient is the
caller, who differs from C by the boundary hypothesis `C ≠ S_T`).

The IHs `ΞInvariantAtCFrame`/`ΞInvariantFrameAtC` are threaded
internally by the framework's `step_CALL_arm_at_C_slack_invariant` —
the consumer never sees them. -/
def WethCallSlack (C : AccountAddress) : Prop :=
  ∀ s : EVM.State, ∀ arg,
    WethReachable C s →
    StateWF s.accountMap →
    C = s.executionEnv.codeOwner →
    (∀ a ∈ s.createdAccounts, a ≠ C) →
    WethInvFr s.accountMap C →
    fetchInstr s.executionEnv s.pc = .ok (.CALL, arg) →
    ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
      s.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
      (∀ acc,
          s.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
          acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
      (μ₂ = ⟨0⟩ ∨ ∃ acc,
          s.accountMap.find?
              (AccountAddress.ofUInt256
                (.ofNat s.executionEnv.codeOwner)) = some acc ∧
          μ₂.toNat ≤ acc.balance.toNat) ∧
      (C ≠ AccountAddress.ofUInt256
              (.ofNat s.executionEnv.codeOwner) ∨
       μ₂ = ⟨0⟩ ∨
       μ₂.toNat + storageSum s.accountMap C
         ≤ balanceOf s.accountMap C)

/-! ### Narrower PC 72 cascade-fact predicate for CALL slack

Like `WethPC60CascadeFacts` for SSTORE, `WethPC72CascadeFacts` captures
exactly the per-state data the CALL slack discharger needs at PC 72.
Once the trace cascade extension lands at PCs 61→72, this predicate
is the precise discharge target. -/

/-- **PC 72 cascade fact predicate.** At every Weth-reachable state at
PC 72 (the unique CALL site, per `WethReachable_call_pc`), the trace
cascade exposes:

* the seven popped CALL parameters: `[gas, to, val, ao, as, ro, rs, x']`
  (the eighth element is the residual `x'` left over by the SSTORE
  prefix's stack discipline);
* `to = AccountAddress.ofUInt256 sender`, with `sender ≠ C` (from
  `weth_caller_ne_C` + the boundary `C ≠ S_T`);
* the post-PC-60 SSTORE-decrement slack: `val.toNat + storageSum σ C
  ≤ balanceOf σ C`;
* the no-wrap fact: for any recipient account, `balance + val.toNat
  < UInt256.size` (Weth withdraw caps val at the SLOAD'd balance, so
  this is bounded by the existing balance + balance ≤ totalETH);
* the funds fact: the codeOwner-as-AccountAddress account has balance
  ≥ val.toNat (this comes from the at-`C` invariant `S(σ) ≤ β(σ)`
  combined with the slack disjunction).

Discharged by extending the trace at PCs 61→72: PC 60's SSTORE
establishes the slack; PCs 61–71 propagate it; PC 70's CALLER push
establishes `to = sender`; the no-wrap and funds derive from the
slack via `WethInvFr` and `StateWF`. -/
def WethPC72CascadeFacts (C : AccountAddress) : Prop :=
  ∀ s : EVM.State,
    WethReachable C s →
    s.pc.toNat = 72 →
    fetchInstr s.executionEnv s.pc = .ok (.CALL, none) →
    StateWF s.accountMap →
    WethInvFr s.accountMap C →
    ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
      s.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
      (∀ acc,
          s.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
          acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
      (μ₂ = ⟨0⟩ ∨ ∃ acc,
          s.accountMap.find?
              (AccountAddress.ofUInt256
                (.ofNat s.executionEnv.codeOwner)) = some acc ∧
          μ₂.toNat ≤ acc.balance.toNat) ∧
      (μ₂ = ⟨0⟩ ∨
       μ₂.toNat + storageSum s.accountMap C
         ≤ balanceOf s.accountMap C)

/-- Recipient-balance no-wrap at PC 72's CALL: for any recipient
account, its balance plus the value being transferred fits in
`UInt256`. This is a **real-world chain bound**: the total ETH supply
plus any single contract's balance fits in `UInt256`, so adding a
withdrawn amount (capped at the contract's storage) cannot wrap.

Cannot be derived from bytecode analysis alone — it's a chain-state
fact orthogonal to WETH's bytecode. -/
def WethCallNoWrapAt72 (C : AccountAddress) : Prop :=
  ∀ s : EVM.State,
    WethReachable C s →
    s.pc.toNat = 72 →
    ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
      s.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
      ∀ acc, s.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
        acc.balance.toNat + μ₂.toNat < UInt256.size

/-- Post-SSTORE slack at PC 72: at every Weth-reachable PC-72 state,
the value being transferred (μ₂) plus storageSum is at most balanceOf,
**and** the caller's account (under the framework's cumbersome address
form `AccountAddress.ofUInt256 (.ofNat codeOwner)`) is found in σ
with balance ≥ μ₂.

Derives from the post-PC-60-SSTORE invariant: at PC 60 (pre-SSTORE),
`storageSum σ_60 ≤ balanceOf σ_60` (WethInvFr); SSTORE decreases
storage by x and preserves balance, so `storageSum σ_61 + x ≤
balanceOf σ_61`. Through PCs 61..71 (no σ change), the slack is
preserved. At PC 72, μ₂ = x (the duplicated withdrawal amount on the
stack from DUP5 at PC 69), giving the slack.

The caller-account-found bundles the address roundtrip identity
`AccountAddress.ofUInt256 (.ofNat codeOwner) = codeOwner` with the
σ-has-C fact (already in WethAccountAtC, but here we materialize the
roundtripped form needed by the cascade-fact predicate).

Threading this requires extending `WethReachable` with WethInvFr
preservation (so the PC 60 walk has access to the pre-SSTORE
invariant). Bundled here as a structural assumption pending that
extension. -/
def WethCallSlackAt72 (C : AccountAddress) : Prop :=
  ∀ s : EVM.State,
    WethReachable C s →
    s.pc.toNat = 72 →
    ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
      s.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
      (μ₂.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C) ∧
      (μ₂ = ⟨0⟩ ∨ ∃ acc,
        s.accountMap.find?
            (AccountAddress.ofUInt256
              (.ofNat s.executionEnv.codeOwner)) = some acc ∧
        μ₂.toNat ≤ acc.balance.toNat)

/-- Extract the post-SSTORE slack witness from a Weth-reachable state at
PC 72. Discharged from the trace cascade threaded through PCs 60..72:
PC 60's pre-SSTORE WethInvFr, plus the SSTORE replace law and the
bound `x ≤ oldVal` from PC 55's LT-not-taken, gives the slack
`x + storageSum_post ≤ balanceOf_post`. PCs 61..71 (PUSH1, DUP5,
CALLER, GAS) preserve the accountMap so the slack survives unchanged,
with the residual `x` propagating to stack[2] at PC 72 (= the CALL
value `μ₂`). -/
private theorem WethReachable_pc72_slack
    (C : AccountAddress) (s : EVM.State)
    (hR : WethReachable C s) (hPC72 : s.pc.toNat = 72) :
    ∃ x : UInt256, s.stack[2]? = some x ∧
      x.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C := by
  obtain ⟨⟨_, _, hPC⟩, _⟩ := hR
  rcases hPC with
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, hSlack⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩
  all_goals first
    | exact hSlack
    | (exfalso; omega)

/-- **`WethCallSlackAt72` is a theorem given σ-has-C.** Discharges the
post-SSTORE slack at PC 72 from the threaded WethTrace cascade plus
σ-has-C. The slack itself comes from `WethReachable_pc72_slack`; the
caller-account-found uses the address roundtrip identity
`AccountAddress.ofUInt256 (.ofNat C) = C` combined with `C =
codeOwner`. The funds bound `μ₂ ≤ acc.balance` follows from
`μ₂ + storageSum ≤ balanceOf` by `storageSum ≥ 0` (i.e.,
`balanceOf σ C = acc.balance` when `σ.find? C = some acc`). -/
theorem weth_call_slack
    (C : AccountAddress)
    (hAccC : WethAccountAtC C) :
    WethCallSlackAt72 C := by
  intro s hR hPC72 μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
  -- Slack from the trace cascade.
  obtain ⟨x, hStk2, hSlack⟩ := WethReachable_pc72_slack C s hR hPC72
  -- Identify μ₂ = x via the stack shape.
  have hμ₂_eq : μ₂ = x := by
    have h_stk2 : s.stack[2]? = some μ₂ := by
      rw [hStk]; rfl
    rw [h_stk2] at hStk2
    injection hStk2
  -- Combined slack: μ₂ + storageSum ≤ balanceOf.
  have h_slack_μ : μ₂.toNat + storageSum s.accountMap C ≤ balanceOf s.accountMap C := by
    rw [hμ₂_eq]; exact hSlack
  refine ⟨h_slack_μ, ?_⟩
  -- Caller-account-found via roundtrip.
  -- σ-has-C: ∃ acc, σ.find? C = some acc.
  obtain ⟨acc, h_find⟩ := hAccC s hR
  -- C = s.executionEnv.codeOwner from WethReachable.
  have hCO : C = s.executionEnv.codeOwner := hR.1.1
  -- Roundtrip: AccountAddress.ofUInt256 (.ofNat codeOwner) = codeOwner.
  have hRoundtrip :
      AccountAddress.ofUInt256 (.ofNat s.executionEnv.codeOwner)
        = s.executionEnv.codeOwner := by
    show Fin.ofNat _ (((Fin.ofNat UInt256.size
            s.executionEnv.codeOwner.val).val) % AccountAddress.size)
         = s.executionEnv.codeOwner
    have hAddrLtUSize : AccountAddress.size ≤ UInt256.size := by decide
    have hCoLtAddr : s.executionEnv.codeOwner.val < AccountAddress.size :=
      s.executionEnv.codeOwner.isLt
    have hCoLtU : s.executionEnv.codeOwner.val < UInt256.size :=
      Nat.lt_of_lt_of_le hCoLtAddr hAddrLtUSize
    have h1 : (Fin.ofNat UInt256.size s.executionEnv.codeOwner.val).val
              = s.executionEnv.codeOwner.val := by
      show s.executionEnv.codeOwner.val % UInt256.size
            = s.executionEnv.codeOwner.val
      exact Nat.mod_eq_of_lt hCoLtU
    rw [h1]
    show Fin.ofNat _ (s.executionEnv.codeOwner.val % AccountAddress.size)
         = s.executionEnv.codeOwner
    rw [Nat.mod_eq_of_lt hCoLtAddr]
    apply Fin.ext
    show s.executionEnv.codeOwner.val % AccountAddress.size
         = s.executionEnv.codeOwner.val
    exact Nat.mod_eq_of_lt hCoLtAddr
  -- Use the roundtrip + hCO to convert σ.find? C into the cumbersome form.
  have h_find_roundtrip :
      s.accountMap.find?
          (AccountAddress.ofUInt256 (.ofNat s.executionEnv.codeOwner))
        = some acc := by
    rw [hRoundtrip, ← hCO]; exact h_find
  -- Funds: μ₂ ≤ acc.balance.
  -- balanceOf σ C = acc.balance when σ.find? C = some acc.
  have h_balanceOf_eq : balanceOf s.accountMap C = acc.balance.toNat := by
    unfold balanceOf
    rw [h_find]; rfl
  -- Goal: μ₂ = ⟨0⟩ ∨ ∃ acc, ... ∧ μ₂ ≤ acc.balance.
  by_cases h_μ_zero : μ₂ = ⟨0⟩
  · exact Or.inl h_μ_zero
  · right
    refine ⟨acc, h_find_roundtrip, ?_⟩
    -- μ₂.toNat + storageSum ≤ balanceOf = acc.balance.
    -- storageSum ≥ 0, so μ₂.toNat ≤ acc.balance.toNat.
    rw [h_balanceOf_eq] at h_slack_μ
    omega

/-- **`WethPC72CascadeFacts` is a theorem given the two narrower
structural facts.** The cascade-fact predicate's three conjuncts are:

1. Recipient no-wrap → from `WethCallNoWrapAt72`.
2. Caller funds (μ₂ ≤ balance σ C) → from the slack via
   `storageSum ≥ 0` and the existence of σ[C].
3. Slack → from `WethCallSlackAt72`.

Conjunct (2)'s caller-existence is from `WethAccountAtC` (already in
the assumptions for pc60). The funds bound `μ₂ ≤ acc.balance` follows
from the slack `μ₂ + storageSum ≤ balanceOf` and `storageSum ≥ 0`. -/
theorem weth_pc72_cascade
    (C : AccountAddress)
    (hNoWrap : WethCallNoWrapAt72 C)
    (hSlack : WethCallSlackAt72 C) :
    WethPC72CascadeFacts C := by
  intro s hR hPC72 _hFetch _hWF _hInv μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
  obtain ⟨h_slack, h_funds⟩ := hSlack s hR hPC72 μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
  refine ⟨?_, h_funds, Or.inr h_slack⟩
  exact hNoWrap s hR hPC72 μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk

/-- **Compose `WethPC72CascadeFacts` into the full `WethCallSlack`.**
Closed-form glue: at every reachable CALL state, the unique CALL PC is
72 (per `WethReachable_call_pc`), so the per-PC cascade-fact predicate
suffices. The third clause of the slack disjunction (`C ≠ ofUInt256
(ofNat codeOwner) ∨ μ₂=0 ∨ slack`) is discharged from the cascade's
narrower form by simply weakening to add the recipient-≠-C disjunct. -/
theorem weth_call_slack_from_cascade
    (C : AccountAddress) (hCascade : WethPC72CascadeFacts C) :
    WethCallSlack C := by
  intro s arg hR hWF hCO _hNC hInv hFetch μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
  -- Narrow the PC to 72 via WethReachable_call_pc.
  have hPC72 : s.pc.toNat = 72 := WethReachable_call_pc hR hFetch
  -- The decode at PC 72 is CALL with arg = none.
  have hFetchNone : fetchInstr s.executionEnv s.pc = .ok (.CALL, none) := by
    obtain ⟨⟨_, hCode, _⟩, _⟩ := hR
    have hpcEq : s.pc = UInt256.ofNat 72 :=
      pc_eq_ofNat_of_toNat s 72 (by decide) hPC72
    unfold fetchInstr
    rw [hCode, hpcEq, decode_bytecode_at_72]
    rfl
  -- Pull the cascade facts.
  obtain ⟨hNoWrap, hFunds, hSlack⟩ :=
    hCascade s hR hPC72 hFetchNone hWF hInv μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
  refine ⟨hNoWrap, hFunds, ?_⟩
  -- Convert (μ₂=0 ∨ slack) to (C ≠ … ∨ μ₂=0 ∨ slack) by weakening.
  cases hSlack with
  | inl h0 => exact Or.inr (Or.inl h0)
  | inr hSl => exact Or.inr (Or.inr hSl)

/-- **Per-step `WethInvFr` preservation discharger.** Discharges
`WethStepInvFrPreserves C` for **strict + SSTORE** ops directly via
the existing closed-form dischargers; the **CALL** case is delegated
to a separate `WethCALLStepInvFr C` assumption (the only branch that
needs the framework's strong-induction IHs).

Case-split on `WethReachable_op_in_allowed`'s op-classification:

* **Strict ops** (most PCs): `EVM_step_strict_preserves_WethInvFr`
  bridges `EVM.step` to `EvmYul.step` and dispatches to
  `EvmYul_step_preserves_WethInvFr_of_strict`.
* **SSTORE PCs (40, 60)**: narrow via `WethReachable_sstore_pc` to
  one of the two SSTORE PCs, then invoke
  `weth_sstore_preserves_pc40_from_cascade` /
  `weth_sstore_preserves_pc60_from_cascade` with the cascade-fact
  predicates derived from σ-has-C (= `weth_account_at_C`) and the
  Θ-pre-credit slack `hPreCredit` (real-world `WethAssumptions` fact).
* **CALL PC (72)**: delegate to the `hCall : WethCALLStepInvFr C`
  argument. This is the only branch that needs strong-induction IHs
  (via the framework's `step_CALL_arm_at_C_slack_invariant`), which
  the per-step interface cannot provide. -/
theorem weth_inv_step_pres
    (C : AccountAddress)
    (hCall : WethCALLStepInvFr C)
    (hPreCredit : WethDepositPreCredit C) :
    WethStepInvFrPreserves C := by
  intro s s' f' cost op arg hR hFetch hStep hRet hRev hStop _hSD
  have hInv : WethInvFr s.accountMap C := hR.2.2.2
  have hCO : C = s.executionEnv.codeOwner := hR.1.1
  -- Op class via the bytecode-walk classification.
  have hAllowed : WethOpAllowed op :=
    WethReachable_op_in_allowed C s op arg hR hFetch
  rcases hAllowed with hStrict | hOpCall | hOpSStore
  · -- Strict op: closed-form preservation.
    exact EVM_step_strict_preserves_WethInvFr op arg C f' cost s s'
      hStrict hStep hInv
  · -- CALL: delegate to the per-state CALL-preservation assumption.
    subst hOpCall
    exact hCall s s' f' cost arg hR hFetch hStep
  · -- SSTORE: narrow to PC 40 or PC 60, dispatch to the cascade-based
    -- discharger.
    subst hOpSStore
    rcases WethReachable_sstore_pc hR hFetch with hPC40 | hPC60
    · -- PC 40: deposit SSTORE.
      have h40 : WethPC40CascadeFacts C :=
        weth_pc40_cascade C
          (weth_deposit_cascade C (weth_account_at_C C))
          hPreCredit
      exact weth_sstore_preserves_pc40_from_cascade C h40 s s' f' cost arg
        hR hCO hInv hPC40 hFetch hStep
    · -- PC 60: withdraw SSTORE.
      have h60 : WethPC60CascadeFacts C :=
        weth_pc60_cascade C (weth_account_at_C C)
      exact weth_sstore_preserves_pc60_from_cascade C h60 s s' f' cost arg
        hR hCO hInv hPC60 hFetch hStep

/-- Initial Weth-execution state (pc = 0, empty stack) inhabits
`WethReachable`, given the deployment-pinned code-identity and the
σ-has-C precondition (the framework's Λ-setup guarantees the codeOwner
account exists in σ at Ξ entry). -/
private theorem WethReachable_initial
    (C : AccountAddress)
    (hDeployed : DeployedAtC C)
    (cA : Batteries.RBSet AccountAddress compare)
    (gbh : BlockHeader) (bs : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM)
    (hCO : I.codeOwner = C)
    (hAcc : accountPresentAt σ C)
    (hInv : WethInvFr σ C) :
    WethReachable C
      { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          gasAvailable := g
          blocks := bs
          genesisBlockHeader := gbh } := by
  refine ⟨WethTrace_initial C hDeployed cA gbh bs σ σ₀ g A I hCO, ?_, hAcc, hInv⟩
  -- Initial state has pc = 0, not pc = 32.
  show ¬ ((⟨0⟩ : UInt256).toNat = 32 ∧ _)
  intro h
  exact absurd h.1 (by decide)

/-! ## §H.2 — `WethStepClosure` discharger

Aggregate the 61 per-PC `WethTrace_step_at_*` walks into a single
`WethReachable`-respecting closure: given a Weth-reachable state and a
non-halt step, the post-state is Weth-reachable. The `WethReachable`
predicate is `WethTrace ∧ ¬(pc=32 ∧ len=0)` (the post-31-REVERT halt
sink is excluded). Each non-halt PC walks to a destination PC ≠ 32
(or PC = 32 with `len = 1` for the JUMPI-taken case at PC 16). Halt
PCs (31, 41, 79, 85) are ruled out by the op-inequalities. -/

/-- **Invariant-aware step closure** for Weth. Maintains `WethReachable`
under non-halt steps, **given** the post-step σ-presence (`hPresStep`)
and the post-step `WethInvFr s'.accountMap C` (`hInv'`) as external
parameters rather than re-deriving them via witnesses or per-step
preservation predicates.

This matches the framework's
`ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware`
interface: the X-loop computes `hInv'` internally via the CALL/SSTORE
arms (`step_bundled_invariant_at_C_invariant_at_C_slack_dispatch`) and
threads it into `hReach_step`. This breaks the chicken-and-egg cycle
that kept `call_inv_step_pres` a structural assumption.

The thin wrapper `weth_step_closure_with_pres` below recovers the
legacy interface (without `hInv'`) by computing it from a per-step
preservation predicate `hInvPres : WethStepInvFrPreserves C`. -/
private theorem weth_step_closure_with_pres_inv_aware
    (C : AccountAddress)
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (hR : WethReachable C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s')
    (hRet : op ≠ .RETURN) (hRev : op ≠ .REVERT)
    (hStop : op ≠ .STOP) (_hSD : op ≠ .SELFDESTRUCT)
    (_hPresZ : accountPresentAt s.accountMap C)
    (hPresStep : accountPresentAt s'.accountMap C)
    (hInv' : WethInvFr s'.accountMap C) :
    WethReachable C s' := by
  obtain ⟨hT, _hNot, hAcc, hInv⟩ := hR
  have hT' := hT
  obtain ⟨hCO, hCode, hPC⟩ := hT
  -- Account-presence at s' is the supplied `hPresStep` parameter.
  have hAcc' : accountPresentAt s'.accountMap C := hPresStep
  -- Case split on the 64 `WethTrace` disjuncts.
  rcases hPC with
    ⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|
    ⟨hpc, hLen, hStk0⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen, hStk0⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|
    ⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen, hCascade36⟩|⟨hpc, hLen, hCascade37⟩|⟨hpc, hLen, hCascade38⟩|
    ⟨hpc, hLen, hCascade39⟩|⟨hpc, hLen, hCascade40⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|
    ⟨hpc, hLen, hStk01⟩|⟨hpc, hLen, hCascade49⟩|⟨hpc, hLen, hCascade50⟩|⟨hpc, hLen, hCascade51⟩|⟨hpc, hLen, hCascade52⟩|⟨hpc, hLen, hCascade55⟩|⟨hpc, hLen, hCascade56⟩|⟨hpc, hLen, hCascade57⟩|
    ⟨hpc, hLen, hCascade58⟩|⟨hpc, hLen, hCascade59⟩|⟨hpc, hLen, hCascade60⟩|⟨hpc, hLen, hSlack61⟩|⟨hpc, hLen, hSlack63⟩|⟨hpc, hLen, hSlack65⟩|⟨hpc, hLen, hSlack67⟩|⟨hpc, hLen, hSlack69⟩|
    ⟨hpc, hLen, hSlack70⟩|⟨hpc, hLen, hSlack71⟩|⟨hpc, hLen, _⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen, hStk0⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|
    ⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩
  -- Case PC=0 (PUSH1 0). Lands at PC=2 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 0 := pc_eq_ofNat_of_toNat s 0 (by decide) hpc
    obtain ⟨hPC', hStk', _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_0 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_0 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 0 2]; decide
  -- Case PC=2 (CALLDATALOAD). Lands at PC=3 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 2 := pc_eq_ofNat_of_toNat s 2 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_2 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd :: tl, hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_CALLDATALOAD_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_2 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 2 1]; decide
  -- Case PC=3 (PUSH1 0xe0). Lands at PC=5 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 3 := pc_eq_ofNat_of_toNat s 3 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_3 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_3 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 3 2]; decide
  -- Case PC=5 (SHR). Lands at PC=6 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 5 := pc_eq_ofNat_of_toNat s 5 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_5 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_SHR_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_5 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 5 1]; decide
  -- Case PC=6 (DUP1). Lands at PC=7 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 6 := pc_eq_ofNat_of_toNat s 6 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_6 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_DUP1_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_6 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 6 1]; decide
  -- Case PC=7 (PUSH4). Lands at PC=12 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 7 := pc_eq_ofNat_of_toNat s 7 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH_at_pc s s' f' cost op arg .PUSH4 (by decide) depositSelector 4
        hFetch hCode hpcEq decode_bytecode_at_7 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_7 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 7 5]; decide
  -- Case PC=12 (EQ). Lands at PC=13 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 12 := pc_eq_ofNat_of_toNat s 12 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_12 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_EQ_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_12 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 12 1]; decide
  -- Case PC=13 (PUSH2). Lands at PC=16 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 13 := pc_eq_ofNat_of_toNat s 13 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH_at_pc s s' f' cost op arg .PUSH2 (by decide) depositLbl 2
        hFetch hCode hpcEq decode_bytecode_at_13 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_13 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 13 3]; decide
  -- Case PC=16 (JUMPI). Two branches: taken→PC=32 len=1, not-taken→PC=17.
  -- Either way `s'.stack.length = 1 ≠ 0` (post-state pops 2 from len=3).
  · have hpcEq : s.pc = UInt256.ofNat 16 := pc_eq_ofNat_of_toNat s 16 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_16 C s s' f' cost op arg hT' hpc hLen hStk0 hFetch hStep
    refine WethReachable_of_WethTrace_len_ne_0 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      have hLenTl : tl.length = 1 := by
        have h1 : (hd1 :: hd2 :: tl).length = 3 := by rw [← hStk_eq]; exact hLen
        simpa using h1
      obtain ⟨_, hStk', _⟩ :=
        step_JUMPI_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_16 hStep
      rw [hStk']; rw [hLenTl]; decide
  -- Case PC=17 (PUSH4). Lands at PC=22 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 17 := pc_eq_ofNat_of_toNat s 17 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH_at_pc s s' f' cost op arg .PUSH4 (by decide) withdrawSelector 4
        hFetch hCode hpcEq decode_bytecode_at_17 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_17 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 17 5]; decide
  -- Case PC=22 (EQ). Lands at PC=23 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 22 := pc_eq_ofNat_of_toNat s 22 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_22 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_EQ_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_22 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 22 1]; decide
  -- Case PC=23 (PUSH2). Lands at PC=26 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 23 := pc_eq_ofNat_of_toNat s 23 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH_at_pc s s' f' cost op arg .PUSH2 (by decide) withdrawLbl 2
        hFetch hCode hpcEq decode_bytecode_at_23 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_23 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 23 3]; decide
  -- Case PC=26 (JUMPI). Two branches: taken→PC=42, not-taken→PC=27. Both ≠ 32.
  -- Hmm, however the witness `s'.pc.toNat ≠ 32` requires casing. Easier: post-len = 0.
  -- Wait, post-len is `tl.length = 0` (pops 2 from len=2). So `s'.stack.length = 0`,
  -- which means we cannot use `len ≠ 0`. Use `pc ≠ 32` and case-split.
  · have hpcEq : s.pc = UInt256.ofNat 26 := pc_eq_ofNat_of_toNat s 26 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_26 C s s' f' cost op arg hT' hpc hLen hStk0 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      have hd1_eq : hd1 = withdrawLbl := by
        have : (hd1 :: hd2 :: tl)[0]? = some withdrawLbl := by
          rw [← hStk_eq]; exact hStk0
        simpa using this
      obtain ⟨hPC', _, _⟩ :=
        step_JUMPI_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_26 hStep
      cases hb : (hd2 != ⟨0⟩) with
      | true =>
        rw [hPC']
        simp only [hb, ↓reduceIte]
        rw [hd1_eq]; show withdrawLbl.toNat ≠ 32; decide
      | false =>
        rw [hPC']
        simp only [hb, Bool.false_eq_true, if_false]
        rw [hpcEq]
        native_decide
  -- Case PC=27 (PUSH1 0). Lands at PC=29 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 27 := pc_eq_ofNat_of_toNat s 27 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_27 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_27 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 27 2]; decide
  -- Case PC=29 (PUSH1 0). Lands at PC=31 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 29 := pc_eq_ofNat_of_toNat s 29 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_29 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_29 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 29 2]; decide
  -- Case PC=31 (REVERT). Halt op — excluded by hRev.
  · have hpcEq : s.pc = UInt256.ofNat 31 := pc_eq_ofNat_of_toNat s 31 (by decide) hpc
    have hDec : decode s.executionEnv.code s.pc = some (.REVERT, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_31
    have ⟨hOp, _⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    exact absurd hOp hRev
  -- Case PC=32 length=0 (post-31-REVERT halt sink). Excluded by `hNot` — input
  -- state is `WethReachable`, so `¬(pc=32 ∧ len=0)`.
  · exact absurd ⟨hpc, hLen⟩ _hNot
  -- Case PC=32 length=1 (deposit JUMPDEST entry). Lands at PC=33 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 32 := pc_eq_ofNat_of_toNat s 32 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_JUMPDEST_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_32 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_32 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 32 1]; decide
  -- Case PC=33 (POP). Lands at PC=34 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 33 := pc_eq_ofNat_of_toNat s 33 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_33 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_POP_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_33 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 33 1]; decide
  -- Case PC=34 (CALLER). Lands at PC=35 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 34 := pc_eq_ofNat_of_toNat s 34 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_CALLER_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_34 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_34 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 34 1]; decide
  -- Case PC=35 (DUP1). Lands at PC=36 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 35 := pc_eq_ofNat_of_toNat s 35 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_35 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_DUP1_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_35 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 35 1]; decide
  -- Case PC=36 (SLOAD). Lands at PC=37 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 36 := pc_eq_ofNat_of_toNat s 36 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_36 C s s' f' cost op arg hT' hpc hLen hCascade36 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_SLOAD_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_36 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 36 1]; decide
  -- Case PC=37 (CALLVALUE). Lands at PC=38 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 37 := pc_eq_ofNat_of_toNat s 37 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_CALLVALUE_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_37 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_37 C s s' f' cost op arg hT' hpc hLen hCascade37 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 37 1]; decide
  -- Case PC=38 (ADD). Lands at PC=39 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 38 := pc_eq_ofNat_of_toNat s 38 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_38 C s s' f' cost op arg hT' hpc hLen hCascade38 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_ADD_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_38 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 38 1]; decide
  -- Case PC=39 (SWAP1). Lands at PC=40 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 39 := pc_eq_ofNat_of_toNat s 39 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_39 C s s' f' cost op arg hT' hpc hLen hCascade39 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_SWAP1_at_pc_local s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_39 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 39 1]; decide
  -- Case PC=40 (SSTORE). Lands at PC=41 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 40 := pc_eq_ofNat_of_toNat s 40 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_40 C s s' f' cost op arg hT' hpc hLen hCascade40 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_SSTORE_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_40 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 40 1]; decide
  -- Case PC=41 (STOP). Halt op — excluded by hStop.
  · have hpcEq : s.pc = UInt256.ofNat 41 := pc_eq_ofNat_of_toNat s 41 (by decide) hpc
    have hDec : decode s.executionEnv.code s.pc = some (.STOP, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_41
    have ⟨hOp, _⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    exact absurd hOp hStop
  -- Case PC=42 (JUMPDEST). Lands at PC=43 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 42 := pc_eq_ofNat_of_toNat s 42 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_JUMPDEST_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_42 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_42 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 42 1]; decide
  -- Case PC=43 (PUSH1 4). Lands at PC=45 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 43 := pc_eq_ofNat_of_toNat s 43 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_43 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_43 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 43 2]; decide
  -- Case PC=45 (CALLDATALOAD). Lands at PC=46 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 45 := pc_eq_ofNat_of_toNat s 45 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_45 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_CALLDATALOAD_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_45 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 45 1]; decide
  -- Case PC=46 (CALLER). Lands at PC=47 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 46 := pc_eq_ofNat_of_toNat s 46 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_CALLER_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_46 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_46 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 46 1]; decide
  -- Case PC=47 (DUP1). Lands at PC=48 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 47 := pc_eq_ofNat_of_toNat s 47 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_47 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_DUP1_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_47 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 47 1]; decide
  -- Case PC=48 (SLOAD). Lands at PC=49 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 48 := pc_eq_ofNat_of_toNat s 48 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_48 C s s' f' cost op arg hT' hpc hLen hStk01 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_SLOAD_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_48 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 48 1]; decide
  -- Case PC=49 (DUP3). Lands at PC=50 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 49 := pc_eq_ofNat_of_toNat s 49 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_49 C s s' f' cost op arg hT' hpc hLen hCascade49 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: hd3 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_DUP3_at_pc s s' f' cost op arg _ hd1 hd2 hd3 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_49 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 49 1]; decide
  -- Case PC=50 (DUP2). Lands at PC=51 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 50 := pc_eq_ofNat_of_toNat s 50 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_50 C s s' f' cost op arg hT' hpc hLen hCascade50 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_DUP2_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_50 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 50 1]; decide
  -- Case PC=51 (LT). Lands at PC=52 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 51 := pc_eq_ofNat_of_toNat s 51 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_51 C s s' f' cost op arg hT' hpc hLen hCascade51 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_LT_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_51 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 51 1]; decide
  -- Case PC=52 (PUSH2). Lands at PC=55 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 52 := pc_eq_ofNat_of_toNat s 52 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH_at_pc s s' f' cost op arg .PUSH2 (by decide) revertLbl 2
        hFetch hCode hpcEq decode_bytecode_at_52 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_52 C s s' f' cost op arg hT' hpc hLen hCascade52 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 52 3]; decide
  -- Case PC=55 (JUMPI). Branches: taken→PC=80, not-taken→PC=56. Both ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 55 := pc_eq_ofNat_of_toNat s 55 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_55 C s s' f' cost op arg hT' hpc hLen hCascade55 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    obtain ⟨slot, oldVal, x, hStk_eq, _⟩ := hCascade55
    obtain ⟨hPC', _, _⟩ :=
      step_JUMPI_at_pc s s' f' cost op arg _ revertLbl (UInt256.lt oldVal x)
        (oldVal :: slot :: x :: []) hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_55 hStep
    cases hb : (UInt256.lt oldVal x != ⟨0⟩) with
    | true =>
      rw [hPC']
      simp only [hb, ↓reduceIte]
      show revertLbl.toNat ≠ 32; decide
    | false =>
      rw [hPC']
      simp only [hb, Bool.false_eq_true, if_false]
      rw [hpcEq]
      native_decide
  -- Case PC=56 (DUP3). Lands at PC=57 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 56 := pc_eq_ofNat_of_toNat s 56 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_56 C s s' f' cost op arg hT' hpc hLen hCascade56 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: hd3 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_DUP3_at_pc s s' f' cost op arg _ hd1 hd2 hd3 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_56 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 56 1]; decide
  -- Case PC=57 (SWAP1). Lands at PC=58 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 57 := pc_eq_ofNat_of_toNat s 57 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_57 C s s' f' cost op arg hT' hpc hLen hCascade57 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_SWAP1_at_pc_local s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_57 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 57 1]; decide
  -- Case PC=58 (SUB). Lands at PC=59 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 58 := pc_eq_ofNat_of_toNat s 58 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_58 C s s' f' cost op arg hT' hpc hLen hCascade58 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_SUB_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_58 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 58 1]; decide
  -- Case PC=59 (SWAP1). Lands at PC=60 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 59 := pc_eq_ofNat_of_toNat s 59 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_59 C s s' f' cost op arg hT' hpc hLen hCascade59 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_SWAP1_at_pc_local s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_59 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 59 1]; decide
  -- Case PC=60 (SSTORE). Lands at PC=61 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 60 := pc_eq_ofNat_of_toNat s 60 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_60 C s s' f' cost op arg hT' hpc hLen hCascade60 hAcc hInv hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_SSTORE_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_60 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 60 1]; decide
  -- Case PC=61 (PUSH1 0). Lands at PC=63 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 61 := pc_eq_ofNat_of_toNat s 61 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_61 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_61 C s s' f' cost op arg hT' hpc hLen hSlack61 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 61 2]; decide
  -- Case PC=63 (PUSH1 0). Lands at PC=65 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 63 := pc_eq_ofNat_of_toNat s 63 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_63 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_63 C s s' f' cost op arg hT' hpc hLen hSlack63 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 63 2]; decide
  -- Case PC=65 (PUSH1 0). Lands at PC=67 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 65 := pc_eq_ofNat_of_toNat s 65 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_65 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_65 C s s' f' cost op arg hT' hpc hLen hSlack65 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 65 2]; decide
  -- Case PC=67 (PUSH1 0). Lands at PC=69 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 67 := pc_eq_ofNat_of_toNat s 67 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_67 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_67 C s s' f' cost op arg hT' hpc hLen hSlack67 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 67 2]; decide
  -- Case PC=69 (DUP5). Lands at PC=70 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 69 := pc_eq_ofNat_of_toNat s 69 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_69 C s s' f' cost op arg hT' hpc hLen hSlack69 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_DUP5_at_pc s s' f' cost op arg _ hd1 hd2 hd3 hd4 hd5 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_69 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 69 1]; decide
  -- Case PC=70 (CALLER). Lands at PC=71 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 70 := pc_eq_ofNat_of_toNat s 70 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_CALLER_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_70 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_70 C s s' f' cost op arg hT' hpc hLen hSlack70 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 70 1]; decide
  -- Case PC=71 (GAS). Lands at PC=72 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 71 := pc_eq_ofNat_of_toNat s 71 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_GAS_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_71 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_71 C s s' f' cost op arg hT' hpc hLen hSlack71 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 71 1]; decide
  -- Case PC=72 (CALL). Lands at PC=73 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 72 := pc_eq_ofNat_of_toNat s 72 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_72 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: hd7 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_CALL_at_pc s s' f' cost op arg _ hd1 hd2 hd3 hd4 hd5 hd6 hd7 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_72 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 72 1]; decide
  -- Case PC=73 (ISZERO). Lands at PC=74 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 73 := pc_eq_ofNat_of_toNat s 73 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_73 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_ISZERO_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_73 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 73 1]; decide
  -- Case PC=74 (PUSH2). Lands at PC=77 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 74 := pc_eq_ofNat_of_toNat s 74 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH_at_pc s s' f' cost op arg .PUSH2 (by decide) revertLbl 2
        hFetch hCode hpcEq decode_bytecode_at_74 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_74 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 74 3]; decide
  -- Case PC=77 (JUMPI). Branches: taken→PC=80, not-taken→PC=78. Both ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 77 := pc_eq_ofNat_of_toNat s 77 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_77 C s s' f' cost op arg hT' hpc hLen hStk0 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      have hd1_eq : hd1 = revertLbl := by
        have : (hd1 :: hd2 :: tl)[0]? = some revertLbl := by
          rw [← hStk_eq]; exact hStk0
        simpa using this
      obtain ⟨hPC', _, _⟩ :=
        step_JUMPI_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_77 hStep
      cases hb : (hd2 != ⟨0⟩) with
      | true =>
        rw [hPC']
        simp only [hb, ↓reduceIte]
        rw [hd1_eq]; show revertLbl.toNat ≠ 32; decide
      | false =>
        rw [hPC']
        simp only [hb, Bool.false_eq_true, if_false]
        rw [hpcEq]
        native_decide
  -- Case PC=78 (POP). Lands at PC=79 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 78 := pc_eq_ofNat_of_toNat s 78 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_78 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_POP_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_78 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 78 1]; decide
  -- Case PC=79 (STOP). Halt op — excluded by hStop.
  · have hpcEq : s.pc = UInt256.ofNat 79 := pc_eq_ofNat_of_toNat s 79 (by decide) hpc
    have hDec : decode s.executionEnv.code s.pc = some (.STOP, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_79
    have ⟨hOp, _⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    exact absurd hOp hStop
  -- Case PC=80 length=3 (JUMPDEST). Lands at PC=81 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 80 := pc_eq_ofNat_of_toNat s 80 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_JUMPDEST_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_80 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_80_len3 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 80 1]; decide
  -- Case PC=80 length=1 (JUMPDEST). Lands at PC=81 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 80 := pc_eq_ofNat_of_toNat s 80 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_JUMPDEST_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_80 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_80_len1 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 80 1]; decide
  -- Case PC=81 length=3 (PUSH1 0). Lands at PC=83 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 81 := pc_eq_ofNat_of_toNat s 81 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_81 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_81_len3 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 81 2]; decide
  -- Case PC=81 length=1 (PUSH1 0). Lands at PC=83 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 81 := pc_eq_ofNat_of_toNat s 81 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_81 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_81_len1 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 81 2]; decide
  -- Case PC=83 length=4 (PUSH1 0). Lands at PC=85 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 83 := pc_eq_ofNat_of_toNat s 83 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_83 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_83_len4 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 83 2]; decide
  -- Case PC=83 length=2 (PUSH1 0). Lands at PC=85 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 83 := pc_eq_ofNat_of_toNat s 83 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_83 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_83_len2 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hInv' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 83 2]; decide
  -- Case PC=85 length=5 (REVERT). Halt op — excluded by hRev.
  · have hpcEq : s.pc = UInt256.ofNat 85 := pc_eq_ofNat_of_toNat s 85 (by decide) hpc
    have hDec : decode s.executionEnv.code s.pc = some (.REVERT, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_85
    have ⟨hOp, _⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    exact absurd hOp hRev
  -- Case PC=85 length=3 (REVERT). Halt op — excluded by hRev.
  · have hpcEq : s.pc = UInt256.ofNat 85 := pc_eq_ofNat_of_toNat s 85 (by decide) hpc
    have hDec : decode s.executionEnv.code s.pc = some (.REVERT, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_85
    have ⟨hOp, _⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    exact absurd hOp hRev

/-- **Pres-aware step closure** for Weth. Maintains `WethReachable` under
non-halt steps, **given** the post-step σ-presence as an external
parameter (`hPresStep`) rather than re-deriving it via a
`ΞPreservesAccountAt C` witness.

Thin wrapper over `weth_step_closure_with_pres_inv_aware`: computes
`hInv'` from the per-step preservation predicate `hInvPres`, then
delegates. -/
private theorem weth_step_closure_with_pres
    (C : AccountAddress)
    (hInvPres : WethStepInvFrPreserves C)
    (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (hR : WethReachable C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s')
    (hRet : op ≠ .RETURN) (hRev : op ≠ .REVERT)
    (hStop : op ≠ .STOP) (_hSD : op ≠ .SELFDESTRUCT)
    (_hPresZ : accountPresentAt s.accountMap C)
    (hPresStep : accountPresentAt s'.accountMap C) :
    WethReachable C s' := by
  have hInv' : WethInvFr s'.accountMap C :=
    hInvPres s s' f' cost op arg hR hFetch hStep hRet hRev hStop _hSD
  exact weth_step_closure_with_pres_inv_aware C s s' f' cost op arg hR hFetch hStep
    hRet hRev hStop _hSD _hPresZ hPresStep hInv'

/-- Step-closure aggregate. Discharges `WethStepClosure C` for any `C`.

Wraps `weth_step_closure_with_pres` by deriving the post-step σ-presence
from the supplied `ΞPreservesAccountAt C` witness via
`EVM_step_preserves_present_no_create`. Kept as a thin wrapper over the
pres-aware variant for legacy callers that supply `hΞ`. -/
theorem weth_step_closure (C : AccountAddress) : WethStepClosure C := by
  intro hΞ hInvPres s s' f' cost op arg hR hFetch hStep hRet hRev hStop hSD
  -- Derive post-step σ-presence from the supplied `hΞ`.
  have hAcc : accountPresentAt s.accountMap C := hR.2.2.1
  have h_no_create : op ≠ .CREATE ∧ op ≠ .CREATE2 :=
    weth_no_create C s op arg hR hFetch
  have hAcc' : accountPresentAt s'.accountMap C :=
    EVM_step_preserves_present_no_create C hΞ op arg f' cost s s'
      h_no_create hStep hAcc
  exact weth_step_closure_with_pres C hInvPres s s' f' cost op arg hR
    hFetch hStep hRet hRev hStop hSD hAcc hAcc'

/-! ## §J.6.7-Weth — discharge of `xi_preserves_C` as a Lean theorem

Routes through `Ξ_preserves_account_at_a_of_Reachable_for_C_with_pres_step`
(EVMYulLean §J.6.7) with `WethReachable C` as the Reachable predicate.

The pres-step framework variant supplies the post-step σ-presence to the
hReach_step closure directly (computed inside the X-loop via the
strong-induction `ΞPreservesAccountAtBdd`), so the closure does not need
an external `ΞPreservesAccountAt C` witness. This breaks the
chicken-and-egg cycle that previously forced `xi_preserves_C` to be a
structural assumption.

The C-arm is fully closed-form. The non-C arm — Ξ executions on
contracts other than `C` — is bundled as `xi_preserves_C_other`, a
strictly narrower assumption: it only constrains executions where
`I.codeOwner ≠ C` (whereas the previous `xi_preserves_C` constrained
executions at any `I.codeOwner`). Real-world: SELFDESTRUCT only removes
the running address `Iₐ ≠ C`; CREATE/CREATE2 only insert; so C is
never removed by non-C executions. -/

/-- **`xi_preserves_C` as a Lean theorem from a narrower `xi_preserves_C_other`
assumption.** The full ΞPreservesAccountAt C witness is derived from:

* The deployment-pinned bytecode (`hDeployed`).
* The σ-presence and invariant at the initial state (`hAccInit`,
  `hInvInit`) — already structural fields in `WethAssumptions`.
* The CALL-only per-step invariant preservation
  (`call_inv_step_pres`) — already a structural field.
* The PC 40 SSTORE pre-credit slack (`hPreCredit`) — already
  `deposit_slack`.
* The non-C arm witness (`hΞ_other`) — the new, strictly narrower
  assumption replacing `xi_preserves_C`. -/
theorem weth_xi_preserves_C
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hCallInvPres : WethCALLStepInvFr C)
    (hPreCredit : WethDepositPreCredit C)
    (hInvInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → WethInvFr σ C)
    (hΞ_other : ∀ (fuel : ℕ) (cA : Batteries.RBSet AccountAddress compare)
                  (gbh : BlockHeader) (bs : ProcessedBlocks)
                  (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
                  (I : ExecutionEnv .EVM),
        I.codeOwner ≠ C →
        accountPresentAt σ C →
        match EVM.Ξ fuel cA gbh bs σ σ₀ g A I with
        | .ok (.success (_, σ', _, _) _) => accountPresentAt σ' C
        | _ => True) :
    ΞPreservesAccountAt C := by
  -- Derive the per-step WethInvFr preservation predicate from the
  -- narrowed CALL-only field plus the in-Lean strict + SSTORE walks.
  have hInvPres : WethStepInvFrPreserves C :=
    weth_inv_step_pres C hCallInvPres hPreCredit
  apply Ξ_preserves_account_at_a_of_Reachable_for_C_with_pres_step
          C C (WethReachable C)
  -- hReach_Z
  · intro s g hR; exact WethReachable_Z_preserves C s g hR
  -- hReach_step (pres-aware)
  · intro s s' f' cost op arg hR hFetch hStep hRet hRev hStop hSD hPresZ hPresStep
    exact weth_step_closure_with_pres C hInvPres s s' f' cost op arg hR
      hFetch hStep hRet hRev hStop hSD hPresZ hPresStep
  -- hReach_decodeSome
  · intro s hR; exact WethReachable_decodeSome C s hR
  -- hReach_no_create
  · intro s op arg hR hFetch; exact weth_no_create C s op arg hR hFetch
  -- hReachInit (C arm only — receives I.codeOwner = C and σ-presence at C)
  · intro cA gbh bs σ σ₀ g A I hCO hPresσ
    refine ⟨?_, ?_, ?_, ?_⟩
    -- WethTrace via WethTrace_initial.
    · exact WethTrace_initial C hDeployed cA gbh bs σ σ₀ g A I hCO
    -- ¬ (pc=32 ∧ stack=0): at the fresh state pc=0 (default), stack=[] (default),
    -- so pc.toNat=0 ≠ 32.
    · intro ⟨h32, _⟩
      -- freshState.pc = (default : EVM.State).pc = ⟨0⟩, so .toNat = 0.
      have : (default : EVM.State).pc.toNat = 0 := by decide
      rw [this] at h32
      cases h32
    -- accountPresentAt freshState.accountMap C: = accountPresentAt σ C.
    · exact hPresσ
    -- WethInvFr freshState.accountMap C: = WethInvFr σ C from hInvInit.
    · exact hInvInit σ I hCO
  -- hΞ_other
  · exact hΞ_other

/-- **`xi_preserves_C_other` as a Lean theorem.** The non-C arm of
Ξ-preservation of σ-presence at C is now fully discharged by the
framework's `Ξ_preserves_account_at_a_universal` (no Reachable, no
hReach_no_create, fully unconditional). The `I.codeOwner ≠ C`
hypothesis is unused but kept for signature compatibility with the
former `xi_preserves_C_other` structural field.

This eliminates the last structural assumption around Ξ-preservation
at C: `xi_preserves_C` is fully derived in `weth_xi_preserves_C` from
the framework's strong-induction closure plus the now-derived
non-C-arm. -/
theorem weth_xi_preserves_C_other
    (C : AccountAddress) :
    ∀ (fuel : ℕ) (cA : Batteries.RBSet AccountAddress compare)
        (gbh : BlockHeader) (bs : ProcessedBlocks)
        (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
        (I : ExecutionEnv .EVM),
      I.codeOwner ≠ C →
      accountPresentAt σ C →
      match EVM.Ξ fuel cA gbh bs σ σ₀ g A I with
      | .ok (.success (_, σ', _, _) _) => accountPresentAt σ' C
      | _ => True := by
  intro fuel cA gbh bs σ σ₀ g A I _hCO h_present
  exact Ξ_preserves_account_at_a_universal C fuel cA gbh bs σ σ₀ g A I h_present

/-- **`bytecodePreservesInvariant` — Weth's bytecode-level §H.2 entry.**

Discharges `ΞPreservesInvariantAtC C` from the deployment witness
(`hDeployed`), the framework's `ΞPreservesAccountAt C` witness (`hΞ`,
used to thread account-presence through the step closure via
`EVM_step_preserves_present_no_create`), the σ-has-C-at-Ξ-entry fact
(`hAccInit`), and two structural bytecode hypotheses (SSTORE
preservation and CALL dispatch). The non-halt step closure is derived
in-Lean by `weth_step_closure C` (aggregating the 61 per-PC walks).
Used by `weth_solvency_invariant` in `Solvency.lean` in place of the
opaque `WethAssumptions.xi_inv` hypothesis. -/
theorem bytecodePreservesInvariant
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hΞ : ΞPreservesAccountAt C)
    (hInvPres : WethStepInvFrPreserves C)
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (hInvInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → WethInvFr σ C)
    (hSStore : WethSStorePreserves C)
    (hCall : WethCallSlack C) :
    ΞPreservesInvariantAtC C := by
  have hStepClosure : WethStepClosure C := weth_step_closure C
  apply ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch
    WethOpAllowed C (WethReachable C)
  · -- hReach_Z
    intro s g h
    exact WethReachable_Z_preserves C s g h
  · -- hReach_step (op-conditional non-halt)
    intro s s' f' cost op arg hR hFetch hStep hRet hRev hStop hSD
    exact hStepClosure hΞ hInvPres s s' f' cost op arg hR hFetch hStep
      hRet hRev hStop hSD
  · -- hReach_decodeSome
    intro s h
    exact WethReachable_decodeSome C s h
  · -- hReach_op (discharged in-Lean by WethReachable_op_in_allowed)
    intro s op arg hR hFetch
    exact WethReachable_op_in_allowed C s op arg hR hFetch
  · -- hDischarge
    exact WethOpAllowed_discharge
  · -- hReach_call_slack (slack-callback form)
    intro s arg hR hWF hCO hNC hInv hFetch μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
    exact hCall s arg hR hWF hCO hNC hInv hFetch μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
  · -- hReach_sstore
    intro s s' f' cost arg hR hWF hCO hInv hFetch hStep
    exact hSStore s s' f' cost arg hR hWF hCO hInv hFetch hStep
  · -- hReachInit
    intro cA gbh bs σ σ₀ g A I hCO
    exact WethReachable_initial C hDeployed cA gbh bs σ σ₀ g A I hCO
      (hAccInit σ I hCO) (hInvInit σ I hCO)

/-- **`bytecodePreservesInvariant_from_cascades` — convenience entry that
takes the per-PC cascade-fact predicates directly.**

Composes `bytecodePreservesInvariant` with `weth_sstore_preserves_from_cascades`
and `weth_call_slack_from_cascade`. This is the natural entry point
once the trace cascade extension lands: instead of asking the consumer
for the broader `WethSStorePreserves` / `WethCallSlack` predicates,
they supply the narrower per-PC cascade-fact predicates that the
trace cascade extension would establish from the per-PC `WethTrace`
disjuncts at PCs 40, 60, 72. -/
theorem bytecodePreservesInvariant_from_cascades
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hΞ : ΞPreservesAccountAt C)
    (hInvPres : WethStepInvFrPreserves C)
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (hInvInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → WethInvFr σ C)
    (h40 : WethPC40CascadeFacts C)
    (h60 : WethPC60CascadeFacts C)
    (h72 : WethPC72CascadeFacts C) :
    ΞPreservesInvariantAtC C :=
  bytecodePreservesInvariant C hDeployed hΞ hInvPres hAccInit hInvInit
    (weth_sstore_preserves_from_cascades C h40 h60)
    (weth_call_slack_from_cascade C h72)

/-- **Convenience entry that derives `pc60_cascade` from σ-has-C.**

This replaces the `h60` field with the narrower σ-has-C structural
fact, leveraging `weth_pc60_cascade` to discharge the cascade fact
predicate from the threaded `WethTrace` cascade.

Consumers prefer this entry: σ-has-C is a small, framework-derivable
fact (Weth's bytecode has no SELFDESTRUCT and Ξ enters at C with
σ[C] = some _; the framework's `Λ_invariant_preserved` chain
preserves it). -/
theorem bytecodePreservesInvariant_from_account_and_cascades
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hΞ : ΞPreservesAccountAt C)
    (hInvPres : WethStepInvFrPreserves C)
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (hInvInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → WethInvFr σ C)
    (h40 : WethPC40CascadeFacts C)
    (h72 : WethPC72CascadeFacts C) :
    ΞPreservesInvariantAtC C :=
  bytecodePreservesInvariant_from_cascades C hDeployed hΞ hInvPres
    hAccInit hInvInit h40 (weth_pc60_cascade C (weth_account_at_C C)) h72

/-- **Convenience entry that derives both pc60 and pc72 cascades from
narrower structural facts.** Replaces the opaque `pc72_cascade` field
with `WethCallNoWrapAt72` (real-world chain bound) and
`WethCallSlackAt72` (post-SSTORE slack — derivable from threading once
WethReachable carries WethInvFr). -/
theorem bytecodePreservesInvariant_from_narrowed
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hΞ : ΞPreservesAccountAt C)
    (hInvPres : WethStepInvFrPreserves C)
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (hInvInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → WethInvFr σ C)
    (hNoWrap : WethCallNoWrapAt72 C)
    (hSlack : WethCallSlackAt72 C)
    (h40 : WethPC40CascadeFacts C) :
    ΞPreservesInvariantAtC C :=
  bytecodePreservesInvariant_from_account_and_cascades C hDeployed
    hΞ hInvPres hAccInit hInvInit h40 (weth_pc72_cascade C hNoWrap hSlack)

/-- **Final convenience entry: all three opaque cascade-fact assumptions
discharged as theorems.** Takes only the narrower structural facts
(`WethCallNoWrapAt72`, `WethDepositPreCredit`) and produces
`ΞPreservesInvariantAtC C`. The `WethCallSlackAt72 C` fact is now
discharged as `weth_call_slack` (using `WethAccountAtC`, itself a
theorem); the `WethDepositCascadeStruct C` fact is discharged as
`weth_deposit_cascade`. -/
theorem bytecodePreservesInvariant_fully_narrowed
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hΞ : ΞPreservesAccountAt C)
    (hInvPres : WethStepInvFrPreserves C)
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (hInvInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → WethInvFr σ C)
    (hNoWrap : WethCallNoWrapAt72 C)
    (hPreCredit : WethDepositPreCredit C) :
    ΞPreservesInvariantAtC C :=
  bytecodePreservesInvariant_from_narrowed C hDeployed hΞ hInvPres hAccInit
    hInvInit hNoWrap (weth_call_slack C (weth_account_at_C C))
    (weth_pc40_cascade C
      (weth_deposit_cascade C (weth_account_at_C C))
      hPreCredit)

/-! ## Invariant-aware variant — discharge `WethCALLStepInvFr` as a theorem

The framework's `ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware`
exposes `WethInvFr s'.accountMap C` to the `hReach_step` callback at every
non-halt step (the framework already established it via the internal
CALL/SSTORE arms). This eliminates the need for a per-step CALL invariant
predicate (`WethCALLStepInvFr C`): the step closure receives `hInv'`
externally rather than computing it via `hInvPres`. -/

/-- **Invariant-aware `bytecodePreservesInvariant`.** Like
`bytecodePreservesInvariant` but uses the framework's invariant-aware
slack-dispatch entry point and `weth_step_closure_with_pres_inv_aware`,
removing the dependency on `WethStepInvFrPreserves C`'s CALL arm. -/
theorem bytecodePreservesInvariant_inv_aware
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hΞ : ΞPreservesAccountAt C)
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (hInvInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → WethInvFr σ C)
    (hSStore : WethSStorePreserves C)
    (hCall : WethCallSlack C) :
    ΞPreservesInvariantAtC C := by
  apply ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware
    WethOpAllowed C (WethReachable C)
  · -- hReach_Z
    intro s g h
    exact WethReachable_Z_preserves C s g h
  · -- hReach_step (invariant-aware: receives hInv' from the framework)
    intro s s' f' cost op arg hR hFetch hStep hRet hRev hStop hSD hInv'
    have hAcc : accountPresentAt s.accountMap C := hR.2.2.1
    have h_no_create : op ≠ .CREATE ∧ op ≠ .CREATE2 :=
      weth_no_create C s op arg hR hFetch
    have hAcc' : accountPresentAt s'.accountMap C :=
      EVM_step_preserves_present_no_create C hΞ op arg f' cost s s'
        h_no_create hStep hAcc
    exact weth_step_closure_with_pres_inv_aware C s s' f' cost op arg hR
      hFetch hStep hRet hRev hStop hSD hAcc hAcc' hInv'
  · -- hReach_decodeSome
    intro s h
    exact WethReachable_decodeSome C s h
  · -- hReach_op
    intro s op arg hR hFetch
    exact WethReachable_op_in_allowed C s op arg hR hFetch
  · -- hDischarge
    exact WethOpAllowed_discharge
  · -- hReach_call_slack
    intro s arg hR hWF hCO hNC hInv hFetch μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
    exact hCall s arg hR hWF hCO hNC hInv hFetch μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
  · -- hReach_sstore
    intro s s' f' cost arg hR hWF hCO hInv hFetch hStep
    exact hSStore s s' f' cost arg hR hWF hCO hInv hFetch hStep
  · -- hReachInit
    intro cA gbh bs σ σ₀ g A I hCO
    exact WethReachable_initial C hDeployed cA gbh bs σ σ₀ g A I hCO
      (hAccInit σ I hCO) (hInvInit σ I hCO)

/-- **Invariant-aware variant of `bytecodePreservesInvariant_fully_narrowed`.**
Composes `bytecodePreservesInvariant_inv_aware` with the in-Lean
discharge of `WethCallSlack` / `WethSStorePreserves` from cascade facts.
Requires **only** `WethCallNoWrapAt72` and `WethDepositPreCredit` —
no `WethStepInvFrPreserves C` needed. -/
theorem bytecodePreservesInvariant_inv_aware_fully_narrowed
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hΞ : ΞPreservesAccountAt C)
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (hInvInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → WethInvFr σ C)
    (hNoWrap : WethCallNoWrapAt72 C)
    (hPreCredit : WethDepositPreCredit C) :
    ΞPreservesInvariantAtC C := by
  have hSlack72 : WethCallSlackAt72 C :=
    weth_call_slack C (weth_account_at_C C)
  have h72 : WethPC72CascadeFacts C := weth_pc72_cascade C hNoWrap hSlack72
  have h40 : WethPC40CascadeFacts C :=
    weth_pc40_cascade C
      (weth_deposit_cascade C (weth_account_at_C C))
      hPreCredit
  have h60 : WethPC60CascadeFacts C := weth_pc60_cascade C (weth_account_at_C C)
  exact bytecodePreservesInvariant_inv_aware C hDeployed hΞ hAccInit hInvInit
    (weth_sstore_preserves_from_cascades C h40 h60)
    (weth_call_slack_from_cascade C h72)

/-- **Per-CALL-step `WethInvFr` preservation as a Lean theorem.**

Discharges the formerly-structural `WethAssumptions.call_inv_step_pres`
field's predicate (`WethCALLStepInvFr C`). Requires the standard Weth
deployment / σ-presence / σ_P-invariant facts plus `StateWF s.accountMap`
and the `cA`-exclusion at `C` (these latter two are framework-level
state-well-formedness hypotheses that are normally threaded through Υ
via `Υ_invariant_preserved`'s preconditions but are not part of
`WethReachable`).

Strategy:
* Derive `ΞPreservesInvariantAtC C` via `bytecodePreservesInvariant_inv_aware_fully_narrowed`
  (no `WethCALLStepInvFr` dependency — that's the whole point).
* Convert the witness to `ΞInvariantAtCFrame C (f+1)` /
  `ΞInvariantFrameAtC C (f+1)` IHs via the framework's witness
  conversion theorems.
* Apply `step_CALL_arm_at_C_slack_invariant` (now public) with the
  IHs and the slack callback derived from `weth_call_slack`.

The `hWF` and `hNC` hypotheses cannot be derived from `WethReachable`
(they're framework-level), so consumers supply them per-state. -/
theorem weth_call_inv_step_pres
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (hInvInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → WethInvFr σ C)
    (hNoWrap : WethCallNoWrapAt72 C)
    (hPreCredit : WethDepositPreCredit C)
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hWF : StateWF s.accountMap)
    (hNC : ∀ a ∈ s.createdAccounts, a ≠ C)
    (hR : WethReachable C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (.CALL, arg))
    (hStep : EVM.step (f' + 1) cost (some (.CALL, arg)) s = .ok s') :
    WethInvFr s'.accountMap C := by
  -- Derive the invariant-witness in-Lean.
  have hΞ : ΞPreservesAccountAt C := Ξ_preserves_account_at_a_universal C
  have hWitness : ΞPreservesInvariantAtC C :=
    bytecodePreservesInvariant_inv_aware_fully_narrowed C hDeployed hΞ
      hAccInit hInvInit hNoWrap hPreCredit
  -- Convert witness to per-fuel IHs at fuel `f' + 1`.
  have hAtCFrame : ΞInvariantAtCFrame C (f' + 1) :=
    ΞInvariantAtCFrame_of_witness C hWitness (f' + 1)
  have hFrame : ΞInvariantFrameAtC C (f' + 1) :=
    ΞInvariantFrameAtC_of_witness C hWitness (f' + 1)
  -- Pull `WethReachable`'s constituents.
  have hCO : C = s.executionEnv.codeOwner := hR.1.1
  have hInv : WethInvFr s.accountMap C := hR.2.2.2
  -- Slack callback derived via `weth_call_slack` (theorem).
  have hSlack : WethCallSlackAt72 C := weth_call_slack C (weth_account_at_C C)
  -- PC = 72 follows from `WethReachable` + CALL fetch.
  have hPC72 : s.pc.toNat = 72 := WethReachable_call_pc hR hFetch
  -- Per-state CALL precondition callback for `step_CALL_arm_at_C_slack_invariant`.
  have h_call_pre :
      ∀ (μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ : UInt256) (tl : Stack UInt256),
        s.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: tl →
        (∀ acc,
            s.accountMap.find? (AccountAddress.ofUInt256 μ₁) = some acc →
            acc.balance.toNat + μ₂.toNat < UInt256.size) ∧
        (μ₂ = ⟨0⟩ ∨ ∃ acc,
            s.accountMap.find?
                (AccountAddress.ofUInt256
                  (.ofNat s.executionEnv.codeOwner)) = some acc ∧
            μ₂.toNat ≤ acc.balance.toNat) ∧
        (C ≠ AccountAddress.ofUInt256
                (.ofNat s.executionEnv.codeOwner) ∨
         μ₂ = ⟨0⟩ ∨
         μ₂.toNat + storageSum s.accountMap C
           ≤ balanceOf s.accountMap C) := by
    intro μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
    -- Pull from the per-PC-72 callbacks: `WethCallNoWrapAt72` + `weth_call_slack`.
    refine ⟨?_, ?_, ?_⟩
    · -- recipient no-wrap.
      exact hNoWrap s hR hPC72 μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk
    · -- sender funds disjunction.
      exact (hSlack s hR hPC72 μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk).2
    · -- slack disjunction (weakened to include `C ≠ ...`).
      have hSlackPart := (hSlack s hR hPC72 μ₀ μ₁ μ₂ μ₃ μ₄ μ₅ μ₆ tl hStk).1
      -- `μ₂.toNat + storageSum ≤ balanceOf` holds unconditionally; weaken
      -- to the three-disjunct form.
      exact Or.inr (Or.inr hSlackPart)
  -- Apply the framework's CALL helper.
  have hBundle :=
    step_CALL_arm_at_C_slack_invariant C f' cost arg s s' hWF hCO hNC
      hAtCFrame hFrame hInv h_call_pre hStep
  exact hBundle.1

end EvmSmith.Weth
