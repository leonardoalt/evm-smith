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
   (s.pc.toNat = 61 ∧ s.stack.length = 1) ∨   -- post-SSTORE [x]
   (s.pc.toNat = 63 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 65 ∧ s.stack.length = 3) ∨
   (s.pc.toNat = 67 ∧ s.stack.length = 4) ∨
   (s.pc.toNat = 69 ∧ s.stack.length = 5) ∨
   (s.pc.toNat = 70 ∧ s.stack.length = 6) ∨
   (s.pc.toNat = 71 ∧ s.stack.length = 7) ∨
   (s.pc.toNat = 72 ∧ s.stack.length = 8) ∨   -- pre-CALL: gas, to, val, ao, as, ro, rs, x
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
  -- (for future cascade-fact threading) so is also 3-conjunct. The rest
  -- are 2-conjunct. PCs 80, 81, 83, 85 each appear twice (different
  -- stack lengths from PC 55/77 entry); both are 2-conjunct.
  rcases hPC with
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
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
       (s'.pc.toNat = 61 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 63 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 65 ∧ s'.stack.length = 3) ∨
       (s'.pc.toNat = 67 ∧ s'.stack.length = 4) ∨
       (s'.pc.toNat = 69 ∧ s'.stack.length = 5) ∨
       (s'.pc.toNat = 70 ∧ s'.stack.length = 6) ∨
       (s'.pc.toNat = 71 ∧ s'.stack.length = 7) ∨
       (s'.pc.toNat = 72 ∧ s'.stack.length = 8) ∨
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
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 43 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 60 1
    · rw [hStk']; exact hLenTl

/-! ### PC 61 — `PUSH1 0` (withdraw: CALL retSize) -/

private theorem WethTrace_step_at_61
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 61) (hLen : s.stack.length = 1)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 61 := pc_eq_ofNat_of_toNat s 61 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_61 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 44 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 61 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 2; simp [hLen]

/-! ### PC 63 — `PUSH1 0` (withdraw: CALL retOff) -/

private theorem WethTrace_step_at_63
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 63) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 63 := pc_eq_ofNat_of_toNat s 63 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_63 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 45 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 63 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 3; simp [hLen]

/-! ### PC 65 — `PUSH1 0` (withdraw: CALL argsSize) -/

private theorem WethTrace_step_at_65
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 65) (hLen : s.stack.length = 3)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 65 := pc_eq_ofNat_of_toNat s 65 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_65 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 46 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 65 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 4; simp [hLen]

/-! ### PC 67 — `PUSH1 0` (withdraw: CALL argsOff) -/

private theorem WethTrace_step_at_67
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 67) (hLen : s.stack.length = 4)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 67 := pc_eq_ofNat_of_toNat s 67 (by decide) hpc
  obtain ⟨hPC', hStk', hEE'⟩ :=
    step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_67 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 47 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 67 2
  · rw [hStk']; show List.length (UInt256.ofNat 0 :: s.stack) = 5; simp [hLen]

/-! ### PC 69 — `DUP5` (withdraw: copy `x` as CALL value) -/

private theorem WethTrace_step_at_69
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 69) (hLen : s.stack.length = 5)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 69 := pc_eq_ofNat_of_toNat s 69 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: tl, hLen2 =>
    obtain ⟨hPC', hStk', hEE'⟩ :=
      step_DUP5_at_pc s s' f' cost op arg _ hd1 hd2 hd3 hd4 hd5 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_69 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 48 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 69 1
    · rw [hStk']; show (hd5 :: s.stack).length = 6; simp [hLen]

/-! ### PC 70 — `CALLER` (withdraw: push recipient = sender) -/

private theorem WethTrace_step_at_70
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 70) (hLen : s.stack.length = 6)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 70 := pc_eq_ofNat_of_toNat s 70 (by decide) hpc
  obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
    step_CALLER_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_70 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 49 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 70 1
  · rw [hStk']; show (v :: s.stack).length = 7; simp [hLen]

/-! ### PC 71 — `GAS` (withdraw: push remaining gas as CALL gas) -/

private theorem WethTrace_step_at_71
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 71) (hLen : s.stack.length = 7)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 71 := pc_eq_ofNat_of_toNat s 71 (by decide) hpc
  obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
    step_GAS_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_71 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 50 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 71 1
  · rw [hStk']; show (v :: s.stack).length = 8; simp [hLen]

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
newVal)`. -/

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
halt sink (PC 32 length=0), plus account-presence at `C`. The X loop
never re-iterates through the halt sink (PC 31 = REVERT exits the X
loop), so dropping it from the reachable set still covers the
X-induction's needs while satisfying the framework's step closure for
non-halt ops. The third conjunct (`accountPresentAt s.accountMap C`)
makes `WethAccountAtC` derivable from `WethReachable` via projection. -/
private def WethReachable (C : AccountAddress) (s : EVM.State) : Prop :=
  WethTrace C s ∧ ¬ (s.pc.toNat = 32 ∧ s.stack.length = 0) ∧
    accountPresentAt s.accountMap C

/-- `Z` (gas-only update) preserves `WethReachable`. -/
private theorem WethReachable_Z_preserves
    (C : AccountAddress) (s : EVM.State) (g : UInt256)
    (h : WethReachable C s) :
    WethReachable C { s with gasAvailable := g } := by
  obtain ⟨hTrace, hNot, hAcc⟩ := h
  refine ⟨WethTrace_Z_preserves C s g hTrace, hNot, ?_⟩
  -- Z preserves accountMap (only changes gasAvailable).
  exact hAcc

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
  obtain ⟨⟨_, hCode, hPC⟩, _hNot⟩ := h
  unfold fetchInstr at hFetch
  rw [hCode] at hFetch
  rcases hPC with
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
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

/-! ## Structural hypotheses (§H.2 closure for Weth's bytecode)

These three predicates capture the load-bearing per-state facts that
`bytecodePreservesInvariant` consumes from the bundle of per-PC walks
plus the bytecode-level slack reasoning. -/

/-- Step closure of `WethReachable` under non-halt operations. The 61
per-PC walks (`WethTrace_step_at_*` above) provide the ingredients —
aggregating them into this aggregate is mechanical case-splitting.

The `hΞ : ΞPreservesAccountAt C` parameter is consumed by the walks
to propagate `accountPresentAt` (the new third conjunct of
`WethReachable`) across each step via the framework's
`EVM_step_preserves_present_no_create`. -/
def WethStepClosure (C : AccountAddress) : Prop :=
  ΞPreservesAccountAt C →
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
    (hT : WethTrace C s) (hpc_ne : s.pc.toNat ≠ 32) :
    WethReachable C s :=
  ⟨hT, fun ⟨h1, _⟩ => hpc_ne h1, hAcc⟩

private theorem WethReachable_of_WethTrace_len_ne_0
    {C : AccountAddress} {s : EVM.State}
    (hAcc : accountPresentAt s.accountMap C)
    (hT : WethTrace C s) (hlen : s.stack.length ≠ 0) :
    WethReachable C s :=
  ⟨hT, fun ⟨_, h2⟩ => hlen h2, hAcc⟩

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
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
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
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
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
    ⟨hpc, _, _⟩|⟨hpc, _, _⟩|⟨hpc, _, hCascade⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
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
  fun _ hR => hR.2.2

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
* `acc.storage.find? slot = some oldVal`,
* the at-`C` Ξ-pre-state β-credit slack:
  `storageSum σ C - oldVal.toNat + newVal.toNat ≤ balanceOf σ C`,
  which combined with the SSTORE-replace law yields the post-step
  invariant.

Discharged by extending the trace at PCs 32→40 with the Θ-pre-credit
slack tracked at the Ξ entry point. (This is the "PC 40 deposit" case
the prior plan flagged as deferable; it requires Θ-side reasoning that
threads through to `WethReachable`.) -/
def WethPC40CascadeFacts (C : AccountAddress) : Prop :=
  ∀ s : EVM.State,
    WethReachable C s →
    s.pc.toNat = 40 →
    fetchInstr s.executionEnv s.pc =
      .ok (.StackMemFlow .SSTORE, none) →
    ∃ (slot : UInt256) (tl : Stack UInt256),
      ∃ (acc : Account .EVM) (oldVal : UInt256),
        s.accountMap.find? C = some acc ∧
        acc.storage.find? slot = some oldVal ∧
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

Discharging in full requires cascade threading through PCs 32..40 —
same pattern as the PCs 47..60 threading already done for pc60. The
threading would establish:

* stack[0] = sender, stack[1] = newBal,
* slot lookup for sender's balance, with old value `oldBal`,
* `newBal = oldBal + msg.value`.

Pending that threading, this is bundled as a structural assumption.
**Bytecode-derivable in principle**, just not yet threaded. -/
def WethDepositCascadeStruct (C : AccountAddress) : Prop :=
  ∀ s : EVM.State,
    WethReachable C s →
    s.pc.toNat = 40 →
    fetchInstr s.executionEnv s.pc =
      .ok (.StackMemFlow .SSTORE, none) →
    ∃ (slot : UInt256) (tl : Stack UInt256),
      ∃ (acc : Account .EVM) (oldVal : UInt256),
        s.accountMap.find? C = some acc ∧
        acc.storage.find? slot = some oldVal ∧
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
      acc.storage.find? slot = some oldVal →
      ((∃ newVal,
          s.stack = slot :: newVal :: tl ∧
          storageSum s.accountMap C - oldVal.toNat + newVal.toNat
            ≤ balanceOf s.accountMap C ∧
          (newVal == default) = false) ∨
       s.stack = slot :: ⟨0⟩ :: tl)

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
      StateWF s.accountMap →
      C = s.executionEnv.codeOwner →
      WethInvFr s.accountMap C →
      s.pc.toNat = 60 →
      fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
      EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
      WethInvFr s'.accountMap C := by
  intro s s' f' cost arg hR _hWF hCO hInv hPC60 hFetch hStep
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
post-SSTORE storageSum by the (preserved) balanceOf. -/
private theorem weth_sstore_preserves_pc40_from_cascade
    (C : AccountAddress) (hCascade : WethPC40CascadeFacts C) :
    ∀ (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat)),
      WethReachable C s →
      StateWF s.accountMap →
      C = s.executionEnv.codeOwner →
      WethInvFr s.accountMap C →
      s.pc.toNat = 40 →
      fetchInstr s.executionEnv s.pc = .ok (.StackMemFlow .SSTORE, arg) →
      EVM.step (f' + 1) cost (some (.StackMemFlow .SSTORE, arg)) s = .ok s' →
      WethInvFr s'.accountMap C := by
  intro s s' f' cost arg hR hWF hCO hInv hPC40 hFetch hStep
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
  obtain ⟨slot, tl, acc, oldVal, h_find, h_old, hCase⟩ :=
    hCascade s hR hPC40 hFetchNone
  cases hCase with
  | inl h =>
    obtain ⟨newVal, hStk, h_slack, hNonZero⟩ := h
    exact WethInvFr_step_SSTORE_at_C_replace_with_slack C s s' f' cost none
      slot newVal oldVal tl hStk hCO acc h_find h_old h_slack hNonZero hInv hStep
  | inr hStk =>
    exact WethSStorePreserves_erase C s s' f' cost none slot oldVal tl
      hCO hStk acc h_find h_old hInv hStep

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
  intro s s' f' cost arg hR hWF hCO hInv hFetch hStep
  rcases WethReachable_sstore_pc hR hFetch with hPC40 | hPC60
  · exact weth_sstore_preserves_pc40_from_cascade C h40 s s' f' cost arg
      hR hWF hCO hInv hPC40 hFetch hStep
  · exact weth_sstore_preserves_pc60_from_cascade C h60 s s' f' cost arg
      hR hWF hCO hInv hPC60 hFetch hStep

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
    (hAcc : accountPresentAt σ C) :
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
  refine ⟨WethTrace_initial C hDeployed cA gbh bs σ σ₀ g A I hCO, ?_, hAcc⟩
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

/-- Step-closure aggregate. Discharges `WethStepClosure C` for any `C`. -/
theorem weth_step_closure (C : AccountAddress) : WethStepClosure C := by
  intro hΞ s s' f' cost op arg hR hFetch hStep hRet hRev hStop _hSD
  obtain ⟨hT, _hNot, hAcc⟩ := hR
  have hT' := hT
  obtain ⟨hCO, hCode, hPC⟩ := hT
  -- Account-presence at s'.accountMap C from per-step preservation.
  have h_no_create : op ≠ .CREATE ∧ op ≠ .CREATE2 :=
    weth_no_create C s op arg ⟨hT', _hNot, hAcc⟩ hFetch
  have hAcc' : accountPresentAt s'.accountMap C :=
    EVM_step_preserves_present_no_create C hΞ op arg f' cost s s'
      h_no_create hStep hAcc
  -- Case split on the 64 `WethTrace` disjuncts.
  rcases hPC with
    ⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|
    ⟨hpc, hLen, hStk0⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen, hStk0⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|
    ⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen, hCascade36⟩|⟨hpc, hLen, hCascade37⟩|⟨hpc, hLen, hCascade38⟩|
    ⟨hpc, hLen, hCascade39⟩|⟨hpc, hLen, hCascade40⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|
    ⟨hpc, hLen, hStk01⟩|⟨hpc, hLen, hCascade49⟩|⟨hpc, hLen, hCascade50⟩|⟨hpc, hLen, hCascade51⟩|⟨hpc, hLen, hCascade52⟩|⟨hpc, hLen, hCascade55⟩|⟨hpc, hLen, hCascade56⟩|⟨hpc, hLen, hCascade57⟩|
    ⟨hpc, hLen, hCascade58⟩|⟨hpc, hLen, hCascade59⟩|⟨hpc, hLen, _⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|
    ⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen, hStk0⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|
    ⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩|⟨hpc, hLen⟩
  -- Case PC=0 (PUSH1 0). Lands at PC=2 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 0 := pc_eq_ofNat_of_toNat s 0 (by decide) hpc
    obtain ⟨hPC', hStk', _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_0 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_0 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 0 2]; decide
  -- Case PC=2 (CALLDATALOAD). Lands at PC=3 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 2 := pc_eq_ofNat_of_toNat s 2 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_2 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 3 2]; decide
  -- Case PC=5 (SHR). Lands at PC=6 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 5 := pc_eq_ofNat_of_toNat s 5 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_5 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 7 5]; decide
  -- Case PC=12 (EQ). Lands at PC=13 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 12 := pc_eq_ofNat_of_toNat s 12 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_12 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 13 3]; decide
  -- Case PC=16 (JUMPI). Two branches: taken→PC=32 len=1, not-taken→PC=17.
  -- Either way `s'.stack.length = 1 ≠ 0` (post-state pops 2 from len=3).
  · have hpcEq : s.pc = UInt256.ofNat 16 := pc_eq_ofNat_of_toNat s 16 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_16 C s s' f' cost op arg hT' hpc hLen hStk0 hFetch hStep
    refine WethReachable_of_WethTrace_len_ne_0 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 17 5]; decide
  -- Case PC=22 (EQ). Lands at PC=23 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 22 := pc_eq_ofNat_of_toNat s 22 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_22 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 23 3]; decide
  -- Case PC=26 (JUMPI). Two branches: taken→PC=42, not-taken→PC=27. Both ≠ 32.
  -- Hmm, however the witness `s'.pc.toNat ≠ 32` requires casing. Easier: post-len = 0.
  -- Wait, post-len is `tl.length = 0` (pops 2 from len=2). So `s'.stack.length = 0`,
  -- which means we cannot use `len ≠ 0`. Use `pc ≠ 32` and case-split.
  · have hpcEq : s.pc = UInt256.ofNat 26 := pc_eq_ofNat_of_toNat s 26 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_26 C s s' f' cost op arg hT' hpc hLen hStk0 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 27 2]; decide
  -- Case PC=29 (PUSH1 0). Lands at PC=31 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 29 := pc_eq_ofNat_of_toNat s 29 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_29 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_29 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 32 1]; decide
  -- Case PC=33 (POP). Lands at PC=34 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 33 := pc_eq_ofNat_of_toNat s 33 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_33 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 34 1]; decide
  -- Case PC=35 (DUP1). Lands at PC=36 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 35 := pc_eq_ofNat_of_toNat s 35 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_35 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 37 1]; decide
  -- Case PC=38 (ADD). Lands at PC=39 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 38 := pc_eq_ofNat_of_toNat s 38 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_38 C s s' f' cost op arg hT' hpc hLen hCascade38 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 42 1]; decide
  -- Case PC=43 (PUSH1 4). Lands at PC=45 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 43 := pc_eq_ofNat_of_toNat s 43 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_43 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_43 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 43 2]; decide
  -- Case PC=45 (CALLDATALOAD). Lands at PC=46 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 45 := pc_eq_ofNat_of_toNat s 45 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_45 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 46 1]; decide
  -- Case PC=47 (DUP1). Lands at PC=48 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 47 := pc_eq_ofNat_of_toNat s 47 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_47 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 52 3]; decide
  -- Case PC=55 (JUMPI). Branches: taken→PC=80, not-taken→PC=56. Both ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 55 := pc_eq_ofNat_of_toNat s 55 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_55 C s s' f' cost op arg hT' hpc hLen hCascade55 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, _hLen2 =>
      obtain ⟨hPC', _, _⟩ :=
        step_SWAP1_at_pc_local s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_59 hStep
      rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 59 1]; decide
  -- Case PC=60 (SSTORE). Lands at PC=61 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 60 := pc_eq_ofNat_of_toNat s 60 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_60 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
      WethTrace_step_at_61 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 61 2]; decide
  -- Case PC=63 (PUSH1 0). Lands at PC=65 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 63 := pc_eq_ofNat_of_toNat s 63 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_63 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_63 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 63 2]; decide
  -- Case PC=65 (PUSH1 0). Lands at PC=67 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 65 := pc_eq_ofNat_of_toNat s 65 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_65 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_65 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 65 2]; decide
  -- Case PC=67 (PUSH1 0). Lands at PC=69 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 67 := pc_eq_ofNat_of_toNat s 67 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_67 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_67 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 67 2]; decide
  -- Case PC=69 (DUP5). Lands at PC=70 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 69 := pc_eq_ofNat_of_toNat s 69 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_69 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
      WethTrace_step_at_70 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 70 1]; decide
  -- Case PC=71 (GAS). Lands at PC=72 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 71 := pc_eq_ofNat_of_toNat s 71 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_GAS_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_71 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_71 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 71 1]; decide
  -- Case PC=72 (CALL). Lands at PC=73 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 72 := pc_eq_ofNat_of_toNat s 72 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_72 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 74 3]; decide
  -- Case PC=77 (JUMPI). Branches: taken→PC=80, not-taken→PC=78. Both ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 77 := pc_eq_ofNat_of_toNat s 77 (by decide) hpc
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_77 C s s' f' cost op arg hT' hpc hLen hStk0 hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 80 1]; decide
  -- Case PC=80 length=1 (JUMPDEST). Lands at PC=81 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 80 := pc_eq_ofNat_of_toNat s 80 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_JUMPDEST_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_80 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_80_len1 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 80 1]; decide
  -- Case PC=81 length=3 (PUSH1 0). Lands at PC=83 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 81 := pc_eq_ofNat_of_toNat s 81 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_81 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_81_len3 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 81 2]; decide
  -- Case PC=81 length=1 (PUSH1 0). Lands at PC=83 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 81 := pc_eq_ofNat_of_toNat s 81 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_81 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_81_len1 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 81 2]; decide
  -- Case PC=83 length=4 (PUSH1 0). Lands at PC=85 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 83 := pc_eq_ofNat_of_toNat s 83 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_83 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_83_len4 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
    rw [hPC', hpcEq, ofNat_add_ofNat_toNat_lt256 83 2]; decide
  -- Case PC=83 length=2 (PUSH1 0). Lands at PC=85 ≠ 32.
  · have hpcEq : s.pc = UInt256.ofNat 83 := pc_eq_ofNat_of_toNat s 83 (by decide) hpc
    obtain ⟨hPC', _, _⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_83 hStep
    have hT_s' : WethTrace C s' :=
      WethTrace_step_at_83_len2 C s s' f' cost op arg hT' hpc hLen hFetch hStep
    refine WethReachable_of_WethTrace_pc_ne_32 hAcc' hT_s' ?_
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
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
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
    exact hStepClosure hΞ s s' f' cost op arg hR hFetch hStep hRet hRev hStop hSD
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
      (hAccInit σ I hCO)

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
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (h40 : WethPC40CascadeFacts C)
    (h60 : WethPC60CascadeFacts C)
    (h72 : WethPC72CascadeFacts C) :
    ΞPreservesInvariantAtC C :=
  bytecodePreservesInvariant C hDeployed hΞ hAccInit
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
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (h40 : WethPC40CascadeFacts C)
    (h72 : WethPC72CascadeFacts C) :
    ΞPreservesInvariantAtC C :=
  bytecodePreservesInvariant_from_cascades C hDeployed hΞ hAccInit
    h40 (weth_pc60_cascade C (weth_account_at_C C)) h72

/-- **Convenience entry that derives both pc60 and pc72 cascades from
narrower structural facts.** Replaces the opaque `pc72_cascade` field
with `WethCallNoWrapAt72` (real-world chain bound) and
`WethCallSlackAt72` (post-SSTORE slack — derivable from threading once
WethReachable carries WethInvFr). -/
theorem bytecodePreservesInvariant_from_narrowed
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hΞ : ΞPreservesAccountAt C)
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (hNoWrap : WethCallNoWrapAt72 C)
    (hSlack : WethCallSlackAt72 C)
    (h40 : WethPC40CascadeFacts C) :
    ΞPreservesInvariantAtC C :=
  bytecodePreservesInvariant_from_account_and_cascades C hDeployed
    hΞ hAccInit h40 (weth_pc72_cascade C hNoWrap hSlack)

/-- **Final convenience entry: all three opaque cascade-fact assumptions
discharged as theorems.** Takes only the narrower structural facts
(`WethAccountAtC`, `WethCallNoWrapAt72`, `WethCallSlackAt72`,
`WethDepositCascadeStruct`, `WethDepositPreCredit`) and produces
`ΞPreservesInvariantAtC C`. -/
theorem bytecodePreservesInvariant_fully_narrowed
    (C : AccountAddress) (hDeployed : DeployedAtC C)
    (hΞ : ΞPreservesAccountAt C)
    (hAccInit : ∀ (σ : AccountMap .EVM) (I : ExecutionEnv .EVM),
        I.codeOwner = C → accountPresentAt σ C)
    (hNoWrap : WethCallNoWrapAt72 C)
    (hSlack : WethCallSlackAt72 C)
    (hDepositCascade : WethDepositCascadeStruct C)
    (hPreCredit : WethDepositPreCredit C) :
    ΞPreservesInvariantAtC C :=
  bytecodePreservesInvariant_from_narrowed C hDeployed hΞ hAccInit hNoWrap hSlack
    (weth_pc40_cascade C hDepositCascade hPreCredit)

end EvmSmith.Weth
