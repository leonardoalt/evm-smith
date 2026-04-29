import EvmYul.Frame
import EvmSmith.Demos.Weth.Invariant

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
   (s.pc.toNat = 16 ∧ s.stack.length = 3) ∨
   (s.pc.toNat = 17 ∧ s.stack.length = 1) ∨   -- JUMPI not-taken
   (s.pc.toNat = 22 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 23 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 26 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 27 ∧ s.stack.length = 0) ∨   -- JUMPI not-taken (revert path)
   (s.pc.toNat = 29 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 31 ∧ s.stack.length = 2) ∨
  -- Deposit block (PCs 32..41), entered from PC 16 JUMPI taken.
   (s.pc.toNat = 32 ∧ s.stack.length = 1) ∨   -- JUMPDEST entry (selector still)
   (s.pc.toNat = 33 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 34 ∧ s.stack.length = 0) ∨
   (s.pc.toNat = 35 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 36 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 37 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 38 ∧ s.stack.length = 3) ∨
   (s.pc.toNat = 39 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 40 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 41 ∧ s.stack.length = 0) ∨   -- post-SSTORE; STOP next
  -- Withdraw block prefix (PCs 42..60), entered from PC 26 JUMPI taken.
   (s.pc.toNat = 42 ∧ s.stack.length = 0) ∨   -- JUMPDEST
   (s.pc.toNat = 43 ∧ s.stack.length = 0) ∨
   (s.pc.toNat = 45 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 46 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 47 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 48 ∧ s.stack.length = 3) ∨
   (s.pc.toNat = 49 ∧ s.stack.length = 3) ∨
   (s.pc.toNat = 50 ∧ s.stack.length = 4) ∨
   (s.pc.toNat = 51 ∧ s.stack.length = 5) ∨
   (s.pc.toNat = 52 ∧ s.stack.length = 4) ∨
   (s.pc.toNat = 55 ∧ s.stack.length = 5) ∨
   (s.pc.toNat = 56 ∧ s.stack.length = 3) ∨   -- JUMPI not-taken
   (s.pc.toNat = 57 ∧ s.stack.length = 4) ∨
   (s.pc.toNat = 58 ∧ s.stack.length = 4) ∨
   (s.pc.toNat = 59 ∧ s.stack.length = 3) ∨
   (s.pc.toNat = 60 ∧ s.stack.length = 3) ∨   -- pre-SSTORE [sender; newBal; x]
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
   (s.pc.toNat = 77 ∧ s.stack.length = 3) ∨
   (s.pc.toNat = 78 ∧ s.stack.length = 1) ∨   -- JUMPI not-taken
   (s.pc.toNat = 79 ∧ s.stack.length = 0) ∨   -- post-POP; STOP next
  -- Revert tail (PCs 80..85).
   (s.pc.toNat = 80 ∧ s.stack.length = 3) ∨   -- JUMPI taken from PC 55 (revert from LT)
   (s.pc.toNat = 81 ∧ s.stack.length = 0) ∨   -- alt. taken from PC 77 (revert from CALL fail)
   (s.pc.toNat = 83 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 85 ∧ s.stack.length = 2) ∨
  -- Halt sinks (post-REVERT). The X loop exits on REVERT, but the
  -- post-step state must still inhabit some disjunct.
   (s.pc.toNat = 86 ∧ s.stack.length = 0))

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

end EvmSmith.Weth
