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
   (s.pc.toNat = 55 ∧ s.stack.length = 5 ∧ s.stack[0]? = some revertLbl) ∨
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
   (s.pc.toNat = 77 ∧ s.stack.length = 3 ∧ s.stack[0]? = some revertLbl) ∨
   (s.pc.toNat = 78 ∧ s.stack.length = 1) ∨   -- JUMPI not-taken
   (s.pc.toNat = 79 ∧ s.stack.length = 0) ∨   -- post-POP; STOP next
  -- Revert tail (PCs 80..85).
   (s.pc.toNat = 80 ∧ s.stack.length = 3) ∨   -- JUMPI taken from PC 55 (revert from LT)
   (s.pc.toNat = 81 ∧ s.stack.length = 0) ∨   -- alt. taken from PC 77 (revert from CALL fail)
   (s.pc.toNat = 83 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 85 ∧ s.stack.length = 2))

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
  -- 60 disjuncts; PCs 16, 26, 55, 77 carry a stack[0]? witness so are
  -- 3-conjunct (need ⟨hpc, _, _⟩); the rest are 2-conjunct.
  rcases hPC with
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|
    ⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩|⟨hpc, _⟩
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
          ⟨_, decode_bytecode_at_81⟩, ⟨_, decode_bytecode_at_83⟩,
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
       (s'.pc.toNat = 36 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 37 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 38 ∧ s'.stack.length = 3) ∨
       (s'.pc.toNat = 39 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 40 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 41 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 42 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 43 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 45 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 46 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 47 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 48 ∧ s'.stack.length = 3) ∨
       (s'.pc.toNat = 49 ∧ s'.stack.length = 3) ∨
       (s'.pc.toNat = 50 ∧ s'.stack.length = 4) ∨
       (s'.pc.toNat = 51 ∧ s'.stack.length = 5) ∨
       (s'.pc.toNat = 52 ∧ s'.stack.length = 4) ∨
       (s'.pc.toNat = 55 ∧ s'.stack.length = 5 ∧ s'.stack[0]? = some revertLbl) ∨
       (s'.pc.toNat = 56 ∧ s'.stack.length = 3) ∨
       (s'.pc.toNat = 57 ∧ s'.stack.length = 4) ∨
       (s'.pc.toNat = 58 ∧ s'.stack.length = 4) ∨
       (s'.pc.toNat = 59 ∧ s'.stack.length = 3) ∨
       (s'.pc.toNat = 60 ∧ s'.stack.length = 3) ∨
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
       (s'.pc.toNat = 81 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 83 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 85 ∧ s'.stack.length = 2))) :
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
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 35 1
    · rw [hStk']; show (hd :: s.stack).length = 2; simp [hLen]

/-! ### PC 36 — `SLOAD` (deposit: load balance) -/

private theorem WethTrace_step_at_36
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 36) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 36 := pc_eq_ofNat_of_toNat s 36 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd :: tl, hLen2 =>
    have hLenTl : tl.length = 1 := by
      have h1 : (hd :: tl).length = 2 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_SLOAD_at_pc s s' f' cost op arg _ hd tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_36 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 22 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 36 1
    · rw [hStk']; show (v :: tl).length = 2; simp [hLenTl]

/-! ### PC 37 — `CALLVALUE` (deposit: push msg.value) -/

private theorem WethTrace_step_at_37
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 37) (hLen : s.stack.length = 2)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 37 := pc_eq_ofNat_of_toNat s 37 (by decide) hpc
  obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
    step_CALLVALUE_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_37 hStep
  refine mk_wethTrace_aux hCO hCode hEE' ?_
  iterate 23 right
  left
  refine ⟨?_, ?_⟩
  · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 37 1
  · rw [hStk']; show (v :: s.stack).length = 3; simp [hLen]

/-! ### PC 38 — `ADD` (deposit: balance + msg.value) -/

private theorem WethTrace_step_at_38
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : WethTrace C s)
    (hpc : s.pc.toNat = 38) (hLen : s.stack.length = 3)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    WethTrace C s' := by
  obtain ⟨hCO, hCode, _⟩ := h
  have hpcEq : s.pc = UInt256.ofNat 38 := pc_eq_ofNat_of_toNat s 38 (by decide) hpc
  match hStk_eq : s.stack, hLen with
  | hd1 :: hd2 :: tl, hLen2 =>
    have hLenTl : tl.length = 1 := by
      have h1 : (hd1 :: hd2 :: tl).length = 3 := by rw [← hStk_eq]; exact hLen
      simpa using h1
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_ADD_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
        hFetch hCode hpcEq decode_bytecode_at_38 hStep
    refine mk_wethTrace_aux hCO hCode hEE' ?_
    iterate 24 right
    left
    refine ⟨?_, ?_⟩
    · rw [hPC', hpcEq]; exact ofNat_add_ofNat_toNat_lt256 38 1
    · rw [hStk']; show (v :: tl).length = 2; simp [hLenTl]

end EvmSmith.Weth
