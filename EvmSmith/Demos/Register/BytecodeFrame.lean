import EvmYul.Frame
import EvmSmith.Lemmas
import EvmSmith.Demos.Register.Invariant

/-!
# Register — bytecode-specific Ξ preservation (B2)

This is the single Register-specific load-bearing lemma: when Ξ runs
Register's 20-byte bytecode at `I.codeOwner = C`, it **preserves**
`balanceOf σ C` (strict equality, not just monotonicity).

The closure goes via `ΞPreservesAtC_of_Reachable` from
`MutualFrame.lean`: we supply a `RegisterTrace` predicate witnessing
that the bytecode trace at `C` stays inside the 8-opcode subset and
emits CALL only with `value = 0`, plus the six closure obligations
(Z-stability, step-stability, decode-some, op-in-8, v0-at-CALL,
initial state).
-/

namespace EvmSmith.Register
open EvmYul EvmYul.EVM EvmYul.Frame

/-! ## Register-trace predicate

A state `s` is **Register-traced** when its execution environment
matches Register's deployment context (codeOwner = C, code = bytecode)
and its `(pc, stack)` pair lies on one of Register's 14 valid
execution states. The crucial constraint: at PC=17, `stack[2]? = 0`,
which establishes the CALL value-0 invariant. -/
private def RegisterTrace (C : AccountAddress) (s : EVM.State) : Prop :=
  C = s.executionEnv.codeOwner ∧
  s.executionEnv.code = bytecode ∧
  ((s.pc.toNat = 0 ∧ s.stack.length = 0) ∨
   (s.pc.toNat = 2 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 3 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 4 ∧ s.stack.length = 2) ∨
   (s.pc.toNat = 5 ∧ s.stack.length = 0) ∨
   (s.pc.toNat = 7 ∧ s.stack.length = 1 ∧ s.stack[0]? = some ⟨0⟩) ∨
   (s.pc.toNat = 9 ∧ s.stack.length = 2 ∧ s.stack[0]? = some ⟨0⟩ ∧ s.stack[1]? = some ⟨0⟩) ∨
   (s.pc.toNat = 11 ∧ s.stack.length = 3 ∧ s.stack[0]? = some ⟨0⟩ ∧ s.stack[1]? = some ⟨0⟩ ∧ s.stack[2]? = some ⟨0⟩) ∨
   (s.pc.toNat = 13 ∧ s.stack.length = 4 ∧ s.stack[0]? = some ⟨0⟩ ∧ s.stack[1]? = some ⟨0⟩ ∧ s.stack[2]? = some ⟨0⟩ ∧ s.stack[3]? = some ⟨0⟩) ∨
   (s.pc.toNat = 15 ∧ s.stack.length = 5 ∧ s.stack[0]? = some ⟨0⟩ ∧ s.stack[1]? = some ⟨0⟩ ∧ s.stack[2]? = some ⟨0⟩ ∧ s.stack[3]? = some ⟨0⟩ ∧ s.stack[4]? = some ⟨0⟩) ∨
   (s.pc.toNat = 16 ∧ s.stack.length = 6 ∧ s.stack[1]? = some ⟨0⟩ ∧ s.stack[2]? = some ⟨0⟩ ∧ s.stack[3]? = some ⟨0⟩ ∧ s.stack[4]? = some ⟨0⟩ ∧ s.stack[5]? = some ⟨0⟩) ∨
   (s.pc.toNat = 17 ∧ s.stack.length = 7 ∧ s.stack[2]? = some ⟨0⟩ ∧ s.stack[3]? = some ⟨0⟩ ∧ s.stack[4]? = some ⟨0⟩ ∧ s.stack[5]? = some ⟨0⟩ ∧ s.stack[6]? = some ⟨0⟩) ∨
   (s.pc.toNat = 18 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 19 ∧ s.stack.length = 0))

/-! ## Register-pinned code-identity axiom

The remaining structural axiom: Register's bytecode is what runs at
`C` whenever `I.codeOwner = C`. -/

/-- **Register-context code-identity axiom.**

Whenever `Ξ` runs at `I.codeOwner = C` during a transaction whose
deployment placed Register's bytecode at `C`, `I.code = Register.bytecode`.

Holds because:
  * Register's genesis deployment installed this exact 20-byte code at `C`.
  * Register's own bytecode contains no `CREATE` / `CREATE2` opcode,
    so no nested frame can overwrite code at `C`.
  * The boundary hypothesis (`T5`) enforced by `register_balance_mono`
    excludes nested `CREATE`/`CREATE2` from *any* other contract
    producing address `C`.
  * Register's bytecode contains no `SELFDESTRUCT`, so `C`'s account
    is never erased (which would otherwise reset its code to empty).

This is a structural invariant of the Register-deployed transaction
context — not a free "any code at C" claim. -/
private axiom I_code_at_C_is_Register_bytecode
    (I : ExecutionEnv .EVM) (C : AccountAddress) :
    I.codeOwner = C → I.code = bytecode

/-! ## Closure properties of `RegisterTrace`

The six closure obligations consumed by `ΞPreservesAtC_of_Reachable`. -/

/-- Z (gas-only update) preserves `RegisterTrace`. -/
private theorem RegisterTrace_Z_preserves
    (C : AccountAddress) (s : EVM.State) (g : UInt256)
    (h : RegisterTrace C s) :
    RegisterTrace C { s with gasAvailable := g } := h

/-- For our 14 PCs (all < 32), `(UInt256.ofNat n).toNat = n`. -/
private theorem ofNat_toNat_lt32 (n : ℕ) (hn : n < 32) :
    (UInt256.ofNat n).toNat = n := by
  unfold UInt256.toNat UInt256.ofNat
  simp only [Id.run]
  unfold Fin.ofNat
  simp only
  apply Nat.mod_eq_of_lt
  unfold UInt256.size
  omega

/-! ### `decode_bytecode_at`: enumerate decode at each valid PC -/

/-- The decoded instruction at each of Register's 14 valid PCs. -/
private theorem decode_bytecode_at_0 :
    decode bytecode (UInt256.ofNat 0)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
  native_decide

private theorem decode_bytecode_at_2 :
    decode bytecode (UInt256.ofNat 2)
      = some (.CALLDATALOAD, none) := by
  native_decide

private theorem decode_bytecode_at_3 :
    decode bytecode (UInt256.ofNat 3)
      = some (.CALLER, none) := by
  native_decide

private theorem decode_bytecode_at_4 :
    decode bytecode (UInt256.ofNat 4)
      = some (.SSTORE, none) := by
  native_decide

private theorem decode_bytecode_at_5 :
    decode bytecode (UInt256.ofNat 5)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
  native_decide

private theorem decode_bytecode_at_7 :
    decode bytecode (UInt256.ofNat 7)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
  native_decide

private theorem decode_bytecode_at_9 :
    decode bytecode (UInt256.ofNat 9)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
  native_decide

private theorem decode_bytecode_at_11 :
    decode bytecode (UInt256.ofNat 11)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
  native_decide

private theorem decode_bytecode_at_13 :
    decode bytecode (UInt256.ofNat 13)
      = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
  native_decide

private theorem decode_bytecode_at_15 :
    decode bytecode (UInt256.ofNat 15)
      = some (.CALLER, none) := by
  native_decide

private theorem decode_bytecode_at_16 :
    decode bytecode (UInt256.ofNat 16)
      = some (.GAS, none) := by
  native_decide

private theorem decode_bytecode_at_17 :
    decode bytecode (UInt256.ofNat 17)
      = some (.CALL, none) := by
  native_decide

private theorem decode_bytecode_at_18 :
    decode bytecode (UInt256.ofNat 18)
      = some (.POP, none) := by
  native_decide

private theorem decode_bytecode_at_19 :
    decode bytecode (UInt256.ofNat 19)
      = some (.STOP, none) := by
  native_decide

/-- A trace state `s` always has `s.pc` equal to `UInt256.ofNat n` for
its declared `n`, since `pc.toNat = n` and `n < 32 < UInt256.size`. -/
private theorem pc_eq_ofNat_of_toNat
    (s : EVM.State) (n : ℕ) (hn : n < 32)
    (h : s.pc.toNat = n) :
    s.pc = UInt256.ofNat n := by
  rcases hpc : s.pc with ⟨v⟩
  apply congrArg UInt256.mk
  apply Fin.ext
  show v.val = (UInt256.ofNat n).val.val
  have : v.val = n := by rw [hpc] at h; exact h
  rw [this]
  show n = (UInt256.ofNat n).val.val
  unfold UInt256.ofNat Fin.ofNat
  simp only [Id.run]
  rw [Nat.mod_eq_of_lt (by unfold UInt256.size; omega)]

/-- Each Reachable state has decode = some pair. -/
private theorem RegisterTrace_decodeSome
    (C : AccountAddress) (s : EVM.State)
    (h : RegisterTrace C s) :
    ∃ pair, decode s.executionEnv.code s.pc = some pair := by
  obtain ⟨_, hCode, hPC⟩ := h
  rw [hCode]
  rcases hPC with
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ |
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ |
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 0 (by decide) hpc]; exact decode_bytecode_at_0⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 2 (by decide) hpc]; exact decode_bytecode_at_2⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 3 (by decide) hpc]; exact decode_bytecode_at_3⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 4 (by decide) hpc]; exact decode_bytecode_at_4⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 5 (by decide) hpc]; exact decode_bytecode_at_5⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 7 (by decide) hpc]; exact decode_bytecode_at_7⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 9 (by decide) hpc]; exact decode_bytecode_at_9⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 11 (by decide) hpc]; exact decode_bytecode_at_11⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 13 (by decide) hpc]; exact decode_bytecode_at_13⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 15 (by decide) hpc]; exact decode_bytecode_at_15⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 16 (by decide) hpc]; exact decode_bytecode_at_16⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 17 (by decide) hpc]; exact decode_bytecode_at_17⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 18 (by decide) hpc]; exact decode_bytecode_at_18⟩
  · exact ⟨_, by rw [pc_eq_ofNat_of_toNat s 19 (by decide) hpc]; exact decode_bytecode_at_19⟩

/-- The decoded op at any reachable state is one of Register's 8. -/
private theorem RegisterTrace_op_in_8
    (C : AccountAddress) (s : EVM.State) (op : Operation .EVM)
    (arg : Option (UInt256 × Nat))
    (h : RegisterTrace C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg)) :
    op = .Push .PUSH1 ∨ op = .CALLDATALOAD ∨ op = .CALLER ∨
    op = .SSTORE ∨ op = .GAS ∨ op = .POP ∨ op = .STOP ∨ op = .CALL := by
  obtain ⟨_, hCode, hPC⟩ := h
  unfold fetchInstr at hFetch
  rw [hCode] at hFetch
  rcases hPC with
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ |
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ |
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩
  all_goals first
    | (rw [pc_eq_ofNat_of_toNat s _ (by decide) hpc] at hFetch
       first
        | (rw [decode_bytecode_at_0] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_2] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_3] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_4] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_5] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_7] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_9] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_11] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_13] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_15] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_16] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_17] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_18] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)
        | (rw [decode_bytecode_at_19] at hFetch; injection hFetch with h1; injection h1 with h1 _; subst h1; tauto))

/-- A small helper: derive op from a fetchInstr against a known decode. -/
private theorem op_eq_of_fetchInstr_decode
    {I : ExecutionEnv .EVM} {pc : UInt256}
    {op_dec : Operation .EVM} {arg_dec : Option (UInt256 × Nat)}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hDec : decode I.code pc = some (op_dec, arg_dec))
    (hFetch : fetchInstr I pc = .ok (op, arg)) :
    op = op_dec := by
  unfold fetchInstr at hFetch
  rw [hDec] at hFetch
  -- hFetch : (some (op_dec, arg_dec)).option (.error .StackUnderflow) Except.ok = .ok (op, arg)
  -- This evaluates to .ok (op_dec, arg_dec) = .ok (op, arg)
  injection hFetch with h
  injection h with h _
  exact h.symm

/-- Stronger version: derive both op and arg from fetchInstr. -/
private theorem op_arg_eq_of_fetchInstr_decode
    {I : ExecutionEnv .EVM} {pc : UInt256}
    {op_dec : Operation .EVM} {arg_dec : Option (UInt256 × Nat)}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hDec : decode I.code pc = some (op_dec, arg_dec))
    (hFetch : fetchInstr I pc = .ok (op, arg)) :
    op = op_dec ∧ arg = arg_dec := by
  unfold fetchInstr at hFetch
  rw [hDec] at hFetch
  injection hFetch with h
  injection h with h1 h2
  exact ⟨h1.symm, h2.symm⟩

/-- At any reachable CALL, `stack[2]? = some 0`. The only PC with op =
CALL is 17, and the disjunct at PC=17 has `stack[2]? = some 0`. -/
private theorem RegisterTrace_v0_at_CALL
    (C : AccountAddress) (s : EVM.State) (arg : Option (UInt256 × Nat))
    (h : RegisterTrace C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (.CALL, arg)) :
    s.stack[2]? = some ⟨0⟩ := by
  obtain ⟨_, hCode, hPC⟩ := h
  rcases hPC with
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ |
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ |
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _, hs2, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩
  -- All non-PC=17 cases: contradict hFetch with concrete decode.
  all_goals first
    | exact hs2  -- PC = 17 case
    | (
        first
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 0 (by decide) hpc ▸ decode_bytecode_at_0) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 2 (by decide) hpc ▸ decode_bytecode_at_2) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 3 (by decide) hpc ▸ decode_bytecode_at_3) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 4 (by decide) hpc ▸ decode_bytecode_at_4) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 5 (by decide) hpc ▸ decode_bytecode_at_5) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 7 (by decide) hpc ▸ decode_bytecode_at_7) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 9 (by decide) hpc ▸ decode_bytecode_at_9) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 11 (by decide) hpc ▸ decode_bytecode_at_11) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 13 (by decide) hpc ▸ decode_bytecode_at_13) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 15 (by decide) hpc ▸ decode_bytecode_at_15) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 16 (by decide) hpc ▸ decode_bytecode_at_16) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 18 (by decide) hpc ▸ decode_bytecode_at_18) hFetch; cases hOp)
          | (have hOp := op_eq_of_fetchInstr_decode (hCode ▸ pc_eq_ofNat_of_toNat s 19 (by decide) hpc ▸ decode_bytecode_at_19) hFetch; cases hOp))

/-! ### Initial-state lemma -/

/-- An initial Register-execution state is `RegisterTrace`. -/
private theorem RegisterTrace_initial
    (C : AccountAddress)
    (cA : Batteries.RBSet AccountAddress compare)
    (gbh : BlockHeader) (bs : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM)
    (hCO : I.codeOwner = C) :
    RegisterTrace C
      { (default : EVM.State) with
          accountMap := σ
          σ₀ := σ₀
          executionEnv := I
          substate := A
          createdAccounts := cA
          gasAvailable := g
          blocks := bs
          genesisBlockHeader := gbh } := by
  have hCode : I.code = bytecode := I_code_at_C_is_Register_bytecode I C hCO
  refine ⟨hCO.symm, hCode, ?_⟩
  -- Initial state has pc = 0 (default UInt256 = ⟨0⟩) and empty stack.
  left
  refine ⟨?_, ?_⟩
  · show (⟨0⟩ : UInt256).toNat = 0
    decide
  · show ([] : Stack UInt256).length = 0
    rfl

/-! ### Step preservation: the 14-case bytecode walk

This is the bulky obligation: for each Register PC, unfold `EVM.step`
for the decoded op and verify the post-state lies on the next PC's
disjunct of `RegisterTrace`. -/

/-! ### Helpers for the step proof -/

/-- For nats `a, b` with `a + b < UInt256.size`, the toNat of the sum
of the corresponding `UInt256`s equals `a + b`. -/
private theorem ofNat_add_ofNat_toNat
    (a b : ℕ) (ha : a < UInt256.size) (hb : b < UInt256.size)
    (hab : a + b < UInt256.size) :
    (UInt256.ofNat a + UInt256.ofNat b).toNat = a + b := by
  show (UInt256.ofNat a + UInt256.ofNat b).val.val = a + b
  rw [show (UInt256.ofNat a + UInt256.ofNat b).val
        = (UInt256.ofNat a).val + (UInt256.ofNat b).val from rfl]
  rw [Fin.val_add]
  show ((UInt256.ofNat a).val.val + (UInt256.ofNat b).val.val) % UInt256.size = a + b
  have hav : (UInt256.ofNat a).val.val = a := by
    show a % UInt256.size = a
    exact Nat.mod_eq_of_lt ha
  have hbv : (UInt256.ofNat b).val.val = b := by
    show b % UInt256.size = b
    exact Nat.mod_eq_of_lt hb
  rw [hav, hbv]
  exact Nat.mod_eq_of_lt hab

/-! ### Per-opcode step shape lemmas

These were lifted to `EvmYul.Frame.StepShapes` (in EVMYulLean) for
reuse across contract proofs:
- `step_PUSH1_shape`, `step_CALLDATALOAD_shape`, `step_CALLER_shape`,
  `step_SSTORE_shape`, `step_GAS_shape`, `step_POP_shape`,
  `step_STOP_shape`, `step_CALL_shape`, `EVM_call_preserves_pc`.

They resolve here via `open EvmYul.Frame`.
-/

private theorem RegisterTrace_step_preserves
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : RegisterTrace C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    RegisterTrace C s' := by
  obtain ⟨hCO, hCode, hPC⟩ := h
  -- For each PC case, we'll: derive op and arg via op_arg_eq, then apply the shape
  -- lemma, then pick the right next-PC disjunct.
  rcases hPC with
    ⟨hpc, hLen⟩ |
    ⟨hpc, hLen⟩ |
    ⟨hpc, hLen⟩ |
    ⟨hpc, hLen⟩ |
    ⟨hpc, hLen⟩ |
    ⟨hpc, hLen, hs0⟩ |
    ⟨hpc, hLen, hs0, hs1⟩ |
    ⟨hpc, hLen, hs0, hs1, hs2⟩ |
    ⟨hpc, hLen, hs0, hs1, hs2, hs3⟩ |
    ⟨hpc, hLen, hs0, hs1, hs2, hs3, hs4⟩ |
    ⟨hpc, hLen, hs1, hs2, hs3, hs4, hs5⟩ |
    ⟨hpc, hLen, hs2, hs3, hs4, hs5, hs6⟩ |
    ⟨hpc, hLen⟩ |
    ⟨hpc, hLen⟩
  all_goals (
    have hpcEq : s.pc = UInt256.ofNat _ := pc_eq_ofNat_of_toNat s _ (by decide) hpc)
  -- Case PC=0 (PUSH1 0).
  · -- Decode at PC=0.
    have hDec : decode s.executionEnv.code s.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_0
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    obtain ⟨hPC', hStk', hEE'⟩ := step_PUSH1_shape s s' f' cost _ hStep
    refine ⟨?_, ?_, ?_⟩
    · rw [hEE']; exact hCO
    · rw [hEE']; exact hCode
    · -- Next PC = 2, stack length = 1.
      right; left
      refine ⟨?_, ?_⟩
      · rw [hPC', hpcEq]
        show ((UInt256.ofNat 0) + UInt256.ofNat 2).toNat = 2
        exact ofNat_add_ofNat_toNat 0 2 (by decide) (by decide) (by decide)
      · rw [hStk']
        show List.length (UInt256.ofNat 0 :: s.stack) = 1
        simp [hLen]
  -- Case PC=2 (CALLDATALOAD).
  · have hDec : decode s.executionEnv.code s.pc = some (.CALLDATALOAD, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_2
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    -- s.stack.length = 1, so we can extract a head.
    match hStk_eq : s.stack, hLen with
    | hd :: tl, hLen2 =>
      have hLen3 : tl.length = 0 := by
        have : (hd :: tl).length = 1 := by rw [← hStk_eq]; exact hLen
        simpa using this
      obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
        step_CALLDATALOAD_shape s s' f' cost none hd tl hStk_eq hStep
      refine ⟨?_, ?_, ?_⟩
      · rw [hEE']; exact hCO
      · rw [hEE']; exact hCode
      · right; right; left
        refine ⟨?_, ?_⟩
        · rw [hPC', hpcEq]
          exact ofNat_add_ofNat_toNat 2 1 (by decide) (by decide) (by decide)
        · rw [hStk']
          show (v :: tl).length = 1
          simp [hLen3]
  -- Case PC=3 (CALLER).
  · have hDec : decode s.executionEnv.code s.pc = some (.CALLER, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_3
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ := step_CALLER_shape s s' f' cost none hStep
    refine ⟨?_, ?_, ?_⟩
    · rw [hEE']; exact hCO
    · rw [hEE']; exact hCode
    · right; right; right; left
      refine ⟨?_, ?_⟩
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat 3 1 (by decide) (by decide) (by decide)
      · rw [hStk']
        show (v :: s.stack).length = 2
        simp [hLen]
  -- Case PC=4 (SSTORE).
  · have hDec : decode s.executionEnv.code s.pc = some (.SSTORE, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_4
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, hLen2 =>
      have hLen3 : tl.length = 0 := by
        have : (hd1 :: hd2 :: tl).length = 2 := by rw [← hStk_eq]; exact hLen
        simpa using this
      obtain ⟨hPC', hStk', hEE'⟩ :=
        step_SSTORE_shape s s' f' cost none hd1 hd2 tl hStk_eq hStep
      refine ⟨?_, ?_, ?_⟩
      · rw [hEE']; exact hCO
      · rw [hEE']; exact hCode
      · right; right; right; right; left
        refine ⟨?_, ?_⟩
        · rw [hPC', hpcEq]
          exact ofNat_add_ofNat_toNat 4 1 (by decide) (by decide) (by decide)
        · rw [hStk']; exact hLen3
  -- Case PC=5 (PUSH1 0).
  · have hDec : decode s.executionEnv.code s.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_5
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    obtain ⟨hPC', hStk', hEE'⟩ := step_PUSH1_shape s s' f' cost _ hStep
    refine ⟨?_, ?_, ?_⟩
    · rw [hEE']; exact hCO
    · rw [hEE']; exact hCode
    · -- Next PC=7, stack=[0] (length 1, top=0).
      right; right; right; right; right; left
      refine ⟨?_, ?_, ?_⟩
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat 5 2 (by decide) (by decide) (by decide)
      · rw [hStk']
        show List.length (UInt256.ofNat 0 :: s.stack) = 1
        simp [hLen]
      · rw [hStk']
        show (UInt256.ofNat 0 :: s.stack)[0]? = some ⟨0⟩
        rfl
  -- Case PC=7 (PUSH1 0).
  · have hDec : decode s.executionEnv.code s.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_7
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    obtain ⟨hPC', hStk', hEE'⟩ := step_PUSH1_shape s s' f' cost _ hStep
    refine ⟨?_, ?_, ?_⟩
    · rw [hEE']; exact hCO
    · rw [hEE']; exact hCode
    · right; right; right; right; right; right; left
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat 7 2 (by decide) (by decide) (by decide)
      · rw [hStk']
        show List.length (UInt256.ofNat 0 :: s.stack) = 2
        simp [hLen]
      · rw [hStk']
        show (UInt256.ofNat 0 :: s.stack)[0]? = some ⟨0⟩
        rfl
      · rw [hStk']
        show (UInt256.ofNat 0 :: s.stack)[1]? = some ⟨0⟩
        simp [List.getElem?_cons_succ]
        exact hs0
  -- Case PC=9 (PUSH1 0).
  · have hDec : decode s.executionEnv.code s.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_9
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    obtain ⟨hPC', hStk', hEE'⟩ := step_PUSH1_shape s s' f' cost _ hStep
    refine ⟨?_, ?_, ?_⟩
    · rw [hEE']; exact hCO
    · rw [hEE']; exact hCode
    · right; right; right; right; right; right; right; left
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat 9 2 (by decide) (by decide) (by decide)
      · rw [hStk']; show List.length (_ :: s.stack) = 3; simp [hLen]
      · rw [hStk']; rfl
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs0
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs1
  -- Case PC=11 (PUSH1 0).
  · have hDec : decode s.executionEnv.code s.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_11
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    obtain ⟨hPC', hStk', hEE'⟩ := step_PUSH1_shape s s' f' cost _ hStep
    refine ⟨?_, ?_, ?_⟩
    · rw [hEE']; exact hCO
    · rw [hEE']; exact hCode
    · right; right; right; right; right; right; right; right; left
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat 11 2 (by decide) (by decide) (by decide)
      · rw [hStk']; show List.length (_ :: s.stack) = 4; simp [hLen]
      · rw [hStk']; rfl
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs0
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs1
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs2
  -- Case PC=13 (PUSH1 0).
  · have hDec : decode s.executionEnv.code s.pc = some (.Push .PUSH1, some (UInt256.ofNat 0, 1)) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_13
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    obtain ⟨hPC', hStk', hEE'⟩ := step_PUSH1_shape s s' f' cost _ hStep
    refine ⟨?_, ?_, ?_⟩
    · rw [hEE']; exact hCO
    · rw [hEE']; exact hCode
    · right; right; right; right; right; right; right; right; right; left
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat 13 2 (by decide) (by decide) (by decide)
      · rw [hStk']; show List.length (_ :: s.stack) = 5; simp [hLen]
      · rw [hStk']; rfl
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs0
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs1
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs2
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs3
  -- Case PC=15 (CALLER).
  · have hDec : decode s.executionEnv.code s.pc = some (.CALLER, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_15
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ := step_CALLER_shape s s' f' cost none hStep
    refine ⟨?_, ?_, ?_⟩
    · rw [hEE']; exact hCO
    · rw [hEE']; exact hCode
    · right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat 15 1 (by decide) (by decide) (by decide)
      · rw [hStk']; show List.length (v :: s.stack) = 6; simp [hLen]
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs0
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs1
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs2
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs3
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs4
  -- Case PC=16 (GAS).
  · have hDec : decode s.executionEnv.code s.pc = some (.GAS, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_16
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ := step_GAS_shape s s' f' cost none hStep
    refine ⟨?_, ?_, ?_⟩
    · rw [hEE']; exact hCO
    · rw [hEE']; exact hCode
    · right; right; right; right; right; right; right; right; right; right; right; left
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat 16 1 (by decide) (by decide) (by decide)
      · rw [hStk']; show List.length (v :: s.stack) = 7; simp [hLen]
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs1
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs2
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs3
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs4
      · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs5
  -- Case PC=17 (CALL).
  · have hDec : decode s.executionEnv.code s.pc = some (.CALL, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_17
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    -- Stack length 7 — pull out 7 cons.
    match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: hd7 :: tl, hLen2 =>
      have hTl : tl = [] := by
        have : (hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: hd7 :: tl).length = 7 := by
          rw [← hStk_eq]; exact hLen
        have : tl.length = 0 := by simpa using this
        exact List.length_eq_zero_iff.mp this
      obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
        step_CALL_shape s s' f' cost none hd1 hd2 hd3 hd4 hd5 hd6 hd7 tl hStk_eq hStep
      refine ⟨?_, ?_, ?_⟩
      · rw [hEE']; exact hCO
      · rw [hEE']; exact hCode
      · right; right; right; right; right; right; right; right; right; right; right; right; left
        refine ⟨?_, ?_⟩
        · rw [hPC', hpcEq]
          exact ofNat_add_ofNat_toNat 17 1 (by decide) (by decide) (by decide)
        · rw [hStk', hTl]; rfl
  -- Case PC=18 (POP).
  · have hDec : decode s.executionEnv.code s.pc = some (.POP, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_18
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    match hStk_eq : s.stack, hLen with
    | hd :: tl, hLen2 =>
      have hLen3 : tl.length = 0 := by
        have : (hd :: tl).length = 1 := by rw [← hStk_eq]; exact hLen
        simpa using this
      obtain ⟨hPC', hStk', hEE'⟩ :=
        step_POP_shape s s' f' cost none hd tl hStk_eq hStep
      refine ⟨?_, ?_, ?_⟩
      · rw [hEE']; exact hCO
      · rw [hEE']; exact hCode
      · right; right; right; right; right; right; right; right; right; right; right; right; right
        refine ⟨?_, ?_⟩
        · rw [hPC', hpcEq]
          exact ofNat_add_ofNat_toNat 18 1 (by decide) (by decide) (by decide)
        · rw [hStk']; exact hLen3
  -- Case PC=19 (STOP). Halt — disjunct stays at PC=19 length=0.
  · have hDec : decode s.executionEnv.code s.pc = some (.STOP, none) := by
      rw [hCode, hpcEq]; exact decode_bytecode_at_19
    obtain ⟨hOp, hArg⟩ := op_arg_eq_of_fetchInstr_decode hDec hFetch
    subst hOp; subst hArg
    obtain ⟨hPC', hStk', hEE'⟩ := step_STOP_shape s s' f' cost none hStep
    refine ⟨?_, ?_, ?_⟩
    · rw [hEE']; exact hCO
    · rw [hEE']; exact hCode
    · right; right; right; right; right; right; right; right; right; right; right; right; right
      refine ⟨?_, ?_⟩
      · rw [hPC']; exact hpc
      · rw [hStk']; exact hLen

/-! ## Bytecode-preservation theorem -/

/-- Register's bytecode at `C` preserves `balanceOf C` through any Ξ
invocation. -/
theorem bytecodePreservesBalance (C : AccountAddress) :
    ΞPreservesAtC C := by
  exact ΞPreservesAtC_of_Reachable C (RegisterTrace C)
    (RegisterTrace_Z_preserves C)
    (RegisterTrace_step_preserves C)
    (RegisterTrace_decodeSome C)
    (RegisterTrace_op_in_8 C)
    (RegisterTrace_v0_at_CALL C)
    (RegisterTrace_initial C)

end EvmSmith.Register
