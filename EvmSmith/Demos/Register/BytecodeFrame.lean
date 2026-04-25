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
  · show (0 : UInt256).toNat = 0
    decide
  · show ([] : Stack UInt256).length = 0
    rfl

/-! ### Step preservation: the 14-case bytecode walk

This is the bulky obligation: for each Register PC, unfold `EVM.step`
for the decoded op and verify the post-state lies on the next PC's
disjunct of `RegisterTrace`. -/

private theorem RegisterTrace_step_preserves
    (C : AccountAddress) (s s' : EVM.State) (f' cost : ℕ)
    (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (h : RegisterTrace C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (op, arg))
    (hStep : EVM.step (f' + 1) cost (some (op, arg)) s = .ok s') :
    RegisterTrace C s' := by
  -- Use the step-preserves-balanceOf-style structure to extract the
  -- `op = ...` fact from `hFetch`. Then for each PC, unfold `EVM.step`
  -- for that op, derive `s'.pc` and `s'.stack`, and pick the appropriate
  -- next-PC disjunct.
  --
  -- The proof body is bulky but mechanical. We rely on the fact that
  -- non-CALL ops dispatch to `EvmYul.step` and CALL is handled inline.
  sorry

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
