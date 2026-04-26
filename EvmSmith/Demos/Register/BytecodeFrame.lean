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

/-! ## Register-pinned code-identity hypothesis

The remaining structural claim: Register's bytecode is what runs at
`C` whenever `I.codeOwner = C`. Stated as a `Prop` predicate consumers
supply as a hypothesis (rather than a global axiom), because as a
universally-quantified-over-`I` claim it is provably false in
isolation — it only holds in the deployment context where `C` was
seeded with Register's bytecode and nothing in the call tree can
overwrite it. -/

/-- **Register-context code-identity hypothesis.**

`DeployedAtC C` asserts that any `ExecutionEnv` with `codeOwner = C`
runs Register's bytecode. Real-world tx contexts satisfy this when:

  * Register's genesis deployment installed this exact 20-byte code at `C`.
  * Register's own bytecode contains no `CREATE` / `CREATE2` opcode,
    so no nested frame can overwrite code at `C`.
  * The boundary hypothesis (`T5`) enforced by `register_balance_mono`
    excludes nested `CREATE`/`CREATE2` from *any* other contract
    producing address `C`.
  * Register's bytecode contains no `SELFDESTRUCT`, so `C`'s account
    is never erased (which would otherwise reset its code to empty).

In Lean, the predicate is logically too strong to be derivable from
`StateWF` + the existing protocol axioms alone — the call-graph
structure that pins it is a property of the tx execution, not the
input state. So `register_balance_mono` takes it as a hypothesis,
mirroring `RegSDExclusion` / `RegDeadAtσP`. -/
def DeployedAtC (C : AccountAddress) : Prop :=
  ∀ I : ExecutionEnv .EVM, I.codeOwner = C → I.code = bytecode

/-! ## Closure properties of `RegisterTrace`

The six closure obligations consumed by `ΞPreservesAtC_of_Reachable`. -/

/-- Z (gas-only update) preserves `RegisterTrace`. -/
private theorem RegisterTrace_Z_preserves
    (C : AccountAddress) (s : EVM.State) (g : UInt256)
    (h : RegisterTrace C s) :
    RegisterTrace C { s with gasAvailable := g } := h

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
its declared `n`, since `pc.toNat = n` and `n < 32 < UInt256.size`.
Thin wrapper over `EvmYul.Frame.pc_eq_ofNat_of_toNat` with the
specialized `n < 32` hypothesis. -/
private theorem pc_eq_ofNat_of_toNat
    (s : EVM.State) (n : ℕ) (hn : n < 32)
    (h : s.pc.toNat = n) :
    s.pc = UInt256.ofNat n :=
  EvmYul.Frame.pc_eq_ofNat_of_toNat s n (by unfold UInt256.size; omega) h

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
  all_goals (rw [pc_eq_ofNat_of_toNat s _ (by decide) hpc])
  exacts [⟨_, decode_bytecode_at_0⟩, ⟨_, decode_bytecode_at_2⟩,
          ⟨_, decode_bytecode_at_3⟩, ⟨_, decode_bytecode_at_4⟩,
          ⟨_, decode_bytecode_at_5⟩, ⟨_, decode_bytecode_at_7⟩,
          ⟨_, decode_bytecode_at_9⟩, ⟨_, decode_bytecode_at_11⟩,
          ⟨_, decode_bytecode_at_13⟩, ⟨_, decode_bytecode_at_15⟩,
          ⟨_, decode_bytecode_at_16⟩, ⟨_, decode_bytecode_at_17⟩,
          ⟨_, decode_bytecode_at_18⟩, ⟨_, decode_bytecode_at_19⟩]

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
  all_goals (rw [pc_eq_ofNat_of_toNat s _ (by decide) hpc] at hFetch)
  all_goals
    simp only [decode_bytecode_at_0, decode_bytecode_at_2, decode_bytecode_at_3,
      decode_bytecode_at_4, decode_bytecode_at_5, decode_bytecode_at_7,
      decode_bytecode_at_9, decode_bytecode_at_11, decode_bytecode_at_13,
      decode_bytecode_at_15, decode_bytecode_at_16, decode_bytecode_at_17,
      decode_bytecode_at_18, decode_bytecode_at_19] at hFetch
  all_goals (injection hFetch with h1; injection h1 with h1 _; subst h1; tauto)

/-- At any reachable CALL, `stack[2]? = some 0`. The only PC with op =
CALL is 17, and the disjunct at PC=17 has `stack[2]? = some 0`. -/
private theorem RegisterTrace_v0_at_CALL
    (C : AccountAddress) (s : EVM.State) (arg : Option (UInt256 × Nat))
    (h : RegisterTrace C s)
    (hFetch : fetchInstr s.executionEnv s.pc = .ok (.CALL, arg)) :
    s.stack[2]? = some ⟨0⟩ := by
  obtain ⟨_, hCode, hPC⟩ := h
  unfold fetchInstr at hFetch
  rw [hCode] at hFetch
  rcases hPC with
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ |
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩ |
    ⟨hpc, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _, hs2, _⟩ | ⟨hpc, _⟩ | ⟨hpc, _⟩
  -- The PC=17 disjunct already provides the witness; every other PC's
  -- decode contradicts `op = .CALL`, so we can dispatch by simping
  -- with the full decode table and falling back to the witness.
  all_goals (rw [pc_eq_ofNat_of_toNat s _ (by decide) hpc] at hFetch)
  all_goals first
    | exact hs2
    | (simp only [decode_bytecode_at_0, decode_bytecode_at_2, decode_bytecode_at_3,
        decode_bytecode_at_4, decode_bytecode_at_5, decode_bytecode_at_7,
        decode_bytecode_at_9, decode_bytecode_at_11, decode_bytecode_at_13,
        decode_bytecode_at_15, decode_bytecode_at_16,
        decode_bytecode_at_18, decode_bytecode_at_19] at hFetch
       cases hFetch)

/-! ### Initial-state lemma -/

/-- An initial Register-execution state is `RegisterTrace`, given the
deployment-pinned code-identity witness. -/
private theorem RegisterTrace_initial
    (C : AccountAddress)
    (hDeployed : DeployedAtC C)
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
  have hCode : I.code = bytecode := hDeployed I hCO
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
        = (UInt256.ofNat a).val + (UInt256.ofNat b).val from rfl,
      Fin.val_add,
      show (UInt256.ofNat a).val.val = a from Nat.mod_eq_of_lt ha,
      show (UInt256.ofNat b).val.val = b from Nat.mod_eq_of_lt hb]
  exact Nat.mod_eq_of_lt hab

/-- Convenience wrapper: for `a, b < 32` (always true for Register's PCs),
discharge all three bounds automatically. -/
private theorem ofNat_add_ofNat_toNat_lt32
    (a b : ℕ) (_ha : a < 32 := by decide) (_hb : b < 32 := by decide)
    (_hab : a + b < 32 := by decide) :
    (UInt256.ofNat a + UInt256.ofNat b).toNat = a + b :=
  ofNat_add_ofNat_toNat a b
    (by unfold UInt256.size; omega) (by unfold UInt256.size; omega)
    (by unfold UInt256.size; omega)

/-! ### Per-opcode step shape lemmas

These were lifted to `EvmYul.Frame.StepShapes` (in EVMYulLean) for
reuse across contract proofs:
- `step_PUSH1_shape`, `step_CALLDATALOAD_shape`, `step_CALLER_shape`,
  `step_SSTORE_shape`, `step_GAS_shape`, `step_POP_shape`,
  `step_STOP_shape`, `step_CALL_shape`, `EVM_call_preserves_pc`.

They resolve here via `open EvmYul.Frame`.
-/

/-- Repackage the proof of `RegisterTrace C s'` from the
shape-lemma outputs (`hEE'`, plus the chosen disjunct of the
post-state's `(pc, stack)` pair). The first three components of
`RegisterTrace` (codeOwner, code) are reduced to one `rw [hEE']`
each. -/
private theorem mk_registerTrace
    {C : AccountAddress} {s s' : EVM.State}
    (hCO : C = s.executionEnv.codeOwner)
    (hCode : s.executionEnv.code = bytecode)
    (hEE' : s'.executionEnv = s.executionEnv)
    (hPC : (s'.pc.toNat = 0 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 2 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 3 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 4 ∧ s'.stack.length = 2) ∨
       (s'.pc.toNat = 5 ∧ s'.stack.length = 0) ∨
       (s'.pc.toNat = 7 ∧ s'.stack.length = 1 ∧ s'.stack[0]? = some ⟨0⟩) ∨
       (s'.pc.toNat = 9 ∧ s'.stack.length = 2 ∧ s'.stack[0]? = some ⟨0⟩ ∧ s'.stack[1]? = some ⟨0⟩) ∨
       (s'.pc.toNat = 11 ∧ s'.stack.length = 3 ∧ s'.stack[0]? = some ⟨0⟩ ∧ s'.stack[1]? = some ⟨0⟩ ∧ s'.stack[2]? = some ⟨0⟩) ∨
       (s'.pc.toNat = 13 ∧ s'.stack.length = 4 ∧ s'.stack[0]? = some ⟨0⟩ ∧ s'.stack[1]? = some ⟨0⟩ ∧ s'.stack[2]? = some ⟨0⟩ ∧ s'.stack[3]? = some ⟨0⟩) ∨
       (s'.pc.toNat = 15 ∧ s'.stack.length = 5 ∧ s'.stack[0]? = some ⟨0⟩ ∧ s'.stack[1]? = some ⟨0⟩ ∧ s'.stack[2]? = some ⟨0⟩ ∧ s'.stack[3]? = some ⟨0⟩ ∧ s'.stack[4]? = some ⟨0⟩) ∨
       (s'.pc.toNat = 16 ∧ s'.stack.length = 6 ∧ s'.stack[1]? = some ⟨0⟩ ∧ s'.stack[2]? = some ⟨0⟩ ∧ s'.stack[3]? = some ⟨0⟩ ∧ s'.stack[4]? = some ⟨0⟩ ∧ s'.stack[5]? = some ⟨0⟩) ∨
       (s'.pc.toNat = 17 ∧ s'.stack.length = 7 ∧ s'.stack[2]? = some ⟨0⟩ ∧ s'.stack[3]? = some ⟨0⟩ ∧ s'.stack[4]? = some ⟨0⟩ ∧ s'.stack[5]? = some ⟨0⟩ ∧ s'.stack[6]? = some ⟨0⟩) ∨
       (s'.pc.toNat = 18 ∧ s'.stack.length = 1) ∨
       (s'.pc.toNat = 19 ∧ s'.stack.length = 0)) :
    RegisterTrace C s' :=
  ⟨by rw [hEE']; exact hCO, by rw [hEE']; exact hCode, hPC⟩

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
  · obtain ⟨hPC', hStk', hEE'⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_0 hStep
    refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inl ⟨?_, ?_⟩))
    · rw [hPC', hpcEq]
      exact ofNat_add_ofNat_toNat_lt32 0 2
    · rw [hStk']
      show List.length (UInt256.ofNat 0 :: s.stack) = 1
      simp [hLen]
  -- Case PC=2 (CALLDATALOAD).
  · match hStk_eq : s.stack, hLen with
    | hd :: tl, hLen2 =>
      have hLen3 : tl.length = 0 := by
        have : (hd :: tl).length = 1 := by rw [← hStk_eq]; exact hLen
        simpa using this
      obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
        step_CALLDATALOAD_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_2 hStep
      refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat_lt32 2 1
      · rw [hStk']
        show (v :: tl).length = 1
        simp [hLen3]
  -- Case PC=3 (CALLER).
  · obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_CALLER_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_3 hStep
    refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))))
    · rw [hPC', hpcEq]
      exact ofNat_add_ofNat_toNat_lt32 3 1
    · rw [hStk']
      show (v :: s.stack).length = 2
      simp [hLen]
  -- Case PC=4 (SSTORE).
  · match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: tl, hLen2 =>
      have hLen3 : tl.length = 0 := by
        have : (hd1 :: hd2 :: tl).length = 2 := by rw [← hStk_eq]; exact hLen
        simpa using this
      obtain ⟨hPC', hStk', hEE'⟩ :=
        step_SSTORE_at_pc s s' f' cost op arg _ hd1 hd2 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_4 hStep
      refine mk_registerTrace hCO hCode hEE'
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))))
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat_lt32 4 1
      · rw [hStk']; exact hLen3
  -- Case PC=5 (PUSH1 0).
  · obtain ⟨hPC', hStk', hEE'⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_5 hStep
    refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))))))
    · rw [hPC', hpcEq]
      exact ofNat_add_ofNat_toNat_lt32 5 2
    · rw [hStk']
      show List.length (UInt256.ofNat 0 :: s.stack) = 1
      simp [hLen]
    · rw [hStk']
      show (UInt256.ofNat 0 :: s.stack)[0]? = some ⟨0⟩
      rfl
  -- Case PC=7 (PUSH1 0).
  · obtain ⟨hPC', hStk', hEE'⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_7 hStep
    refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩)))))))
    · rw [hPC', hpcEq]
      exact ofNat_add_ofNat_toNat_lt32 7 2
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
  · obtain ⟨hPC', hStk', hEE'⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_9 hStep
    refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩))))))))
    · rw [hPC', hpcEq]
      exact ofNat_add_ofNat_toNat_lt32 9 2
    · rw [hStk']; show List.length (_ :: s.stack) = 3; simp [hLen]
    · rw [hStk']; rfl
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs0
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs1
  -- Case PC=11 (PUSH1 0).
  · obtain ⟨hPC', hStk', hEE'⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_11 hStep
    refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩)))))))))
    · rw [hPC', hpcEq]
      exact ofNat_add_ofNat_toNat_lt32 11 2
    · rw [hStk']; show List.length (_ :: s.stack) = 4; simp [hLen]
    · rw [hStk']; rfl
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs0
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs1
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs2
  -- Case PC=13 (PUSH1 0).
  · obtain ⟨hPC', hStk', hEE'⟩ :=
      step_PUSH1_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_13 hStep
    refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))))))))))
    · rw [hPC', hpcEq]
      exact ofNat_add_ofNat_toNat_lt32 13 2
    · rw [hStk']; show List.length (_ :: s.stack) = 5; simp [hLen]
    · rw [hStk']; rfl
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs0
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs1
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs2
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs3
  -- Case PC=15 (CALLER).
  · obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_CALLER_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_15 hStep
    refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))))))))))
    · rw [hPC', hpcEq]
      exact ofNat_add_ofNat_toNat_lt32 15 1
    · rw [hStk']; show List.length (v :: s.stack) = 6; simp [hLen]
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs0
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs1
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs2
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs3
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs4
  -- Case PC=16 (GAS).
  · obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
      step_GAS_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_16 hStep
    refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))))))))))))
    · rw [hPC', hpcEq]
      exact ofNat_add_ofNat_toNat_lt32 16 1
    · rw [hStk']; show List.length (v :: s.stack) = 7; simp [hLen]
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs1
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs2
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs3
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs4
    · rw [hStk']; simp [List.getElem?_cons_succ]; exact hs5
  -- Case PC=17 (CALL).
  · match hStk_eq : s.stack, hLen with
    | hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: hd7 :: tl, hLen2 =>
      have hTl : tl = [] := by
        have : (hd1 :: hd2 :: hd3 :: hd4 :: hd5 :: hd6 :: hd7 :: tl).length = 7 := by
          rw [← hStk_eq]; exact hLen
        have : tl.length = 0 := by simpa using this
        exact List.length_eq_zero_iff.mp this
      obtain ⟨hPC', ⟨v, hStk'⟩, hEE'⟩ :=
        step_CALL_at_pc s s' f' cost op arg _ hd1 hd2 hd3 hd4 hd5 hd6 hd7 tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_17 hStep
      refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩)))))))))))))
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat_lt32 17 1
      · rw [hStk', hTl]; rfl
  -- Case PC=18 (POP).
  · match hStk_eq : s.stack, hLen with
    | hd :: tl, hLen2 =>
      have hLen3 : tl.length = 0 := by
        have : (hd :: tl).length = 1 := by rw [← hStk_eq]; exact hLen
        simpa using this
      obtain ⟨hPC', hStk', hEE'⟩ :=
        step_POP_at_pc s s' f' cost op arg _ hd tl hStk_eq
          hFetch hCode hpcEq decode_bytecode_at_18 hStep
      refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨?_, ?_⟩))))))))))))))
      · rw [hPC', hpcEq]
        exact ofNat_add_ofNat_toNat_lt32 18 1
      · rw [hStk']; exact hLen3
  -- Case PC=19 (STOP). Halt — disjunct stays at PC=19 length=0.
  · obtain ⟨hPC', hStk', hEE'⟩ :=
      step_STOP_at_pc s s' f' cost op arg _ hFetch hCode hpcEq decode_bytecode_at_19 hStep
    refine mk_registerTrace hCO hCode hEE' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨?_, ?_⟩))))))))))))))
    · rw [hPC']; exact hpc
    · rw [hStk']; exact hLen

/-! ## Bytecode-preservation theorem -/

/-- Register's bytecode at `C` preserves `balanceOf C` through any Ξ
invocation, given the deployment-pinned code-identity witness. -/
theorem bytecodePreservesBalance (C : AccountAddress) (hDeployed : DeployedAtC C) :
    ΞPreservesAtC C := by
  exact ΞPreservesAtC_of_Reachable C (RegisterTrace C)
    (RegisterTrace_Z_preserves C)
    (RegisterTrace_step_preserves C)
    (RegisterTrace_decodeSome C)
    (RegisterTrace_op_in_8 C)
    (RegisterTrace_v0_at_CALL C)
    (RegisterTrace_initial C hDeployed)

end EvmSmith.Register
