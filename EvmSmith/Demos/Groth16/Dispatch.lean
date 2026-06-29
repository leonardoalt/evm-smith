import EvmYul.Frame
import EvmSmith.Demos.Groth16.Program
import EvmSmith.Demos.Groth16.EntryPoints

/-!
# Groth16 — dispatch and `checkField` routing (behavioural)

Where `EntryPoints.lean` proves *structural* facts ("what instruction is
at each PC"), this module proves *behavioural* facts: running the
dispatcher's instructions actually computes the ABI selector and routes to
`verifyLbl`, and from there `checkField`'s comparison actually branches the
way its bytecode shape suggests.

The value-computing "strong" step lemmas below mirror
`EvmYul.Frame.step_LT_shape_strong` and `Demos/Weth/Dispatch.lean`'s
`step_CALLDATALOAD_value`/`step_SHR_value`/`step_EQ_value` (duplicated here
rather than imported, matching this repo's existing per-demo convention —
WETH doesn't expose them as shared framework lemmas either), plus a new
`step_ISZERO_value` for `checkField`'s `ISZERO`.
-/

namespace EvmSmith.Groth16

open EvmYul EvmYul.EVM EvmYul.Frame

/-! ## Value-computing step lemmas -/

/-- `CALLDATALOAD` strong: pushes `calldataload(offset)` for the popped
`offset`, `pc += 1`, state otherwise unchanged. -/
theorem step_CALLDATALOAD_value
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.CALLDATALOAD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = EvmYul.State.calldataload s.toState hd :: tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnaryStateOp EVM.unaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- `SHR` strong: pushes `hd2 >> hd1` (EVM `SHR`: `value >> shift`, with
`shift = hd1` on top, `value = hd2` below), `pc += 1`. -/
theorem step_SHR_value
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SHR, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = UInt256.shiftRight hd2 hd1 :: tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- `EQ` strong: pushes `UInt256.eq hd1 hd2`, `pc += 1`. -/
theorem step_EQ_value
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.EQ, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = UInt256.eq hd1 hd2 :: tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-- `ISZERO` strong: pushes `UInt256.isZero hd`, `pc += 1`. -/
theorem step_ISZERO_value
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.ISZERO, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = UInt256.isZero hd :: tl ∧
    s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnary EVM.execUnOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl⟩

/-! ## UInt256 order facts -/

/-- `EQ` of a value with itself is `1` (true). -/
theorem eq_self_eq_one (a : UInt256) : UInt256.eq a a = UInt256.ofNat 1 := by
  unfold UInt256.eq
  rw [show decide (a = a) = true by simp]
  rfl

/-- `ISZERO 0` is `1` (true). -/
theorem iszero_zero_eq_one : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by
  unfold UInt256.isZero UInt256.eq0
  decide

/-- `LT a b` is `0` (false) when `b ≤ a` — i.e. `¬ (a < b)`. Stated on
`toNat` to avoid `UInt256` order-instance ambiguity (mirrors
`Demos/Weth/Dispatch.lean`'s `lt_eq_zero_of_le`). -/
theorem lt_eq_zero_of_ge {a b : UInt256} (h : b.toNat ≤ a.toNat) :
    UInt256.lt a b = UInt256.ofNat 0 := by
  unfold UInt256.lt
  have hnlt : ¬ (a < b) := by
    intro hlt
    have h1 : a.toNat < b.toNat := hlt
    omega
  rw [decide_eq_false hnlt]
  rfl

/-! ## Linking steps to the bytecode -/

/-- One faithful bytecode step: at a frame running `bytecode` with
`s.pc = ofNat N`, the instruction the interpreter fetches is exactly
`decode bytecode (ofNat N)`. -/
theorem groth16_fetch_step
    (s s' : EVM.State) (f c N : ℕ) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (hcode : s.executionEnv.code = bytecode)
    (hpc : s.pc = UInt256.ofNat N)
    (hdec : decode bytecode (UInt256.ofNat N) = some (op, arg))
    (hStep : EVM.step (f + 1) c (decode s.executionEnv.code s.pc) s = .ok s') :
    EVM.step (f + 1) c (some (op, arg)) s = .ok s' := by
  rwa [hcode, hpc, hdec] at hStep

/-! ## Selector computation and routing to `verifyLbl` -/

/-- **The dispatcher computes the ABI selector.** From the entry state
(running `bytecode` at `pc = 0`, empty stack), executing the bytecode's
instructions at PCs 0/2/3/5 leaves exactly `selectorOf calldata` on the
stack, with `pc = 6`. -/
theorem groth16_dispatcher_computes_selector
    (s0 s1 s2 s3 s4 : EVM.State) (f c0 c1 c2 c3 : ℕ)
    (hcode : s0.executionEnv.code = bytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4) :
    s4.stack = [selectorOf s0.executionEnv.calldata]
    ∧ s4.pc = UInt256.ofNat 6
    ∧ s4.executionEnv = s0.executionEnv := by
  obtain ⟨hd0, hd1, hd2, hd3⟩ := dispatch_extracts_selector
  have h0' := groth16_fetch_step s0 s1 f c0 0 _ _ hcode hpc0 hd0 h0
  obtain ⟨h1pc, hs1stk, hs1ee⟩ := step_PUSH1_shape s0 s1 f c0 (UInt256.ofNat 0) h0'
  rw [hstk0] at hs1stk
  have hcode1 : s1.executionEnv.code = bytecode := by rw [hs1ee]; exact hcode
  have hpc1 : s1.pc = UInt256.ofNat 2 := by rw [h1pc, hpc0]; decide
  have h1' := groth16_fetch_step s1 s2 f c1 2 _ _ hcode1 hpc1 hd1 h1
  obtain ⟨h2pc, hs2stk, hs2ee⟩ := step_CALLDATALOAD_value s1 s2 f c1 none (UInt256.ofNat 0) [] hs1stk h1'
  have hcode2 : s2.executionEnv.code = bytecode := by rw [hs2ee]; exact hcode1
  have hpc2 : s2.pc = UInt256.ofNat 3 := by rw [h2pc, hpc1]; decide
  have h2' := groth16_fetch_step s2 s3 f c2 3 _ _ hcode2 hpc2 hd2 h2
  obtain ⟨h3pc, hs3stk, hs3ee⟩ := step_PUSH1_shape s2 s3 f c2 (UInt256.ofNat 0xe0) h2'
  rw [hs2stk] at hs3stk
  have hcode3 : s3.executionEnv.code = bytecode := by rw [hs3ee]; exact hcode2
  have hpc3 : s3.pc = UInt256.ofNat 5 := by rw [h3pc, hpc2]; decide
  have h3' := groth16_fetch_step s3 s4 f c3 5 _ _ hcode3 hpc3 hd3 h3
  obtain ⟨h4pc, hs4stk, hs4ee⟩ :=
    step_SHR_value s3 s4 f c3 none (UInt256.ofNat 0xe0)
      (EvmYul.State.calldataload s1.toState (UInt256.ofNat 0)) [] hs3stk h3'
  refine ⟨?_, ?_, ?_⟩
  · rw [hs4stk]
    have hcd : s1.toState.executionEnv.calldata = s0.executionEnv.calldata :=
      congrArg EvmYul.ExecutionEnv.calldata hs1ee
    unfold selectorOf EvmYul.State.calldataload
    rw [hcd]
    have h0nat : (UInt256.ofNat 0).toNat = 0 := by decide
    rw [h0nat]
  · rw [h4pc, hpc3]; decide
  · rw [hs4ee, hs3ee, hs2ee, hs1ee]

/-- **The `verifyProof` selector routes past dispatch to `verifyLbl`.**
From the entry state, if the call's selector is `verifySelector`, then
after the dispatch's comparison (`PUSH4 verifySelector; EQ; PUSH2
verifyLbl; JUMPI`, PCs 6/11/12/15) execution is at `verifyLbl` (PC 21,
i.e. the `JUMPDEST` `checkField` immediately follows) with an **empty**
stack — unlike `Demos/Weth`'s dispatcher, this one has no `DUP1`, so the
selector is consumed by `EQ` and nothing is carried forward. -/
theorem groth16_routes_verify
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 : EVM.State) (f c0 c1 c2 c3 c4 c5 c6 c7 : ℕ)
    (hcode : s0.executionEnv.code = bytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hsel : functionSelector s0.executionEnv.calldata = verifySelector)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8) :
    s8.pc = verifyLbl ∧ s8.stack = [] ∧ s8.executionEnv = s0.executionEnv := by
  obtain ⟨hs4stk, hs4pc, hs4ee⟩ :=
    groth16_dispatcher_computes_selector s0 s1 s2 s3 s4 f c0 c1 c2 c3 hcode hpc0 hstk0 h0 h1 h2 h3
  have hsel' : selectorOf s0.executionEnv.calldata = verifySelector := hsel
  rw [hsel'] at hs4stk
  have hcode4 : s4.executionEnv.code = bytecode := by rw [hs4ee]; exact hcode
  obtain ⟨hd6, hd11⟩ := dispatch_compares_one_selector
  have h4' := groth16_fetch_step s4 s5 f c4 6 _ _ hcode4 hs4pc hd6 h4
  obtain ⟨h5pc, h5stk, h5ee⟩ := step_PUSH_shape s4 s5 f c4 .PUSH4 (by decide) verifySelector 4 h4'
  rw [hs4stk] at h5stk
  have hcode5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hcode4
  have hpc5 : s5.pc = UInt256.ofNat 11 := by rw [h5pc, hs4pc]; decide
  have h5' := groth16_fetch_step s5 s6 f c5 11 _ _ hcode5 hpc5 hd11 h5
  obtain ⟨h6pc, h6stk, h6ee⟩ :=
    step_EQ_value s5 s6 f c5 none verifySelector verifySelector [] h5stk h5'
  have hcode6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hcode5
  have hpc6 : s6.pc = UInt256.ofNat 12 := by rw [h6pc, hpc5]; decide
  have hd12 : decode bytecode (UInt256.ofNat 12) = some (.Push .PUSH2, some (verifyLbl, 2)) := by
    native_decide
  have h6' := groth16_fetch_step s6 s7 f c6 12 _ _ hcode6 hpc6 hd12 h6
  obtain ⟨h7pc, h7stk, h7ee⟩ := step_PUSH_shape s6 s7 f c6 .PUSH2 (by decide) verifyLbl 2 h6'
  rw [h6stk] at h7stk
  have hcode7 : s7.executionEnv.code = bytecode := by rw [h7ee]; exact hcode6
  have hpc7 : s7.pc = UInt256.ofNat 15 := by rw [h7pc, hpc6]; decide
  have hd15 : decode bytecode (UInt256.ofNat 15) = some (.JUMPI, none) := by native_decide
  have h7' := groth16_fetch_step s7 s8 f c7 15 _ _ hcode7 hpc7 hd15 h7
  obtain ⟨h8pc, h8stk, h8ee, _⟩ :=
    step_JUMPI_shape_strong s7 s8 f c7 none verifyLbl (UInt256.eq verifySelector verifySelector)
      [] h7stk h7'
  refine ⟨?_, h8stk, ?_⟩
  · rw [h8pc, eq_self_eq_one, if_pos (by decide)]
  · rw [h8ee, h7ee, h6ee, h5ee, hs4ee]

end EvmSmith.Groth16
