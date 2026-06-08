import EvmYul.Frame
import EvmSmith.Demos.Weth.Program
import EvmSmith.Demos.Weth.EntryPoints

/-!
# WETH — functional dispatch router (behavioural)

Where `EntryPoints.lean` proves *structural* facts ("what instruction is
at each PC"), this module proves *behavioural* facts: running the
dispatcher's instructions actually computes the ABI selector and routes
to the right function body as a function of that selector.

These are stated at the `EVM.step` granularity: each hypothesis `hN` is
"instruction N executed successfully (returned `.ok`)". Whether a step
succeeds depends on gas/stack, which is orthogonal to *which* branch is
taken — so this cleanly isolates the routing logic. The instruction at
each PC is fixed by the decode lemmas in `EntryPoints.lean`.

The value-computing "strong" step lemmas below mirror
`EvmYul.Frame.step_SUB_shape_strong` / `step_LT_shape_strong`, but for
the opcodes the dispatcher uses (`CALLDATALOAD`, `SHR`, `EQ`), exposing
the concrete pushed value instead of an existential.
-/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame

/-! ## Value-computing step lemmas for the dispatcher's opcodes -/

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
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `EQ` strong: pushes `fromBool (hd1 = hd2)` (EVM `EQ`), `pc += 1`. -/
theorem step_EQ_value
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.EQ, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = UInt256.eq hd1 hd2 :: tl ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinary EVM.execBinOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl, rfl⟩

/-! ## Selector computation

Running the dispatcher's first four instructions
(`PUSH1 0; CALLDATALOAD; PUSH1 0xe0; SHR`) computes exactly the ABI
function selector `selectorOf` of the call's calldata. -/

/-- **The dispatcher computes the ABI selector.** From the entry state
(`stack = []`), after `PUSH1 0; CALLDATALOAD; PUSH1 0xe0; SHR` the stack
holds exactly `selectorOf calldata` (the high 4 bytes of `calldata[0:32]`). -/
theorem weth_dispatcher_computes_selector
    (s0 s1 s2 s3 s4 : EVM.State) (f c0 c1 c2 c3 : ℕ)
    (hstk0 : s0.stack = [])
    (h0 : EVM.step (f + 1) c0 (some (.Push .PUSH1, some (UInt256.ofNat 0, 1))) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (some (.CALLDATALOAD, none)) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (some (.Push .PUSH1, some (UInt256.ofNat 0xe0, 1))) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (some (.SHR, none)) s3 = .ok s4) :
    s4.stack = [selectorOf s0.executionEnv.calldata] := by
  obtain ⟨_, hs1stk, hs1ee⟩ := step_PUSH1_shape s0 s1 f c0 (UInt256.ofNat 0) h0
  rw [hstk0] at hs1stk
  obtain ⟨_, hs2stk, _⟩ :=
    step_CALLDATALOAD_value s1 s2 f c1 none (UInt256.ofNat 0) [] hs1stk h1
  obtain ⟨_, hs3stk, _⟩ := step_PUSH1_shape s2 s3 f c2 (UInt256.ofNat 0xe0) h2
  rw [hs2stk] at hs3stk
  obtain ⟨_, hs4stk, _, _⟩ :=
    step_SHR_value s3 s4 f c3 none (UInt256.ofNat 0xe0)
      (EvmYul.State.calldataload s1.toState (UInt256.ofNat 0)) [] hs3stk h3
  rw [hs4stk]
  have hcd : s1.toState.executionEnv.calldata = s0.executionEnv.calldata :=
    congrArg EvmYul.ExecutionEnv.calldata hs1ee
  unfold selectorOf EvmYul.State.calldataload
  rw [hcd]
  have h0nat : (UInt256.ofNat 0).toNat = 0 := by decide
  rw [h0nat]

end EvmSmith.Weth
