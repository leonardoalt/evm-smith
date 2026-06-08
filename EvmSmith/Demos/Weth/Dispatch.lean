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

/-! ## Value-computing step lemmas for the deposit body -/

/-- `CALLER` strong: pushes the caller address (as a `UInt256` slot key,
which is exactly `addressSlot caller`), `pc += 1`. -/
theorem step_CALLER_value
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.CALLER, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = UInt256.ofNat s.executionEnv.source.val :: s.stack ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `CALLVALUE` strong: pushes `msg.value` (the wei sent with the call),
`pc += 1`. -/
theorem step_CALLVALUE_value
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hStep : EVM.step (f' + 1) cost (some (.CALLVALUE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = s.executionEnv.weiValue :: s.stack ∧
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchExecutionEnvOp EVM.executionEnvOp at hStep
  simp only [Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `ADD` strong: pushes `hd1 + hd2` (EVM `ADD`), `pc += 1`. -/
theorem step_ADD_value
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd1 hd2 : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd1 :: hd2 :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.ADD, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧
    s'.stack = UInt256.add hd1 hd2 :: tl ∧
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

/-- `SSTORE` strong: the post-state's `accountMap` is the pre-state's
with the codeOwner's account updated to set `storage[slot] := newVal`
(`slot` on top, `newVal` second). -/
theorem step_SSTORE_to_insert
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (slot newVal : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = slot :: newVal :: tl)
    (acc : Account .EVM)
    (h_find : s.accountMap.find? s.executionEnv.codeOwner = some acc)
    (hStep : EVM.step (f' + 1) cost (some (.SSTORE, arg)) s = .ok s') :
    s'.accountMap
      = s.accountMap.insert s.executionEnv.codeOwner (acc.updateStorage slot newVal) := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryStateOp EVM.binaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  simp only [accountMap_replaceStackAndIncrPC]
  show (EvmYul.State.sstore s.toState slot newVal).accountMap
       = s.accountMap.insert s.executionEnv.codeOwner (acc.updateStorage slot newVal)
  unfold EvmYul.State.sstore
  simp only [EvmYul.State.lookupAccount, h_find, Option.option]
  rfl

/-! ## Deposit postcondition

Running the deposit body credits the caller's recorded token balance by
`msg.value`. Stated as the exact effect on the contract's account: the
caller's storage slot goes from `oldVal` to `oldVal + msg.value`. -/

/-- **deposit credits the caller by `msg.value`.** From the deposit
entry (stack `[selector]`, executing at the contract `C`), after the
deposit body `POP; CALLER; DUP1; SLOAD; CALLVALUE; ADD; SWAP1; SSTORE`
the contract's account has `storage[addressSlot caller]` set to its old
value plus `msg.value` — and nothing else in the account map changes.
This holds unconditionally (the deposit body has no branch), so deposit
always credits and never reverts on its own. -/
theorem weth_deposit_credits_caller
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : EVM.State) (f c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℕ)
    (C : AccountAddress) (acc : Account .EVM) (sel : UInt256)
    (hCo : s0.executionEnv.codeOwner = C)
    (hstk0 : s0.stack = [sel])
    (hfind : s0.accountMap.find? C = some acc)
    (h0 : EVM.step (f + 1) c0 (some (.JUMPDEST, none)) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (some (.POP, none)) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (some (.CALLER, none)) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (some (.DUP1, none)) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (some (.SLOAD, none)) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (some (.CALLVALUE, none)) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (some (.ADD, none)) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (some (.SWAP1, none)) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (some (.SSTORE, none)) s8 = .ok s9) :
    s9.accountMap
      = s0.accountMap.insert C
          (acc.updateStorage (UInt256.ofNat s0.executionEnv.source.val)
            (UInt256.add s0.executionEnv.weiValue
              (acc.lookupStorage (UInt256.ofNat s0.executionEnv.source.val)))) := by
  -- JUMPDEST: stack/accountMap/ee unchanged
  obtain ⟨_, h1stk, h1ee, h1am⟩ := step_JUMPDEST_shape_strong s0 s1 f c0 none h0
  rw [hstk0] at h1stk
  -- POP: drop selector
  obtain ⟨_, h2stk, h2ee, h2am⟩ := step_POP_shape_strong s1 s2 f c1 none sel [] h1stk h1
  -- CALLER: push caller = ofNat source.val
  obtain ⟨_, h3stk, h3ee, h3am⟩ := step_CALLER_value s2 s3 f c2 none h2
  rw [h2stk] at h3stk
  -- DUP1: [caller, caller]
  obtain ⟨_, h4stk, h4ee, h4am⟩ :=
    step_DUP1_shape_strong s3 s4 f c3 none (UInt256.ofNat s2.executionEnv.source.val) [] h3stk h3
  rw [h3stk] at h4stk
  -- SLOAD: pops caller, pushes oldVal
  obtain ⟨_, h5stk, h5ee, h5am⟩ :=
    step_SLOAD_shape_strong s4 s5 f c4 none (UInt256.ofNat s2.executionEnv.source.val)
      [UInt256.ofNat s2.executionEnv.source.val] h4stk h4
  -- CALLVALUE: push value
  obtain ⟨_, h6stk, h6ee, h6am⟩ := step_CALLVALUE_value s5 s6 f c5 none h5
  rw [h5stk] at h6stk
  -- ADD: value + oldVal
  obtain ⟨_, h7stk, h7ee, h7am⟩ :=
    step_ADD_value s6 s7 f c6 none s5.executionEnv.weiValue
      (s4.lookupAccount s4.executionEnv.codeOwner |>.option ⟨0⟩
        (Account.lookupStorage (k := UInt256.ofNat s2.executionEnv.source.val)))
      [UInt256.ofNat s2.executionEnv.source.val] h6stk h6
  -- SWAP1: [caller, newVal]
  obtain ⟨_, h8stk, h8ee, h8am⟩ :=
    step_SWAP1_shape_strong s7 s8 f c7 none
      (UInt256.add s5.executionEnv.weiValue
        (s4.lookupAccount s4.executionEnv.codeOwner |>.option ⟨0⟩
          (Account.lookupStorage (k := UInt256.ofNat s2.executionEnv.source.val))))
      (UInt256.ofNat s2.executionEnv.source.val) [] h7stk h7
  -- SSTORE: insert updated account
  -- Establish s8.executionEnv.codeOwner = C and s8.accountMap.find? C = some acc.
  have hee : s8.executionEnv = s0.executionEnv := by
    rw [h8ee, h7ee, h6ee, h5ee, h4ee, h3ee, h2ee, h1ee]
  have ham : s8.accountMap = s0.accountMap := by
    rw [h8am, h7am, h6am, h5am, h4am, h3am, h2am, h1am]
  have h8co : s8.executionEnv.codeOwner = C := by rw [hee]; exact hCo
  have h8find : s8.accountMap.find? s8.executionEnv.codeOwner = some acc := by
    rw [ham, h8co]; exact hfind
  obtain h9am :=
    step_SSTORE_to_insert s8 s9 f c8 none
      (UInt256.ofNat s2.executionEnv.source.val)
      (UInt256.add s5.executionEnv.weiValue
        (s4.lookupAccount s4.executionEnv.codeOwner |>.option ⟨0⟩
          (Account.lookupStorage (k := UInt256.ofNat s2.executionEnv.source.val))))
      [] h8stk acc h8find h8
  rw [h9am, h8co, ham]
  -- Now reconcile s2/s4/s5 executionEnv & accountMap with s0's.
  have h2ee0 : s2.executionEnv = s0.executionEnv := by rw [h2ee, h1ee]
  have h4ee0 : s4.executionEnv = s0.executionEnv := by rw [h4ee, h3ee, h2ee, h1ee]
  have h5ee0 : s5.executionEnv = s0.executionEnv := by rw [h5ee, h4ee, h3ee, h2ee, h1ee]
  have h4am0 : s4.accountMap = s0.accountMap := by rw [h4am, h3am, h2am, h1am]
  -- Expose the SLOAD's account lookup, then rewrite everything to s0.
  simp only [EvmYul.State.lookupAccount]
  rw [h2ee0, h5ee0, h4ee0, h4am0, hCo, hfind]
  rfl

end EvmSmith.Weth
