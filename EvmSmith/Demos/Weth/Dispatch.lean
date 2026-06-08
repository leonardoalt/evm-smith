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
    s'.executionEnv = s.executionEnv ∧
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnaryStateOp EVM.unaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨rfl, rfl, rfl, rfl⟩

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

/-! ## Linking steps to the bytecode

The real interpreter (`EVM.X`) executes, at each state `s`, the
instruction `decode s.executionEnv.code s.pc` — the opcode the *bytecode*
decodes to at the current program counter. The theorems below therefore
take each step in that exact form, with the contract's code pinned to
`bytecode` and the program counter threaded, so every executed
instruction is the bytecode's — not a hand-supplied opcode. -/

/-- One faithful bytecode step. At a frame running `bytecode` with
`s.pc = ofNat N`, the instruction the interpreter fetches is exactly
`decode bytecode (ofNat N)`; given the decode fact, `EVM.step` on the
fetched instruction is `EVM.step` on the concrete `some (op, arg)`. -/
theorem weth_fetch_step
    (s s' : EVM.State) (f c N : ℕ) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (hcode : s.executionEnv.code = bytecode)
    (hpc : s.pc = UInt256.ofNat N)
    (hdec : decode bytecode (UInt256.ofNat N) = some (op, arg))
    (hStep : EVM.step (f + 1) c (decode s.executionEnv.code s.pc) s = .ok s') :
    EVM.step (f + 1) c (some (op, arg)) s = .ok s' := by
  rwa [hcode, hpc, hdec] at hStep

/-! ## Selector computation

Running the dispatcher's first four bytecode instructions (at PCs 0, 2,
3, 5 — `PUSH1 0; CALLDATALOAD; PUSH1 0xe0; SHR`) computes exactly the ABI
function selector `selectorOf` of the call's calldata. -/

/-- **The dispatcher computes the ABI selector.** From the entry state
(running `bytecode` at `pc = 0`, empty stack), executing the bytecode's
instructions at PCs 0/2/3/5 leaves exactly `selectorOf calldata` (the
high 4 bytes of `calldata[0:32]`) on the stack. Each `hN` runs
`decode s.executionEnv.code s.pc` — the instruction the interpreter
fetches from the bytecode at the current pc. -/
theorem weth_dispatcher_computes_selector
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
    ∧ s4.executionEnv = s0.executionEnv
    ∧ s4.accountMap = s0.accountMap := by
  have h0' := weth_fetch_step s0 s1 f c0 0 _ _ hcode hpc0
    (by native_decide : decode bytecode (UInt256.ofNat 0) = some (.Push .PUSH1, some (UInt256.ofNat 0, 1))) h0
  obtain ⟨h1pc, hs1stk, hs1ee, ha1⟩ := step_PUSH1_shape_strong s0 s1 f c0 (UInt256.ofNat 0) h0'
  rw [hstk0] at hs1stk
  have hcode1 : s1.executionEnv.code = bytecode := by rw [hs1ee]; exact hcode
  have hpc1 : s1.pc = UInt256.ofNat 2 := by rw [h1pc, hpc0]; decide
  have h1' := weth_fetch_step s1 s2 f c1 2 _ _ hcode1 hpc1
    (by native_decide : decode bytecode (UInt256.ofNat 2) = some (.CALLDATALOAD, none)) h1
  obtain ⟨h2pc, hs2stk, hs2ee, ha2⟩ :=
    step_CALLDATALOAD_value s1 s2 f c1 none (UInt256.ofNat 0) [] hs1stk h1'
  have hcode2 : s2.executionEnv.code = bytecode := by rw [hs2ee]; exact hcode1
  have hpc2 : s2.pc = UInt256.ofNat 3 := by rw [h2pc, hpc1]; decide
  have h2' := weth_fetch_step s2 s3 f c2 3 _ _ hcode2 hpc2
    (by native_decide : decode bytecode (UInt256.ofNat 3) = some (.Push .PUSH1, some (UInt256.ofNat 0xe0, 1))) h2
  obtain ⟨h3pc, hs3stk, hs3ee, ha3⟩ := step_PUSH1_shape_strong s2 s3 f c2 (UInt256.ofNat 0xe0) h2'
  rw [hs2stk] at hs3stk
  have hcode3 : s3.executionEnv.code = bytecode := by rw [hs3ee]; exact hcode2
  have hpc3 : s3.pc = UInt256.ofNat 5 := by rw [h3pc, hpc2]; decide
  have h3' := weth_fetch_step s3 s4 f c3 5 _ _ hcode3 hpc3
    (by native_decide : decode bytecode (UInt256.ofNat 5) = some (.SHR, none)) h3
  obtain ⟨h4pc, hs4stk, hs4ee, ha4⟩ :=
    step_SHR_value s3 s4 f c3 none (UInt256.ofNat 0xe0)
      (EvmYul.State.calldataload s1.toState (UInt256.ofNat 0)) [] hs3stk h3'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs4stk]
    have hcd : s1.toState.executionEnv.calldata = s0.executionEnv.calldata :=
      congrArg EvmYul.ExecutionEnv.calldata hs1ee
    unfold selectorOf EvmYul.State.calldataload
    rw [hcd]
    have h0nat : (UInt256.ofNat 0).toNat = 0 := by decide
    rw [h0nat]
  · rw [h4pc, hpc3]; decide
  · rw [hs4ee, hs3ee, hs2ee, hs1ee]
  · rw [ha4, ha3, ha2, ha1]

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
    (hcode : s0.executionEnv.code = bytecode)
    (hpc0 : s0.pc = UInt256.ofNat 32)
    (hCo : s0.executionEnv.codeOwner = C)
    (hstk0 : s0.stack = [sel])
    (hfind : s0.accountMap.find? C = some acc)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9) :
    s9.accountMap
      = s0.accountMap.insert C
          (acc.updateStorage (UInt256.ofNat s0.executionEnv.source.val)
            (UInt256.add s0.executionEnv.weiValue
              (acc.lookupStorage (UInt256.ofNat s0.executionEnv.source.val)))) := by
  -- JUMPDEST (pc 32)
  have h0' := weth_fetch_step s0 s1 f c0 32 _ _ hcode hpc0
    (by native_decide : decode bytecode (UInt256.ofNat 32) = some (.JUMPDEST, none)) h0
  obtain ⟨h1pc, h1stk, h1ee, h1am⟩ := step_JUMPDEST_shape_strong s0 s1 f c0 none h0'
  rw [hstk0] at h1stk
  have hcd1 : s1.executionEnv.code = bytecode := by rw [h1ee]; exact hcode
  have hp1 : s1.pc = UInt256.ofNat 33 := by rw [h1pc, hpc0]; decide
  -- POP (pc 33)
  have h1' := weth_fetch_step s1 s2 f c1 33 _ _ hcd1 hp1
    (by native_decide : decode bytecode (UInt256.ofNat 33) = some (.POP, none)) h1
  obtain ⟨h2pc, h2stk, h2ee, h2am⟩ := step_POP_shape_strong s1 s2 f c1 none sel [] h1stk h1'
  have hcd2 : s2.executionEnv.code = bytecode := by rw [h2ee]; exact hcd1
  have hp2 : s2.pc = UInt256.ofNat 34 := by rw [h2pc, hp1]; decide
  -- CALLER (pc 34)
  have h2' := weth_fetch_step s2 s3 f c2 34 _ _ hcd2 hp2
    (by native_decide : decode bytecode (UInt256.ofNat 34) = some (.CALLER, none)) h2
  obtain ⟨h3pc, h3stk, h3ee, h3am⟩ := step_CALLER_value s2 s3 f c2 none h2'
  rw [h2stk] at h3stk
  have hcd3 : s3.executionEnv.code = bytecode := by rw [h3ee]; exact hcd2
  have hp3 : s3.pc = UInt256.ofNat 35 := by rw [h3pc, hp2]; decide
  -- DUP1 (pc 35)
  have h3' := weth_fetch_step s3 s4 f c3 35 _ _ hcd3 hp3
    (by native_decide : decode bytecode (UInt256.ofNat 35) = some (.DUP1, none)) h3
  obtain ⟨h4pc, h4stk, h4ee, h4am⟩ :=
    step_DUP1_shape_strong s3 s4 f c3 none (UInt256.ofNat s2.executionEnv.source.val) [] h3stk h3'
  rw [h3stk] at h4stk
  have hcd4 : s4.executionEnv.code = bytecode := by rw [h4ee]; exact hcd3
  have hp4 : s4.pc = UInt256.ofNat 36 := by rw [h4pc, hp3]; decide
  -- SLOAD (pc 36)
  have h4' := weth_fetch_step s4 s5 f c4 36 _ _ hcd4 hp4
    (by native_decide : decode bytecode (UInt256.ofNat 36) = some (.SLOAD, none)) h4
  obtain ⟨h5pc, h5stk, h5ee, h5am⟩ :=
    step_SLOAD_shape_strong s4 s5 f c4 none (UInt256.ofNat s2.executionEnv.source.val)
      [UInt256.ofNat s2.executionEnv.source.val] h4stk h4'
  have hcd5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hcd4
  have hp5 : s5.pc = UInt256.ofNat 37 := by rw [h5pc, hp4]; decide
  -- CALLVALUE (pc 37)
  have h5' := weth_fetch_step s5 s6 f c5 37 _ _ hcd5 hp5
    (by native_decide : decode bytecode (UInt256.ofNat 37) = some (.CALLVALUE, none)) h5
  obtain ⟨h6pc, h6stk, h6ee, h6am⟩ := step_CALLVALUE_value s5 s6 f c5 none h5'
  rw [h5stk] at h6stk
  have hcd6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hcd5
  have hp6 : s6.pc = UInt256.ofNat 38 := by rw [h6pc, hp5]; decide
  -- ADD (pc 38)
  have h6' := weth_fetch_step s6 s7 f c6 38 _ _ hcd6 hp6
    (by native_decide : decode bytecode (UInt256.ofNat 38) = some (.ADD, none)) h6
  obtain ⟨h7pc, h7stk, h7ee, h7am⟩ :=
    step_ADD_value s6 s7 f c6 none s5.executionEnv.weiValue
      (s4.lookupAccount s4.executionEnv.codeOwner |>.option ⟨0⟩
        (Account.lookupStorage (k := UInt256.ofNat s2.executionEnv.source.val)))
      [UInt256.ofNat s2.executionEnv.source.val] h6stk h6'
  have hcd7 : s7.executionEnv.code = bytecode := by rw [h7ee]; exact hcd6
  have hp7 : s7.pc = UInt256.ofNat 39 := by rw [h7pc, hp6]; decide
  -- SWAP1 (pc 39)
  have h7' := weth_fetch_step s7 s8 f c7 39 _ _ hcd7 hp7
    (by native_decide : decode bytecode (UInt256.ofNat 39) = some (.SWAP1, none)) h7
  obtain ⟨h8pc, h8stk, h8ee, h8am⟩ :=
    step_SWAP1_shape_strong s7 s8 f c7 none
      (UInt256.add s5.executionEnv.weiValue
        (s4.lookupAccount s4.executionEnv.codeOwner |>.option ⟨0⟩
          (Account.lookupStorage (k := UInt256.ofNat s2.executionEnv.source.val))))
      (UInt256.ofNat s2.executionEnv.source.val) [] h7stk h7'
  have hcd8 : s8.executionEnv.code = bytecode := by rw [h8ee]; exact hcd7
  have hp8 : s8.pc = UInt256.ofNat 40 := by rw [h8pc, hp7]; decide
  -- SSTORE (pc 40): insert updated account
  have h8' := weth_fetch_step s8 s9 f c8 40 _ _ hcd8 hp8
    (by native_decide : decode bytecode (UInt256.ofNat 40) = some (.SSTORE, none)) h8
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
      [] h8stk acc h8find h8'
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

/-! ## Withdraw postcondition (state update)

When `withdraw` proceeds past its balance check, it decrements the
caller's recorded balance by `x` (the requested amount). Stated as the
exact effect on the contract's account: `storage[caller]` goes from
`balance` to `balance - x`. -/

/-- The `LT` gate: when `x ≤ balance`, `LT balance x` is `0`, so the
withdraw block's `JUMPI` is **not** taken (it does not jump to the
revert label). Stated on `toNat` to avoid `UInt256` order-instance
ambiguity. -/
theorem lt_eq_zero_of_le {a b : UInt256} (h : b.toNat ≤ a.toNat) :
    UInt256.lt a b = UInt256.ofNat 0 := by
  unfold UInt256.lt
  have hnlt : ¬ (a < b) := by
    intro hlt
    have h1 : a.toNat < b.toNat := hlt
    omega
  rw [decide_eq_false hnlt]
  rfl

/-- **`withdraw` decrements the caller by `x`.** From the withdraw entry
(running `bytecode` at `pc = 42`, stack `[]`, executing at `C`), with
sufficient balance (`x ≤ balance`, so the `LT` gate falls through), the
withdraw state-update block (PCs 42–60:
`JUMPDEST; PUSH1 4; CALLDATALOAD; CALLER; DUP1; SLOAD; DUP3; DUP2; LT;
PUSH2 revertLbl; JUMPI; DUP3; SWAP1; SUB; SWAP1; SSTORE`) sets the
contract's `storage[addressSlot caller]` from `balance` to `balance - x`
(`x = calldata[4:36]`), and no other account changes. Each `hN` runs the
bytecode's instruction at the current pc. -/
theorem weth_withdraw_decrements_caller
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 : EVM.State)
    (f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : ℕ)
    (C : AccountAddress) (acc : Account .EVM)
    (hcode : s0.executionEnv.code = bytecode)
    (hpc0 : s0.pc = UInt256.ofNat 42)
    (hCo : s0.executionEnv.codeOwner = C)
    (hstk0 : s0.stack = [])
    (hfind : s0.accountMap.find? C = some acc)
    (hle : (EvmYul.State.calldataload s0.toState (UInt256.ofNat 4)).toNat
            ≤ (acc.lookupStorage (UInt256.ofNat s0.executionEnv.source.val)).toNat)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9)
    (h9 : EVM.step (f + 1) c9 (decode s9.executionEnv.code s9.pc) s9 = .ok s10)
    (h10 : EVM.step (f + 1) c10 (decode s10.executionEnv.code s10.pc) s10 = .ok s11)
    (h11 : EVM.step (f + 1) c11 (decode s11.executionEnv.code s11.pc) s11 = .ok s12)
    (h12 : EVM.step (f + 1) c12 (decode s12.executionEnv.code s12.pc) s12 = .ok s13)
    (h13 : EVM.step (f + 1) c13 (decode s13.executionEnv.code s13.pc) s13 = .ok s14)
    (h14 : EVM.step (f + 1) c14 (decode s14.executionEnv.code s14.pc) s14 = .ok s15)
    (h15 : EVM.step (f + 1) c15 (decode s15.executionEnv.code s15.pc) s15 = .ok s16) :
    s16.accountMap
      = s0.accountMap.insert C
          (acc.updateStorage (UInt256.ofNat s0.executionEnv.source.val)
            (UInt256.sub (acc.lookupStorage (UInt256.ofNat s0.executionEnv.source.val))
              (EvmYul.State.calldataload s0.toState (UInt256.ofNat 4)))) := by
  set xV := EvmYul.State.calldataload s2.toState (UInt256.ofNat 4) with hxV
  set caller := UInt256.ofNat s3.executionEnv.source.val with hcaller
  -- JUMPDEST (42)
  have h0' := weth_fetch_step s0 s1 f c0 42 _ _ hcode hpc0
    (by native_decide : decode bytecode (UInt256.ofNat 42) = some (.JUMPDEST, none)) h0
  obtain ⟨h1pc, h1stk, h1ee, h1am⟩ := step_JUMPDEST_shape_strong s0 s1 f c0 none h0'
  rw [hstk0] at h1stk
  have hcd1 : s1.executionEnv.code = bytecode := by rw [h1ee]; exact hcode
  have hp1 : s1.pc = UInt256.ofNat 43 := by rw [h1pc, hpc0]; decide
  -- PUSH1 4 (43)
  have h1' := weth_fetch_step s1 s2 f c1 43 _ _ hcd1 hp1
    (by native_decide : decode bytecode (UInt256.ofNat 43) = some (.Push .PUSH1, some (UInt256.ofNat 4, 1))) h1
  obtain ⟨h2pc, h2stk, h2ee, h2am⟩ := step_PUSH1_shape_strong s1 s2 f c1 (UInt256.ofNat 4) h1'
  rw [h1stk] at h2stk
  have hcd2 : s2.executionEnv.code = bytecode := by rw [h2ee]; exact hcd1
  have hp2 : s2.pc = UInt256.ofNat 45 := by rw [h2pc, hp1]; decide
  -- CALLDATALOAD (45)
  have h2' := weth_fetch_step s2 s3 f c2 45 _ _ hcd2 hp2
    (by native_decide : decode bytecode (UInt256.ofNat 45) = some (.CALLDATALOAD, none)) h2
  obtain ⟨h3pc, h3stk, h3ee, h3am⟩ :=
    step_CALLDATALOAD_value s2 s3 f c2 none (UInt256.ofNat 4) [] h2stk h2'
  have hcd3 : s3.executionEnv.code = bytecode := by rw [h3ee]; exact hcd2
  have hp3 : s3.pc = UInt256.ofNat 46 := by rw [h3pc, hp2]; decide
  -- CALLER (46)
  have h3' := weth_fetch_step s3 s4 f c3 46 _ _ hcd3 hp3
    (by native_decide : decode bytecode (UInt256.ofNat 46) = some (.CALLER, none)) h3
  obtain ⟨h4pc, h4stk, h4ee, h4am⟩ := step_CALLER_value s3 s4 f c3 none h3'
  rw [h3stk] at h4stk
  have hcd4 : s4.executionEnv.code = bytecode := by rw [h4ee]; exact hcd3
  have hp4 : s4.pc = UInt256.ofNat 47 := by rw [h4pc, hp3]; decide
  -- DUP1 (47)
  have h4' := weth_fetch_step s4 s5 f c4 47 _ _ hcd4 hp4
    (by native_decide : decode bytecode (UInt256.ofNat 47) = some (.DUP1, none)) h4
  obtain ⟨h5pc, h5stk, h5ee, h5am⟩ := step_DUP1_shape_strong s4 s5 f c4 none caller [xV] h4stk h4'
  rw [h4stk] at h5stk
  have hcd5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hcd4
  have hp5 : s5.pc = UInt256.ofNat 48 := by rw [h5pc, hp4]; decide
  set balV := s5.lookupAccount s5.executionEnv.codeOwner |>.option ⟨0⟩
      (Account.lookupStorage (k := caller)) with hbalV
  -- SLOAD (48)
  have h5' := weth_fetch_step s5 s6 f c5 48 _ _ hcd5 hp5
    (by native_decide : decode bytecode (UInt256.ofNat 48) = some (.SLOAD, none)) h5
  obtain ⟨h6pc, h6stk, h6ee, h6am⟩ := step_SLOAD_shape_strong s5 s6 f c5 none caller [caller, xV] h5stk h5'
  have hcd6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hcd5
  have hp6 : s6.pc = UInt256.ofNat 49 := by rw [h6pc, hp5]; decide
  -- DUP3 (49)
  have h6' := weth_fetch_step s6 s7 f c6 49 _ _ hcd6 hp6
    (by native_decide : decode bytecode (UInt256.ofNat 49) = some (.DUP3, none)) h6
  obtain ⟨h7pc, h7stk, h7ee, h7am⟩ := step_DUP3_shape_strong s6 s7 f c6 none balV caller xV [] h6stk h6'
  rw [h6stk] at h7stk
  have hcd7 : s7.executionEnv.code = bytecode := by rw [h7ee]; exact hcd6
  have hp7 : s7.pc = UInt256.ofNat 50 := by rw [h7pc, hp6]; decide
  -- DUP2 (50)
  have h7' := weth_fetch_step s7 s8 f c7 50 _ _ hcd7 hp7
    (by native_decide : decode bytecode (UInt256.ofNat 50) = some (.DUP2, none)) h7
  obtain ⟨h8pc, h8stk, h8ee, h8am⟩ :=
    step_DUP2_shape_strong s7 s8 f c7 none xV balV [caller, xV] h7stk h7'
  rw [h7stk] at h8stk
  have hcd8 : s8.executionEnv.code = bytecode := by rw [h8ee]; exact hcd7
  have hp8 : s8.pc = UInt256.ofNat 51 := by rw [h8pc, hp7]; decide
  -- LT (51)
  have h8' := weth_fetch_step s8 s9 f c8 51 _ _ hcd8 hp8
    (by native_decide : decode bytecode (UInt256.ofNat 51) = some (.LT, none)) h8
  obtain ⟨h9pc, h9stk, h9ee, h9am⟩ :=
    step_LT_shape_strong s8 s9 f c8 none balV xV [balV, caller, xV] h8stk h8'
  have hcd9 : s9.executionEnv.code = bytecode := by rw [h9ee]; exact hcd8
  have hp9 : s9.pc = UInt256.ofNat 52 := by rw [h9pc, hp8]; decide
  -- PUSH2 revertLbl (52)
  have h9' := weth_fetch_step s9 s10 f c9 52 _ _ hcd9 hp9
    (by native_decide : decode bytecode (UInt256.ofNat 52) = some (.Push .PUSH2, some (revertLbl, 2))) h9
  obtain ⟨h10pc, h10stk, h10ee, h10am⟩ := step_PUSH_shape_strong s9 s10 f c9 .PUSH2 (by decide) revertLbl 2 h9'
  rw [h9stk] at h10stk
  have hcd10 : s10.executionEnv.code = bytecode := by rw [h10ee]; exact hcd9
  have hp10 : s10.pc = UInt256.ofNat 55 := by rw [h10pc, hp9]; decide
  -- Establish the gate-pass fact (LT balV xV = 0) from `hle`.
  have h2ee0 : s2.executionEnv = s0.executionEnv := by rw [h2ee, h1ee]
  have h3ee0 : s3.executionEnv = s0.executionEnv := by rw [h3ee, h2ee, h1ee]
  have h5ee0 : s5.executionEnv = s0.executionEnv := by rw [h5ee, h4ee, h3ee, h2ee, h1ee]
  have h5am0 : s5.accountMap = s0.accountMap := by rw [h5am, h4am, h3am, h2am, h1am]
  have hcallerEq : caller = UInt256.ofNat s0.executionEnv.source.val := by rw [hcaller, h3ee0]
  have hxVEq : xV = EvmYul.State.calldataload s0.toState (UInt256.ofNat 4) := by
    rw [hxV]; unfold EvmYul.State.calldataload
    rw [show s2.toState.executionEnv.calldata = s0.toState.executionEnv.calldata from
        congrArg EvmYul.ExecutionEnv.calldata h2ee0]
  have hbalEq : balV = acc.lookupStorage caller := by
    rw [hbalV]; simp only [EvmYul.State.lookupAccount]; rw [h5am0, h5ee0, hCo, hfind]; rfl
  have hgate : UInt256.lt balV xV = UInt256.ofNat 0 := by
    apply lt_eq_zero_of_le
    rw [hxVEq, hbalEq, hcallerEq]; exact hle
  -- JUMPI (55): not taken, pc → 56
  have h10' := weth_fetch_step s10 s11 f c10 55 _ _ hcd10 hp10
    (by native_decide : decode bytecode (UInt256.ofNat 55) = some (.JUMPI, none)) h10
  obtain ⟨h11pc, h11stk, h11ee, h11am⟩ :=
    step_JUMPI_shape_strong s10 s11 f c10 none revertLbl (UInt256.lt balV xV)
      [balV, caller, xV] h10stk h10'
  have hcd11 : s11.executionEnv.code = bytecode := by rw [h11ee]; exact hcd10
  have hp11 : s11.pc = UInt256.ofNat 56 := by
    rw [h11pc, hgate, if_neg (by decide), hp10]; decide
  -- DUP3 (56)
  have h11' := weth_fetch_step s11 s12 f c11 56 _ _ hcd11 hp11
    (by native_decide : decode bytecode (UInt256.ofNat 56) = some (.DUP3, none)) h11
  obtain ⟨h12pc, h12stk, h12ee, h12am⟩ := step_DUP3_shape_strong s11 s12 f c11 none balV caller xV [] h11stk h11'
  rw [h11stk] at h12stk
  have hcd12 : s12.executionEnv.code = bytecode := by rw [h12ee]; exact hcd11
  have hp12 : s12.pc = UInt256.ofNat 57 := by rw [h12pc, hp11]; decide
  -- SWAP1 (57)
  have h12' := weth_fetch_step s12 s13 f c12 57 _ _ hcd12 hp12
    (by native_decide : decode bytecode (UInt256.ofNat 57) = some (.SWAP1, none)) h12
  obtain ⟨h13pc, h13stk, h13ee, h13am⟩ :=
    step_SWAP1_shape_strong s12 s13 f c12 none xV balV [caller, xV] h12stk h12'
  have hcd13 : s13.executionEnv.code = bytecode := by rw [h13ee]; exact hcd12
  have hp13 : s13.pc = UInt256.ofNat 58 := by rw [h13pc, hp12]; decide
  -- SUB (58)
  have h13' := weth_fetch_step s13 s14 f c13 58 _ _ hcd13 hp13
    (by native_decide : decode bytecode (UInt256.ofNat 58) = some (.SUB, none)) h13
  obtain ⟨h14pc, h14stk, h14ee, h14am⟩ :=
    step_SUB_shape_strong s13 s14 f c13 none balV xV [caller, xV] h13stk h13'
  have hcd14 : s14.executionEnv.code = bytecode := by rw [h14ee]; exact hcd13
  have hp14 : s14.pc = UInt256.ofNat 59 := by rw [h14pc, hp13]; decide
  -- SWAP1 (59)
  have h14' := weth_fetch_step s14 s15 f c14 59 _ _ hcd14 hp14
    (by native_decide : decode bytecode (UInt256.ofNat 59) = some (.SWAP1, none)) h14
  obtain ⟨h15pc, h15stk, h15ee, h15am⟩ :=
    step_SWAP1_shape_strong s14 s15 f c14 none (UInt256.sub balV xV) caller [xV] h14stk h14'
  have hcd15 : s15.executionEnv.code = bytecode := by rw [h15ee]; exact hcd14
  have hp15 : s15.pc = UInt256.ofNat 60 := by rw [h15pc, hp14]; decide
  -- SSTORE (60)
  have h15' := weth_fetch_step s15 s16 f c15 60 _ _ hcd15 hp15
    (by native_decide : decode bytecode (UInt256.ofNat 60) = some (.SSTORE, none)) h15
  have hee : s15.executionEnv = s0.executionEnv := by
    rw [h15ee, h14ee, h13ee, h12ee, h11ee, h10ee, h9ee, h8ee, h7ee, h6ee, h5ee, h4ee,
        h3ee, h2ee, h1ee]
  have ham : s15.accountMap = s0.accountMap := by
    rw [h15am, h14am, h13am, h12am, h11am, h10am, h9am, h8am, h7am, h6am, h5am, h4am,
        h3am, h2am, h1am]
  have h15co : s15.executionEnv.codeOwner = C := by rw [hee]; exact hCo
  have h15find : s15.accountMap.find? s15.executionEnv.codeOwner = some acc := by
    rw [ham, h15co]; exact hfind
  obtain h16am :=
    step_SSTORE_to_insert s15 s16 f c15 none caller (UInt256.sub balV xV) [xV] h15stk acc h15find h15'
  rw [h16am, h15co, ham, hcallerEq, hxVEq, hbalEq, hcallerEq]

/-! ## Dispatch routing

Given the selector a call carries, the dispatcher routes to the matching
function body (or reverts). Built on `weth_dispatcher_computes_selector`
plus the `EQ`/`JUMPI` branch. -/

/-- `EQ` of a value with itself is `1` (true). -/
theorem eq_self_eq_one (a : UInt256) : UInt256.eq a a = UInt256.ofNat 1 := by
  unfold UInt256.eq
  rw [show decide (a = a) = true by simp]
  rfl

/-- `EQ` of two distinct values is `0` (false). -/
theorem eq_ne_eq_zero {a b : UInt256} (h : a ≠ b) : UInt256.eq a b = UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [decide_eq_false h]
  rfl

/-- **A `deposit` selector routes to the deposit body.** From the entry
state, if the call's selector is `depositSelector`, then after the
dispatch prefix (`…; DUP1; PUSH4 depositSelector; EQ; PUSH2 depositLbl;
JUMPI`) execution is at `depositLbl` (PC 32, the deposit body) with the
selector left on the stack. -/
theorem weth_routes_deposit
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : EVM.State) (f c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℕ)
    (hcode : s0.executionEnv.code = bytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hsel : selectorOf s0.executionEnv.calldata = depositSelector)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9) :
    s9.pc = depositLbl ∧ s9.stack = [depositSelector] := by
  obtain ⟨hs4stk, hs4pc, hs4ee, _⟩ :=
    weth_dispatcher_computes_selector s0 s1 s2 s3 s4 f c0 c1 c2 c3 hcode hpc0 hstk0 h0 h1 h2 h3
  rw [hsel] at hs4stk
  have hcode4 : s4.executionEnv.code = bytecode := by rw [hs4ee]; exact hcode
  have h4' := weth_fetch_step s4 s5 f c4 6 _ _ hcode4 hs4pc
    (by native_decide : decode bytecode (UInt256.ofNat 6) = some (.DUP1, none)) h4
  obtain ⟨h5pc, h5stk, h5ee, _⟩ := step_DUP1_shape_strong s4 s5 f c4 none depositSelector [] hs4stk h4'
  rw [hs4stk] at h5stk
  have hcode5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hcode4
  have hpc5 : s5.pc = UInt256.ofNat 7 := by rw [h5pc, hs4pc]; decide
  have h5' := weth_fetch_step s5 s6 f c5 7 _ _ hcode5 hpc5
    (by native_decide : decode bytecode (UInt256.ofNat 7) = some (.Push .PUSH4, some (depositSelector, 4))) h5
  obtain ⟨h6pc, h6stk, h6ee, _⟩ := step_PUSH_shape_strong s5 s6 f c5 .PUSH4 (by decide) depositSelector 4 h5'
  rw [h5stk] at h6stk
  have hcode6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hcode5
  have hpc6 : s6.pc = UInt256.ofNat 12 := by rw [h6pc, hpc5]; decide
  have h6' := weth_fetch_step s6 s7 f c6 12 _ _ hcode6 hpc6
    (by native_decide : decode bytecode (UInt256.ofNat 12) = some (.EQ, none)) h6
  obtain ⟨h7pc, h7stk, h7ee, _⟩ :=
    step_EQ_value s6 s7 f c6 none depositSelector depositSelector [depositSelector] h6stk h6'
  have hcode7 : s7.executionEnv.code = bytecode := by rw [h7ee]; exact hcode6
  have hpc7 : s7.pc = UInt256.ofNat 13 := by rw [h7pc, hpc6]; decide
  have h7' := weth_fetch_step s7 s8 f c7 13 _ _ hcode7 hpc7
    (by native_decide : decode bytecode (UInt256.ofNat 13) = some (.Push .PUSH2, some (depositLbl, 2))) h7
  obtain ⟨h8pc, h8stk, h8ee, _⟩ := step_PUSH_shape_strong s7 s8 f c7 .PUSH2 (by decide) depositLbl 2 h7'
  rw [h7stk] at h8stk
  have hcode8 : s8.executionEnv.code = bytecode := by rw [h8ee]; exact hcode7
  have hpc8 : s8.pc = UInt256.ofNat 16 := by rw [h8pc, hpc7]; decide
  have h8' := weth_fetch_step s8 s9 f c8 16 _ _ hcode8 hpc8
    (by native_decide : decode bytecode (UInt256.ofNat 16) = some (.JUMPI, none)) h8
  obtain ⟨h9pc, h9stk, _, _⟩ :=
    step_JUMPI_shape_strong s8 s9 f c8 none depositLbl
      (UInt256.eq depositSelector depositSelector) [depositSelector] h8stk h8'
  refine ⟨?_, h9stk⟩
  rw [h9pc, eq_self_eq_one, if_pos (by decide)]

/-- **A `withdraw` selector routes to the withdraw body.** From the entry
state, if the call's selector is `withdrawSelector`, the dispatcher's
first comparison (against `depositSelector`) fails and falls through, the
second (against `withdrawSelector`) matches, and execution lands at
`withdrawLbl` (PC 42, the withdraw body) with an empty stack. -/
theorem weth_routes_withdraw
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 : EVM.State)
    (f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : ℕ)
    (hcode : s0.executionEnv.code = bytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hsel : selectorOf s0.executionEnv.calldata = withdrawSelector)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9)
    (h9 : EVM.step (f + 1) c9 (decode s9.executionEnv.code s9.pc) s9 = .ok s10)
    (h10 : EVM.step (f + 1) c10 (decode s10.executionEnv.code s10.pc) s10 = .ok s11)
    (h11 : EVM.step (f + 1) c11 (decode s11.executionEnv.code s11.pc) s11 = .ok s12)
    (h12 : EVM.step (f + 1) c12 (decode s12.executionEnv.code s12.pc) s12 = .ok s13) :
    s13.pc = withdrawLbl ∧ s13.stack = [] := by
  obtain ⟨hs4stk, hs4pc, hs4ee, _⟩ :=
    weth_dispatcher_computes_selector s0 s1 s2 s3 s4 f c0 c1 c2 c3 hcode hpc0 hstk0 h0 h1 h2 h3
  rw [hsel] at hs4stk
  have hcode4 : s4.executionEnv.code = bytecode := by rw [hs4ee]; exact hcode
  have h4' := weth_fetch_step s4 s5 f c4 6 _ _ hcode4 hs4pc
    (by native_decide : decode bytecode (UInt256.ofNat 6) = some (.DUP1, none)) h4
  obtain ⟨h5pc, h5stk, h5ee, _⟩ := step_DUP1_shape_strong s4 s5 f c4 none withdrawSelector [] hs4stk h4'
  rw [hs4stk] at h5stk
  have hcode5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hcode4
  have hpc5 : s5.pc = UInt256.ofNat 7 := by rw [h5pc, hs4pc]; decide
  have h5' := weth_fetch_step s5 s6 f c5 7 _ _ hcode5 hpc5
    (by native_decide : decode bytecode (UInt256.ofNat 7) = some (.Push .PUSH4, some (depositSelector, 4))) h5
  obtain ⟨h6pc, h6stk, h6ee, _⟩ := step_PUSH_shape_strong s5 s6 f c5 .PUSH4 (by decide) depositSelector 4 h5'
  rw [h5stk] at h6stk
  have hcode6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hcode5
  have hpc6 : s6.pc = UInt256.ofNat 12 := by rw [h6pc, hpc5]; decide
  have h6' := weth_fetch_step s6 s7 f c6 12 _ _ hcode6 hpc6
    (by native_decide : decode bytecode (UInt256.ofNat 12) = some (.EQ, none)) h6
  obtain ⟨h7pc, h7stk, h7ee, _⟩ :=
    step_EQ_value s6 s7 f c6 none depositSelector withdrawSelector [withdrawSelector] h6stk h6'
  have hcode7 : s7.executionEnv.code = bytecode := by rw [h7ee]; exact hcode6
  have hpc7 : s7.pc = UInt256.ofNat 13 := by rw [h7pc, hpc6]; decide
  have h7' := weth_fetch_step s7 s8 f c7 13 _ _ hcode7 hpc7
    (by native_decide : decode bytecode (UInt256.ofNat 13) = some (.Push .PUSH2, some (depositLbl, 2))) h7
  obtain ⟨h8pc, h8stk, h8ee, _⟩ := step_PUSH_shape_strong s7 s8 f c7 .PUSH2 (by decide) depositLbl 2 h7'
  rw [h7stk] at h8stk
  have hcode8 : s8.executionEnv.code = bytecode := by rw [h8ee]; exact hcode7
  have hpc8 : s8.pc = UInt256.ofNat 16 := by rw [h8pc, hpc7]; decide
  have h8' := weth_fetch_step s8 s9 f c8 16 _ _ hcode8 hpc8
    (by native_decide : decode bytecode (UInt256.ofNat 16) = some (.JUMPI, none)) h8
  obtain ⟨h9pc, h9stk, h9ee, _⟩ :=
    step_JUMPI_shape_strong s8 s9 f c8 none depositLbl
      (UInt256.eq depositSelector withdrawSelector) [withdrawSelector] h8stk h8'
  -- First gate falls through (deposit ≠ withdraw): s9.pc = 17, stack = [withdrawSelector].
  have hcode9 : s9.executionEnv.code = bytecode := by rw [h9ee]; exact hcode8
  have hpc9 : s9.pc = UInt256.ofNat 17 := by
    rw [h9pc, eq_ne_eq_zero selectors_distinct, if_neg (by decide), hpc8]; decide
  have h9' := weth_fetch_step s9 s10 f c9 17 _ _ hcode9 hpc9
    (by native_decide : decode bytecode (UInt256.ofNat 17) = some (.Push .PUSH4, some (withdrawSelector, 4))) h9
  obtain ⟨h10pc, h10stk, h10ee, _⟩ := step_PUSH_shape_strong s9 s10 f c9 .PUSH4 (by decide) withdrawSelector 4 h9'
  rw [h9stk] at h10stk
  have hcode10 : s10.executionEnv.code = bytecode := by rw [h10ee]; exact hcode9
  have hpc10 : s10.pc = UInt256.ofNat 22 := by rw [h10pc, hpc9]; decide
  have h10' := weth_fetch_step s10 s11 f c10 22 _ _ hcode10 hpc10
    (by native_decide : decode bytecode (UInt256.ofNat 22) = some (.EQ, none)) h10
  obtain ⟨h11pc, h11stk, h11ee, _⟩ :=
    step_EQ_value s10 s11 f c10 none withdrawSelector withdrawSelector [] h10stk h10'
  have hcode11 : s11.executionEnv.code = bytecode := by rw [h11ee]; exact hcode10
  have hpc11 : s11.pc = UInt256.ofNat 23 := by rw [h11pc, hpc10]; decide
  have h11' := weth_fetch_step s11 s12 f c11 23 _ _ hcode11 hpc11
    (by native_decide : decode bytecode (UInt256.ofNat 23) = some (.Push .PUSH2, some (withdrawLbl, 2))) h11
  obtain ⟨h12pc, h12stk, h12ee, _⟩ := step_PUSH_shape_strong s11 s12 f c11 .PUSH2 (by decide) withdrawLbl 2 h11'
  rw [h11stk] at h12stk
  have hcode12 : s12.executionEnv.code = bytecode := by rw [h12ee]; exact hcode11
  have hpc12 : s12.pc = UInt256.ofNat 26 := by rw [h12pc, hpc11]; decide
  have h12' := weth_fetch_step s12 s13 f c12 26 _ _ hcode12 hpc12
    (by native_decide : decode bytecode (UInt256.ofNat 26) = some (.JUMPI, none)) h12
  obtain ⟨h13pc, h13stk, _, _⟩ :=
    step_JUMPI_shape_strong s12 s13 f c12 none withdrawLbl
      (UInt256.eq withdrawSelector withdrawSelector) [] h12stk h12'
  refine ⟨?_, h13stk⟩
  rw [h13pc, eq_self_eq_one, if_pos (by decide)]

/-! ## Withdraw's outbound transfer (#3)

The withdraw block's call-setup sequence builds a `CALL` that sends `x`
wei to the caller with empty calldata. -/

/-- **`withdraw` sends `x` to the caller.** From the post-update point
(stack `[x]`, where `x` is the requested amount), the call-setup sequence
`PUSH1 0 ×4; DUP5; CALLER; GAS` leaves the seven `CALL` arguments on the
stack as `[gas, caller, x, 0, 0, 0, 0]` (and `x` still below): i.e. a
`CALL` to `caller` (`= addressSlot caller`'s address) with `value = x`,
`argsSize = 0` and `retSize = 0` — a bare ETH transfer of `x` to the
caller carrying no calldata. (The actual balance movement is then the
EVM's `CALL`/`Θ` semantics.) -/
theorem weth_withdraw_call_sends_x
    (s0 s1 s2 s3 s4 s5 s6 s7 : EVM.State) (f c0 c1 c2 c3 c4 c5 c6 : ℕ) (x : UInt256)
    (hcode : s0.executionEnv.code = bytecode)
    (hpc0 : s0.pc = UInt256.ofNat 61)
    (hstk0 : s0.stack = [x])
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7) :
    ∃ g, s7.stack =
      [g, UInt256.ofNat s0.executionEnv.source.val, x,
       UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, x] := by
  have h0' := weth_fetch_step s0 s1 f c0 61 _ _ hcode hpc0
    (by native_decide : decode bytecode (UInt256.ofNat 61) = some (.Push .PUSH1, some (UInt256.ofNat 0, 1))) h0
  obtain ⟨h1pc, h1stk, h1ee, _⟩ := step_PUSH1_shape_strong s0 s1 f c0 (UInt256.ofNat 0) h0'
  rw [hstk0] at h1stk
  have hcd1 : s1.executionEnv.code = bytecode := by rw [h1ee]; exact hcode
  have hp1 : s1.pc = UInt256.ofNat 63 := by rw [h1pc, hpc0]; decide
  have h1' := weth_fetch_step s1 s2 f c1 63 _ _ hcd1 hp1
    (by native_decide : decode bytecode (UInt256.ofNat 63) = some (.Push .PUSH1, some (UInt256.ofNat 0, 1))) h1
  obtain ⟨h2pc, h2stk, h2ee, _⟩ := step_PUSH1_shape_strong s1 s2 f c1 (UInt256.ofNat 0) h1'
  rw [h1stk] at h2stk
  have hcd2 : s2.executionEnv.code = bytecode := by rw [h2ee]; exact hcd1
  have hp2 : s2.pc = UInt256.ofNat 65 := by rw [h2pc, hp1]; decide
  have h2' := weth_fetch_step s2 s3 f c2 65 _ _ hcd2 hp2
    (by native_decide : decode bytecode (UInt256.ofNat 65) = some (.Push .PUSH1, some (UInt256.ofNat 0, 1))) h2
  obtain ⟨h3pc, h3stk, h3ee, _⟩ := step_PUSH1_shape_strong s2 s3 f c2 (UInt256.ofNat 0) h2'
  rw [h2stk] at h3stk
  have hcd3 : s3.executionEnv.code = bytecode := by rw [h3ee]; exact hcd2
  have hp3 : s3.pc = UInt256.ofNat 67 := by rw [h3pc, hp2]; decide
  have h3' := weth_fetch_step s3 s4 f c3 67 _ _ hcd3 hp3
    (by native_decide : decode bytecode (UInt256.ofNat 67) = some (.Push .PUSH1, some (UInt256.ofNat 0, 1))) h3
  obtain ⟨h4pc, h4stk, h4ee, _⟩ := step_PUSH1_shape_strong s3 s4 f c3 (UInt256.ofNat 0) h3'
  rw [h3stk] at h4stk
  have hcd4 : s4.executionEnv.code = bytecode := by rw [h4ee]; exact hcd3
  have hp4 : s4.pc = UInt256.ofNat 69 := by rw [h4pc, hp3]; decide
  have h4' := weth_fetch_step s4 s5 f c4 69 _ _ hcd4 hp4
    (by native_decide : decode bytecode (UInt256.ofNat 69) = some (.DUP5, none)) h4
  obtain ⟨h5pc, h5stk, h5ee, _⟩ :=
    step_DUP5_shape_strong s4 s5 f c4 none (UInt256.ofNat 0) (UInt256.ofNat 0)
      (UInt256.ofNat 0) (UInt256.ofNat 0) x [] h4stk h4'
  rw [h4stk] at h5stk
  have hcd5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hcd4
  have hp5 : s5.pc = UInt256.ofNat 70 := by rw [h5pc, hp4]; decide
  have h5' := weth_fetch_step s5 s6 f c5 70 _ _ hcd5 hp5
    (by native_decide : decode bytecode (UInt256.ofNat 70) = some (.CALLER, none)) h5
  obtain ⟨h6pc, h6stk, h6ee, _⟩ := step_CALLER_value s5 s6 f c5 none h5'
  rw [h5stk] at h6stk
  have hcd6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hcd5
  have hp6 : s6.pc = UInt256.ofNat 71 := by rw [h6pc, hp5]; decide
  have h6' := weth_fetch_step s6 s7 f c6 71 _ _ hcd6 hp6
    (by native_decide : decode bytecode (UInt256.ofNat 71) = some (.GAS, none)) h6
  obtain ⟨_, ⟨g, h7stk⟩, _, _⟩ := step_GAS_shape_strong s6 s7 f c6 none h6'
  refine ⟨g, ?_⟩
  rw [h7stk, h6stk]
  have hee : s5.executionEnv = s0.executionEnv := by rw [h5ee, h4ee, h3ee, h2ee, h1ee]
  rw [hee]

/-! ## Unknown selector: reverts with no state change (#4)

A call whose selector matches neither entry point passes through both
dispatch comparisons (both `JUMPI`s fall through, so neither function
body is entered) and changes no account — the dispatcher only runs
stack/calldata ops, never `SSTORE`/`CALL`. Execution then reaches the
`REVERT` at PC 31. -/

/-- **Unknown selector ⇒ no body entered, no state change.** From the
entry state, if the call's selector is neither `depositSelector` nor
`withdrawSelector`, then: the first `JUMPI` falls through
(`s9.pc = s8.pc + 1`, not `depositLbl`), the second `JUMPI` falls through
(`s13.pc = s12.pc + 1`, not `withdrawLbl`), and the account map is
unchanged across the whole dispatch (`s15.accountMap = s0.accountMap`).
Execution thus proceeds to the dispatcher's `REVERT` having entered no
function and modified no state. -/
theorem weth_unknown_selector_no_state_change
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : EVM.State)
    (f c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : ℕ)
    (hcode : s0.executionEnv.code = bytecode)
    (hpc0 : s0.pc = UInt256.ofNat 0)
    (hstk0 : s0.stack = [])
    (hne_dep : selectorOf s0.executionEnv.calldata ≠ depositSelector)
    (hne_wd : selectorOf s0.executionEnv.calldata ≠ withdrawSelector)
    (h0 : EVM.step (f + 1) c0 (decode s0.executionEnv.code s0.pc) s0 = .ok s1)
    (h1 : EVM.step (f + 1) c1 (decode s1.executionEnv.code s1.pc) s1 = .ok s2)
    (h2 : EVM.step (f + 1) c2 (decode s2.executionEnv.code s2.pc) s2 = .ok s3)
    (h3 : EVM.step (f + 1) c3 (decode s3.executionEnv.code s3.pc) s3 = .ok s4)
    (h4 : EVM.step (f + 1) c4 (decode s4.executionEnv.code s4.pc) s4 = .ok s5)
    (h5 : EVM.step (f + 1) c5 (decode s5.executionEnv.code s5.pc) s5 = .ok s6)
    (h6 : EVM.step (f + 1) c6 (decode s6.executionEnv.code s6.pc) s6 = .ok s7)
    (h7 : EVM.step (f + 1) c7 (decode s7.executionEnv.code s7.pc) s7 = .ok s8)
    (h8 : EVM.step (f + 1) c8 (decode s8.executionEnv.code s8.pc) s8 = .ok s9)
    (h9 : EVM.step (f + 1) c9 (decode s9.executionEnv.code s9.pc) s9 = .ok s10)
    (h10 : EVM.step (f + 1) c10 (decode s10.executionEnv.code s10.pc) s10 = .ok s11)
    (h11 : EVM.step (f + 1) c11 (decode s11.executionEnv.code s11.pc) s11 = .ok s12)
    (h12 : EVM.step (f + 1) c12 (decode s12.executionEnv.code s12.pc) s12 = .ok s13)
    (h13 : EVM.step (f + 1) c13 (decode s13.executionEnv.code s13.pc) s13 = .ok s14)
    (h14 : EVM.step (f + 1) c14 (decode s14.executionEnv.code s14.pc) s14 = .ok s15) :
    s9.pc = s8.pc + ⟨1⟩ ∧ s13.pc = s12.pc + ⟨1⟩ ∧ s15.accountMap = s0.accountMap := by
  obtain ⟨hs4stk, hs4pc, hs4ee, hs4am⟩ :=
    weth_dispatcher_computes_selector s0 s1 s2 s3 s4 f c0 c1 c2 c3 hcode hpc0 hstk0 h0 h1 h2 h3
  have hcode4 : s4.executionEnv.code = bytecode := by rw [hs4ee]; exact hcode
  -- DUP1 (6)
  have h4' := weth_fetch_step s4 s5 f c4 6 _ _ hcode4 hs4pc
    (by native_decide : decode bytecode (UInt256.ofNat 6) = some (.DUP1, none)) h4
  obtain ⟨h5pc, h5stk, h5ee, a4⟩ :=
    step_DUP1_shape_strong s4 s5 f c4 none (selectorOf s0.executionEnv.calldata) [] hs4stk h4'
  rw [hs4stk] at h5stk
  have hcd5 : s5.executionEnv.code = bytecode := by rw [h5ee]; exact hcode4
  have hp5 : s5.pc = UInt256.ofNat 7 := by rw [h5pc, hs4pc]; decide
  -- PUSH4 dep (7)
  have h5' := weth_fetch_step s5 s6 f c5 7 _ _ hcd5 hp5
    (by native_decide : decode bytecode (UInt256.ofNat 7) = some (.Push .PUSH4, some (depositSelector, 4))) h5
  obtain ⟨h6pc, h6stk, h6ee, a5⟩ := step_PUSH_shape_strong s5 s6 f c5 .PUSH4 (by decide) depositSelector 4 h5'
  rw [h5stk] at h6stk
  have hcd6 : s6.executionEnv.code = bytecode := by rw [h6ee]; exact hcd5
  have hp6 : s6.pc = UInt256.ofNat 12 := by rw [h6pc, hp5]; decide
  -- EQ (12)
  have h6' := weth_fetch_step s6 s7 f c6 12 _ _ hcd6 hp6
    (by native_decide : decode bytecode (UInt256.ofNat 12) = some (.EQ, none)) h6
  obtain ⟨h7pc, h7stk, h7ee, a6⟩ :=
    step_EQ_value s6 s7 f c6 none depositSelector (selectorOf s0.executionEnv.calldata)
      [selectorOf s0.executionEnv.calldata] h6stk h6'
  have hcd7 : s7.executionEnv.code = bytecode := by rw [h7ee]; exact hcd6
  have hp7 : s7.pc = UInt256.ofNat 13 := by rw [h7pc, hp6]; decide
  -- PUSH2 depLbl (13)
  have h7' := weth_fetch_step s7 s8 f c7 13 _ _ hcd7 hp7
    (by native_decide : decode bytecode (UInt256.ofNat 13) = some (.Push .PUSH2, some (depositLbl, 2))) h7
  obtain ⟨h8pc, h8stk, h8ee, a7⟩ := step_PUSH_shape_strong s7 s8 f c7 .PUSH2 (by decide) depositLbl 2 h7'
  rw [h7stk] at h8stk
  have hcd8 : s8.executionEnv.code = bytecode := by rw [h8ee]; exact hcd7
  have hp8 : s8.pc = UInt256.ofNat 16 := by rw [h8pc, hp7]; decide
  -- JUMPI (16): not taken
  have h8' := weth_fetch_step s8 s9 f c8 16 _ _ hcd8 hp8
    (by native_decide : decode bytecode (UInt256.ofNat 16) = some (.JUMPI, none)) h8
  obtain ⟨h9pc, h9stk, h9ee, a8⟩ :=
    step_JUMPI_shape_strong s8 s9 f c8 none depositLbl
      (UInt256.eq depositSelector (selectorOf s0.executionEnv.calldata))
      [selectorOf s0.executionEnv.calldata] h8stk h8'
  have hcd9 : s9.executionEnv.code = bytecode := by rw [h9ee]; exact hcd8
  have hp9 : s9.pc = UInt256.ofNat 17 := by
    rw [h9pc, eq_ne_eq_zero (Ne.symm hne_dep), if_neg (by decide), hp8]; decide
  -- PUSH4 wd (17)
  have h9' := weth_fetch_step s9 s10 f c9 17 _ _ hcd9 hp9
    (by native_decide : decode bytecode (UInt256.ofNat 17) = some (.Push .PUSH4, some (withdrawSelector, 4))) h9
  obtain ⟨h10pc, h10stk, h10ee, a9⟩ := step_PUSH_shape_strong s9 s10 f c9 .PUSH4 (by decide) withdrawSelector 4 h9'
  rw [h9stk] at h10stk
  have hcd10 : s10.executionEnv.code = bytecode := by rw [h10ee]; exact hcd9
  have hp10 : s10.pc = UInt256.ofNat 22 := by rw [h10pc, hp9]; decide
  -- EQ (22)
  have h10' := weth_fetch_step s10 s11 f c10 22 _ _ hcd10 hp10
    (by native_decide : decode bytecode (UInt256.ofNat 22) = some (.EQ, none)) h10
  obtain ⟨h11pc, h11stk, h11ee, a10⟩ :=
    step_EQ_value s10 s11 f c10 none withdrawSelector (selectorOf s0.executionEnv.calldata) [] h10stk h10'
  have hcd11 : s11.executionEnv.code = bytecode := by rw [h11ee]; exact hcd10
  have hp11 : s11.pc = UInt256.ofNat 23 := by rw [h11pc, hp10]; decide
  -- PUSH2 wdLbl (23)
  have h11' := weth_fetch_step s11 s12 f c11 23 _ _ hcd11 hp11
    (by native_decide : decode bytecode (UInt256.ofNat 23) = some (.Push .PUSH2, some (withdrawLbl, 2))) h11
  obtain ⟨h12pc, h12stk, h12ee, a11⟩ := step_PUSH_shape_strong s11 s12 f c11 .PUSH2 (by decide) withdrawLbl 2 h11'
  rw [h11stk] at h12stk
  have hcd12 : s12.executionEnv.code = bytecode := by rw [h12ee]; exact hcd11
  have hp12 : s12.pc = UInt256.ofNat 26 := by rw [h12pc, hp11]; decide
  -- JUMPI (26): not taken
  have h12' := weth_fetch_step s12 s13 f c12 26 _ _ hcd12 hp12
    (by native_decide : decode bytecode (UInt256.ofNat 26) = some (.JUMPI, none)) h12
  obtain ⟨h13pc, h13stk, h13ee, a12⟩ :=
    step_JUMPI_shape_strong s12 s13 f c12 none withdrawLbl
      (UInt256.eq withdrawSelector (selectorOf s0.executionEnv.calldata)) [] h12stk h12'
  have hcd13 : s13.executionEnv.code = bytecode := by rw [h13ee]; exact hcd12
  have hp13 : s13.pc = UInt256.ofNat 27 := by
    rw [h13pc, eq_ne_eq_zero (Ne.symm hne_wd), if_neg (by decide), hp12]; decide
  -- PUSH1 0 (27)
  have h13' := weth_fetch_step s13 s14 f c13 27 _ _ hcd13 hp13
    (by native_decide : decode bytecode (UInt256.ofNat 27) = some (.Push .PUSH1, some (UInt256.ofNat 0, 1))) h13
  obtain ⟨h14pc, _, h14ee, a13⟩ := step_PUSH1_shape_strong s13 s14 f c13 (UInt256.ofNat 0) h13'
  have hcd14 : s14.executionEnv.code = bytecode := by rw [h14ee]; exact hcd13
  have hp14 : s14.pc = UInt256.ofNat 29 := by rw [h14pc, hp13]; decide
  -- PUSH1 0 (29)
  have h14' := weth_fetch_step s14 s15 f c14 29 _ _ hcd14 hp14
    (by native_decide : decode bytecode (UInt256.ofNat 29) = some (.Push .PUSH1, some (UInt256.ofNat 0, 1))) h14
  obtain ⟨_, _, _, a14⟩ := step_PUSH1_shape_strong s14 s15 f c14 (UInt256.ofNat 0) h14'
  refine ⟨?_, ?_, ?_⟩
  · rw [h9pc, eq_ne_eq_zero (Ne.symm hne_dep), if_neg (by decide)]
  · rw [h13pc, eq_ne_eq_zero (Ne.symm hne_wd), if_neg (by decide)]
  · rw [a14, a13, a12, a11, a10, a9, a8, a7, a6, a5, a4, hs4am]

end EvmSmith.Weth
