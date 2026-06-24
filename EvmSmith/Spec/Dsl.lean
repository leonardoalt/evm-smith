import EvmYul.Frame

/-!
# A tiny, contract-agnostic EVM spec eDSL

Reusable vocabulary for stating a contract's behaviour as a Solidity-style
pre/post spec, with **no** dependence on any particular contract. A
contract-specific spec layer (e.g. `Demos/Weth/SpecDSL.lean`) builds on
this with its own `balance[·]`, entry points, etc.

What lives here:

* `evmRun` — a gas-free interpreter: iterate the real `EVM.step`, decoding
  each instruction from the running account's own code, until a halt. It
  is the EVM frame loop `EVM.X` with gas ignored (the one modelling
  assumption); nothing in it is contract-specific.
* `Halts` / the `ensures` macro and the generic run accessors
  (`sender`/`value`/`returndata`/`storage`).
* transaction-level plumbing (`ExecContext`, `runTx`, `afterTx`) and
  `ethBalance`.
-/

namespace EvmSmith.Spec

open EvmYul EvmYul.EVM EvmYul.Frame Batteries

/-- An on-chain account / contract address. -/
abbrev Address := AccountAddress

/-- Cosmetic label for a contract-enforced precondition (reads like
Solidity's `require`). Definitionally just `p`, so it adds no logical
content — it only makes `requires p → …` read as a requirement rather
than an implication. -/
abbrev requires (p : Prop) : Prop := p

/-- Cosmetic label for an *external* assumption a guarantee is conditional
on (something not enforced by the contract, e.g. the recipient not
reentering). Definitionally just `p`. -/
abbrev assuming (p : Prop) : Prop := p

/-! ## The gas-free interpreter -/

/-- The halting opcodes (where `EVM.X` stops the frame). -/
def isHaltOp : Operation .EVM → Bool
  | .STOP => true
  | .REVERT => true
  | .RETURN => true
  | _ => false

/-- The frame's return data at a halt (matching `EVM.X`'s `H`): the
returned memory slice for `RETURN`/`REVERT`, empty for `STOP`. -/
def haltOutput (s : EVM.State) : Operation .EVM → ByteArray
  | .RETURN => s.toMachineState.H_return
  | .REVERT => s.toMachineState.H_return
  | _ => .empty

/-- Run gas-free from `s`: fetch-and-`EVM.step` until a halt opcode,
returning the (pre-halt) state and the halt's return data. `callFuel`
bounds any nested call; the outer `ℕ` bounds the number of instructions. -/
def evmRun (callFuel : ℕ) : ℕ → EVM.State → Option (EVM.State × ByteArray)
  | 0, _ => none
  | n + 1, s =>
    match decode s.executionEnv.code s.pc with
    | none => none
    | some (op, arg) =>
      if isHaltOp op then some (s, haltOutput s op)
      else
        match EVM.step (callFuel + 1) 0 (some (op, arg)) s with
        | .ok s' => evmRun callFuel n s'
        | .error _ => none

/-- One non-halting `evmRun` step: peel off the `EVM.step` fact and the
remaining run. -/
theorem evmRun_succ_step
    (callFuel n : ℕ) (s : EVM.State) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (res : EVM.State × ByteArray)
    (hdec : decode s.executionEnv.code s.pc = some (op, arg))
    (hnh : isHaltOp op = false)
    (hrun : evmRun callFuel (n + 1) s = some res) :
    ∃ s1, EVM.step (callFuel + 1) 0 (some (op, arg)) s = .ok s1
        ∧ evmRun callFuel n s1 = some res := by
  rw [evmRun, hdec] at hrun
  simp only [hnh] at hrun
  cases hstep : EVM.step (callFuel + 1) 0 (some (op, arg)) s with
  | error e => rw [hstep] at hrun; simp at hrun
  | ok s1 => rw [hstep] at hrun; exact ⟨s1, rfl, hrun⟩

/-- A halting `evmRun` step returns the current state and the halt
output. -/
theorem evmRun_halt_step
    (callFuel n : ℕ) (s : EVM.State) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (res : EVM.State × ByteArray)
    (hdec : decode s.executionEnv.code s.pc = some (op, arg))
    (hh : isHaltOp op = true)
    (hrun : evmRun callFuel (n + 1) s = some res) :
    res = (s, haltOutput s op) := by
  rw [evmRun, hdec] at hrun
  simp only [hh, if_true] at hrun
  exact (Option.some.inj hrun).symm

/-! ## Per-opcode helpers (contract-agnostic) -/

/-- `SSTORE` advances the pc by one and preserves the execution
environment. -/
theorem step_SSTORE_pc_ee
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (slot newVal : UInt256) (tl : Stack UInt256)
    (hStk : s.stack = slot :: newVal :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.SSTORE, arg)) s = .ok s') :
    s'.pc = s.pc + UInt256.ofNat 1 ∧ s'.executionEnv = s.executionEnv := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchBinaryStateOp EVM.binaryStateOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop2, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  refine ⟨?_, ?_⟩
  · simp only [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]
  · show (EvmYul.State.sstore s.toState slot newVal).executionEnv = s.executionEnv
    rw [sstore_preserves_executionEnv]

/-- `ISZERO` preserves the account map (a pure stack op). -/
theorem step_ISZERO_am
    (s s' : EVM.State) (f' cost : ℕ) (arg : Option (UInt256 × Nat))
    (hd : UInt256) (tl : Stack UInt256) (hStk : s.stack = hd :: tl)
    (hStep : EVM.step (f' + 1) cost (some (.ISZERO, arg)) s = .ok s') :
    s'.accountMap = s.accountMap := by
  unfold EVM.step at hStep
  simp only [bind, Except.bind, pure, Except.pure] at hStep
  unfold EvmYul.step at hStep
  simp only [Id.run] at hStep
  unfold dispatchUnary EVM.execUnOp at hStep
  rw [hStk] at hStep
  simp only [Stack.pop, Id_run_ok, Except.ok.injEq] at hStep
  subst hStep
  simp only [accountMap_replaceStackAndIncrPC]

/-- Faithful 256-bit addition is commutative. -/
theorem uint256_add_comm (a b : UInt256) : a + b = b + a := by
  show UInt256.add a b = UInt256.add b a
  unfold UInt256.add
  congr 1
  apply Fin.ext
  rw [Fin.val_add, Fin.val_add, Nat.add_comm]

/-! ## Running the contract (fuel hidden)

`Halts s s' o` : running the gas-free interpreter from `s` reaches a halt
at `s'`, returning `o`. The interpreter fuel is existentially hidden. -/
def Halts (s s' : EVM.State) (o : ByteArray) : Prop :=
  ∃ callFuel N, evmRun callFuel N s = some (s', o)

/-! ## Running up to the first external call

`evmRunToCall` is like `evmRun` but stops *just before* the contract
executes its first `CALL`, returning that pre-call state — the point at
which the contract's own effects are done but it has not yet handed
control to anyone. `ReachesCall s s'` : that point is `s'`. -/

/-- Is this the external-call opcode? -/
def isCallOp : Operation .EVM → Bool
  | .CALL => true
  | _ => false

/-- Run gas-free from `s` until just before the first `CALL`, returning
that pre-call state (or `none` if it halts first / runs out of fuel). -/
def evmRunToCall (callFuel : ℕ) : ℕ → EVM.State → Option EVM.State
  | 0, _ => none
  | n + 1, s =>
    match decode s.executionEnv.code s.pc with
    | none => none
    | some (op, arg) =>
      if isCallOp op then some s
      else if isHaltOp op then none
      else
        match EVM.step (callFuel + 1) 0 (some (op, arg)) s with
        | .ok s' => evmRunToCall callFuel n s'
        | .error _ => none

/-- One non-call, non-halt `evmRunToCall` step. -/
theorem evmRunToCall_succ_step
    (callFuel n : ℕ) (s : EVM.State) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (res : EVM.State)
    (hdec : decode s.executionEnv.code s.pc = some (op, arg))
    (hnc : isCallOp op = false) (hnh : isHaltOp op = false)
    (hrun : evmRunToCall callFuel (n + 1) s = some res) :
    ∃ s1, EVM.step (callFuel + 1) 0 (some (op, arg)) s = .ok s1
        ∧ evmRunToCall callFuel n s1 = some res := by
  rw [evmRunToCall, hdec] at hrun
  simp only [hnc, hnh] at hrun
  cases hstep : EVM.step (callFuel + 1) 0 (some (op, arg)) s with
  | error e => rw [hstep] at hrun; simp at hrun
  | ok s1 => rw [hstep] at hrun; exact ⟨s1, rfl, hrun⟩

/-- At the `CALL`, `evmRunToCall` returns the (pre-call) current state. -/
theorem evmRunToCall_at_call
    (callFuel n : ℕ) (s : EVM.State) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
    (res : EVM.State)
    (hdec : decode s.executionEnv.code s.pc = some (op, arg))
    (hc : isCallOp op = true)
    (hrun : evmRunToCall callFuel (n + 1) s = some res) :
    res = s := by
  rw [evmRunToCall, hdec] at hrun
  simp only [hc, if_true] at hrun
  exact (Option.some.inj hrun).symm

/-- The contract reaches the point just before its first external `CALL`,
in state `s'`. -/
def ReachesCall (s s' : EVM.State) : Prop :=
  ∃ callFuel N, evmRunToCall callFuel N s = some s'

/-! ## Solidity-style surface notation

Bound, by convention, to a pre-state `s`, a post-state `s'`, and return
data `o`. `ensures BODY` is the postcondition of running the contract: it
introduces `s'`/`o` and the run. `sender`/`value` are the call's
`msg.sender` / `msg.value`. -/

set_option hygiene false in
section
notation "sender" => s.executionEnv.source
notation "value"  => s.executionEnv.weiValue
notation "returndata" => o
notation "empty"      => ByteArray.empty
notation "storage"        => s'.accountMap
notation "old" "storage"  => s.accountMap

macro "ensures " body:term : term =>
  `(∀ {s' : EvmYul.EVM.State} {o : ByteArray}, EvmSmith.Spec.Halts s s' o → $body)

macro "before_call" ":" body:term : term =>
  `(∀ {s' : EvmYul.EVM.State}, EvmSmith.Spec.ReachesCall s s' → $body)
end

/-! ## Transaction-level plumbing -/

/-- The ambient chain/block plumbing `EVM.Υ` needs besides the pre-state
and the transaction. -/
structure ExecContext where
  fuel    : ℕ
  baseFee : ℕ
  block   : BlockHeader
  genesis : BlockHeader
  history : ProcessedBlocks

/-- Run one transaction `tx` (sender `S_T`) on `σ` in context `ctx`. Thin
wrapper over `EVM.Υ`; returns `.ok` post-state or `.error`. -/
def runTx (ctx : ExecContext) (σ : AccountMap .EVM)
    (tx : Transaction) (S_T : Address) :=
  EVM.Υ ctx.fuel σ ctx.baseFee ctx.block ctx.genesis ctx.history tx S_T

/-- A predicate `Q` holds of the post-state after running `tx` (vacuous if
the transaction reverts). -/
def afterTx (ctx : ExecContext) (σ : AccountMap .EVM)
    (tx : Transaction) (S_T : Address) (Q : AccountMap .EVM → Prop) : Prop :=
  match runTx ctx σ tx S_T with
  | .ok (σ', _, _, _) => Q σ'
  | .error _ => True

/-- An account's on-chain ETH balance (in wei). Unknown account ⇒ `0`. -/
def ethBalance (σ : AccountMap .EVM) (a : Address) : ℕ :=
  balanceOf σ a

end EvmSmith.Spec
