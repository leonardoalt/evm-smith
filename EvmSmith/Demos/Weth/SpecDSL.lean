import EvmSmith.Demos.Weth.Behaviour

/-!
# WETH — a tiny spec eDSL

Vocabulary that lets the behavioural guarantees in `Spec.lean` read like a
Solidity-style pre/post spec (`balance[msg.sender]`, `old …`, `after run:`,
`untouched (others)`, `returndata = empty`). Every piece here is a thin
`def`/`notation`; the readable theorems prove by delegation to the
`weth_*_run_impl` engine in `Behaviour.lean`, so Lean checks that the
pretty statement *is* the proven one.
-/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Layer1

/-! ## Entry points -/

/-- The contract's two ABI entry points, plus the catch-all for any other
selector. -/
inductive Entry | deposit | withdraw | unknown
deriving DecidableEq

/-! ## Running the contract (fuel hidden)

`Halts s s' o` : running WETH's gas-free interpreter from `s` reaches a
halt at `s'`, returning `o`. The interpreter fuel is existentially hidden. -/
def Halts (s s' : EVM.State) (o : ByteArray) : Prop :=
  ∃ callFuel N, wethRun callFuel N s = some (s', o)

/-! ## "This is a call to f"

`Calls e s` bundles the genuine call-entry conditions: we start at the
contract's first instruction (`pc = 0`, empty stack), the code is WETH's,
the account exists, and the ABI selector matches entry point `e`. -/
def Calls (e : Entry) (s : EVM.State) : Prop :=
  s.executionEnv.code = wethBytecode
  ∧ s.pc = UInt256.ofNat 0
  ∧ s.stack = []
  ∧ (∃ acc, s.accountMap.find? s.executionEnv.codeOwner = some acc)
  ∧ (match e with
     | .deposit  => functionSelector s.executionEnv.calldata = depositSelector
     | .withdraw => functionSelector s.executionEnv.calldata = withdrawSelector
     | .unknown  => functionSelector s.executionEnv.calldata ≠ depositSelector
                  ∧ functionSelector s.executionEnv.calldata ≠ withdrawSelector)

/-! ## The no-reentrancy assumption

`NoReentrancy s` : the external `CALL` does not reenter to change the
caller's recorded balance at this contract (the codeless-recipient
assumption `withdraw` needs end-to-end). Quantified over all interpreter
fuels so the statement need not mention fuel. -/
def NoReentrancy (s : EVM.State) : Prop :=
  ∀ callFuel (sa sb : EVM.State),
    EVM.step (callFuel + 1) 0 (some (.CALL, none)) sa = .ok sb →
    recordedBalance sb.accountMap s.executionEnv.codeOwner s.executionEnv.source
      = recordedBalance sa.accountMap s.executionEnv.codeOwner s.executionEnv.source

/-! ## Bridge lemmas

Each accessor below is *definitionally* its `Behaviour.lean` counterpart;
these `rfl` lemmas make that explicit (and let the readable proofs rewrite
between the two views). -/

theorem calls_deposit_iff (s : EVM.State) :
    Calls .deposit s ↔
      (s.executionEnv.code = wethBytecode ∧ s.pc = UInt256.ofNat 0 ∧ s.stack = []
       ∧ (∃ acc, s.accountMap.find? s.executionEnv.codeOwner = some acc)
       ∧ functionSelector s.executionEnv.calldata = depositSelector) := Iff.rfl

theorem halts_iff (s s' : EVM.State) (o : ByteArray) :
    Halts s s' o ↔ ∃ callFuel N, wethRun callFuel N s = some (s', o) := Iff.rfl

/-! ## Solidity-style surface notation

The notations below are bound, by convention, to a pre-state `s`, a
post-state `s'`, and return data `o`. `ensures BODY` is the postcondition
of running the contract: it introduces `s'`/`o` and the run, and inside
`BODY` bare `balance[a]` reads the post-state, `old balance[a]` the
pre-state (both at the call's own contract). `sender`/`value`/`amount` are
the call's `msg.sender` / `msg.value` / decoded `uint256` argument. -/

set_option hygiene false in
section
notation "sender" => s.executionEnv.source
notation "value"  => s.executionEnv.weiValue
notation "amount" => EvmYul.State.calldataload s.toState (UInt256.ofNat 4)
notation:max "balance" "[" a "]"        => recordedBalance s'.accountMap s.executionEnv.codeOwner a
notation:max "old" "balance" "[" a "]"  => recordedBalance s.accountMap s.executionEnv.codeOwner a
notation "returndata" => o
notation "empty"      => ByteArray.empty
notation "storage"     => s'.accountMap
notation "old" "storage" => s.accountMap
notation "untouched" "(" "others" ")" =>
  (∀ b, b ≠ s.executionEnv.source →
    recordedBalance s'.accountMap s.executionEnv.codeOwner b
      = recordedBalance s.accountMap s.executionEnv.codeOwner b)

macro "ensures " body:term : term =>
  `(∀ {s' : EvmYul.EVM.State} {o : ByteArray}, Halts s s' o → $body)
end

/-- Faithful 256-bit addition is commutative (for the idiomatic
`balance += value` reading in the deposit spec). -/
theorem uint256_add_comm (a b : UInt256) : a + b = b + a := by
  show UInt256.add a b = UInt256.add b a
  unfold UInt256.add
  congr 1
  apply Fin.ext
  rw [Fin.val_add, Fin.val_add, Nat.add_comm]

/-! ## Solvency vocabulary

The `≤`-style solvency property and the transaction wrappers behind
`weth_is_always_solvent`. Readable `ℕ`-valued wrappers, *definitionally*
equal to the proof-side predicates (the `*_iff_*` bridges witness it). -/

/-- WETH's actual on-chain ETH balance (in wei) at `weth`. Unknown ⇒ `0`. -/
def ethBalance (σ : AccountMap .EVM) (weth : Address) : ℕ :=
  balanceOf σ weth

/-- User `user`'s WETH token balance *recorded in storage* (in wei). -/
def tokenBalanceOf (σ : AccountMap .EVM) (weth user : Address) : ℕ :=
  ((σ.find? weth).map
      (fun acc => (acc.storage.findD (tokenBalanceSlot user) ⟨0⟩).toNat)).getD 0

/-- The total WETH token supply recorded in storage (`storageSum`). -/
def recordedTokenSupply (σ : AccountMap .EVM) (weth : Address) : ℕ :=
  storageSum σ weth

/-- **Solvency.** Recorded token supply never exceeds the ETH actually
held: `recordedTokenSupply σ weth ≤ ethBalance σ weth`. -/
def Solvent (σ : AccountMap .EVM) (weth : Address) : Prop :=
  recordedTokenSupply σ weth ≤ ethBalance σ weth

/-- `Solvent` is definitionally the proof-side invariant `WethInv`. -/
theorem solvent_iff_wethInv (σ : AccountMap .EVM) (weth : Address) :
    Solvent σ weth ↔ WethInv σ weth := Iff.rfl

/-- `Solvent` is definitionally the framework's `StorageSumLeBalance`. -/
theorem solvent_iff_storageSumLeBalance (σ : AccountMap .EVM) (weth : Address) :
    Solvent σ weth ↔ StorageSumLeBalance σ weth := Iff.rfl

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

/-- WETH is solvent after running `tx` (vacuous if the tx reverts). -/
def SolventAfter (ctx : ExecContext) (σ : AccountMap .EVM)
    (tx : Transaction) (S_T weth : Address) : Prop :=
  match runTx ctx σ tx S_T with
  | .ok (σ', _, _, _) => Solvent σ' weth
  | .error _ => True

/-- The deployment / chain-state bundle the solvency guarantee is
conditional on (exactly the proof-side `WethAssumptions`). -/
abbrev SolvencyAssumptions (ctx : ExecContext) (σ : AccountMap .EVM)
    (tx : Transaction) (S_T weth : Address) : Prop :=
  WethAssumptions σ ctx.fuel ctx.baseFee ctx.block ctx.genesis ctx.history tx S_T weth

end EvmSmith.Weth
