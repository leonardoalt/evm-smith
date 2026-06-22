import EvmSmith.Demos.Weth.Behaviour
import EvmSmith.Spec.Dsl

/-!
# WETH-specific spec vocabulary

The WETH layer on top of the contract-agnostic `EvmSmith/Spec/Dsl.lean`
(which provides `evmRun`/`Halts`/`ensures`/`sender`/`value`/`returndata`/
`storage`, the transaction plumbing `ExecContext`/`runTx`/`afterTx`, and
`ethBalance`). Here live only the pieces that mention WETH: its entry
points, its `balance[·]` ledger (the address-as-slot layout), its ABI
argument `amount`, the token-solvency property, and the no-reentrancy
assumption. Each readable theorem in `Spec.lean` proves by delegation to
the `weth_*_run_impl` engine in `Behaviour.lean`.
-/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Layer1 EvmSmith.Spec

/-! ## Entry points -/

/-- WETH's two ABI entry points, plus the catch-all for any other
selector. -/
inductive Entry | deposit | withdraw | unknown
deriving DecidableEq

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
caller's recorded balance at this contract.

This is an **assumption**, not a theorem — and it is *not* what makes WETH
safe. WETH's *solvency* (`weth_is_always_solvent`) is proven
**unconditionally**, against arbitrary reentering recipients: the `SSTORE`
runs before the `CALL` (checks-effects-interactions), so a reentrant
`withdraw` sees the already-decremented balance and the `LT` gate blocks
over-withdrawal. `NoReentrancy` is needed only for `withdraw`'s *exact*
end-balance (`balance = old − amount`): a reentering recipient could call
`deposit` during the callback and change the final figure, so the precise
delta — unlike solvency — is conditional. It holds vacuously for a
codeless (EOA) recipient. Quantified over all interpreter fuels so the
statement need not mention fuel. -/
def NoReentrancy (s : EVM.State) : Prop :=
  ∀ callFuel (sa sb : EVM.State),
    EVM.step (callFuel + 1) 0 (some (.CALL, none)) sa = .ok sb →
    recordedBalance sb.accountMap s.executionEnv.codeOwner s.executionEnv.source
      = recordedBalance sa.accountMap s.executionEnv.codeOwner s.executionEnv.source

/-- `Calls .deposit s` unfolded — the explicit entry conditions. -/
theorem calls_deposit_iff (s : EVM.State) :
    Calls .deposit s ↔
      (s.executionEnv.code = wethBytecode ∧ s.pc = UInt256.ofNat 0 ∧ s.stack = []
       ∧ (∃ acc, s.accountMap.find? s.executionEnv.codeOwner = some acc)
       ∧ functionSelector s.executionEnv.calldata = depositSelector) := Iff.rfl

/-! ## WETH-specific surface notation

On top of the generic `sender`/`value`/`returndata`/`storage`: the token
`balance[a]` ledger (post-state by default, `old balance[a]` for the
pre-state, both at the call's own contract) and the ABI `amount`. -/

set_option hygiene false in
section
notation "amount" => EvmYul.State.calldataload s.toState (UInt256.ofNat 4)
notation:max "balance" "[" a "]"        => recordedBalance s'.accountMap s.executionEnv.codeOwner a
notation:max "old" "balance" "[" a "]"  => recordedBalance s.accountMap s.executionEnv.codeOwner a
notation "untouched" "(" "others" ")" =>
  (∀ b, b ≠ s.executionEnv.source →
    recordedBalance s'.accountMap s.executionEnv.codeOwner b
      = recordedBalance s.accountMap s.executionEnv.codeOwner b)
end

/-! ## Token-solvency vocabulary

The `≤`-style solvency property behind `weth_is_always_solvent`. Readable
`ℕ`-valued wrappers, *definitionally* equal to the proof-side predicates. -/

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

/-- WETH is solvent after running `tx` (vacuous if the tx reverts). The
WETH instance of the generic `afterTx`. -/
def SolventAfter (ctx : ExecContext) (σ : AccountMap .EVM)
    (tx : Transaction) (S_T weth : Address) : Prop :=
  afterTx ctx σ tx S_T (fun σ' => Solvent σ' weth)

/-- The deployment / chain-state bundle the solvency guarantee is
conditional on (exactly the proof-side `WethAssumptions`). -/
abbrev SolvencyAssumptions (ctx : ExecContext) (σ : AccountMap .EVM)
    (tx : Transaction) (S_T weth : Address) : Prop :=
  WethAssumptions σ ctx.fuel ctx.baseFee ctx.block ctx.genesis ctx.history tx S_T weth

end EvmSmith.Weth
