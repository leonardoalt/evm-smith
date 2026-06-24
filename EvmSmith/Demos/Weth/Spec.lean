import EvmSmith.Demos.Weth.SpecDSL

/-!
# WETH — the spec, as an interface

This file is **the spec a reader opens**: a single `structure WethSpec`
whose fields *are* WETH's guarantees, each a short pre/post statement read
like a Solidity function spec — and **no proofs**. The proof that WETH's
bytecode satisfies every field lives in `SpecProofs.lean`
(`weth_spec : WethSpec`), which delegates to the `weth_*_run_impl` engine
in `Behaviour.lean`. So this file is the interface; that file is the
witness. Vocabulary (`balance[·]`, `sender`, `ensures`, `Calls`,
`Solvent`, …) is in `SpecDSL.lean` / `Spec/Dsl.lean`.

## The contract (86 bytes of runtime code)

| Selector     | Solidity                | Behaviour                                   |
|--------------|-------------------------|---------------------------------------------|
| `0xd0e30db0` | `deposit() payable`     | `balance[msg.sender] += msg.value`          |
| `0x2e1a7d4d` | `withdraw(uint256 x)`   | require `balance[msg.sender] ≥ x`; subtract `x`; then `CALL` `x` wei back to `msg.sender` |

Token balances live at `storage[address]` directly (not Solidity's hashed
`mapping` slot) — see `tokenBalanceSlot` in `SpecDSL.lean`. In each field,
`Calls .f s` means `s` is the entry of a call to `f`; `ensures …` is the
postcondition of running to halt (`balance[a]` post-state, `old balance[a]`
pre-state); `before_call: …` is the postcondition at the point of the
outbound `CALL`.
-/

namespace EvmSmith.Weth

open EvmYul EvmYul.EVM EvmYul.Frame Batteries EvmSmith.Layer1 EvmSmith.Spec

/-- **WETH's guarantees, as an interface.** Each field is a behaviour the
bytecode is proven to obey (witness: `weth_spec` in `SpecProofs.lean`). -/
structure WethSpec where
  /-- **`deposit()`** credits the caller by `msg.value`, leaves every other
  balance untouched, and returns no data. -/
  deposit : ∀ (s : EVM.State), Calls .deposit s →
    ensures
      balance[sender] = old balance[sender] + value
    ∧ untouched (others)
    ∧ returndata = empty

  /-- **`withdraw(x)` — own debit (unconditional).** By the time withdraw
  makes its external `CALL` it has already decremented the caller by exactly
  `x` (checks-effects-interactions). No reentrancy assumption: this is the
  contract's own effect, before any external code runs. -/
  withdraw_debits : ∀ (s : EVM.State), Calls .withdraw s →
    amount ≤ old balance[sender] →
    before_call:
      balance[sender] = old balance[sender] - amount

  /-- **`withdraw(x)` — exact end-balance.** Run to halt *through* the
  external `CALL`, the caller ends debited by exactly `x` — given sufficient
  balance and that the recipient does not reenter to change balances
  (`NoReentrancy`; needed only for this *exact* figure, not for solvency). -/
  withdraw : ∀ (s : EVM.State), Calls .withdraw s →
    amount ≤ old balance[sender] → NoReentrancy s →
    ensures
      balance[sender] = old balance[sender] - amount

  /-- **Unknown selector** reverts, changing no account (no fallback /
  `receive`). -/
  fallback : ∀ (s : EVM.State), Calls .unknown s →
    ensures
      storage = old storage

  /-- **Always solvent.** After *any* Ethereum transaction, WETH's recorded
  token supply never exceeds the ETH it holds (or the transaction reverted),
  given a well-formed pre-state, WETH not being the sender/miner, a valid
  transaction, and the deployment / chain-state bundle. -/
  solvent : ∀ (ctx : ExecContext) (σ : AccountMap .EVM)
      (tx : Transaction) (S_T weth : Address),
      StateWF σ → Solvent σ weth → weth ≠ S_T → weth ≠ ctx.block.beneficiary →
      TxValid σ S_T tx ctx.block ctx.baseFee → SolvencyAssumptions ctx σ tx S_T weth →
      SolventAfter ctx σ tx S_T weth

/-! ## ABI decoding — correspondence to Solidity's compiler output

The behavioural guarantees above are phrased in terms of `functionSelector`
(which entry point a call dispatches to) and `withdrawArg`/`amount` (the
decoded `uint256`). These two `rfl` lemmas pin those notions to the *exact*
EVM calldata operations the Solidity compiler emits for ABI dispatch and
decoding — so "the selector" / "the argument" in this spec is, by
construction, the ABI's, with no gap to what the compiler guarantees.

(The remaining abstract identity — that `shr(224, calldataload(0))` equals
the leading 4 bytes `calldata[0:4]`, and `calldataload(4)` the slice
`calldata[4:36]` — is the EVM semantics of `CALLDATALOAD` + `SHR`, i.e. a
big-endian word's high bytes; we take it as the meaning of those opcodes
rather than re-deriving it through the byte-array primitives.) -/

/-- **Selector = `shr(224, calldataload(0))`.** The dispatched function
selector is the high 4 bytes of the first calldata word — exactly the
`msg.sig` extraction the Solidity compiler emits in its dispatcher
prologue. -/
theorem selector_is_abi (s : EVM.State) :
    functionSelector s.executionEnv.calldata
      = UInt256.shiftRight
          (EvmYul.State.calldataload s.toState (UInt256.ofNat 0)) (UInt256.ofNat 0xe0) :=
  rfl

/-- **Argument = `calldataload(4)`.** `withdraw`'s `uint256` argument is the
calldata word at offset 4 (`calldata[4:36]`) — exactly the argument load
the Solidity compiler emits for the first `uint256` parameter. -/
theorem withdraw_arg_is_abi (s : EVM.State) :
    withdrawArg s = EvmYul.State.calldataload s.toState (UInt256.ofNat 4) :=
  rfl

end EvmSmith.Weth
