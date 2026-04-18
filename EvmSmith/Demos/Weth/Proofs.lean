import EvmSmith.Demos.Weth.Upsilon

/-!
# Correctness of the `Weth` program — main safety invariant

## The invariant

    I σ C := match σ.find? C with
            | none     => True
            | some acc => totalBalance acc.storage ≤ acc.balance.toNat

where `totalBalance` is the `ℕ`-valued sum of token balances stored
in `C`'s storage (modeling Σ balances[addr] over all addrs). The
invariant is "user funds never lost" — the contract always holds at
least enough ETH to cover all recorded token balances. Weakened from
equality to `≤` because ETH can be force-fed into `C` via
`SELFDESTRUCT` or coinbase rewards. `ℕ` is used to sidestep modular-
arithmetic pitfalls where a wrapped sum could trivially satisfy `≤`.

## The four layers

- **Layer 0** — `Std.TransCmp`/`Std.ReflCmp` instances for `UInt256`,
  plus `UInt256.sub` bridge lemmas.
  File: `EvmSmith/Lemmas/UInt256Order.lean`. **Closed.**
- **Layer 1** — `totalBalance` sum behaviour under `RBMap.insert` and
  `RBMap.erase`, via Batteries' `exists_insert_toList_zoom_*` and a
  locally-derived erase permutation lemma.
  File: `EvmSmith/Lemmas/RBMapSum.lean`. **Closed.**
- **Layer 2** — `Θ_preserves_I`: fuel induction on the `Ξ`/`Θ` mutual
  recursion, covering frame, balance-transfer, reentrance, precompile
  frame, and `Weth_Ξ_preserves_I` for the program-specific content.
  File: `EvmSmith/Demos/Weth/Theta.lean`. **Skeleton.**
- **Layer 3** — `Υ_preserves_I`: wraps `Θ_preserves_I` with the
  post-Θ steps (gas refund, beneficiary fee, selfdestruct sweep,
  dead-account sweep, tstorage wipe).
  File: `EvmSmith/Demos/Weth/Upsilon.lean`. **Skeleton.**

## Shared definitions

`I`, `totalBalance`, `codeAt`, and `initial_state` live in
`EvmSmith/Demos/Weth/Invariant.lean` so every layer can use them
without circular imports. This file (`Proofs.lean`) consumes Layer 3's
`Υ_preserves_I` and states the final user-facing theorem.
-/

namespace EvmSmith.WethProofs
open EvmSmith.WethInvariant EvmSmith.WethProofs.Layer3
     EvmYul EvmYul.EVM EvmSmith EvmSmith.Weth

export EvmSmith.WethInvariant (I totalBalance codeAt initial_state)

/-! ## The main theorem -/

/-- **The main theorem**: Weth's safety invariant is preserved by
    every transaction. Delegates to `Layer3.Υ_preserves_I`. -/
theorem weth_always_safe
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_genesis : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress)
    (hI : I σ C) (hCode : codeAt σ C)
    (hCNotBeneficiary : C ≠ H.beneficiary)
    (hCNotSender     : C ≠ S_T) :
    match EVM.Υ fuel σ H_f H H_genesis blocks tx S_T with
    | .ok (σ', _, _, _) => I σ' C
    | .error _          => True := by
  have h := Υ_preserves_I fuel σ H_f H H_genesis blocks tx S_T C
              hI hCode hCNotBeneficiary hCNotSender
  split <;> rename_i heq
  · rw [heq] at h; exact h.1
  · trivial

end EvmSmith.WethProofs
