import EvmYul.Frame
import EvmSmith.Demos.Weth.Program

/-!
# Weth — solvency invariant bundle (§2.1)

`WethInv σ C` is the relational solvency invariant

  `Σ_a storageOf σ C (addressSlot a) ≤ balanceOf σ C`,

i.e. the contract's ETH balance is at least as large as the sum of
all users' token balances tracked in storage. We package it together
with the deployment-pinned code-identity in `RegInv`, the Weth
analogue of Register's invariant bundle.

Unlike Register's bundle, `RegInv` has no monotone balance lower
bound — Weth's withdraw block can decrease `balanceOf σ C`, so the
right shape is the *relative* invariant
`storageSum σ C ≤ balanceOf σ C`. The full §H mutual closure tracks
the slack `balanceOf σ C − storageSum σ C` through the call tree.

## Transit-lemma intuition

* **Sender debit at `S_T ≠ C`**: `β(C)` and storage at `C` are both
  unchanged (the modification is at `S_T`), so the invariant is
  preserved verbatim.
* **Θ value transfer in to `C`**: `β(C)` increases by the value;
  storage at `C` is unchanged. The slack grows, invariant preserved.
* **SSTORE-then-CALL withdraw at `C`**: `S` decreases by `x` at the
  SSTORE, `β` decreases by `x` at the CALL — net Δ(β−S) = 0.
* **All Υ-tail steps** (refund, beneficiary fee, SD sweep, dead
  sweep, tstorage wipe): `β(C)` and `S(C)` are unchanged (boundary
  hypotheses ensure `C` is not the sender / miner / SD'd / dead).

These transit lemmas are landed alongside §2.6's body factor + tail.
This file establishes only the predicate definition + the `RegInv`
bundle structure.
-/

namespace EvmSmith.Weth
open EvmYul EvmYul.Frame

/-- The Weth solvency invariant: contract balance ≥ sum of all
user-balance storage slots. -/
def WethInv (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  storageSum σ C ≤ balanceOf σ C

/-- The runtime code at address `C` is Weth's bytecode. Mirrors
Register's `codeAt` for the Weth analogue of the deployment-pinned
hypothesis. -/
def codeAt (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  (σ.find? C).map (·.code) = some bytecode

/-- The Weth inductive-invariant bundle.

Mirror of `EvmSmith.Register.RegInv`, but tracking the *relative*
solvency invariant rather than a monotone balance lower bound. The
deployment-pinned code identity (`code`) is inductive: no step in the
transaction deposits new code at `C` (ruled out by Keccak T5 +
Weth's no-SELFDESTRUCT-in-bytecode property).

The SELFDESTRUCT exclusion `C ∉ A.selfDestructSet` is kept as a
separate hypothesis (`WethSDExclusion`, see ASSUMPTIONS.md F1)
rather than a `RegInv` conjunct — same posture as Register. -/
structure RegInv (σ : AccountMap .EVM) (C : AccountAddress) : Prop where
  inv  : WethInv σ C
  code : codeAt σ C

/-! ## Trivial-shape transit lemmas

These follow directly from `find?`-equality / `storageSum_of_find?_eq`
plus `balanceOf_of_find?_eq`. They appear repeatedly in the Υ-tail
analysis (§2.6) and the Θ value-transfer-in argument. -/

/-- If two states agree on `find? C`, they have the same `WethInv`. -/
theorem WethInv_of_find?_eq
    {σ σ' : AccountMap .EVM} {C : AccountAddress}
    (h : σ'.find? C = σ.find? C)
    (hInv : WethInv σ C) :
    WethInv σ' C := by
  unfold WethInv
  rw [storageSum_of_find?_eq h, balanceOf_of_find?_eq h]
  exact hInv

/-- Inserting an account at `a ≠ C` preserves `WethInv σ C`. -/
theorem WethInv_insert_ne
    (σ : AccountMap .EVM) (C a : AccountAddress) (acc' : Account .EVM)
    (h_ne : a ≠ C)
    (hInv : WethInv σ C) :
    WethInv (σ.insert a acc') C :=
  WethInv_of_find?_eq (find?_insert_ne σ a C acc' h_ne) hInv

/-- A balance-only update at `C` (storage and code preserved) preserves
the invariant whenever the new balance is at least the old.

Used at Θ value-transfer-in to `C`: `balance += value`, storage
unchanged. -/
theorem WethInv_balance_increase_at_C
    (σ : AccountMap .EVM) (C : AccountAddress) (acc_old acc_new : Account .EVM)
    (hFind : σ.find? C = some acc_old)
    (hStg : acc_new.storage = acc_old.storage)
    (hBal : acc_old.balance.toNat ≤ acc_new.balance.toNat)
    (hInv : WethInv σ C) :
    WethInv (σ.insert C acc_new) C := by
  unfold WethInv at *
  -- New storageSum at C = sum over acc_new.storage = sum over acc_old.storage = storageSum σ C.
  have h_find_new : (σ.insert C acc_new).find? C = some acc_new :=
    find?_insert_self σ C acc_new
  rw [storageSum_of_find?_some _ _ acc_new h_find_new, hStg]
  rw [storageSum_of_find?_some _ _ acc_old hFind] at hInv
  -- New balance at C = acc_new.balance.toNat ≥ acc_old.balance.toNat.
  have h_bal_new :
      balanceOf (σ.insert C acc_new) C = acc_new.balance.toNat := by
    unfold balanceOf; rw [h_find_new]; rfl
  rw [h_bal_new]
  have h_bal_old : balanceOf σ C = acc_old.balance.toNat := by
    unfold balanceOf; rw [hFind]; rfl
  rw [h_bal_old] at hInv
  exact Nat.le_trans hInv hBal

end EvmSmith.Weth
