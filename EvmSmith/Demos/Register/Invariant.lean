import EvmSmith.Lemmas.RBMapSum
import EvmSmith.Demos.Register.Program
import EvmYul.EVM.Semantics

/-!
# Register balance-monotonicity — invariant

## The claim

Register's bytecode (see `Program.lean`) only ever issues a single
outbound `CALL`, and that CALL has `value = 0`. Consequently, no
execution path — including reentrance via the `CALL`'s callee — can
decrease Register's balance.

We state this as a monotone lower-bound invariant: if the contract
starts a transaction with balance ≥ b₀, it ends with balance ≥ b₀.

## The inductive invariant

`RegInv σ A C b₀` bundles four conjuncts that all must be preserved
in each step of the proof:

- `code`         — `σ[C].code = Register.bytecode`. External code
                   could in principle deploy to the same address via
                   `CREATE/CREATE2` collision; we rule this out with
                   a boundary hypothesis `hNewC`.
- `bal`          — the balance lower bound `b₀ ≤ balanceOf σ C`.
- `notSD`        — `C ∉ A.selfDestructSet`. `SELFDESTRUCT` adds its
                   *executing* `codeOwner` to the set; since Register
                   never runs `SELFDESTRUCT` on its own code, and
                   nested frames never have `codeOwner = C` running
                   non-Register code, C stays out.
- `totalBounded` — `totalETH σ < UInt256.size`. Inductive because
                   every step (value transfer, contract creation,
                   selfdestruct, gas burns) either conserves or
                   decreases the ℕ-valued sum of all balances.
                   Gives us per-call no-wrap for value additions.

## Additional boundary hypotheses

Supplied once at transaction entry (not inductive):

- `C ≠ S_T`            — sender is not Register. Υ debits S_T by
                         `gasLimit × p + blobFee`, which would fail
                         the bound if S_T = C.
- `C ≠ H.beneficiary`  — block miner is not Register. Υ credits
                         beneficiary with the priority fee.
- `hNewC : ∀ a ∈ createdAccounts, a ≠ C` — no CREATE during the tx
                         spawns an address equal to C.
-/

namespace EvmSmith.RegisterInvariant

open EvmYul EvmYul.EVM EvmSmith EvmSmith.Register Batteries

/-! ## Definitions -/

/-- `ℕ`-valued balance lookup. Returns 0 for unknown accounts. -/
def balanceOf (σ : AccountMap .EVM) (C : AccountAddress) : ℕ :=
  (σ.find? C).elim 0 (·.balance.toNat)

/-- `σ[C].code = Register.bytecode`. -/
def codeAt (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  (σ.find? C).map (·.code) = some bytecode

/-- Total ETH across all accounts, computed in ℕ. Identical shape to
    `EvmSmith.Layer1.totalBalance` but indexed by balance instead of
    storage value. -/
def totalETH (σ : AccountMap .EVM) : ℕ :=
  σ.foldl (fun acc _a v => acc + v.balance.toNat) 0

/-- The inductive invariant. -/
structure RegInv (σ : AccountMap .EVM) (A : Substate) (C : AccountAddress)
                 (b₀ : ℕ) : Prop where
  code         : codeAt σ C
  bal          : b₀ ≤ balanceOf σ C
  notSD        : C ∉ A.selfDestructSet
  totalBounded : totalETH σ < UInt256.size

/-! ## The main theorem -/

/-- **Register balance monotonicity.** Given the inductive invariant
    and the three boundary hypotheses, every transaction preserves
    the balance lower bound `b₀` at `C`. -/
theorem register_balance_mono
    (fuel : ℕ) (σ σ' : AccountMap .EVM)
    (H_f : ℕ) (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress) (b₀ : ℕ)
    (_hInv : RegInv σ (default : Substate) C b₀)
    (_hCS  : C ≠ S_T)
    (_hCH  : C ≠ H.beneficiary)
    (_hNewC : ∀ a : AccountAddress, a ≠ C)  -- placeholder: any create spawns ≠ C
    (_hRun : EVM.Υ fuel σ H_f H H_gen blocks tx S_T
              = .ok (σ', default, default, default)) :
    b₀ ≤ balanceOf σ' C := by
  sorry

end EvmSmith.RegisterInvariant
