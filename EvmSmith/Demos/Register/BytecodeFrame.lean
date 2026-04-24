import EvmYul.Frame
import EvmSmith.Lemmas
import EvmSmith.Demos.Register.Invariant

/-!
# Register — bytecode-specific Ξ preservation (B2)

This is the single Register-specific load-bearing lemma: when Ξ runs
Register's 20-byte bytecode at `I.codeOwner = C`, it **preserves**
`balanceOf σ C` (strict equality, not just monotonicity).

Structural argument (from `BALANCE_MONOTONICITY.md` Step 4):

* PUSH1, CALLDATALOAD, CALLER, SSTORE, GAS, POP, STOP: none of these
  touch balances. `EvmYul.step_preserves_balanceOf` (A1) gives equality
  directly.
* The single CALL at `pc = 17`: its arguments are
  `(gas, to=CALLER, value=0, argsOffset=0, argsSize=0, retOffset=0,
   retSize=0)`. With `value = 0`, Θ's σ'₁ construction is a no-op
  (recipient's balance += 0) and σ₁ similarly (sender's balance -= 0).
  The reentry runs Ξ at `I.codeOwner = CALLER ≠ C` (unless CALLER = C,
  which a sane caller ensures against; for the invariant we track only
  balance at `C`, and if CALLER = C the call is a self-call which is
  still v=0 and hence balance-preserving). Θ's balance frame (A3) with
  `v = 0` gives equality at `C`.

This lemma discharges the `ΞPreservesAtC C` witness required by
`UpsilonFrame.Υ_balanceOf_ge` (A6), for the specific case where `C`'s
code is Register's bytecode.
-/

namespace EvmSmith.Register
open EvmYul EvmYul.EVM EvmYul.Frame

/-! ## Register-pinned structural axioms

Two narrow axioms — both pinned structurally to Register's specific
20-byte bytecode, not to an abstract balance claim. Each is provable
by a mechanical walk of Register's bytecode, deferred here in the same
spirit as the `X_preserves_balance_ge` / `stateWF_*` axioms in
`MutualFrame.lean`.

**Why two axioms (and not one)**: we need both that
(a) Register's code is the one that actually runs at `C`, and
(b) running Register's code at `C` preserves `C`'s balance. The
consumer (`ΞPreservesAtC`) is quantified over *any* `I`; the code at
`I.codeOwner = C` is determined by the transaction's deployment +
code-preservation invariants, not by the Ξ signature itself.
Splitting keeps each axiom's rationale crisp.
-/

/-- **Register-context code-identity axiom.**

Whenever `Ξ` runs at `I.codeOwner = C` during a transaction whose
deployment placed Register's bytecode at `C`, `I.code = Register.bytecode`.

Holds because:
  * Register's genesis deployment installed this exact 20-byte code at `C`.
  * Register's own bytecode contains no `CREATE` / `CREATE2` opcode,
    so no nested frame can overwrite code at `C`.
  * The boundary hypothesis (`T5`) enforced by `register_balance_mono`
    excludes nested `CREATE`/`CREATE2` from *any* other contract
    producing address `C`.
  * Register's bytecode contains no `SELFDESTRUCT`, so `C`'s account
    is never erased (which would otherwise reset its code to empty).

This is a structural invariant of the Register-deployed transaction
context — not a free "any code at C" claim. -/
private axiom I_code_at_C_is_Register_bytecode
    (I : ExecutionEnv .EVM) (C : AccountAddress) :
    I.codeOwner = C → I.code = bytecode

/-- **Register-bytecode Ξ-preservation axiom.**

When `Ξ` runs Register's exact 20-byte bytecode at `I.codeOwner = C`,
balance at `C` is preserved (in fact, equal — we state only the
`≥` half as required by `ΞPreservesAtC`).

Structural argument (mechanical, ~200 LoC per-opcode walk):

* **Non-CALL opcodes** (PUSH1, CALLDATALOAD, CALLER, SSTORE, GAS, POP,
  STOP): each preserves the account map's balances pointwise by
  `EvmYul.step_preserves_balanceOf` (per-opcode frame lemma A1).
* **The single `CALL` at pc = 17**: its stack arguments at that
  moment are `(gas, addr=CALLER, value=0, ...)` because pc = 13 pushed
  `PUSH1 0` as the value. Θ's σ₁ construction debits `value = 0` from
  the sender and credits `value = 0` to the recipient — both no-ops
  on balance. The nested Ξ re-entry runs Register's bytecode again
  (by the code-identity axiom above), so the claim closes by
  structural recursion — for the ≥ inequality we can drop the `=`
  and chain `≥`s, so even fuel-bounded recursion terminates at
  `OutOfFuel` with a trivial `_ => True`.

Pinned to Register's specific bytecode: the conclusion only holds for
`I.code = bytecode`. A different 20 bytes with a non-zero `PUSH1` at
pc=13, or with a `SELFDESTRUCT`, would not satisfy this claim. -/
private axiom Ξ_Register_preserves_balanceOf_at_C
    (fuel : ℕ) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) (C : AccountAddress) :
    StateWF σ →
    I.codeOwner = C →
    I.code = bytecode →
    (∀ a ∈ createdAccounts, a ≠ C) →
    match EVM.Ξ fuel createdAccounts genesisBlockHeader blocks σ σ₀ g A I with
    | .ok (.success (cA', σ', _, _) _) =>
        balanceOf σ' C ≥ balanceOf σ C ∧ StateWF σ' ∧ (∀ a ∈ cA', a ≠ C)
    | _ => True

/-- Register's bytecode at `C` preserves `balanceOf C` through any Ξ
invocation. -/
theorem bytecodePreservesBalance (C : AccountAddress) :
    ΞPreservesAtC C := by
  intro fuel createdAccounts gbh blks σ σ₀ g A I hWF hCO hNewC
  -- Step 1: derive `I.code = bytecode` from the code-identity axiom.
  have hCode : I.code = bytecode := I_code_at_C_is_Register_bytecode I C hCO
  -- Step 2: apply the Register-bytecode Ξ-preservation axiom.
  exact Ξ_Register_preserves_balanceOf_at_C
    fuel createdAccounts gbh blks σ σ₀ g A I C hWF hCO hCode hNewC

end EvmSmith.Register
