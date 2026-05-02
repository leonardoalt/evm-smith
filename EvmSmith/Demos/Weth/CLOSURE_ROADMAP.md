# Weth solvency proof — closure roadmap

**State**: `weth_solvency_invariant` is a typed Lean theorem, build green,
0 sorries. Conditional on `WethAssumptions` (5 fields: 4 Register-shape,
1 genuinely irreducible real-world fact).

## All bytecode-derivable / framework-coupled assumptions discharged

This work discharged **every bytecode-derivable and framework-coupled
assumption** in `WethAssumptions` as theorems or via framework simplification:

* `weth_pc60_cascade : WethAccountAtC C → WethPC60CascadeFacts C`
* `weth_pc72_cascade : WethCallNoWrapAt72 C → WethCallSlackAt72 C → WethPC72CascadeFacts C`
* `weth_pc40_cascade : WethDepositCascadeStruct C → WethDepositPreCredit C → WethPC40CascadeFacts C`
* `weth_account_at_C : WethAccountAtC C` (per-state σ-has-C)
* `weth_deposit_cascade : WethDepositCascadeStruct C` (PCs 32→40 threading)
* `weth_call_slack : WethCallSlackAt72 C` (PCs 60→72 threading w/ WethInvFr in WethReachable)
* `weth_xi_preserves_C : ΞPreservesAccountAt C` (mod xi_preserves_C_other narrowing)
* `weth_xi_preserves_C_other` (universal Ξ-preservation via framework's `Ξ_preserves_account_at_a_universal`)
* `weth_call_inv_step_pres` (CALL-step WethInvFr preservation via framework's `_inv_aware` slack-dispatch variant)
* `inv_at_initial` — eliminated by framework's inv-aware `hReachInit` exposing `WethInvFr σ C` directly.
* `account_at_initial` — eliminated by dropping the structurally-unused `ΞPreservesInvariantAtC C` parameter from `Υ_invariant_preserved` (it was passed through to `Υ_output_invariant_preserves` as `_hWitness`, never consumed in the proof body).

## Current `WethAssumptions` (5 fields)

```lean
structure WethAssumptions ... : Prop where
  -- Register-shape (4): accepted posture identical to Register.
  deployed         : DeployedAtC C
  sd_excl          : WethSDExclusion ...
  dead_at_σP       : WethDeadAtσP ...
  inv_at_σP        : WethInvAtσP ...
  -- Narrow structural / real-world (1).
  call_no_wrap     : WethCallNoWrapAt72 C
```

## Discharge status of remaining assumptions

| Assumption | Status | What's needed to discharge |
|---|---|---|
| `deployed` | Register-shape, accepted | — |
| `sd_excl` | Register-shape, accepted | — |
| `dead_at_σP` | Register-shape, accepted | — |
| `inv_at_σP` | Register-shape, accepted | — |
| `call_no_wrap` | **Genuinely irreducible** | Chain-state real-world bound on balance + value. |

## Framework infrastructure landed this session

EVMYulLean's `MutualFrame.lean` § I + § J:

* **§ I (Θ-side)** — `accountPresentAt` predicate, leaf lemmas, `Θ_preserves_account_at_a`, `EVM_call_preserves_account_at_a`.
* **§ J.1-J.4** — per-op preservation: SSTORE/TSTORE/SELFDESTRUCT (already present), `EvmYul.step_accountMap_eq_of_strict` bridge, `EVM_step_handled_preserves_present`, `EVM_step_CALL_preserves_present` (and CALLCODE/DELEGATECALL/STATICCALL), dispatcher `EVM_step_preserves_present_no_create`.
* **§ J.5-J.7** — bounded variants: `ΞPreservesAccountAtBdd a f`, `Θ_preserves_account_at_a_bdd`, `EVM_call_preserves_account_at_a_bdd`, `X_preserves_account_at_a_bdd`. Reachable-closure wrappers `Θ_..._of_Reachable`, `EVM_call_..._of_Reachable`.
* **§ J.5b** — `Λ_preserves_account_at_a` (the load-bearing Λ-side theorem). `EVM_step_CREATE_preserves_present` and `_CREATE2_preserves_present`. Universal `EVM_step_preserves_present` (no no-create constraint).
* **§ J.5c-J.6** — `X_preserves_account_at_a_bdd_universal` (handles `decode = none` via STOP arm). `Ξ_preserves_account_at_a_universal : ∀ a, ΞPreservesAccountAt a` — the universal closure!
* **§ J.6.6/J.6.7 / `_inv_aware`** — pres-step variants: `Ξ_preserves_account_at_a_of_Reachable_for_C_with_pres_step` (avoids chicken-and-egg circularity for reachability+invariant). `ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch_inv_aware` exposes `WethInvFr s'.accountMap C` to `hReach_step` callback.

Plus 12+ strong shape lemmas covering every Weth opcode (DUP1/2/3/5, SWAP1, PUSH (generic), JUMPI, JUMPDEST, POP, CALLER, CALLVALUE, ADD, GAS, PUSH1).

## Net effect

From a starting point of 3 opaque `Weth*CascadeFacts` predicates plus implicit framework gaps (xi_preserves_C, inv_step_pres), the session produced:

- **9 cascade-style and step-preservation theorems** in the Weth-side proof (replacing all opaque cascade-fact assumptions).
- **~5000 LoC of framework infrastructure** in EVMYulLean, including the universal `Ξ_preserves_account_at_a_universal` theorem.
- **`WethAssumptions` reduced from 7 (originally) to 5 fields** where 4 are Register-shape (accepted) and 1 is a genuinely irreducible real-world fact.

The headline `weth_solvency_invariant` theorem is unchanged. Its conditional hypotheses are now strictly partitioned: 4 Register-shape (accepted posture) and 1 real-world irreducible (`call_no_wrap`). **Every bytecode-derivable and framework-coupled assumption has been discharged.** The previous `deposit_slack : WethDepositPreCredit C` field has been eliminated by simplifying `Υ_invariant_preserved` to drop a structurally-unused `ΞPreservesInvariantAtC C` parameter.
