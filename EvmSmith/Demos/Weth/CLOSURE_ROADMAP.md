# Weth solvency proof — closure roadmap

**State**: `weth_solvency_invariant` is a typed Lean theorem, build green,
0 sorries. Conditional on `WethAssumptions` (currently 11 fields, but
many are bytecode-derivable in principle).

## Major theorems landed this session

All four originally-opaque cascade-style assumptions are now theorems:

* `weth_pc60_cascade : WethAccountAtC C → WethPC60CascadeFacts C`
  — derived from threaded WethTrace cascade PCs 47..60.
* `weth_pc72_cascade : WethCallNoWrapAt72 C → WethCallSlackAt72 C → WethPC72CascadeFacts C`
  — composed from narrowed structural facts.
* `weth_pc40_cascade : WethDepositCascadeStruct C → WethDepositPreCredit C → WethPC40CascadeFacts C`
  — from PCs 32..40 cascade + Θ-pre-credit.
* `weth_account_at_C : WethAccountAtC C` — projected from `accountPresentAt s.accountMap C`
  conjunct now in `WethReachable`.
* `weth_deposit_cascade : WethDepositCascadeStruct C` — derived from
  threaded WethTrace cascade PCs 32..40 (findD-style).

## Current `WethAssumptions` shape

```lean
structure WethAssumptions ... : Prop where
  -- Register-shape (4): accepted posture identical to Register.
  deployed         : DeployedAtC C
  sd_excl          : WethSDExclusion ...
  dead_at_σP       : WethDeadAtσP ...
  inv_at_σP        : WethInvAtσP ...
  -- Bytecode/framework-narrowed (7).
  deposit_slack    : WethDepositPreCredit C
  account_at_initial : ∀ σ I, I.codeOwner = C → accountPresentAt σ C
  inv_at_initial   : ∀ σ I, I.codeOwner = C → WethInvFr σ C
  inv_step_pres    : WethStepInvFrPreserves C
  xi_preserves_C   : ΞPreservesAccountAt C
  call_no_wrap     : WethCallNoWrapAt72 C
  call_slack       : WethCallSlackAt72 C
```

## Discharge status of remaining assumptions

| Assumption | Status | What's needed |
|---|---|---|
| `deposit_slack` | **Genuinely irreducible** | Υ-side Θ-pre-credit lift. Not bytecode-derivable. |
| `account_at_initial` | Real-world | σ-has-C at Ξ entry. Trivial in real chain state. |
| `inv_at_initial` | Real-world | WethInvFr at Ξ entry. Derivable from top-level `hInv : WethInv σ C`. |
| `inv_step_pres` | Bytecode-derivable | Needs framework `hReach_step` refactor to expose `StateWF`/IHs. |
| `xi_preserves_C` | Bytecode-derivable | Needs framework variant taking I-restricted closures + `hΞ_other` discharge for non-Weth I (requires `EVM_step_preserves_codeOwner` + SELFDESTRUCT-non-Iₐ framework lemmas). |
| `call_no_wrap` | **Genuinely irreducible** | Chain-state real-world bound on balance + value. |
| `call_slack` | Bytecode-derivable | PCs 60→72 cascade threading using newly-accessible WethInvFr in WethReachable. ~500 LoC mechanical. |

## Session totals

* **evm-smith**: 29 commits including 12 PCs 47→60 cascade threading + 5 PCs 36→40 cascade threading + 5 cascade-fact dischargers + WethReachable extensions.
* **EVMYulLean**: 17+ commits including §I (Θ-side preservation) + §J (Ξ/X/step preservation, op-conditional variants, C-restricted variants) + 12 strong shape lemmas (SLOAD/LT/SUB/DUP1/2/3/5/SWAP1/PUSH/JUMPI/POP/CALLER/CALLVALUE/ADD/JUMPDEST/GAS).
* All builds green throughout.

## Framework infrastructure now in place

EVMYulLean's `MutualFrame.lean` §I + §J provides:
- `accountPresentAt σ a` predicate + `accountPresentAt_insert`.
- `Θ_preserves_account_at_a` (witness-driven and Reachable-driven variants).
- `Λ_preserves_account_at_a` — pending (CREATE not in Weth, so not strictly needed).
- `EVM.step` per-op preservation: `EVM_step_handled_preserves_present`, `_CALL/CALLCODE/DELEGATECALL/STATICCALL_preserves_present`, dispatcher `EVM_step_preserves_present_no_create`.
- `X_preserves_account_at_a` and bounded variant.
- `Ξ_preserves_account_at_a_of_Reachable` (universal form with closures).
- `Ξ_preserves_account_at_a_of_Reachable_op_conditional` (handles halt ops).
- `Ξ_preserves_account_at_a_of_Reachable_for_C` (C-restricted with hΞ_other).
- Reachable-closure wrappers `Θ_..._of_Reachable`, `EVM_call_..._of_Reachable`.

## Remaining bytecode-derivable assumptions (priority order)

### `call_slack` — most tractable next target (~500 LoC)

Thread the slack through PCs 60→72 in WethTrace. WethInvFr is now in WethReachable
(commit `6d954c5`), so the PC 60 walk can use it to establish PC 61's slack via the
SSTORE delta law (`storageSum_sstore_replace_eq_findD`). PCs 61-71 walks preserve the
slack via accountMap-preservation (strong shape lemmas exist for all needed ops).
At PC 72, extract the slack and discharge `WethCallSlackAt72 C` mirroring
`weth_pc60_cascade` and `weth_deposit_cascade`.

### `inv_step_pres` — needs framework refactor

Currently a black-box assumption. Discharging requires framework's
`ΞPreservesInvariantAtC_of_Reachable_general_call_slack_dispatch`'s `hReach_step` to
expose the post-step WethInvFr derivation slot. This is a multi-piece framework
refactor (~300 LoC).

### `xi_preserves_C` — chain of framework gaps

`Ξ_preserves_account_at_a_of_Reachable_for_C` exists but takes `hΞ_other` for non-C
contracts. Discharging `hΞ_other` requires:
- `EVM_step_preserves_codeOwner` (executionEnv unchanged across step).
- SELFDESTRUCT preserves σ at non-Iₐ addresses.
- Mutual closure with X.

~400-600 LoC of framework engineering.

## Net effect

From a starting point of 3 opaque `Weth*CascadeFacts` predicates plus the implicit
`xi_preserves_C` framework gap, this session produced:

- 5 cascade-style assumptions discharged as theorems.
- 7 narrower structural facts replacing 1 opaque cascade-fact (after expansion: the
  refactor of `WethReachable` traded 1 opaque field for 2 new ones, but those 2 are
  significantly narrower in kind and bytecode-derivable in principle).
- ~3000 LoC of framework infrastructure landed in EVMYulLean.
- The `WethReachable` predicate now carries σ-has-C and WethInvFr as state-level
  invariants — the foundation for the remaining bytecode-derivable dischargers.

The headline `weth_solvency_invariant` theorem is unchanged. Its conditional
hypotheses are now strictly narrower and clearly partitioned into "real-world
irreducible" vs "bytecode-derivable with mechanical work".
