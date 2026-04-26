# Register/Balance monotonicity soundness audit (2026-04-26)

Scope audited:

- `EvmSmith/Demos/Register/BytecodeFrame.lean`
- `EvmSmith/Demos/Register/BalanceMono.lean`
- `EvmSmith/Demos/Register/Invariant.lean`
- `EvmSmith/Demos/Register/Program.lean`

## Executive summary

I found one **high-severity trusted-core soundness risk** and two **medium-severity proof-contract gaps**.

## Findings

### 1) High — global code-identity axiom can over-approximate reality

`BytecodeFrame.lean` introduces:

```lean
private axiom I_code_at_C_is_Register_bytecode
    (I : ExecutionEnv .EVM) (C : AccountAddress) :
    I.codeOwner = C → I.code = bytecode
```

This is a very strong axiom: once `codeOwner = C` is known, code is forced to be Register bytecode with no direct premise tying it to transaction-local deployment, no-`CREATE`, or no-selfdestruct assumptions.

Impact:

- The trusted base now includes a proposition that can rewrite arbitrary `ExecutionEnv` code at `C` to Register bytecode.
- If any other theorem can build/exhibit an `ExecutionEnv` with `codeOwner = C` and non-Register code, this axiom would make the logic inconsistent.
- Even without inconsistency, this bypasses proving the key deployment/code-preservation property from semantics.

Suggested hardening:

- Replace this axiom with a theorem parameterized by explicit runtime assumptions (e.g. deployment witness + no-overwrite obligations), then thread those assumptions through `RegisterTrace_initial`.
- If unavoidable short-term, isolate it in a dedicated "Trusted" module and make all downstream theorems visibly depend on that trusted hypothesis.

### 2) Medium — `register_balance_mono` relies on structural postconditions supplied as assumptions

`register_balance_mono` requires:

- `hSDExcl : RegSDExclusion ...`
- `hDeadAtσP : RegDeadAtσP ...`

Both are predicates over the actual `Υ` run result decomposition and are currently passed in as hypotheses rather than derived.

Impact:

- The theorem is conditionally correct but not fully mechanized from EVM semantics alone.
- Consumers may over-read it as "proved from model + boundary assumptions only", while two additional run-structural obligations are externally assumed.

Suggested hardening:

- Keep theorem as-is but rename or document as `register_balance_mono_assuming_tail_facts` (or similar).
- Prioritize closing Phase A strong-frame plumbing so these become derived lemmas rather than user-supplied hypotheses.

### 3) Medium — initial invariant code witness is currently unused in body-factor proof

In `register_Υ_body_factors`, the parameter:

```lean
(_hCode : codeAt σ C)
```

is intentionally ignored (`_`-prefixed) and does not contribute to proof obligations.

Impact:

- The theorem signature suggests dependence on an initial code-at-`C` invariant, but current proof does not require it.
- This can hide spec drift: either theorem is stronger than necessary (signature should be simplified), or a missing logical link was intended but not encoded.

Suggested hardening:

- Either remove `_hCode` from `register_Υ_body_factors`, or actually consume it in a lemma connecting initial code to the dead/code preservation assumptions.

## Non-findings / checks performed

- Register bytecode indeed hardcodes `CALL` value to zero (`PUSH1 0` before `CALLER`, `GAS`, `CALL`), matching the local trace invariant shape.
- No `sorry`/`admit` was found under `EvmSmith/Demos/Register` for the audited files.

## Recommended priority order

1. Eliminate or externalize `I_code_at_C_is_Register_bytecode` into explicit assumptions.
2. Derive `RegSDExclusion` and `RegDeadAtσP` from strengthened frame outputs.
3. Tighten theorem signatures to match actual dependency graph.
