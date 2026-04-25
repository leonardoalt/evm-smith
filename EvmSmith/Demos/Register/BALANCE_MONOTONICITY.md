# Register Balance Monotonicity

This document describes the end-to-end Lean proof that **Register's
balance never decreases across an Ethereum transaction**, in the
presence of arbitrary reentrancy.

The proof composes the EVMYulLean frame library
(`EVMYulLean/FRAME_LIBRARY.md`) with a small bytecode-specific closure
local to Register. The headline result is `register_balance_mono` in
`BalanceMono.lean`.

## What is Register?

A 20-byte demo contract whose runtime bytecode is:

```
pc  bytes    mnemonic           effect
 0  60 00    PUSH1 0x00         storage offset
 2  35       CALLDATALOAD       x = cd[0:32]
 3  33       CALLER             sender
 4  55       SSTORE             storage[sender] = x
 5  60 00    PUSH1 0            retSize
 7  60 00    PUSH1 0            retOffset
 9  60 00    PUSH1 0            argsSize
11  60 00    PUSH1 0            argsOffset
13  60 00    PUSH1 0            value = 0   ← the load-bearing fact
15  33       CALLER             addr = sender
16  5a       GAS                gas
17  f1       CALL               invoke; reentrance possible here
18  50       POP                discard success flag
19  00       STOP
```

The single CALL emitted by Register has `value = 0` (pushed at PC=13).
This is the only fact about the bytecode that the proof *really* uses;
everything else is bookkeeping.

## The headline theorem

In `BalanceMono.lean`:

```lean
theorem register_balance_mono
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress) (b₀ : ℕ)
    (hWF : StateWF σ)                              -- T1: total ETH < 2^255
    (hInv : RegInv σ C b₀)                         -- pre-state has b₀ at C and code = bytecode
    (hS_T : C ≠ S_T)                               -- C is not the tx sender
    (hBen : C ≠ H.beneficiary)                     -- C is not the miner
    (hValid : TxValid σ S_T tx H H_f)              -- T4: tx-validity (was an axiom; now a hypothesis)
    (hSDExcl : RegSDExclusion σ fuel H_f H H_gen blocks tx S_T C)
                                                    -- post-Υ substate's SD set excludes C
    (hDeadAtσP : RegDeadAtσP σ fuel H_f H H_gen blocks tx S_T C) :
                                                    -- post-Θ/Λ state has non-empty code at C
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => b₀ ≤ balanceOf σ' C
    | .error _ => True
```

The conclusion: after any single Ethereum transaction (`Υ`), the
balance at C is `≥ b₀`, the lower bound carried by `RegInv`.

## What axioms are used

After this proof, the entire workspace (EVMYulLean + EvmSmith) contains
exactly **three axioms**:

| Axiom | Where | Why |
|-------|-------|-----|
| `precompile_preserves_accountMap` | `EVMYulLean/EvmYul/Frame/MutualFrame.lean:122` | T2: precompiles are pure relative to the account map |
| `lambda_derived_address_ne_C` | `EVMYulLean/EvmYul/Frame/MutualFrame.lean:141` | T5: Keccak collision-resistance — no CREATE/CREATE2 produces address C |
| `I_code_at_C_is_Register_bytecode` | `EvmSmith/Demos/Register/BytecodeFrame.lean:70` | Deployment-pinned: any frame with `I.codeOwner = C` runs Register's bytecode |

All three are real-world structural assumptions:

* **T2** is the standard "precompiles are pure" assumption.
* **T5** is Keccak collision-resistance, the same assumption every
  Ethereum security argument relies on.
* The Register-specific axiom is the deployment claim: at C, the
  installed code is Register's, and nothing in the call tree can
  overwrite it. This holds because Register's bytecode contains no
  CREATE/CREATE2/SELFDESTRUCT and T5 excludes external contracts from
  deriving address C.

In particular, **no axiom about Register's balance behaviour or stack
contents** appears anywhere — those facts are all theorems.

## Proof structure

```
register_balance_mono                                       (BalanceMono.lean:343)
  │
  ↓ uses
  │
Υ_balanceOf_ge                                              (UpsilonFrame.lean:795)
  │
  ↓ takes 3 witnesses
  │
  ├── bytecodePreservesBalance C : ΞPreservesAtC C          (BytecodeFrame.lean:347)
  │     │
  │     ↓ via ΞPreservesAtC_of_Reachable                    (MutualFrame.lean:4960)
  │     │
  │     └── 6 closure lemmas on RegisterTrace               (BytecodeFrame.lean:30)
  │         │
  │         ├── RegisterTrace_Z_preserves                   (trivial — Z only changes gas)
  │         ├── RegisterTrace_step_preserves                (14-case bytecode walk)
  │         ├── RegisterTrace_decodeSome                    (decide over fixed PCs)
  │         ├── RegisterTrace_op_in_8                       (decide over fixed PCs)
  │         ├── RegisterTrace_v0_at_CALL                    (extract from PC=17 disjunct)
  │         └── RegisterTrace_initial                       (uses I_code_at_C axiom)
  │
  ├── register_Υ_tail_invariant : ΥTailInvariant            (BalanceMono.lean:98)
  │     │
  │     ↓ from
  │     │
  │     └── hSDExcl + hDeadAtσP                             (caller-supplied hypotheses)
  │
  └── register_Υ_body_factors : ΥBodyFactors                (BalanceMono.lean:264)
        │
        ↓ via
        │
        ├── σ_to_σP_balance_mono_Θ                          (Θ-dispatch case)
        └── σ_to_σP_balance_mono_Λ                          (Λ-dispatch case)
              │
              ↓ each uses
              │
              ├── Θ_balanceOf_ge / Λ_balanceOf_ge           (closed in MutualFrame)
              ├── balanceOf_σ₀_eq                           (sender debit at S_T ≠ C)
              ├── σ₀_StateWF                                (StateWF preserved across debit)
              └── tx_validity hypothesis                    (no longer an axiom)
```

### The three witnesses for `Υ_balanceOf_ge`

#### 1. `ΞPreservesAtC C` — the bytecode witness

Says: *Ξ run with `I.codeOwner = C` preserves `balanceOf σ C` (and
`StateWF`, and `cA`-exclusion at C).*

Discharged by `bytecodePreservesBalance C`, which calls
`ΞPreservesAtC_of_Reachable` from the framework. The framework's entry
point takes a contract-specific `Reachable : EVM.State → Prop`
predicate plus six closure lemmas. For Register, `Reachable` is
`RegisterTrace`:

```lean
private def RegisterTrace (C : AccountAddress) (s : EVM.State) : Prop :=
  C = s.executionEnv.codeOwner ∧
  s.executionEnv.code = bytecode ∧
  ((s.pc.toNat = 0  ∧ s.stack.length = 0) ∨
   (s.pc.toNat = 2  ∧ s.stack.length = 1) ∨
   …
   (s.pc.toNat = 17 ∧ s.stack.length = 7 ∧
       s.stack[2]? = some ⟨0⟩ ∧ … ∧ s.stack[6]? = some ⟨0⟩) ∨
   (s.pc.toNat = 18 ∧ s.stack.length = 1) ∨
   (s.pc.toNat = 19 ∧ s.stack.length = 0))
```

Each PC has its own stack-shape clause. The PC=17 clause is the
load-bearing one: when CALL is about to execute, the stack has 0 at
index 2 (the value position), so the spawned Θ runs with `value = 0`
and Θ's σ'₁ + σ₁ frame is a balance no-op.

Closure proofs (in `BytecodeFrame.lean`):

* `RegisterTrace_Z_preserves` — `Z` (the X-loop's gas-gate) only
  modifies `gasAvailable`; trivial.
* `RegisterTrace_step_preserves` — the **14-case bytecode walk**
  (~230 LoC). For each PC, looks up the decoded op, unfolds the
  appropriate `EvmYul.step` body, derives the post-state's pc and
  stack length, and lands in the next PC's disjunct.
* `RegisterTrace_decodeSome`, `RegisterTrace_op_in_8` — closed by
  `decide` over the bytecode + the 14 valid PCs.
* `RegisterTrace_v0_at_CALL` — extracts `stack[2]? = some 0` from
  the PC=17 disjunct.
* `RegisterTrace_initial` — uses the `I_code_at_C_is_Register_bytecode`
  axiom to derive `I.code = bytecode` from `I.codeOwner = C`, then
  the initial PC=0 + empty stack.

#### 2. `ΥTailInvariant` — the post-dispatch tail

Says: *the post-Υ substate `A`'s `selfDestructSet` and dead-account
filter both exclude C.*

Discharged in `BalanceMono.lean` from two consumer-supplied
hypotheses:

* `RegSDExclusion` — `C ∉ A.selfDestructSet`. Holds in practice
  because Register has no SELFDESTRUCT and any sub-frame's `Iₐ ≠ C`
  by `I_code_at_C_is_Register_bytecode` (anything else at C runs
  Register, which has no SELFDESTRUCT).
* `RegDeadAtσP` — `State.dead σ_P C = false`. Holds because C's
  account in σ_P retains Register's bytecode (non-empty code), so
  the dead-account filter cannot include C.

These are stated structurally on Υ's `.ok` output and are vacuously
`True` on `.error`. They mirror the spirit of T5: real-world
structural facts about the tx execution that the contract author
trusts the protocol to satisfy. The framework's open future work is
to derive these inside Lean by strengthening `Θ_balanceOf_ge` /
`Λ_balanceOf_ge` to expose substate-tracking and code-frame outputs.

#### 3. `ΥBodyFactors` — the body-factorisation witness

Says: *Υ's body factors as Θ/Λ-dispatch composed with a pure tail
transformation; the post-dispatch state σ_P satisfies `balanceOf σ_P
C ≥ balanceOf σ C`.*

Discharged by `register_Υ_body_factors` (in `BalanceMono.lean`),
which:

1. Cases on `tx.base.recipient` (`some t` → Θ-dispatch; `none` →
   Λ-dispatch).
2. In the Θ branch, applies `Θ_balanceOf_ge` at the post-debit state σ₀.
3. In the Λ branch, applies `Λ_balanceOf_ge` at σ₀.
4. Threads the `RegDeadAtσP` hypothesis to discharge the second
   conjunct of `ΥBodyFactors`.

The chain `σ → σ₀ → σ_P` is bounded by:

* `balanceOf σ₀ C = balanceOf σ C` (sender debit at `S_T ≠ C` doesn't
  touch C; from `balanceOf_σ₀_eq`).
* `balanceOf σ_P C ≥ balanceOf σ₀ C` (from `Θ_balanceOf_ge` /
  `Λ_balanceOf_ge`, with `bytecodePreservesBalance C` as the at-C
  witness).

## Why is this hard?

Reentrancy is the headline difficulty. When Register's CALL at PC=17
spawns an outer call, the recipient is `CALLER` — which could be C
itself (self-call) or any other address. The recursive Ξ either:

* Runs Register again at C (self-call): handled by the strong-fuel
  induction inside `Ξ_balanceOf_ge_bundled`, which feeds itself via
  `ΞAtCFrame C n` at smaller fuel.
* Runs some other contract X ≠ C: handled by `ΞFrameAtC C n` (also
  fuel-bounded, also from the strong induction).

The whole point of the `MutualFrame` machinery is to feed both forms
of the IH simultaneously through the joint Θ/Λ/Ξ closure.

## Files in this proof

| File | Purpose | LoC |
|------|---------|-----|
| `Program.lean` | Bytecode + opcode listing | ~80 |
| `Invariant.lean` | `RegInv σ C b₀` predicate | ~40 |
| `BytecodeFrame.lean` | `RegisterTrace` + 6 closure lemmas + `bytecodePreservesBalance` | ~800 |
| `BalanceMono.lean` | Composition: helpers + `register_balance_mono` | ~360 |

## Boundary hypotheses, in plain English

The seven hypotheses on `register_balance_mono` correspond to:

1. **`hWF : StateWF σ`** — total ETH supply is < 2^255. Real-world
   ground truth (T1).
2. **`hInv : RegInv σ C b₀`** — pre-tx, C has at least `b₀` ETH and
   has Register's bytecode installed. Provided by the deployment.
3. **`hS_T : C ≠ S_T`** — Register isn't the tx sender. (If it were,
   the tx-level gas debit would drain its balance.)
4. **`hBen : C ≠ H.beneficiary`** — Register isn't the miner.
   (Technically not strictly needed since miner credits are
   non-negative, but kept for narrative clarity.)
5. **`hValid : TxValid σ S_T tx H H_f`** — the tx passes node-level
   validation: upfront cost ≤ sender balance, no underflow on debit,
   value fundable, recipient no-wrap. Was a global axiom; now an
   explicit hypothesis the caller provides.
6. **`hSDExcl`** — post-tx substate's SD-set excludes C.
7. **`hDeadAtσP`** — post-Θ/Λ state has non-empty code at C
   (Register's bytecode preserved).

(6) and (7) are call-tree-level structural facts. They follow from
"Register's bytecode contains no SELFDESTRUCT" + the `I_code_at_C`
axiom + T5; both are not currently derivable inside Lean from the
closed Θ/Λ outputs alone, since `Θ_balanceOf_ge` / `Λ_balanceOf_ge`
expose balance + StateWF + cA-exclusion but not substate-tracking or
code-preservation. Strengthening Θ/Λ to expose substate / code-frame
information is the main path to discharging (6)+(7) inside Lean —
that's a separate refactor of `MutualFrame.lean`.
