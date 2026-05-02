# Trust assumptions

The proofs in EVM-Smith are conditional on a small, explicit set of
assumptions. This document spells them out so consumers can see
exactly what they're trusting and why.

The assumptions split into three categories:

1. [Logical foundations](#1-logical-foundations) — Lean's core.
2. [EVMYulLean modeling](#2-evmyullean-modeling) — what the EVM
   formalization assumes about the actual EVM.
3. [Per-contract structural facts](#3-per-contract-structural-facts) —
   contract-specific assumptions bundled in each proof's
   `*Assumptions` structure.

For the explicit `axiom` declarations referenced from the framework
(T2 and T5), see [`AXIOMS.md`](./AXIOMS.md).

---

## 1. Logical foundations

You trust **Lean 4's type checker** — that the proof compiles. The
type checker is small (a few thousand lines of trusted code) and
widely used. Every Lean / Mathlib proof in the broader ecosystem
relies on the same foundation.

You also trust Lean's three foundational axioms (propositional
extensionality, quotient soundness, classical choice). These are
shared across the Lean ecosystem and are not specific to this
project.

If the Lean kernel or its core axioms were unsound, every Lean proof
would be unsound. This is the same trust foundation as Coq / Agda /
Isabelle / any other proof assistant.

---

## 2. EVMYulLean modeling

EVMYulLean ([`leonardoalt/EVMYulLean`](https://github.com/leonardoalt/EVMYulLean))
is a Lean 4 formalization of Ethereum's Yellow Paper. The bulk of it
is **mechanically-checked theorems** — these you verify by running
`lake build`, not by trusting them.

What you trust beyond the type checker:

### 2.1 Two explicit axioms

EVMYulLean has exactly two `axiom` declarations the EVM-Smith proofs
depend on:

- `precompile_preserves_accountMap` (Yellow Paper section T2)
- `lambda_derived_address_ne_C` (Yellow Paper section T5)

Full details — what each says, why it's stated as an axiom, the risk
if false, and the path to discharging it — are in
[`AXIOMS.md`](./AXIOMS.md).

### 2.2 Definitional faithfulness

The EVM is defined in EVMYulLean by the Lean definitions of
`EVM.step`, `EVM.X`, `EVM.Ξ`, `EVM.Θ`, `EVM.Lambda`, `EVM.Υ`, the
gas schedule (`EvmYul/EVM/Gas.lean`), the precompiled contracts, the
state and machine-state types, etc.

You trust that these definitions accurately model the actual EVM
behavior. EVMYulLean follows the Yellow Paper closely; bugs in the
definitions would invalidate the proofs.

This is the standard "modeling fidelity" question shared by every
formal verification project — the proof is only as good as the model
it's proving against. The Yellow Paper itself is the spec; EVMYulLean
encodes it; we use that encoding.

### 2.3 Pre-Cancun semantics — SELFDESTRUCT

EVMYulLean models the EVM as it was **before EIP-6780 (Cancun,
March 2024)**.

- **Pre-Cancun**: `SELFDESTRUCT` could remove an arbitrary contract
  from the state, transferring its balance to the beneficiary.
- **Post-Cancun**: `SELFDESTRUCT` only deletes contracts that were
  created in the same transaction. Pre-existing contracts can't be
  destroyed — `SELFDESTRUCT` just transfers their balance.

Our proofs handle the **stricter pre-Cancun semantics**. The relevant
SELFDESTRUCT-exclusion assumptions in per-contract proofs (e.g.
`*SDExclusion`) are conservatively stated against the more permissive
pre-Cancun model. On post-Cancun mainnet these assumptions are
automatically satisfied for any pre-existing deployment, since
SELFDESTRUCT can no longer delete it.

### 2.4 Gas accounting

Gas is fully tracked in EVMYulLean:

- Per-instruction gas schedule from Yellow Paper Appendix G
  (`EvmYul/EVM/Gas.lean`).
- Memory expansion cost.
- Dynamic call-gas computation (`Ccallgas`).
- The X-loop deducts gas at each step; underflow produces an
  out-of-gas `.error`.

Our proofs are **partial-correctness** statements: safety holds on
successful runs (`Υ` returns `.ok`), and the conclusion is vacuous on
errors (`.error _ => True`). We don't claim termination or
gas-bounded execution; we claim that *if* the transaction succeeds,
the safety property holds.

Out-of-gas, REVERT, invalid opcode, stack underflow — all of these
fall into the EVM's normal error handling, accurately modeled by
EVMYulLean.

---

## 3. Per-contract structural facts

Each contract proof bundles a small structure of structural
hypotheses about how the contract is set up at the chain level. The
shapes recur across demos:

### 3.1 Deployment

**`DeployedAtC C`** — the contract's specific bytecode is installed
at address `C`. Real-world: someone deployed it, in genesis or a
prior transaction, and it hasn't been replaced.

In the EVM, the only way for `C`'s code to change after deployment is
SELFDESTRUCT (pre-Cancun) or a CREATE2-collision (ruled out by T5).
So `DeployedAtC` together with the SELFDESTRUCT-exclusion below
captures "C's code is what we proved against, throughout the
transaction".

### 3.2 SELFDESTRUCT exclusion

**`*SDExclusion`** — across the entire transaction's call tree, no
`SELFDESTRUCT` instruction targets `C`.

Note this is a claim about *every* contract in the call tree, not
just the contract being proven. SELFDESTRUCT only inserts the
*executing-frame* address into the self-destruct set, so for some
other contract `D ≠ C` to add `C`, `D` would have to be running *as*
`C` — which can't happen unless `C`'s deployed code is `D`, which
`DeployedAtC` rules out.

Combined with the pre-Cancun SELFDESTRUCT modeling assumption
(section 2.3), this becomes automatic on post-Cancun mainnet.

### 3.3 Liveness at dispatch

**`*DeadAtσP`** — after the EVM's outer Θ/Λ dispatch (the layer that
handles the value transfer and call setup before code execution
begins), `C` still has non-empty code at the dispatched state.

The contract isn't un-deployed mid-transaction. This is essentially
the same fact as `DeployedAtC`, restated against the post-dispatch
state where code execution actually begins.

### 3.4 Boundary conditions

The transaction's structural facts:

- `C ≠ msg.sender` — the contract is not the transaction sender.
- `C ≠ block.beneficiary` — the contract is not the block coinbase
  recipient.

These keep the proof's account-balance reasoning clean (no special
case for the transaction's own gas-payment / coinbase reward
flowing to the contract being proved).

### 3.5 Chain-state bounds

Some proofs need facts about the chain's current balance state that
aren't derivable from any bytecode reasoning. The most common:

- **`recipient_balance + value < 2^256`** for outbound CALLs with
  non-zero value. The EVM's UInt256 arithmetic doesn't overflow on
  real chain state because the total ETH supply is bounded.

These are **genuinely irreducible** structural facts — they encode
real-world constraints (chain-state bounds, total supply, etc.) that
no amount of bytecode-level reasoning can establish.

---

## Summary table

| Layer | What you trust | Where to verify |
|---|---|---|
| Lean kernel | Type checker correctness | Lean ecosystem standard |
| Lean axioms | Propext, quotient soundness, classical choice | Lean ecosystem standard |
| EVMYulLean axioms | T2 (precompile purity), T5 (Keccak collision) | [`AXIOMS.md`](./AXIOMS.md) |
| EVMYulLean definitions | `EVM.step` / `Υ` / etc. match real EVM | Yellow Paper × source review |
| Pre-Cancun semantics | EVMYulLean models pre-EIP-6780 EVM | Strictly conservative for post-Cancun mainnet |
| Per-contract `*Assumptions` | Deployment + SD-exclusion + boundary + chain bounds | Per-demo report, e.g. [`Weth/REPORT_WETH.md`](./EvmSmith/Demos/Weth/REPORT_WETH.md) |
