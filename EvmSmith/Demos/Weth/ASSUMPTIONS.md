# Weth solvency proof — assumption list (historical, for approval)

> **Status (post-proof):** this document is the original assumption
> list circulated for approval before the proof was implemented. The
> assumption list it proposed was accepted, the proof shipped, and the
> live conditional hypotheses on `weth_solvency_invariant` are now
> documented in [`REPORT_WETH.md`](./REPORT_WETH.md) (see "What's
> still assumed (5 fields)"). Read this file for *why* each
> assumption was originally taken; read `REPORT_WETH.md` for what's
> *currently* true. Some items below (notably the Phase A.2 / `(F)`
> framework-gap items) have since been discharged.

These are the practical real-world assumptions we'd take as
hypotheses on `weth_solvency_invariant`. Each one is something a
Solidity dev writing/auditing Weth would normally assume — protocol
behaviour they don't have to think about. Mark each ✅ to accept,
✏️ to amend, or ❌ to reject.

Categorised: **(P) protocol-level** = pure EVM/blockchain trust
assumptions; **(D) deployment-level** = facts about *this specific
deployed contract* (where it lives, what bytecode it has);
**(B) tx-boundary** = the standard "Weth isn't the sender / miner"
shape; **(F) framework-gap** = items derivable in principle but
needing the open Phase A.2 closure.

---

## (P) Protocol-level — already used in Register, no change

These are *axioms* in `EVMYulLean/EvmYul/Frame/MutualFrame.lean` and
remain unchanged.

### P1. T2 — precompile purity ☐
> The 10 precompiles (ECREC, SHA256, RIPEMD160, IDENTITY, EXPMOD,
> BN_ADD, BN_MUL, SNARKV, BLAKE2_F, plus the EIP-4844 point-eval)
> do not modify the account map.

Used in Register. Standard real-world assumption: a Solidity dev
assumes `keccak256(...)` and `ecrecover(...)` are pure.

### P2. T5 — Keccak collision-resistance for `C` ☐
> No CREATE/CREATE2-derived address equals `C`.

Used in Register. The deployment address is fixed at deploy time,
and Keccak-256's collision-resistance makes it computationally
infeasible to construct a constructor + salt that hashes to `C`. A
Solidity dev assumes this when analysing storage layouts and
deployment.

---

## (D) Deployment-level — Weth analogue of Register's `DeployedAtC`

### D1. `DeployedAtC C` ☐
> For every `ExecutionEnv I` that arises during the Υ run with
> `I.codeOwner = C`, the running code `I.code` is Weth's exact 86-byte
> bytecode.

Caller-supplied hypothesis on `weth_solvency_invariant`. Same shape
as Register's. Holds in the deployment context where `C` was seeded
with Weth's bytecode and (a) Weth has no SELFDESTRUCT in its own
bytecode (so `C` is never erased), (b) by T5 no CREATE/CREATE2
overwrites `C`. Solidity devs accept this as "the deployed contract
runs the deployed bytecode."

---

## (B) Tx-boundary — same shape as Register

### B1. `C ≠ S_T` ☐
> Weth is not the transaction sender.

Weth has no private key (it's a contract), so it cannot sign txs.
Standard.

### B2. `C ≠ H.beneficiary` ☐
> Weth is not the block miner.

Two flavours: either Weth's address isn't a miner address (true in
practice; coinbase is an EOA), or even if it were, miner credit is
non-negative so the invariant survives anyway. Kept for narrative
clarity.

### B3. `StateWF σ` (T1) ☐
> Total ETH supply at the entry state σ is `< UInt256.size / 2 = 2^255`.

Same as Register. Real-world: total ETH supply is `~120M ETH ≈ 1.2 ×
10^26` wei, vastly below `2^255 ≈ 5.8 × 10^76`.

### B4. `TxValid σ S_T tx H H_f` ☐
> The transaction passes node-level validation: upfront cost ≤
> sender balance, value fundable, recipient no-wrap, etc.

Same as Register. Real-world: the node won't admit a tx that fails
this gate.

---

## (F) Framework-gap — derivable in principle, currently hypotheses

### F1. `WethSDExclusion` (analogue of `RegSDExclusion`) ☐
> The post-Υ substate's `selfDestructSet` excludes `C`.

Holds because:
- Weth's bytecode has no SELFDESTRUCT op (verifiable by a `decide`
  walk over the 86 bytes).
- Sub-frames at `Iₐ ≠ C` insert their own `Iₐ ≠ C` into the SD-set
  (by `selfdestruct_preserves_SD_exclude_C`, our committed leaf
  lemma).
- Sub-frames at `Iₐ = C` run Weth's bytecode (D1) which has no
  SELFDESTRUCT, so they don't insert anything.

Will be derivable inside Lean once Phase A.2 (joint Θ/Λ/Ξ side-channel
SD-tracking) closes — same status as Register. Until then: explicit
hypothesis, same shape.

### F2. `WethDeadAtσP` (analogue of `RegDeadAtσP`) ☐
> The post-Θ/Λ-dispatch state σ_P has non-empty code at `C` (i.e.
> `State.dead σ_P C = false`).

Holds because:
- C's code at the entry state is Weth's bytecode (non-empty).
- T5 prevents CREATE/CREATE2 from producing C.
- D1 + no-SELFDESTRUCT prevents Weth's own frames from erasing C's
  code.

Same Phase A.2 dependency as F1.

---

---

## Summary — assumption list (final)

To approve the plan, please mark:

| Category | Items | Action |
|----------|-------|--------|
| Protocol (P) | P1, P2 | Accept (already in trusted base for Register) |
| Deployment (D) | D1 | Accept as `WethDeployedAtC` hypothesis |
| Tx-boundary (B) | B1, B2, B3, B4 | Accept (same shape as Register) |
| Framework-gap (F) | F1, F2 | Accept as hypotheses *for now* (derivable when Phase A.2 lands; same posture as Register) |

**Nothing Weth-specific is an assumption.** Items previously listed as
"W" are all proof obligations — see the next section.

---

## Proof obligations — *theorems we will prove*, not assumptions

Listed here so the work is visible up front. Each one is derivable
from EVM semantics + the protocol axioms above and **must** land as a
real Lean theorem in the formalization.

### Inside the framework (`EVMYulLean/EvmYul/Frame/`)

* **`step_modifies_storage_only_at_codeOwner`** — single-step lemma:
  if `EvmYul.step op arg s = .ok s'`, then for any address `a ≠
  s.executionEnv.codeOwner`, the storage at `a` is unchanged. Pure
  SSTORE semantics. ~30 LoC, lives in `StepFrame.lean`.

* **`Θ/Λ/Ξ_storage_unchanged_outside_codeOwner`** — bundled lift of
  the above through the Θ/Λ/Ξ mutual recursion: storage at any
  address `a` is only modifiable from the chain of frames that ever
  had `codeOwner = a`. Mirrors the existing balance-frame mutual
  closure but for storage. The body-channel proof is small because
  most ops don't touch any storage; only SSTORE does.

* **Storage-sum primitives** (`StorageSum.lean`): `storageSum`,
  `storageSum_unchanged_at_other_account`, `storageSum_sstore_delta`.
  Pure RBMap.foldl reasoning.

### In Weth's directory (`EvmSmith/Demos/Weth/`)

* **`addressSlot_injective`** — `decide`-level. Zero-extend of a
  20-byte address into a UInt256 is injective.

* **Per-PC stack/storage shape lemmas** for Weth's 86-byte trace
  (`WethTrace_step_preserves`) — analogous to Register's 14-PC walk
  but ~30 PCs. Each PC case proves the per-step Δβ and ΔS deltas
  are paired in a way that preserves `WethInv`.

* **No-reentrancy-drain bytecode lemma** — derivable from the
  walk: state update at PC 60 (SSTORE the decremented balance)
  precedes the external CALL at PC 72. Reentrant withdraw frames
  see the decremented `storage[CALLER]` and either revert at the
  `LT` check (PC 51) or recurse on a strictly smaller balance,
  terminating by fuel induction.

* **`balance_changes_at_C_classified`** — exhaustively, β(C)
  changes only via Θ value transfer, SELFDESTRUCT with beneficiary
  = C, CREATE-with-value to C (excluded by T5), or coinbase reward
  (excluded by B2). For each channel, ΔS at C is paired
  appropriately (zero or matching).

These obligations together are what makes the proof real — they're
the bytecode-walk content of `WethTrace_step_preserves` plus the
storage-side helpers that pair with it. No hand-waving allowed.

---

## What's the genuinely *new* trust ask compared to Register?

**Nothing.** All `(P)`, `(D)`, `(B)`, `(F)` items have direct Register
counterparts at the exact same trust level. The Weth proof's *new
work* is entirely in the proof-obligations section above — provable
content, not trust.
