# Weth solvency invariant — informal proof

**Claim** (informally): for the Weth contract deployed at address `C`,
at every point during a transaction's execution,

> `accountMap[C].balance ≥ Σ_{a : Address} storage[C][addressSlot a]`

i.e. the contract's ETH balance is at least as large as the sum of all
users' token balances tracked in storage.

A stronger property — `balance == Σ tokens` — is *not* true in
general, because external sources (SELFDESTRUCT-funded transfers,
coinbase rewards, and `CREATE`-with-value to a CREATE-derived address
that happens to equal `C`, the last excluded by Keccak T5) can
inflate balance without increasing storage. So the right shape is
the **`≥` form**.

Vocabulary used throughout:
- `C` is Weth's deployment address.
- `S_T` is the transaction sender.
- Greek `Υ` is the transaction-level driver, `Θ` the message call
  iterator, `Ξ` the interpreter, all from EVMYulLean.

## What Weth does

Deposit-payable two-function contract (86 runtime bytes):

```
deposit()  payable :  storage[msg.sender] += msg.value
withdraw(uint256 x):  require storage[msg.sender] ≥ x
                       storage[msg.sender] -= x      ← state update first
                       CALL msg.sender value=x       ← external interaction after
                       require CALL succeeded
```

Storage layout: a user `a`'s balance is at slot `addressSlot a` (the
20-byte address zero-extended to 32 bytes — Solidity's `mapping(address => uint256)`
layout for a single mapping at slot 0).

**Reentrancy posture**: storage is decremented *before* the external
`CALL`. Any reentrant invocation of `withdraw` from the inner CALL's
recipient sees the already-decremented balance, so the next withdraw
underflows the `LT` check and reverts.

## Why the invariant holds

Define
```
β(σ) := balanceOf σ C
S(σ) := Σ_a storageOf σ C (addressSlot a)
I(σ) := β(σ) ≥ S(σ)        — the solvency invariant
```

We need: `I(σ) ⇒ I(σ')` for every state transition `σ ⟶ σ'` reachable
in a tx where `C` is Weth's deployment address.

State transitions break into:
- **Tx-level prefixes/suffixes** (sender debit, refund, beneficiary
  fee, SELFDESTRUCT sweep, dead-account sweep, tstorage wipe), all
  outside Ξ.
- **Steps inside Ξ** at any frame `I` in the call tree.

### Tx-level transitions (outside Ξ)

For each tx-level transition, neither `β(C)` nor storage at `C` is
touched:

* **Sender debit** (`σ₀ := σ.insert S_T {balance: balance - upfrontCost}`).
  `S_T ≠ C` (Weth is not the tx sender — it has no private key). So
  `β(σ₀) = β(σ)` and storage at `C` is unchanged: `S(σ₀) = S(σ)`.
* **Refund + beneficiary fee** at `σ_P → σ_F`. Both increase
  balance at addresses `S_T` and `H.beneficiary`, both ≠ `C`.
  `β(σ_F) = β(σ_P)`, `S(σ_F) = S(σ_P)`.
* **SELFDESTRUCT sweep** (`A.selfDestructSet.foldl erase σ`). For
  Weth the SD-set excludes `C` (Weth's bytecode has no SELFDESTRUCT;
  see assumptions). So balance and storage at `C` are unchanged.
* **Dead-account sweep**. Filters out accounts that are dead at `σ_F`.
  `C`'s account is non-dead (Weth's bytecode is non-empty), so `C`
  is not erased.
* **tstorage wipe**. Touches every account's transient storage; not
  the persistent storage we sum over.

So `I` is preserved across all Υ tail steps. The only place where `I`
can change is **inside Ξ**, in steps that touch either `β(C)` or
`storage[C][·]`. We classify those steps next.

### Steps inside Ξ that can change `β(C)` or `S`

For every step at every frame `I` in the call tree, we examine what
can change. Let `s` be the pre-step state, `s'` the post-step state.

#### Frames at `I.codeOwner ≠ C`

Most of the call tree. The frame is running someone else's bytecode,
not Weth's. What can such a frame do that affects β(C) or S?

* **Storage at `C`**: only `SSTORE` modifies storage, and only at
  `s.executionEnv.codeOwner`. Since the codeOwner is `≠ C`, storage
  at `C` is untouched. `S(σ') = S(σ)`.
* **Balance at `C`**: changeable via:
  - **CALL/CALLCODE/STATICCALL/DELEGATECALL** from this frame to
    Weth: routed through Θ, which transfers `value` from the source
    frame's `Iₐ` to `C`. β(C) **increases** by `value` ≥ 0. `I` is
    preserved (only the LHS goes up).
  - **SELFDESTRUCT** of this frame, beneficiary = `C`: β(C)
    **increases** by the destructing frame's whole balance. `I`
    preserved.
  - **CREATE/CREATE2** with non-zero value targeting `C` as the
    derived address: by Keccak T5 (`lambda_derived_address_ne_C`),
    no derived address equals `C`. So this case is excluded.
  - Coinbase reward etc. happens outside Ξ.
* No other op at a non-Weth frame can affect either side.

So at any frame with codeOwner ≠ C, the invariant is preserved (in
fact, β(C) is monotone-non-decreasing).

#### Frames at `I.codeOwner = C` running Weth's bytecode

By the deployment-pinned code identity (assumption `DeployedAtC C`):
any such frame runs Weth's exact 86-byte bytecode. Walk through it:

##### Dispatch prefix (PCs 0–31)

PUSH/CALLDATALOAD/SHR/DUP/EQ/PUSH/JUMPI ×2 / REVERT path. None of
these ops touch `accountMap[C].balance` or `storage[C]`. β and S
unchanged.

##### Deposit block (PCs 32–41)

Stack effect: pops nothing of interest, eventually reaches
`SSTORE` at PC 40 storing `(s_old + msg.value)` at slot `addressSlot
msg.sender`.

Frame-level reasoning:
- This frame at `codeOwner = C` was *entered* via Θ, with a value
  transfer of `msg.value` already performed in σ'₁/σ₁: the caller's
  balance debited by `msg.value`, `C`'s balance credited by `msg.value`.
  So `β(σ_after_value_transfer) = β(σ_before_value_transfer) + msg.value`.
- The deposit-block ops *don't* touch β. They only:
  - read calldata (no state change),
  - read CALLER (no state change),
  - read SLOAD `storage[msg.sender]` (no state change),
  - read CALLVALUE (no state change),
  - SSTORE the new balance.

So across the deposit block:
- β increase since frame entry: `+msg.value`
- S increase: only the storage entry at `addressSlot msg.sender`
  changes from `old` to `old + msg.value`. Difference: `+msg.value`.
- ΔS = ΔS at slot `addressSlot msg.sender` = `+msg.value`.
- Δβ = `+msg.value` (from the value transfer).

Net: `Δ(β − S) = 0`. `I` preserved.

##### Withdraw block (PCs 42–79)

- PCs 42–55: arithmetic reads + the `LT` gate. No state change. If
  balance < x: jump to revertLbl (80) → REVERT, no state change.
- PCs 56–60: `SUB` then `SSTORE` of `storage[msg.sender] = old − x`.
  ΔS at this slot: `−x`. Δβ: 0 (SSTORE doesn't touch balance).
  After this step: `β − S = β − S + x`, i.e. `I` *temporarily
  becomes more slack* (balance can withstand x extra).
- PCs 61–72: stack setup + `CALL` with `value = x`, recipient =
  CALLER. Routed through Θ, which transfers `x` from `C` to CALLER:
  Δβ at C: `−x`.
  - The inner Ξ run at the recipient could be *anyone's* code
    (including Weth itself, if CALLER = C — but CALLER cannot equal
    C: Weth has no private key, so it never originates a call as
    msg.sender at the EOA level, and any frame nested inside has its
    own caller, with C only in the call chain via the original
    transaction sender).
  - During the inner Ξ run: by the codeOwner ≠ C frame analysis
    above, β(C) is monotone-non-decreasing and S is unchanged
    (storage[C] is only modifiable from frames at C). So
    `I` is preserved through the inner Ξ.
  - **What about reentrant CALL into Weth's withdraw?** The inner
    code can call back into C. That spawns a new Weth frame at C.
    The reentrant frame sees `storage[msg.sender]` already
    decremented by the outer withdraw's SSTORE (effects before
    interactions). The `LT` check at PC 51 either reverts (preserving
    I trivially) or proceeds with another decrement-then-call,
    which we handle by induction.
- PCs 73–77: ISZERO + JUMPI on success flag. No state change beyond
  the inner Ξ.
- PCs 78–79: POP, STOP. No state change.

Net for the whole withdraw block (without reentry):
- ΔS: `−x` from the SSTORE at PC 60.
- Δβ at C: `−x` from the CALL at PC 72 (plus any monotone increase
  from the inner Ξ).
- `Δ(β − S) ≥ 0`. `I` preserved.

With reentry, by induction on the call depth (bounded by the EVM's
1024-frame limit and the gas budget): each reentrant withdraw
follows the same pattern — decrement-then-call — so `I` is preserved
recursively. The base case is the leaf frame (deepest nesting),
where the inner CALL hits gas/depth limit or runs a no-op.

##### Revert path (PCs 80–85)

`REVERT` halts the frame and rolls back all state changes since the
frame's entry. Net effect on the parent's σ: same as if the frame
had never run (modulo gas). `I` trivially preserved.

### Putting it together

For the OUTER Υ run starting from a state with `I(σ) = true`:
1. Tx-level prefix preserves I (sender ≠ C).
2. Top-level dispatch (Θ or Λ) enters either:
   - Λ: this is a CREATE tx. Λ runs the constructor's Ξ. By Keccak
     T5 the deployed address ≠ C; no Λ frame is ever at codeOwner = C.
     So the inner Ξ runs at codeOwner ≠ C throughout, and I is
     preserved by the non-C analysis above.
   - Θ: this is a regular tx. If the recipient is C, Θ enters Weth's
     deposit/withdraw frame; the per-block analysis above applies.
     If the recipient ≠ C, the inner Ξ never reaches a Weth frame
     unless it explicitly CALLs C; the same analysis applies to that
     CALL.
3. Tx-level tail (refund + beneficiary + sweeps + wipe) preserves I.

Conclusion: `I(σ) ⇒ I(σ')` for σ' the post-Υ state.

## Summary of the load-bearing facts

The proof relies on:

1. **Storage at C is only modifiable from a frame with codeOwner = C**
   — pure EVM semantics fact about SSTORE. (Provable; not assumed.)
2. **Balance at C is changeable only by Θ value-transfer (in or out),
   SELFDESTRUCT-with-beneficiary-C, or CREATE/CREATE2 to C** — pure
   EVM semantics. (Provable.)
3. **Keccak T5**: `lambda_derived_address_ne_C` excludes
   CREATE/CREATE2 from producing C. (Existing axiom.)
4. **Deployment-pinning**: `DeployedAtC C` — any frame at codeOwner = C
   runs Weth's bytecode. (Hypothesis on the consumer theorem.)
5. **Weth has no SELFDESTRUCT** in its bytecode — `decide` over the
   86 bytes. (Provable.)
6. **The deposit and withdraw blocks balance their `Δβ` and `ΔS`
   pointwise** — discharged by a per-PC bytecode walk
   (`WethTrace_step_preserves`).
7. **C is not the tx sender**, **not the miner**, **not the
   transaction recipient at the tx level when the recipient is a
   non-Weth address**, etc. (Real-world boundary hypotheses.)

Three pieces are specific to the relational solvency shape (not
shared with monotone-balance proofs):

- A *relative* invariant `I = (β ≥ S)` rather than a monotone
  lower bound.
- Storage-sum reasoning: the `S(σ) = Σ_a storageOf σ C (addressSlot a)`
  predicate and its preservation under SSTORE/insert/erase.
- A non-zero-value CALL chain at the at-C step, handled by the
  framework's `_inv_aware` slack-dispatch variant (see
  [`REPORT_FRAMEWORK.md`](./REPORT_FRAMEWORK.md)).

The proof has shipped — see [`REPORT_WETH.md`](./REPORT_WETH.md) for
the live conditional hypotheses and theorem statement.
