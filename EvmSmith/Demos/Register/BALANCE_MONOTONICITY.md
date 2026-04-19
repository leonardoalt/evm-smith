# Register — balance monotonicity: manual proof

Informal proof that Register's balance is non-decreasing across one Ethereum
transaction, written at the EVM-semantics level (no Lean).

## The claim

Let `C` be Register's address. Let `β(t)` be the balance of `C` at EVM
simulation time `t`. A transaction executes from time `0` to time `T`.

**Theorem.** `β(T) ≥ β(0)`.

## Boundary hypotheses

1. **`sender ≠ C`** — `C` is not the transaction sender. (Otherwise `Υ`'s
   pre-dispatch gas debit `β(sender) -= gasLimit·price + blobFee` would
   drain `β(C)`.)
2. **`miner ≠ C`** — `C` is not the block miner. (Not strictly needed for
   monotonicity — the miner-credit is non-negative — but excludes a corner
   case where miner = sender coincidentally.)
3. **No `CREATE` or `CREATE2` step in the transaction's call tree produces
   address `C`.** (Otherwise a nested untrusted call could deploy foreign
   code at `C` mid-transaction, after which arbitrary code would execute
   with `codeOwner = C`.) Under Keccak-256 collision-resistance this holds
   for any sane transaction — it's a Keccak-collision boundary assumption,
   not an adversarial property.

## The argument

### Step 1 — classify balance-changing opcodes

From the EVM spec, over a single opcode step `t → t+1`, the only ways any
address's balance `β(·)` can change are:

- **`SELFDESTRUCT`** executed by the current frame, whose executing
  code-address is `Iₐ`. Effect: `β(Iₐ) → 0`; `β(recipient) += old β(Iₐ)`.
- **`CALL`** / **`CALLCODE`** / **`DELEGATECALL`** / **`STATICCALL`** /
  **`CREATE`** / **`CREATE2`** with value `v`. Effect: `β(Iₐ) -= v`;
  `β(recipient) += v`. (DELEGATECALL and STATICCALL always have `v = 0`.)
- **Transaction-level**: `Υ`'s pre-dispatch debit `β(sender) -= gasLimit·p
  + blobFee`; post-dispatch credits `β(sender) += refund` and
  `β(miner) += (gasLimit - gStar)·f`.

Every other opcode leaves all balances pointwise unchanged.

### Step 2 — when can `β(C)` decrease?

Scan step 1:

- **Tx-level entry debit from `sender`**: decreases `β(sender)`. Hits
  `β(C)` only if `sender = C`. Excluded by hypothesis 1.
- **Tx-level exit credits**: non-decreasing in all addresses.
- **`SELFDESTRUCT`**: decreases `β(Iₐ)`. Hits `β(C)` only if `Iₐ = C`
  at that moment.
- **`CALL`-family with `v > 0`**: decreases `β(Iₐ)`. Hits `β(C)` only if
  `Iₐ = C` at that moment.

So the only execution steps that *could* decrease `β(C)` are steps
executing inside a frame where **the current executing address is `C`**,
and that frame is running one of: `SELFDESTRUCT`, `CALL` with `v > 0`,
`CALLCODE` with `v > 0`, `CREATE` with `v > 0`, or `CREATE2` with `v > 0`.

### Step 3 — what runs inside frames where `Iₐ = C`?

A frame has `Iₐ = C` exactly when it was entered by a message call whose
recipient is `C`. Such a frame executes `code(C, t)` — the runtime code
deployed at address `C` at the moment the frame was entered.

At `t = 0`: `code(C, 0) = Register's bytecode` (given by deployment).

At `t > 0`: `code(C, t)` can only change if some step deposits new code
at `C`. This happens exactly when a successful `CREATE` or `CREATE2`
whose computed address equals `C` runs to completion. Register's own
bytecode contains no `CREATE`/`CREATE2` opcode, but a nested external
contract could. Hypothesis 3 excludes this possibility.

Under hypothesis 3: `code(C, t) = Register's bytecode` for all `t ∈ [0, T]`.

### Step 4 — inspect Register's bytecode

Register's runtime (20 bytes):

```
  pc  bytes    mnemonic            effect
  0   60 00    PUSH1 0x00          storage-value calldata offset
  2   35       CALLDATALOAD        x = cd[0:32]
  3   33       CALLER              sender
  4   55       SSTORE              storage[sender] = x
  5   60 00    PUSH1 0             retSize
  7   60 00    PUSH1 0             retOffset
  9   60 00    PUSH1 0             argsSize
  11  60 00    PUSH1 0             argsOffset
  13  60 00    PUSH1 0             value = 0
  15  33       CALLER              address = sender
  16  5a       GAS                 gas = remaining
  17  f1       CALL                invoke; reentrance possible here
  18  50       POP                 discard success flag
  19  00       STOP
```

By direct inspection:

- **No `SELFDESTRUCT` opcode** anywhere in the bytecode. So `SELFDESTRUCT`
  with `Iₐ = C` never executes.
- **Exactly one `CALL` opcode** (at `pc = 17`). Its stack arguments —
  built up by the preceding `PUSH1 0` at `pc = 13` — force `value = 0`.
  So `CALL` from `Iₐ = C` always has `v = 0`.
- **No `CALLCODE`, `CREATE`, or `CREATE2` opcodes.**

### Step 5 — conclusion

Combining steps 2, 3, 4: no step in the transaction decreases `β(C)`.
Therefore `β(T) ≥ β(0)`. ∎

## One-paragraph summary

> Register's bytecode contains no `SELFDESTRUCT` and its only `CALL` has
> `value = 0`. Every EVM opcode that debits an address's balance either
> (a) is `SELFDESTRUCT` executing at that address, or (b) is a
> `CALL`-family opcode from that address with value > 0. Hence no opcode
> debits `C` unless it runs while `codeOwner = C` with Register's
> bytecode, and Register's bytecode contains neither — under the boundary
> assumption that no `CREATE`/`CREATE2` in this tx produces address `C`.

## Notes on reentrancy

The global-timeline argument doesn't need a separate reentrance induction.
Reentrant calls are just frames in the call tree; every frame with
`Iₐ = C` runs the same bytecode (by step 3), so step 4 applies uniformly
to every such frame. Frames with `Iₐ ≠ C` cannot debit `β(C)` at all
(by step 2). At the global timeline level all frames are treated
uniformly — no inductive case split on call depth is needed.

## What would be needed for a Lean proof

- **Per-opcode frame lemma** (one-time, ~500 lines mechanical): for every
  opcode other than `SELFDESTRUCT`, `EvmYul.step op arg s` leaves
  `s.accountMap` pointwise unchanged.
- **`SELFDESTRUCT` case** (~50 lines): executed at `Iₐ`, the balance
  transfer preserves `β(C)` when `Iₐ ≠ C`.
- **`EVM.step` routing** (~200 lines): for `CALL`/`CALLCODE`/
  `DELEGATECALL`/`STATICCALL`/`CREATE`/`CREATE2`, the semantics route
  through the `call`/`Lambda` helpers; balance effects delegate to those.
- **`X` / `Ξ` preservation** (~100 lines each): fuel induction composing
  the per-step lemmas.
- **`Θ` preservation** (~200 lines): value-transfer frame + `Ξ` IH.
- **`Υ` housekeeping** (~150 lines): compose `Θ`/`Lambda` dispatch with
  sender-debit, refund, beneficiary-fee, SD sweep, dead-account sweep,
  tstorage-wipe frame lemmas.

Total: ~1200 lines of mechanical Lean proof. All of it is local — the
argument is standard frame-composition, nothing novel.

Key helper lemmas already available in `EvmSmith/Lemmas/BalanceOf.lean`:
`find?_insert_ne`, `find?_erase_ne`, `find?_erase_fold_ne`,
`find?_increaseBalance_ne`, `balanceOf_insert_ne`, `balanceOf_erase_ne`,
`balanceOf_erase_fold_ne`, `balanceOf_increaseBalance_ne`,
`balanceOf_increaseBalance_self_of_noWrap`.

Per-opcode step equations already available in `EvmSmith/Lemmas.lean`
(covers Register's bytecode in full): `runOp_push1`, `runOp_calldataload`,
`runOp_caller`, `runOp_sstore`, `runOp_pop`, `runOp_stop`, and more.
