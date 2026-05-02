# Foundry tests for the `Register` runtime bytecode

The `Register` contract is a 20-byte EVM program that reads one
`uint256` from calldata, stores it at `storage[msg.sender]` (`SSTORE`
+ `CALLER`), then issues a `CALL` to `msg.sender` with `value = 0` —
exposing reentrancy as part of the safety question.

This test suite covers the storage-update behavior end-to-end against
a real `forge` EVM:

- `test_Register_writes_slot` — the calldata word lands at
  `storage[sender]`.
- `test_Register_isolates_senders` — distinct senders write to
  distinct slots; storage is keyed by `msg.sender`.
- `test_Register_overwrites` — a second call from the same sender
  overwrites the previous slot value.
- `test_Register_empty_calldata_stores_zero` — `CALLDATALOAD` on
  empty calldata pushes 0.
- `test_Register_zero_value_clears_slot` — writing `0` zeros the
  slot.
- `test_Register_one_sender_does_not_touch_another` — overwriting
  one sender's slot leaves another sender's slot intact.

## Running

From this directory:

```bash
forge test
```

Requires Foundry ≥ 1.0 on `PATH` and the `lib/forge-std` submodule
initialised.

## Bytecode provenance

`test/Register.bytecode.hex` is generated from the Lean side by:

```bash
# from the repo root:
lake exe register-dump-bytecode
```

Re-run whenever `Program.lean :: bytecode` changes; commit the
updated hex file.

## See also

- `../Program.lean` — assembly listing with PCs and the 20-byte
  `bytecode` value.
- `../BalanceMono.lean` — sorry-free `register_balance_mono` headline
  theorem (Register's balance is non-decreasing across any single
  Ethereum transaction, under arbitrary reentrancy).
- `../BALANCE_MONOTONICITY.md` — end-to-end walkthrough of the proof
  structure.
