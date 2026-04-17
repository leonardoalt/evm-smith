# Foundry tests for the `add3` runtime bytecode

This Foundry project tests the runtime bytecode defined in
`../Program.lean :: bytecode`. The tests install the 19-byte runtime
at a test address via `vm.etch`, then call it with raw calldata (no
function selector) to verify it sums three calldata words correctly.

## Running

From this directory:

```bash
forge test
```

Requires Foundry ≥ 1.0 on `PATH` and the `lib/forge-std` submodule
initialised (`git submodule update --init --recursive` from the repo
root).

## Bytecode provenance

`test/Add3.bytecode.hex` is generated from the Lean side by:

```bash
# from the repo root:
lake exe add3-dump-bytecode
```

Re-run this whenever `Program.lean :: bytecode` changes. The hex file
is committed to git so `forge test` works without first running
`lake exe`.

## What the tests cover

- `test_Add3_concrete` — basic sums (1+2+3, 10+20+30, 0+0+0).
- `test_Add3_wraps` — arithmetic wrapping at 2^256.
- `test_Add3_shortCalldata` — empty, 32-byte, 64-byte calldata
  (`CALLDATALOAD` zero-pads past end of calldata).
- `test_Add3_longCalldata` — 128-byte calldata (trailing word
  ignored).
- `testFuzz_Add3` — 256-run fuzz sweep over `(uint256, uint256,
  uint256)` triples, matching `unchecked { a + b + c }`.

## See also

- `../Program.lean` — the `Program` value and the 19-byte `bytecode`.
- `../Proofs.lean` — the Lean proof that the compute prefix produces
  `a + b + c` on the stack. (The `MSTORE`/`RETURN` suffix's
  byte-level behaviour is exercised by these tests rather than
  proved — see the `Proofs.lean` docstring for why.)
