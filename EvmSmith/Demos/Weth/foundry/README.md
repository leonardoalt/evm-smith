# Foundry tests for the `Weth` runtime bytecode

The `Weth` contract is a minimal wrapped-ETH token in raw EVM
bytecode (86 bytes original, 77 bytes after the PUSH0 pass, 74
bytes after the V2 CALLER-trick pass). Two selector-dispatched
entry points:

| Selector     | Signature             | Effect                                                         |
|--------------|-----------------------|----------------------------------------------------------------|
| `0xd0e30db0` | `deposit()` payable   | `balance[msg.sender] += msg.value`                             |
| `0x2e1a7d4d` | `withdraw(uint256 x)` | if `balance ≥ x`: decrement + send `x` wei to `msg.sender`; else revert |

This test suite covers:

- **13 concrete and fuzz tests** (`Weth.t.sol`) for the happy paths,
  wrapping edge cases, short/long calldata, unknown selectors, and
  empty calldata.
- **`test_Weth_reentrancy_does_not_drain`** — deploys a malicious
  attacker contract whose `receive()` tries to re-enter `withdraw`
  during the outer CALL; the checks-effects-interactions ordering
  in the bytecode means the nested call sees the already-decremented
  balance and the `LT` gate blocks it.
- **Two invariant tests** (256 fuzz runs × 50 depth = 12 800
  transition checks each):
  - `invariant_user_funds_never_lost` — `Σ storage[sender] ≤
    contract.balance`. Weakened from equality to `≤` to tolerate
    force-fed ETH (e.g. via `SELFDESTRUCT` or coinbase rewards)
    that arrives outside our bytecode.
  - `invariant_ghost_accounting_consistent` — handler-ghost
    accounting matches contract balance.
- **`WethGasCompare.t.sol`** — 4-way per-tx gas comparison across
  the original bytecode, two optimized variants, and an idiomatic
  Solidity port. See [Optimizations](#optimizations-and-equivalence-proofs)
  below.

## Optimizations and equivalence proofs

The latest commits add two layered optimization passes on top of the
86-byte original. Each pass is shipped with a sorry-free Lean
equivalence proof against the previous variant, so the
`weth_solvency_invariant` theorem (proved against the original
bytecode in `../Solvency.lean`) lifts to every optimized variant
through observable equivalence.

| Variant      | Size      | Source              | Lean equivalence proof    | Hex artifact                       |
|--------------|----------:|---------------------|---------------------------|------------------------------------|
| `WETH_ORIG`  | 86 bytes  | `../Program.lean`            | (baseline)                       | `test/Weth.bytecode.hex`           |
| `WETH_OPT`   | 77 bytes  | `../OptimizedProgram.lean`   | block-level vs `WETH_ORIG`       | `test/Weth.optimized.bytecode.hex` |
| `WETH_OPT2`  | 74 bytes  | `../OptimizedProgramV2.lean` | block-level vs `WETH_OPT`        | `test/Weth.optimizedV2.bytecode.hex` |
| `WETH_SOL`   | 517 bytes | `src/WethSolidity.sol`       | (different storage layout — behavioral parity only) | (deployed via `new WethSolidity()`) |

### V0.5: 1-byte revert-tail peephole (`OptimizedProgram.lean`, early version)

A throwaway warm-up pass — `PUSH1 0; PUSH1 0; REVERT` (the final
revert tail) becomes `PUSH1 0; DUP1; REVERT` (4 bytes vs 5, same 3-gas
ops). Saves 1 byte, 0 gas, and shifts no PC labels because it sits
at the end of the bytecode. Was superseded by V1 below; the
equivalence proof technique (per-block `runSeq`-fusion via
`runSeq_cons_ok` plus per-opcode `runOp_*` lemmas, then an
observable-equivalence corollary stating both runs land in `.ok` of
a shared post-state helper) carries forward.

### V1 — PUSH0 pass (`OptimizedProgram.lean`)

EIP-3855: every `PUSH1 0` (`60 00`, 2 bytes, 3 gas) in the runtime
becomes `PUSH0` (`5f`, 1 byte, 2 gas). Nine swap sites; three
`PUSH2 <label>` immediates shift to compensate; new label values
`depositLblOpt = 29`, `withdrawLblOpt = 39`, `revertLblOpt = 73`.

The proof structure: split the bytecode into the four blocks where
`PUSH1 0` appears (`selectorLoad`, `noSelectorRevert`, `callPushes`
— the four CALL-arg pushes — and the final `revertBlock`), state
each as a pair of `EvmSmith.Program` values, and prove a per-block
equivalence theorem of the shape:

> Both `runSeq orig s` and `runSeq opt s` land in `.ok` of an
> explicit shared post-state helper (`selectorLoadPost`,
> `revertPost`, `fourZerosPost`) parameterized over the differing
> `pcEnd`.

Observable-equivalence corollaries derive
`r_orig.{stack,toState,toMachineState} = r_opt.{...}` by `rfl`
against those helpers. All non-swap sites remain byte-identical.

### V2 — CALLER-twice + drop-POP (`OptimizedProgramV2.lean`)

Three runtime-gas wins layered on top of V1, exploiting that
`CALLER` is a `BASE` (2-gas) opcode while `DUP1` / `SWAP1` are
`VERYLOW` (3-gas):

- **Deposit body**: drop `DUP1` after the first `CALLER`, replace
  the `SWAP1` before `SSTORE` with a second `CALLER`. Saves 4 gas
  + 1 byte per deposit.
- **Withdraw body**: same trick. `DUP3` collapses to `DUP2` because
  `sender` no longer sits between `bal` and `x` on the stack. Saves
  4 gas on success, 3 on insufficient-balance revert, 1 byte.
- **Drop the dead `POP` before `STOP`** on withdraw success: the
  leftover `x` is discarded with the call frame on halt anyway.
  Saves 2 gas + 1 byte per successful withdraw.

Proofs (all sorry-free, in `OptimizedProgramV2.lean`):

- `depositBlock_v2_equiv` — full state agreement modulo `pc`.
- `withdrawPreCallBlock_run` / `withdrawPreCallBlockV2_run` — both
  pre-CALL success paths land at the shared SSTORE post-state under
  `UInt256.lt bal x = 0`.
- `postCallSuccessTail_v2_equiv` — halt-state agreement; the stacks
  differ but are unobservable post-frame.

### Measured per-tx gas (Foundry, EIP-3855 schedule)

From `forge test --match-contract WethGasCompareTest -vv`:

| path                 | orig (86B) | PUSH0-opt (77B) | V2-opt (74B) | Solidity (517B) | Δ V1 vs orig | Δ V2 vs V1 | Δ Sol vs orig |
|----------------------|-----------:|----------------:|-------------:|----------------:|-------------:|-----------:|--------------:|
| `deposit()`          |     31 789 |          31 788 |       31 784 |          32 052 |           −1 |         −4 |          +263 |
| `withdraw()` ok      |     32 642 |          32 637 |       32 631 |          33 093 |           −5 |         −6 |          +451 |
| `withdraw()` insuff. |      5 200 |           5 197 |        5 194 |           5 419 |           −3 |         −3 |          +219 |
| bad selector         |      2 998 |           2 995 |        2 995 |           3 061 |           −3 |          0 |           +63 |

`WethGasCompareTest` asserts `gOpt ≤ gOrig` and `gOpt2 ≤ gOpt` on
every path, plus a `test_behavior_parity_deposit_withdraw` round
that confirms storage matches across all four impls after a
deposit + partial withdraw (using `_rawSlot` for the bytecodes,
`_solSlot` for Solidity's keccak-derived mapping slot).

## Running

From this directory:

```bash
forge test
```

Requires Foundry ≥ 1.0 on `PATH` and the `lib/forge-std` submodule
initialised.

## Handler pattern

Foundry's invariant fuzzer can't call selectors directly on an etched
address (no ABI). `test/WethHandler.sol` is a standard handler
contract: it exposes `deposit(uint256, uint256)` and
`withdraw(uint256, uint256)` methods that the fuzzer targets, and
they internally dispatch via `.call` / `.call{value:}` against the
etched Weth with the right selectors. Ghost variables
(`ghostTotalDeposited`, `ghostTotalWithdrawn`, `actors[]`) track
state for the invariant checks.

## Bytecode provenance

The three hex artifacts under `test/` are generated from the Lean
side. From the repo root:

```bash
lake exe weth-dump-bytecode        # -> test/Weth.bytecode.hex            (86 B, original)
lake exe weth-opt-dump-bytecode    # -> test/Weth.optimized.bytecode.hex  (77 B, V1 / PUSH0)
lake exe weth-opt-v2-dump-bytecode # -> test/Weth.optimizedV2.bytecode.hex (74 B, V2)
```

Re-run the relevant command whenever the matching
`Program.lean :: bytecode` / `OptimizedProgram.lean :: bytecodeOpt` /
`OptimizedProgramV2.lean :: bytecodeOptV2` value changes; commit the
updated hex file. `EvmSmith/Demos/Tests.lean` carries `#guard`
assertions pinning the byte sizes, the swap-site PCs, the shifted
`PUSH2` label immediates, the `JUMPDEST` positions, and the
per-block program-list lengths — any drift fails the build at
elaboration time.

## See also

- `../Program.lean` — assembly listing with PCs, dispatch layout,
  basic-block definitions, and the 86-byte `bytecode` value.
- `../OptimizedProgram.lean` — V1 (PUSH0) bytecode + per-block
  equivalence theorems against `Program.lean`.
- `../OptimizedProgramV2.lean` — V2 (CALLER-twice + drop-POP)
  bytecode + per-block equivalence theorems against
  `OptimizedProgram.lean`.
- `../Solvency.lean` — sorry-free `weth_solvency_invariant` headline
  theorem (`Σ storage[sender] ≤ balanceOf σ' C` after any single
  Ethereum transaction, conditional on a 5-field `WethAssumptions`
  bundle). Holds against the original bytecode and lifts to V1 / V2
  through the per-block equivalences.
- `../REPORT_WETH.md` — end-to-end report on what's proved and what
  the structural assumptions are.
