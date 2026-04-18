# Foundry tests for the `Weth` runtime bytecode

The `Weth` contract is a minimal wrapped-ETH token in raw EVM
bytecode (86 bytes). Two selector-dispatched entry points:

| Selector     | Signature             | Effect                                                         |
|--------------|-----------------------|----------------------------------------------------------------|
| `0xd0e30db0` | `deposit()` payable   | `balance[msg.sender] += msg.value`                             |
| `0x2e1a7d4d` | `withdraw(uint256 x)` | if `balance ≥ x`: decrement + send `x` wei to `msg.sender`; else revert |

This test suite covers:

- **13 concrete and fuzz tests** for the happy paths, wrapping edge
  cases, short/long calldata, unknown selectors, and empty calldata.
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

`test/Weth.bytecode.hex` is generated from the Lean side by:

```bash
# from the repo root:
lake exe weth-dump-bytecode
```

Re-run whenever `Program.lean :: bytecode` changes; commit the
updated hex file.

## See also

- `../Program.lean` — assembly listing with PCs, dispatch layout,
  basic-block definitions, and the 86-byte `bytecode` value.
- `../Proofs.lean` — status of Lean-side proofs (currently deferred
  in favor of Foundry end-to-end coverage).
- `.claude/weth-plan.md` — full design document with scope and
  rationale.
