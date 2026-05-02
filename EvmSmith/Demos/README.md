# EVM-Smith demos

This directory contains the worked examples that ship with the
framework. Each demo includes a program (raw EVM bytecode), proofs
about its behavior, and (where relevant) Foundry tests.

## What's already proved

### Single-opcode safety (`DemoProofs.lean`)

| Theorem | Statement |
| --- | --- |
| `add_underflow` | `ADD` on an empty stack errors with `StackUnderflow`. |
| `add_spec` | `ADD` on `[a, b, rest]` leaves `[a+b, rest]` on the stack. |
| `add_pc` | `ADD` increments the program counter by 1. |
| `uint256_add_comm` | Addition on `UInt256` is commutative. |
| `push_push_add_peephole` | `PUSH32 b ; PUSH32 a ; ADD` and `PUSH32 (a+b)` leave the same stack. |

The last one is the literal soundness condition for a constant-folding
optimizer pass.

### Add3 — arithmetic correctness (`Add3/Proofs.lean`)

A small contract that reads three 256-bit words from calldata, sums
them, and returns the sum.

| Theorem | Statement |
| --- | --- |
| `compute_correct` | Running the 8-opcode compute prefix on a state whose `CALLDATALOAD` at offsets 0/32/64 returns `a`/`b`/`c` leaves `a + b + c` on top of the stack. |

We prove the arithmetic part. The `MSTORE ; RETURN` suffix's
`H_return = (a+b+c).toByteArray` is *not* proved because the byte-level
round-trip goes through the `ffi.ByteArray.zeroes` opaque FFI
primitive, which is irreducible in Lean's kernel. End-to-end behavior
is demonstrated with concrete inputs through `lake exe evm-smith`.

### Register — storage contract (`Register/Proofs.lean`)

A 20-byte contract that reads one `uint256` from calldata, stores it at
`storage[msg.sender]` (SSTORE + CALLER), then issues a single `CALL`
with value 0 to `msg.sender` — exposing reentrancy as part of the
safety question.

| Theorem | Statement |
| --- | --- |
| `program_result` | Exact structural post-state of `runSeq program s0`. |
| `program_updates_caller_account` | After the call, the code owner's account is exactly `acc.updateStorage (addressSlot sender) x`. |
| `program_preserves_other_accounts` | Every account address other than the code owner is unchanged. |

### Register — balance monotonicity (`Register/BalanceMono.lean`)

The headline cross-transaction proof:

> *After any single Ethereum transaction (`Υ`), Register's balance at
> its deployment address `C` is `≥` the balance it had before the
> transaction.*

This holds **in the presence of arbitrary reentrancy** through the
`CALL` Register itself emits, plus any nested CREATE / CREATE2 /
SELFDESTRUCT paths the EVM allows. See
[`Register/BALANCE_MONOTONICITY.md`](./Register/BALANCE_MONOTONICITY.md)
for the full structure.

### WETH — solvency (`Weth/Solvency.lean`)

An 86-byte WETH-style contract with `deposit` / `withdraw` and
state-mutating outbound `CALL`. The headline claim:

> *After any single Ethereum transaction, the sum of stored token
> balances at WETH's address is at most WETH's actual ETH balance:*
> `storageSum σ' C ≤ balanceOf σ' C`.

`weth_solvency_invariant` is conditional on `WethAssumptions` (5
structural fields — see top-level `README.md` "Assumptions" section).
Every assumption that was *about WETH's bytecode behavior* has been
discharged as a Lean theorem. The remaining 5 assumptions are
real-world / framework-coupled facts.

Reports on what was built and what was proved:
- [`Weth/REPORT_FRAMEWORK.md`](./Weth/REPORT_FRAMEWORK.md) — framework infrastructure landed in EVMYulLean.
- [`Weth/REPORT_WETH.md`](./Weth/REPORT_WETH.md) — main theorems and assumptions on the WETH side.

## Running the demos

```bash
lake exe evm-smith
```

Expected output:

```
ADD: top = (some 7)
PUSH1 42: top = (some 42)
DUP1: stack = [7, 7, 8]
parity: runOp stack = (some [7])
parity: runOpFull stack = (some [7])
parity stacks match? true

-- add3 program (reads 3 u256 from calldata, returns sum) --
add3(1, 2, 3) → 6 (expected 6, ok? true)
add3(10, 20, 30) → 60 (expected 60, ok? true)
add3(100, 200, 300) → 600 (expected 600, ok? true)
add3(0, 0, 0) → 0 (expected 0, ok? true)
```

The upstream's `step` also emits the opcode name (e.g. `ADD`) to stderr
via `dbg_trace` — normal, not an error.

## Checking the proofs

Proofs are elaborated as part of `lake build`. A clean `sorry`-free
build is the verification. To be explicit:

```bash
lake build EvmSmith.Demos.DemoProofs
lake build EvmSmith.Demos.Add3.Proofs
lake build EvmSmith.Demos.Register.BalanceMono
lake build EvmSmith.Demos.Weth.Solvency
```

Open any of these in an editor with Lean 4 support to step through
interactively.

## Running the tests

`EvmSmith/Tests/Guards.lean` contains ~40 `#guard` assertions covering
arithmetic, comparison/bitwise, stack manipulation, pushes, error
paths, PC increment, and `runOp` / `runOpFull` parity. Each is
evaluated at elaboration time; any failure aborts the build. No native
linking, no FFI workaround required.

```bash
lake build EvmSmith.Tests.Guards
```

## Running the Foundry tests

WETH's Foundry test suite (15 tests including invariant runs and an
explicit reentrancy test) lives in `Weth/foundry/`:

```bash
cd EvmSmith/Demos/Weth/foundry
forge test
```

The tests exercise the deployed bytecode against a chain. They're
complementary to (not a substitute for) the Lean proofs.

## Regenerating bytecode

After editing `Add3/Program.lean :: bytecode`:

```bash
lake exe add3-dump-bytecode     # regenerates the hex file
```

A `#guard` in `EvmSmith/Tests/Guards.lean` pins the byte length as a
structural backstop.

## Writing your own program + proof

Template (drop a pair of files in `EvmSmith/Demos/MyProgram/`):

```lean
-- EvmSmith/Demos/MyProgram/Program.lean
import EvmSmith.Framework

namespace EvmSmith.MyProgram
open EvmYul EvmYul.EVM

def program : EvmSmith.Program :=
  [ (.Push .PUSH1, some (UInt256.ofNat 42, 1))
  , (.ADD,         none)
  , ...
  ]

end EvmSmith.MyProgram
```

```lean
-- EvmSmith/Demos/MyProgram/Proofs.lean
import EvmSmith.Lemmas
import EvmSmith.Demos.MyProgram.Program

namespace EvmSmith.MyProgramProofs
open EvmYul EvmYul.EVM EvmSmith

theorem program_correct (s0 : EVM.State) (...) :
    (runSeq MyProgram.program s0).map (·.stack.head?) = .ok (some ...) := by
  ...

end EvmSmith.MyProgramProofs
```

`Add3/Program.lean` + `Add3/Proofs.lean` show the full single-block
pattern. `Register/BalanceMono.lean` and `Weth/Solvency.lean` show the
cross-transaction invariant pattern using the EVMYulLean Frame
library.
