# EVM-Smith

**A framework for AI systems to write EVM bytecode and prove it safe.**

The goal is experiment with AI-generated smart contracts: an AI writes a
contract directly in EVM assembly, and then, in the same workflow, writes
Lean 4 proofs about the contract's behavior against the official EVM
semantics. This repo is the scaffolding — a thin Lean framework that makes
the "write + prove" loop ergonomic enough to automate.

The EVM semantics come from [`NethermindEth/EVMYulLean`](https://github.com/NethermindEth/EVMYulLean), a Lean 4 formalization of the Ethereum Yellow Paper. EVM-Smith is a consumer of that formalization.

## How it's meant to be used

1. Write a program as a `Program` value — a list of `(opcode, optional push-arg)` pairs. Optionally emit the raw bytecode as a `ByteArray`.
2. Run it against an `EVM.State` (`runSeq`) to get empirical behavior. `lake exe evm-smith` exercises the shipped demo.
3. State safety properties (functional correctness, peephole equivalence, error-freeness, invariants) as Lean theorems and prove them with the upstream semantics as ground truth.

The worked example in the repo is `Add3`: a small contract that reads three
256-bit words from calldata, sums them, and returns the sum. `Add3Proofs`
proves the arithmetic correctness against the EVM semantics. The
correctness theorem is the template an AI would produce for its own
programs.

## Project layout

```
EvmSmith/
├── Framework.lean            # mkState, withCalldata, runOp, runOpFull, runSeq, Program
├── Lemmas.lean               # Per-opcode step lemmas + runSeq fusion — reusable across programs
├── Demos/                    # What ships with the repo: IO demos + the Add3 worked example
│   ├── Main.lean             # lake exe entrypoint: runs all demos
│   ├── Demos.lean            # IO demos (ADD, PUSH, DUP, parity, add3 end-to-end)
│   ├── DemoProofs.lean       # Five single-opcode safety theorems (template)
│   └── Add3/
│       ├── Program.lean      # Example program: sum three calldata words
│       └── Proofs.lean       # Correctness of Add3.compute
└── Tests/
    └── Guards.lean           # ~40 #guard assertions evaluated at elaboration time
```

When an AI adds a new contract, the natural place is `EvmSmith/Demos/MyContract/Program.lean` (the program) and `EvmSmith/Demos/MyContract/Proofs.lean` (its safety theorems). `Framework.lean` is the runtime surface; `Lemmas.lean` is the proof-time surface — extend it with one `runOp_<opcode>` lemma per new opcode your program uses.

## What's already proved

### Single-opcode safety (`EvmSmith/Demos/DemoProofs.lean`)

| Theorem | Statement |
| --- | --- |
| `add_underflow` | `ADD` on an empty stack errors with `StackUnderflow`. |
| `add_spec` | `ADD` on `[a, b, rest]` leaves `[a+b, rest]` on the stack. |
| `add_pc` | `ADD` increments the program counter by 1. |
| `uint256_add_comm` | Addition on `UInt256` is commutative. |
| `push_push_add_peephole` | `PUSH32 b ; PUSH32 a ; ADD` and `PUSH32 (a+b)` leave the same stack. |

The last one is the literal soundness condition for a constant-folding optimizer pass.

### Program-level safety (`EvmSmith/Demos/Add3/Proofs.lean`)

| Theorem | Statement |
| --- | --- |
| `compute_correct` | Running the 8-opcode compute prefix of `add3` (`PUSH1 0; CALLDATALOAD; PUSH1 32; CALLDATALOAD; ADD; PUSH1 64; CALLDATALOAD; ADD`) on a state whose `CALLDATALOAD` at offsets 0/32/64 returns `a`/`b`/`c` leaves `a + b + c` on top of the stack. |

We prove the arithmetic part. The `MSTORE ; RETURN` suffix's `H_return = (a+b+c).toByteArray` is *not* proved because the byte-level round-trip goes through the `ffi.ByteArray.zeroes` opaque FFI primitive, which is irreducible in Lean's kernel. See the docstring in `EvmSmith/Demos/Add3/Proofs.lean` for the full explanation. End-to-end behavior is demonstrated with concrete inputs through `lake exe evm-smith`.

### Wrapped-ETH token (`EvmSmith/Demos/Weth/`)

Third worked example — an 86-byte WETH-style contract. Adds three qualitatively new things: function dispatch via 4-byte selectors, control flow (JUMP/JUMPI/JUMPDEST), and cross-transaction state-mutating CALL for the ETH refund in `withdraw`. Safety claim — `Σ storage[sender] ≤ contract.balance` — is verified end-to-end via Foundry invariant testing (256 fuzz runs × 50 calls per run). Checks-effects-interactions ordering is tested against an explicit reentrant attacker contract. Lean-side block-level proofs are deferred; see `EvmSmith/Demos/Weth/Proofs.lean` for the status.

### Program-level safety (`EvmSmith/Demos/Register/Proofs.lean`)

A second worked example: a 6-byte contract that reads one `uint256` from calldata and stores it at `storage[msg.sender]` (SSTORE + CALLER).

| Theorem | Statement | Status |
| --- | --- | --- |
| `program_result` | Exact structural post-state of `runSeq program s0`. | ✅ Proved |
| `program_updates_caller_account` | After the call, the code owner's account is exactly `acc.updateStorage (addressSlot sender) x`. | ✅ Proved |
| `program_preserves_other_accounts` | Every account address other than the code owner is unchanged. | ✅ Proved |
| `program_sets_sender_slot` | `findD`-form functional correctness: the sender's slot reads back as `x`. | ⚠ `sorry` |
| `program_preserves_other_slots` | Slot frame: any other slot in the same account is unchanged. | ⚠ `sorry` |

The two `sorry`-marked theorems are blocked on RBMap API gaps in Batteries — specifically `find?_erase_of_ne` and `findD_insert_self`. A follow-up pass (or an upstream Batteries PR) closes them; see the docstring in `EvmSmith/Demos/Register/Proofs.lean`. The three proved theorems are the load-bearing ones: `program_updates_caller_account` is the functional-correctness claim in its most direct form, and the missing theorems are surface restatements.

## Requirements

- [`elan`](https://github.com/leanprover/elan) (Lean version manager). The toolchain pinned in `lean-toolchain` (currently `leanprover/lean4:v4.22.0`) downloads automatically on first build.
- A working C compiler (`cc` on `PATH`) — the upstream needs it for keccak/SHA256/elliptic-curve FFI.
- Network access on first build (to fetch Mathlib, `amosnier/sha-2`, `brainhub/SHA3IUF`).
- ~2 GB free disk (most of it Mathlib).

## Building

Clone the upstream semantics as a sibling directory:

```bash
git clone https://github.com/NethermindEth/EVMYulLean.git
```

Then:

```bash
lake build
```

First build is cold: toolchain download (~200 MB), Mathlib build, C crypto compile. Budget 10–30 minutes depending on network and CPU. Incremental builds are seconds.

### One-time workaround

The upstream's `extern_lib` target runs `git submodule update --init` for its `EthereumTests` directory when linking the native library. Because this project sits outside the upstream git repo, that command fails. Create an empty directory at the workspace root once to satisfy the existence check:

```bash
mkdir -p EthereumTests
```

This is only needed for `lake exe` (which links the native lib). `lake build` alone does not require it.

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

The upstream's `step` also emits the opcode name (e.g. `ADD`) to stderr via `dbg_trace` — normal, not an error.

## Checking the proofs

Proofs are elaborated as part of `lake build`. A clean `sorry`-free build is the verification. To be explicit:

```bash
lake build EvmSmith.Demos.DemoProofs
lake build EvmSmith.Demos.Add3.Proofs
```

Open either file in an editor with Lean 4 support to step through interactively.

## Running the tests

`EvmSmith/Tests/Guards.lean` contains ~40 `#guard` assertions covering arithmetic, comparison/bitwise, stack manipulation, pushes, error paths, PC increment, and `runOp` / `runOpFull` parity. Each is evaluated at elaboration time; any failure aborts the build. No native linking, no FFI workaround required.

```bash
lake build EvmSmith.Tests.Guards
```

## Running the Foundry tests

Each worked example ships with a Foundry test suite:

- `EvmSmith/Demos/Add3/foundry/` — 5 tests covering arithmetic,
  wrapping, short/long calldata, and a 256-run fuzz.
- `EvmSmith/Demos/Register/foundry/` — 8 tests covering per-sender
  writes, sender isolation, overwrites, empty / zero-value edge
  cases, and two fuzz sweeps over `(sender, value)` pairs.
- `EvmSmith/Demos/Weth/foundry/` — 15 tests: 13 concrete/fuzz
  covering the deposit/withdraw flows + unknown-selector reverts
  + arithmetic edge cases + reentrancy; plus two invariant tests
  (`invariant_user_funds_never_lost` and
  `invariant_ghost_accounting_consistent`) that each run 256 random
  transaction sequences of depth 50 against the etched bytecode.

Both suites install the runtime at a test address via `vm.etch` and
call it with raw calldata (no function selector).

Requires [Foundry](https://book.getfoundry.sh/) ≥ 1.0 on `PATH` (this
machine has 1.5.1 at `~/.foundry/bin/forge`; install via `foundryup`
if missing). Also requires the `forge-std` git submodule:

```bash
git submodule update --init --recursive         # once

cd EvmSmith/Demos/Add3/foundry && forge test     # 5 tests
cd EvmSmith/Demos/Register/foundry && forge test # 8 tests
cd EvmSmith/Demos/Weth/foundry && forge test     # 15 tests (incl. 2 invariants)
```

Expected output: 5 passing tests (`test_Add3_concrete`,
`test_Add3_wraps`, `test_Add3_shortCalldata`, `test_Add3_longCalldata`,
`testFuzz_Add3`).

### Bytecode sync

The Foundry tests read the runtime bytecode from
`EvmSmith/Demos/Add3/foundry/test/Add3.bytecode.hex`, which is generated
by a tiny Lean executable:

```bash
lake exe add3-dump-bytecode     # regenerate the hex file
```

Run this after any edit to `EvmSmith/Demos/Add3/Program.lean :: bytecode`.
A `#guard` in `EvmSmith/Tests/Guards.lean` pins the byte length as a
structural backstop.

## Using the framework

Minimal example — run `ADD` on a two-element stack and inspect the top:

```lean
import EvmSmith.Framework
open EvmSmith EvmYul

def example : Option UInt256 :=
  topOf <| runOp .ADD (mkState [UInt256.ofNat 10, UInt256.ofNat 32])
  -- some 42

#eval example
```

Two runners are available:

- `runOp` — uses the pure `EvmYul.step`. No fuel, no gas, no `execLength` bump. Preferred for proofs because the post-state stays minimal.
- `runOpFull` — uses the production `EVM.step` with `fuel := 1`, `gasCost := 0`. Agrees with `runOp` on `stack` and `pc`. Use this to confirm parity with the full driver.

Both return `Except EVM.ExecutionException EVM.State`. Sequence multiple opcodes with `runSeq : Program → EVM.State → Except _ EVM.State`.

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

`EvmSmith/Demos/Add3/Program.lean` + `EvmSmith/Demos/Add3/Proofs.lean` show the full pattern.

## Limitations

- **Bytes-level round-trips** (e.g. `MSTORE` → `RETURN` producing the bytes of `a + b + c`) go through `ffi.ByteArray.zeroes`, which is `opaque`. Proofs that need it would require an axiomatized round-trip lemma. Not fatal — prove the stack-level property instead, as `Add3Proofs` does.
- **No helpers for storage, memory beyond calldata, code-copy.** Contracts that touch `SLOAD`/`SSTORE` / `MLOAD`/`MSTORE` as part of their spec need to hand-patch `{ s with … }` to set up the initial state. Add helpers to `Framework.lean` as you hit them.
- **System opcodes** (`CALL`, `CREATE`, `SELFDESTRUCT`, …) are not exercised by the demos. They need account-map setup the framework doesn't provide.
- **No gas reasoning.** `runOpFull` deducts gas but the theorems ignore it; proving gas bounds would need a separate track.
- **`unfold; rfl` depends on reducibility.** Most demo proofs close by `unfold EvmYul.step; rfl`. That works only as long as the upstream keeps `step`, `execBinOp`, `Stack.pop*`, etc. reducible `def`s. An upstream `@[irreducible]` annotation would break every proof simultaneously — at that point, proofs would need to go through named characterization lemmas instead.

## License

The `EvmSmith/` code in this repository is MIT-licensed (see `LICENSE` if present; otherwise consider it MIT). The upstream `EVMYulLean` has its own license — see `EVMYulLean/license.txt`.
