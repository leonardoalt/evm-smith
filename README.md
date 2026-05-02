# EVM-Smith

**A framework for AI systems to write EVM bytecode and prove it safe.**

The goal is to experiment with AI-generated smart contracts: an AI
writes a contract directly in EVM assembly and, in the same workflow,
writes Lean 4 proofs about the contract's behavior against the
official EVM semantics. This repo is the scaffolding — a thin Lean
framework that makes the "write + prove" loop ergonomic enough to
automate.

The EVM semantics come from
[`NethermindEth/EVMYulLean`](https://github.com/NethermindEth/EVMYulLean),
a Lean 4 formalization of the Ethereum Yellow Paper. EVM-Smith is a
consumer of that formalization.

**This repo currently requires the
[`leonardoalt/EVMYulLean`](https://github.com/leonardoalt/EVMYulLean)
fork**, which carries the Frame library — balance- and
solvency-frame infrastructure that is not yet upstreamed. See
[`FRAME_LIBRARY.md`](https://github.com/leonardoalt/EVMYulLean/blob/main/FRAME_LIBRARY.md) for
what's in the fork.

## How it's meant to be used

1. Write a program as a `Program` value — a list of `(opcode, optional
   push-arg)` pairs. Optionally emit the raw bytecode as a
   `ByteArray`.
2. Run it against an `EVM.State` (`runSeq`) to get empirical behavior.
3. State safety properties (functional correctness, invariants,
   error-freeness) as Lean theorems and prove them with the upstream
   semantics as ground truth.

## Project layout

```
EvmSmith/
├── Framework.lean            # mkState, withCalldata, runOp, runOpFull, runSeq, Program
├── Lemmas.lean               # Per-opcode step lemmas + runSeq fusion — reusable across programs
├── Demos/                    # Worked examples — see Demos/README.md
│   ├── Main.lean             # lake exe entrypoint: runs all demos
│   ├── Demos.lean            # IO demos
│   ├── DemoProofs.lean       # Single-opcode safety theorems
│   ├── Add3/                 # Arithmetic correctness
│   ├── Register/             # Storage + reentrancy + balance monotonicity
│   └── Weth/                 # Solvency invariant
└── Tests/
    └── Guards.lean           # ~40 #guard assertions evaluated at elaboration time
```

When an AI adds a new contract, the natural place is
`EvmSmith/Demos/MyContract/Program.lean` (the program) and
`EvmSmith/Demos/MyContract/Proofs.lean` (its safety theorems).
`Framework.lean` is the runtime surface; `Lemmas.lean` is the
proof-time surface — extend it with one `runOp_<opcode>` lemma per new
opcode your program uses.

## Demos, proofs, tests

Per-demo specifics — what's already proved, how to run each demo,
how to check the proofs, how to run the unit tests, how to run the
Foundry tests, how to regenerate bytecode artifacts, how to write
your own program + proof — all live in
[**`EvmSmith/Demos/README.md`**](./EvmSmith/Demos/README.md).

## Assumptions

The proofs in this repo are conditional on a small, explicit set of
assumptions. Two documents spell them out:

- [**`AXIOMS.md`**](./AXIOMS.md) — the two explicit `axiom`
  declarations in the EVMYulLean framework (T2: precompile purity;
  T5: Keccak collision resistance). What each says, why it's stated
  as an axiom, and the path to discharging it.

- [**`TRUST_ASSUMPTIONS.md`**](./TRUST_ASSUMPTIONS.md) — the broader
  trust picture: Lean's logical foundations, EVMYulLean's modeling
  fidelity (definitional faithfulness, pre-Cancun SELFDESTRUCT
  semantics, gas accounting, partial-correctness framing), and the
  per-contract structural-fact pattern (`DeployedAtC`, SD-exclusion,
  liveness at dispatch, boundary conditions, chain-state bounds).

Per-demo specifics on which structural facts each proof requires are
in the demo's own report (e.g.
[`EvmSmith/Demos/Weth/REPORT_WETH.md`](./EvmSmith/Demos/Weth/REPORT_WETH.md)).

## Requirements

- [`elan`](https://github.com/leanprover/elan) (Lean version manager).
  The toolchain pinned in `lean-toolchain` (currently
  `leanprover/lean4:v4.22.0`) downloads automatically on first build.
- A working C compiler (`cc` on `PATH`) — the upstream needs it for
  keccak / SHA256 / elliptic-curve FFI.
- Network access on first build (to fetch Mathlib, `amosnier/sha-2`,
  `brainhub/SHA3IUF`).
- ~2 GB free disk (most of it Mathlib).

## Building

Clone the **`leonardoalt/EVMYulLean` fork** as a sibling directory:

```bash
git clone https://github.com/leonardoalt/EVMYulLean.git
```

The fork's `main` branch is what this repo expects on disk; the
NethermindEth upstream alone won't satisfy the imports. The fork's
extra commits implement the Frame library
([`FRAME_LIBRARY.md`](https://github.com/leonardoalt/EVMYulLean/blob/main/FRAME_LIBRARY.md)).

Then:

```bash
lake build
```

First build is cold: toolchain download (~200 MB), Mathlib build, C
crypto compile. Budget 10–30 minutes depending on network and CPU.
Incremental builds are seconds.

### One-time workaround

The upstream's `extern_lib` target runs `git submodule update --init`
for its `EthereumTests` directory when linking the native library.
Because this project sits outside the upstream git repo, that command
fails. Create an empty directory at the workspace root once:

```bash
mkdir -p EthereumTests
```

This is only needed for `lake exe` (which links the native lib).
`lake build` alone does not require it.

## Using the framework

Minimal example — run `ADD` on a two-element stack and inspect the
top:

```lean
import EvmSmith.Framework
open EvmSmith EvmYul

def example : Option UInt256 :=
  topOf <| runOp .ADD (mkState [UInt256.ofNat 10, UInt256.ofNat 32])
  -- some 42

#eval example
```

Two runners are available:

- `runOp` — uses the pure `EvmYul.step`. No fuel, no gas, no
  `execLength` bump. Preferred for proofs because the post-state
  stays minimal.
- `runOpFull` — uses the production `EVM.step` with `fuel := 1`,
  `gasCost := 0`. Agrees with `runOp` on `stack` and `pc`. Use this
  to confirm parity with the full driver.

Both return `Except EVM.ExecutionException EVM.State`. Sequence
multiple opcodes with `runSeq : Program → EVM.State →
Except _ EVM.State`.

## Limitations

- **Bytes-level round-trips** (e.g. `MSTORE` → `RETURN` producing the
  bytes of `a + b + c`) go through `ffi.ByteArray.zeroes`, which is
  `opaque`. Proofs that need it would require an axiomatized
  round-trip lemma.
- **Storage slot-level claims need `LawfulOrd UInt256`** (not
  registered) and **`Batteries.RBMap.find?_erase_*` lemmas** (don't
  exist upstream). Account-map-level claims are the workaround.
- **Partial correctness, not termination.** Theorems claim safety on
  successful runs (`Υ` returns `.ok`); failure paths (out-of-gas,
  REVERT, invalid opcode) leave the conclusion vacuous
  (`.error _ => True`). Gas is fully tracked in EVMYulLean (Yellow
  Paper Appendix G), so the EVM's error semantics are accurately
  modeled — we just don't claim termination.
- **`unfold; rfl` depends on reducibility.** Most demo proofs close
  by `unfold EvmYul.step; rfl`. An upstream `@[irreducible]`
  annotation on any of `step`, `execBinOp`, `Stack.pop*`, etc. would
  break every proof simultaneously — at that point, proofs would
  need to go through named characterization lemmas instead.

## License

The `EvmSmith/` code in this repository is MIT-licensed (see `LICENSE`
if present; otherwise consider it MIT). The upstream `EVMYulLean` has
its own license — see `EVMYulLean/license.txt`.
