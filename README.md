# EVM-Smith

**A framework for AI systems to write EVM bytecode and prove it safe.**

> ⚠️ **Experimental research codebase.** Not audited, not production-ready.
> Don't deploy code based on this repo to a live chain. The proofs ship as
> a research artifact demonstrating the workflow; the deployments themselves
> are demos.

The goal is to experiment with AI-generated smart contracts bypassing compilers
entirely: an AI writes a contract directly in EVM assembly and, in the same
workflow, writes Lean 4 proofs about the contract's behavior against the
official EVM semantics. This repo is the scaffolding — a thin Lean framework
that makes the "write + prove" loop ergonomic enough to automate.

The EVM semantics come from
[`NethermindEth/EVMYulLean`](https://github.com/NethermindEth/EVMYulLean),
a Lean 4 formalization of the Ethereum Yellow Paper. EVM-Smith is a
consumer of that formalization.

This repo's `EVMYulLean/` is a submodule pointing at the
[`leonardoalt/EVMYulLean`](https://github.com/leonardoalt/EVMYulLean)
fork, which carries the **Frame library** — cross-transaction
preservation infrastructure that lifts a single-contract bytecode
walk into a per-account inductive invariant that survives the entire
`Υ` driver, including arbitrary reentrancy, nested CREATE / CREATE2,
and SELFDESTRUCT. The library supports balance lower bounds,
relational solvency-style bounds (`Σ storage ≤ balance`),
account-presence preservation, code-identity preservation, and other
per-account state-shape invariants — see
[`FRAME_LIBRARY.md`](https://github.com/leonardoalt/EVMYulLean/blob/main/FRAME_LIBRARY.md)
for the full surface. The two worked examples (Register's balance
monotonicity and WETH's solvency) are entirely consumers of this
library.

## Proof status

* **0 sorries** anywhere in the codebase or its dependency
  (EVMYulLean, including the Frame library).
* **2 practical axioms beyond Lean's standard foundations** in the
  entire trust base: `precompile_preserves_accountMap` (T2:
  precompile purity, provable by case inspection) and
  `lambda_derived_address_ne_C` (T5: Keccak collision-resistance,
  the standard cryptographic ground assumption every Ethereum
  security argument relies on). Both are documented in
  [`AXIOMS.md`](./AXIOMS.md). Verify with `#print axioms <theorem>`.
* Every claim about a contract's bytecode behaviour is a **proved theorem**.

The proofs are conditional on a small, explicit set of structural
hypotheses spelled out per demo (e.g. WETH's 5-field
`WethAssumptions` bundle). See [`TRUST_ASSUMPTIONS.md`](./TRUST_ASSUMPTIONS.md)
for the broader picture.

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
│   ├── Weth/                 # Solvency invariant
│   └── Tests.lean            # #guard assertions evaluated at elaboration time
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

Clone with submodules:

```bash
git clone --recursive https://github.com/leonardoalt/evm-smith.git
cd evm-smith
lake build
```

(If you forgot `--recursive`, run `git submodule update --init --recursive`
inside the repo to fetch them.)

Submodules pulled:
- `EVMYulLean/` — the [`leonardoalt/EVMYulLean`](https://github.com/leonardoalt/EVMYulLean) fork carrying the Frame library
  ([`FRAME_LIBRARY.md`](https://github.com/leonardoalt/EVMYulLean/blob/main/FRAME_LIBRARY.md)).
  The NethermindEth upstream alone won't satisfy the imports.
- Each demo's `foundry/lib/forge-std/` — for the Foundry test suites.

First build is cold: toolchain download (~200 MB), Mathlib build, C
crypto compile. Budget 10–30 minutes depending on network and CPU.
Incremental builds are seconds.

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
- **Upstream Batteries gaps for storage-slot reasoning** — the
  derived `Ord UInt256` doesn't carry `LawfulOrd`, and Batteries has
  no `find?_erase_*` lemmas on `RBMap`. We register the needed
  `OrientedCmp`/`TransCmp`/`ReflCmp` instances locally
  (`EvmSmith/Lemmas/UInt256Order.lean`) and proved
  `find?_erase_ne` plus a list-level erase characterisation
  directly through `RBNode.del`
  (`EvmSmith/Lemmas/BalanceOf.lean`, `Lemmas/RBMapSum.lean`,
  `EVMYulLean/EvmYul/Frame/StorageSum.lean`). Storage-sum reasoning
  works (the WETH solvency proof depends on it). See
  `.claude/batteries-wishlist.md` for the upstream PRs that would
  let us delete these workarounds.
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

This project is licensed under either of

<!-- markdown-link-check-disable -->
- [Apache License, Version 2.0](https://www.apache.org/licenses/LICENSE-2.0) ([`LICENSE-APACHE`](LICENSE-APACHE))
- [MIT license](https://opensource.org/licenses/MIT) ([`LICENSE-MIT`](LICENSE-MIT))
<!-- markdown-link-check-enable -->

at your option.
