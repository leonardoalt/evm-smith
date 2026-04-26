# For AI agents

This file orients an AI coding agent (Claude, Cursor, Aider, Copilot,
etc.) working in this repo. Humans should read
[`README.md`](./README.md) first — it has the full story.

## TL;DR

**EVM-Smith** is a Lean 4 framework for writing EVM bytecode as data
and proving safety properties about it against the upstream semantics
in [`NethermindEth/EVMYulLean`](https://github.com/NethermindEth/EVMYulLean).
The intended workflow is: AI writes a bytecode program → AI writes a
Lean proof of its correctness → `lake build` verifies both.

## Where to look

- **[`README.md`](./README.md)** — human-oriented documentation:
  what the project is, how to build, what's already proved, the
  limitations.
- **[`.claude/skills/`](./.claude/skills/)** — task-oriented
  playbooks. Use these when you're about to do one of the named
  tasks; each contains a skeleton, templates, and common pitfalls.
- **[`EvmSmith/Framework.lean`](./EvmSmith/Framework.lean)** — the
  runtime surface (`mkState`, `runOp`, `runSeq`, `Program`).
- **[`EvmSmith/Lemmas.lean`](./EvmSmith/Lemmas.lean)** — the
  proof-time surface (per-opcode step lemmas, `runSeq_cons_ok`
  fusion). Read the header comment for why this file exists and why
  it isn't yet upstream.
- **[`EvmSmith/Demos/Add3/`](./EvmSmith/Demos/Add3/)** — the
  canonical arithmetic worked example. Copy its shape when adding a
  new program. Contains `Program.lean`, `Proofs.lean`,
  `DumpBytecode.lean` (emits hex for Foundry), and `foundry/` (a
  Foundry test suite that loads the runtime bytecode via `vm.etch`
  and exercises it with raw calldata).
- **[`EvmSmith/Demos/Register/`](./EvmSmith/Demos/Register/)** — a
  storage-using worked example: `storage[msg.sender] = x` followed by
  a value-0 `CALL` to `msg.sender`, exposing reentrancy. Exercises
  `CALLER`/`SSTORE`/`CALL`/`POP`/`STOP`. Three locally proved
  invariants (`Proofs.lean`: structural post-state, caller-account
  update, account-frame). **Plus the headline cross-transaction
  result**: `BalanceMono.lean :: register_balance_mono` —
  Register's balance is non-decreasing across any single Ethereum
  transaction, *under arbitrary reentrancy*, sorry-free. Proof
  composes a per-PC bytecode walk in `BytecodeFrame.lean` with the
  EVMYulLean frame library (see "Frame library" below). End-to-end
  walkthrough:
  [`BALANCE_MONOTONICITY.md`](./EvmSmith/Demos/Register/BALANCE_MONOTONICITY.md).
- **[`EvmSmith/Demos/Weth/`](./EvmSmith/Demos/Weth/)** — a
  wrapped-ETH token contract in raw bytecode. Function dispatch via
  4-byte selectors, JUMP/JUMPI/JUMPDEST control flow, SSTORE
  state-update before CALL (checks-effects-interactions). 86 bytes
  of runtime. Lean proofs deferred (see `Proofs.lean`); Foundry
  covers full end-to-end safety: 13 concrete/fuzz tests plus two
  invariant tests (256×50 = 12800 transitions each) and an explicit
  reentrancy test. Main safety claim: `Σ storage[sender] ≤
  contract.balance`. The invariant-side blockers are now mostly
  about Weth's own bytecode walk (the framework is closed); see
  [`weth-invariant-blockers.md`](./.claude/weth-invariant-blockers.md).

## Frame library — for proving cross-transaction / reentrancy-resistant invariants

If your contract needs to maintain a per-account invariant *across*
an entire Ethereum transaction (`Υ`), through nested CALL / CREATE /
SELFDESTRUCT and arbitrary reentrancy, the proof goes through the
**Frame library** in
[`EVMYulLean/EvmYul/Frame/`](./EVMYulLean/EvmYul/Frame/) (closed in
this repo's branch of EVMYulLean — see
[`EVMYulLean/FRAME_LIBRARY.md`](./EVMYulLean/FRAME_LIBRARY.md) for the
overview).

The consumer entry point is **`ΞPreservesAtC_of_Reachable`**: you
supply a contract-specific `Reachable : EVM.State → Prop`
predicate that captures your bytecode trace, plus six closure
obligations, and you get the per-bytecode `ΞPreservesAtC C` witness
that feeds `Υ_balanceOf_ge` (the transaction-level frame).

Three reusable building blocks:

* **[`StepShapes.lean`](./EVMYulLean/EvmYul/Frame/StepShapes.lean)**
  (81 lemmas) — for each opcode, a single-step lemma describing the
  post-state's `pc`, `stack`, `executionEnv` shape after `EVM.step`.
  Coverage spans pushes, arithmetic primops, DUP/SWAP, control flow,
  copy ops, environment readers, and CALL.
* **[`PcWalk.lean`](./EVMYulLean/EvmYul/Frame/PcWalk.lean)**
  (54 wrappers) — `step_OP_at_pc` lemmas combining `decode-bytecode`
  extraction with the matching shape, so each PC case in a contract
  walk compresses to one tactic invocation.
* **[`MutualFrame.lean`](./EVMYulLean/EvmYul/Frame/MutualFrame.lean)** —
  `Θ_balanceOf_ge`, `Λ_balanceOf_ge`, `Ξ_balanceOf_ge_bundled`, the
  joint mutual closure. Don't dive in unless you need to extend the
  bundle's outputs.

The proof pattern is documented in [`/prove-balance-invariant`](./.claude/skills/prove-balance-invariant.md) and demonstrated end-to-end by `EvmSmith/Demos/Register/BalanceMono.lean`. Generalisation roadmap (open work): [`GENERALIZATION_PLAN.md`](./GENERALIZATION_PLAN.md).

## Skills

| Skill | When to use |
|-------|-------------|
| [`/add-program`](./.claude/skills/add-program.md) | Scaffold a new bytecode program under `EvmSmith/Demos/<Name>/Program.lean`. |
| [`/prove-program`](./.claude/skills/prove-program.md) | Write a *single-tx, runSeq-level* correctness theorem (functional shape, post-state). |
| [`/prove-balance-invariant`](./.claude/skills/prove-balance-invariant.md) | Write a *cross-transaction, reentrancy-resistant* per-account invariant via the Frame library + `ΞPreservesAtC_of_Reachable`. |
| [`/add-opcode-lemma`](./.claude/skills/add-opcode-lemma.md) | Extend `EvmSmith/Lemmas.lean` with a missing opcode lemma (needed when your program uses an opcode the existing lemmas don't cover). |
| [`/debug-proof`](./.claude/skills/debug-proof.md) | Diagnose a failing proof — `whnf` timeout, `simp` no-progress, pattern mismatch, FFI opacity, etc. |
| [`/refresh-bytecode`](./.claude/skills/refresh-bytecode.md) | After editing a program's `bytecode` in Lean, regenerate the hex dump that the Foundry tests read. |

## Constraints an agent should know

- **`EVMYulLean/` is a working fork**, not a read-only upstream. It's
  gitignored in this repo because it's a sibling clone with its own
  git history. The fork is `leonardoalt/EVMYulLean`; clone its `main`
  branch (which now carries the Frame library) — the NethermindEth
  upstream alone won't satisfy the imports. When extending the
  framework — new step shapes, new closure-frame conjuncts, bytecode-walk
  machinery — modifications belong there. Use `git -C EVMYulLean ...`
  for git ops; commit incrementally; push to the `fork` remote
  (already configured). Modifications that should return to upstream
  Nethermind/EVMYulLean are tracked in `EVMYulLean/UPSTREAM_WISHLIST.md`
  (also gitignored).
- **Do not commit `.lake/`, `EthereumTests/`, or `EVMYulLean/`.**
  They're in `.gitignore` for good reasons (build artifacts, empty
  workaround dir, external dep).
- **Byte-level round-trips are not provable.** `ffi.ByteArray.zeroes`
  is `opaque`; any proof that depends on reading back bytes through
  `ByteArray.write` won't close. State properties at the stack /
  storage level instead. See the `debug-proof` skill for the full
  workaround.
- **Namespace convention**: the Lean namespace for a new program
  called `<Name>` is `EvmSmith.<Name>`, and its correctness namespace
  is `EvmSmith.<Name>Proofs`. The file path may live under
  `EvmSmith/Demos/<Name>/` for organisational reasons; this
  intentional mismatch is acceptable (see `EvmSmith/Demos/Add3/`).
- **Keep `EvmSmith/Framework.lean` minimal.** It's the user-facing
  runtime API; don't accumulate helpers there. Proof-only utilities
  go in `EvmSmith/Lemmas.lean`; program-specific code goes under
  `EvmSmith/Demos/<Name>/`.

## Build / verify / run

```bash
# First-time setup:
mkdir -p EthereumTests                         # upstream submodule-check workaround
git submodule update --init --recursive        # pulls forge-std for the Foundry tests

# Verify all proofs + tests (10-30min cold, seconds incremental):
lake build

# Run the IO demos end-to-end:
lake exe evm-smith

# Run the Foundry tests for add3 (requires Foundry ≥ 1.0 on PATH):
cd EvmSmith/Demos/Add3/foundry && forge test
```

See `README.md` → "Requirements" and "Building" for the full
prerequisites.

## If you're about to do something big

If the task is more than a small, local change — e.g. refactoring
`Framework.lean`, changing the proof strategy in `Lemmas.lean`,
adding a new subdirectory structure — pause and check in with the
human first. The existing design has specific justifications that
are documented in-file (read the header docstrings of
`Framework.lean` and `Lemmas.lean`) and in
`EVMYulLean/UPSTREAM_WISHLIST.md`. Don't silently rework them.
