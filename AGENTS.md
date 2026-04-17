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
  canonical worked example. Copy its shape when adding a new program.

## Skills

| Skill | When to use |
|-------|-------------|
| [`/add-program`](./.claude/skills/add-program.md) | Scaffold a new bytecode program under `EvmSmith/Demos/<Name>/Program.lean`. |
| [`/prove-program`](./.claude/skills/prove-program.md) | Write a correctness theorem for a program, chaining step lemmas via `runSeq_cons_ok`. |
| [`/add-opcode-lemma`](./.claude/skills/add-opcode-lemma.md) | Extend `EvmSmith/Lemmas.lean` with a missing opcode lemma (needed when your program uses an opcode the existing lemmas don't cover). |
| [`/debug-proof`](./.claude/skills/debug-proof.md) | Diagnose a failing proof — `whnf` timeout, `simp` no-progress, pattern mismatch, FFI opacity, etc. |

## Constraints an agent should know

- **Do not modify `EVMYulLean/`.** It's a separate clone of an upstream
  repo, gitignored here. Improvements that should land there are
  tracked in `EVMYulLean/UPSTREAM_WISHLIST.md` (also gitignored).
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
# First-time setup (one-off workaround for upstream's submodule check):
mkdir -p EthereumTests

# Verify all proofs + tests (10-30min cold, seconds incremental):
lake build

# Run the IO demos end-to-end:
lake exe evm-smith
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
