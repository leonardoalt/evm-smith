---
name: refresh-bytecode
description: After editing a program's `bytecode : ByteArray` in Lean (e.g., `EvmSmith/Demos/Add3/Program.lean`), regenerate the hex file that the Foundry test suite reads via `vm.readFile` + `vm.parseBytes`. Use whenever the Lean bytecode changes, or the Foundry tests are failing with a bytecode-shape mismatch.
---

# Refreshing the bytecode hex file

The Foundry test suites (`EvmSmith/Demos/<Name>/foundry/`) read the
runtime bytecode from a generated file in `foundry/test/`, produced
by a dedicated `lake exe` target per program. When you edit the
Lean-side `bytecode` literal, the hex file becomes stale and
`forge test` either fails or passes against the old bytecode.

## When this applies

You only need this skill if:

- You changed `bytecode : ByteArray` in a `Program.lean` file, AND
- That program has a companion `DumpBytecode.lean` + `foundry/`
  directory.

If you are creating a *new* program from scratch, use the `add-program`
skill instead — it covers the Foundry wiring as part of the scaffold.

## How

For `add3` specifically:

```bash
lake exe add3-dump-bytecode
```

This writes `EvmSmith/Demos/Add3/foundry/test/Add3.bytecode.hex`.
Commit the updated file alongside the `Program.lean` edit.

For other programs (when we have them), the pattern will be:

```bash
lake exe <program>-dump-bytecode
```

Check `lakefile.lean` for the exact exe names.

## What else to update

- **`EvmSmith/Tests/Guards.lean`** — if the byte length changed, the
  `#guard EvmSmith.<Name>.bytecode.size == <n>` assertion will fire
  and needs its `<n>` updated to match.
- **Foundry test file** — if the semantics of the program changed, the
  `test_<Name>_concrete` expected values may need updating too. The
  Foundry test is checking behavior, not just shape.
- **`Proofs.lean`** — if the bytecode change reflects a semantics
  change (not just an encoding tweak), the correctness theorem in
  `<Name>Proofs.lean` likely needs re-proving.
- **Commit the hex file** — it's tracked in git so someone who clones
  the repo can `forge test` without first running `lake exe`.

## Why this exists at all

The Lean side is the source of truth. The Foundry side needs the
same bytes to install at a test address via `vm.etch`. Options for
bridging the two were considered (hard-coded hex with comment, shell
script, post-commit hook); the generator-to-file approach was chosen
because it puts the source of truth in one place and surfaces drift
at `forge test` time when the hex file is stale.
