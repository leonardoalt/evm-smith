# Storage Layout Optimization

Solidity and Vyper have rigid/strict storage layouts.  If we write EVM
directly, we don't have that restriction, and can therefore optimize how
storage is accessed. This type of change is considered too dangerous for human
smart contract developers, but if we can automatically do it **and** prove
correctness/equivalence to the original one, that's ideal.

## ERC-20

Take an ERC-20 for example. Each user address has their balance. Why can't we
use the address directly as the storage slot for the balances?  We'd have to
find a solution for allowances as well, but we can start with balances.

## Task

### Investigation

Take a standard implementation of ERC-20 in Solidity with tests (from known
libraries such as Solady e.g.), and compile to EVM bytecode (we're interested
in the runtime part). Explain what the storage layout is in md file.

### Goal

We want to optimize the runtime bytecode for gas by simplifying storage
layout/access.

### Changes

Change the storage layout of the balances to be the address of the user
directly.  Allowances can stay as is.

### Tests

Run the same tests that the original library has with the modified bytecode to
ensure they still pass with the optimized implementation.
Compare the gas spent in both implementations for various operations and save
all results.

### Proof of Equivalence

Prove that the new bytecode is equivalent to the original one, that is, that
the affected functions (likely mint, burn, transfer, transferFrom, etc) do not
have their final behavior changed with the new storage layout.  Use evm-smith
for these proofs, similar to what we already did for proofs of equivalence for
optimizations in the latest commits.

### Report

Write a final report with everything that was done.

### Draft post

Draft a blog post with motivation, explanation of why/what/how, examples, the
changes, the theorems that are proven (in an understandable high level way for
humans to read), conclusion.

### Workflow

- Make a plan before each step.
- Spawn a sub-agent to review the plan, do this in a loop until reviewer is happy.
- Review each step after implemented.
- If spawning a sub-agent for implementation:
    - Review the results.
    - Do not let the sub-agent perform destructive actions.
    - Commit before spawning it.
- Commit every time you make progress/advance. Do not push.
- Do not ask for human feedback, continue working with your knowledge and
  sub-agents as needed.
- Continue until task is fully completed as specified.

## Keccak

Solidity is known for using Keccak to derive a unique storage slot for a
mapping + key, so we'll need to reason about Keccak in the equivalence proofs.
However, we don't care about the result of Keccak, and this is important! The
result of Keccak only influences the storage slot itself, but we're changing
the layout, so Keccak will actually vanish in the functions we're changing
after our optimizations. We only have to prove that the stored value is still
sound. Maybe just showing that the storage layout is injective per user address
is enough, or something like that. Make use of that information in a smart way.

## Proofs

Using axioms, hypotheses and sorries is okay initially to set up the skeleton
of the proofs, but they should all be closed to fully finish the task! We
should be left with no sorries, no new axioms (besides the one in evm-smith)
and no new style hypotheses.

## Tooling

These are installed: foundry, git, lean etc.  Evaluate if any tools are missing
and report immediately so I can install them right away before you start,
though I think we have everything already.

## Troubleshooting

If you get stuck, try to take a step back, re-evaluate, plan, re-plan, spawn
hyperfocused sub-agents, keep grinding.
