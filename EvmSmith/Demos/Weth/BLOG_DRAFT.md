# evm-smith: smart contracts in EVM bytecode + Lean proofs, without a compiler

> _tl;dr_: Can AI write EVM bytecode + Lean proofs of inductive
> invariants under reentrancy, bypassing the compiler entirely?
> **Yes**. Here's what 86 bytes of WETH bytecode plus a sorry-free
> Lean solvency proof look like.

I was inspired by [Yoichi Hirai](https://x.com/pirapira)'s new project
[evm-asm](https://github.com/Verified-zkEVM/evm-asm), where AIs write an
Ethereum block verifier directly in [RISC-V](https://riscv.org/) assembly,
together with [Lean](https://lean-lang.org/) proofs of correctness.  I find the
idea of completely bypassing the compiler fascinating, a paradigm shift that
removes massive dependencies and costs (HLL compilers), and where humans only
need to read/audit the formal specification, here in the form of Lean theorems.

My first thought was: can we do the same for Ethereum smart contracts? I was
convinced AIs can write EVM assembly quite well, but can they write the proofs
too? Can they prove inductive invariants in the presence of potential
reentrancy, over any callstack length, considering every possible malicious
external contract?

To test this, I asked Claude to write EVM assembly and Lean proofs for
increasingly harder problems, such as contracts that "read 3 numbers and add
them" and that "let any account set the value of storage slot `msg.sender`",
with different properties being proved for each contract. I used
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean) to get formal and
executable semantics for EVM bytecode.

All the contracts, tests and proofs landed in
[evm-smith](https://github.com/leonardoalt/evm-smith), a new framework that
provides the machinery for AI to write combined EVM bytecode and Lean proofs.

My requirements were:

- I will describe what the smart contract should do, but I shouldn't write it.
- I will read the EVM assembly.
- I will describe the properties that should be proven, but I shouldn't write theorems nor proofs.
- I will read the main theorems and check for sorries and new axioms.

Claude was quite efficient at proving properties for the simpler contracts, and
we quickly got to the final boss of this experiment, a WETH-clone solvency
proof.

## A WETH contract + solvency proof, end-to-end, in Lean

The goal was to write a minimal Wrapped-ETH (WETH) clone with two functions:

- `deposit()`: when a user sends ETH to the contract, their token balance
  increases by the same amount.
- `withdraw(amount)`: if the user has enough tokens, decrement the user's
  balance and send back the corresponding ETH.

Real [WETH on
Ethereum](https://etherscan.io/token/0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2#code)
is of course more complicated (events, ERC-20 functions, allowances), but this
minimal version captures the critical solvency property.

The artifacts are:
- [EVM
  assembly](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Program.lean#L162).
  If you are a smart contract dev, I encourage you to read the assembly to get
  an idea that this _should_ be correct.
- [Foundry
  tests](https://github.com/leonardoalt/evm-smith/tree/main/EvmSmith/Demos/Weth/foundry)
  for our contract. Useful for integration, fuzzing and deployment.
- [Solvency
  theorem/proof](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Solvency.lean#L338).
  The final proof.

This article explains what we (Claude and I) built, what's actually been
proved, what's still assumed, and what I think the experiment means for how
smart-contract development might evolve. The Lean snippets and proof realated
content is kept high level for the purose of this article, but a full technical
report is available at [WETH proof technical
report](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/REPORT_WETH.md).

## What's the property?

**Solvency**: at every moment in the contract's life, the sum of all
users' stored token balances is at most the contract's actual ETH
balance. If this holds, every user can always withdraw their full
balance.

[In Lean](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Invariant.lean):

```lean
def WethInv (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  storageSum σ C ≤ balanceOf σ C
```

`σ` is the EVM state, `C` is WETH's address; `storageSum σ C` sums
every storage slot at `C` (each slot holds one user's token balance,
so this sum is total user tokens), `balanceOf σ C` is `C`'s actual
ETH balance. The whole expression: tokens owed ≤ ETH held.

## What's a "proof" here?

A Lean theorem. Lean is a dependently-typed proof assistant: if the
file compiles, the theorem holds.

Our [headline theorem](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Solvency.lean#L338),
in pseudotype form:

```lean
theorem weth_solvency_invariant :
    -- standard tx-boundary hypotheses + 5 chain-level assumptions
    WethInv σ C →                          -- pre-state solvency
    match EVM.Υ ... σ ... with
    | .ok (σ', _) => WethInv σ' C          -- post-state solvency
    | .error _    => True                  -- vacuous on failure
```

`EVM.Υ` is the EVM's transaction processor, formalized in EVMYulLean from the
Yellow Paper. The headline claim is: **any execution path through any opcode
sequence reachable from any caller, including malicious reentrant ones, can't
violate solvency.**

The `.error` branch is partial correctness: we prove safety on successful runs,
not that the contract always succeeds. EVMYulLean fully models the failure
semantics (gas, REVERT, rollback) so failure paths are handled by the model.
And because WETH decrements the user's balance *before* the outbound CALL, even
on a failed CALL the accounting still adds up: the user's balance went down,
they didn't get paid (checks-effects-interactions, captured by the proof).

## What are Θ, Λ, Ξ, Υ?

The Yellow Paper's layered execution functions, kept in EVMYulLean:

- **Υ** — transaction processor (outermost layer).
- **Θ** — call frame: CALL / CALLCODE / DELEGATECALL / STATICCALL.
- **Λ** — creation frame: CREATE / CREATE2.
- **Ξ** — bytecode execution.

## How is this proved?

On a high level: walk through WETH's bytecode instruction by instruction, prove
that every reachable state preserves the invariant, then bridge that per-step
preservation up to the transaction level via a generic frame library
(`EvmYul/Frame/`) that takes care of arbitrary reentrancy, nested CALLs, and
CREATE.  The framework is the heavy lifting; the contract-specific part is the
per-PC walk plus a small bundle of structural facts feeding the bridge. Details
and a theorem call-graph are in the
[REPORT](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/REPORT_WETH.md).

## What's still assumed?

There are five structural assumptions, packaged in a [`WethAssumptions`
bundle](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Solvency.lean):

```lean
structure WethAssumptions ... : Prop where
  deployed         : DeployedAtC C
  sd_excl          : WethSDExclusion ...
  dead_at_σP       : WethDeadAtσP ...
  inv_at_σP        : WethInvAtσP ...
  call_no_wrap     : WethCallNoWrapAt72 C
```

1. **`deployed`**: WETH's 86-byte bytecode is actually installed at C.
2. **`sd_excl`**: no `SELFDESTRUCT` in the call tree targets C.
   (Moot on post-Cancun mainnet per EIP-6780; the proof handles the
   stricter pre-Cancun semantics.)
3. **`dead_at_σP`**: after the EVM dispatches value transfer + the
   contract call, C still has non-empty code.
4. **`inv_at_σP`**: after that same dispatch step (still before WETH's
   code runs), solvency still holds, i.e. the value transfer's
   bookkeeping moves don't break solvency.
5. **`call_no_wrap`**: when WETH transfers ETH back on withdraw, the
   recipient's balance plus the transfer doesn't overflow `UInt256`.

Items 1-4 describe the chain state at the moment WETH's code begins
executing; item 5 is a real-world balance bound.

**Crucially, no assumption is about WETH's bytecode behavior**. What the
SSTOREs do, what the CALL does, how the LT/JUMPI gate enforces solvency are all
mechanically checked Lean theorems.

## What's the trust boundary?

To trust the WETH solvency theorem, we trust:

1. **Lean's type checker** (the proof compiles).
2. **EVMYulLean's modeling choices**: its definitions of `EVM.Υ`,
   `EVM.step`, etc. accurately model the EVM. Plus two explicit
   axioms: `precompile_preserves_accountMap` (precompile purity,
   provable by case inspection) and `lambda_derived_address_ne_C`
   (CREATE-derived addresses never collide with C, equivalent to
   Keccak collision-resistance).
3. **The 5 `WethAssumptions` fields** above.

## Do we still need compilers?

Today's smart contracts go HLL (Solidity, Vyper) → compiler → bytecode →
deploy. The compiler sits in the trusted base: a compiler bug can introduce a
vulnerability invisible to source review. Besides, developing the compilers
takes time and money.

This experiment skips the compiler entirely: the AI writes the assembly and a
Lean proof that the bytecode satisfies the safety property. Both live at the
same level of abstraction (machine code + machine-checked proof about machine
code), eliminating the translation gap where bugs can hide.

Formal verification of EVM bytecode isn't novel. What's new here is the
workflow: a one-time framework investment + AI-generated contract code and
proof, with the human doing none of the writing and reading only the spec,
axioms, and theorem statements. The development process in this future is
actually faster, cheaper, and safer.

## What do humans still need to do?

If the AI writes the bytecode and the proof, what's left?

**Read the spec, axioms, and assumptions.** Lean theorem statements
are the specification, `WethInv σ C := storageSum σ C ≤ balanceOf σ C`
is the property; the assumption bundle and the framework axioms are
the trust surface. If you can read those, you can audit the claim.
You need to be able to read Lean to verify the proof.

One potential way to lower this requirement: thin eDSLs built in Lean itself
acting as human-readable IRs with verified compilers down to bytecode, keeping
the proof at the bytecode level but the specification readable to
non-Lean-fluent reviewers. This may even be somewhat required in the
near-future, although it feels like developers converging to being able to read
Lean is inevitable and a great outcome.

## What's the scale of the code?

The cost splits in three tiers, in decreasing order of reusability:

- **Generic framework infrastructure**: ~12500 lines of new Lean
  in EVMYulLean's [`EvmYul/Frame/`](https://github.com/leonardoalt/EVMYulLean/tree/main/EvmYul/Frame)
  library: mutual-induction preservation results for Ξ/Θ/Λ/X
  (in [`MutualFrame.lean`](https://github.com/leonardoalt/EVMYulLean/blob/main/EvmYul/Frame/MutualFrame.lean)),
  account-presence preservation, the universal Ξ-preservation theorem,
  generic Υ-tail helpers (in [`UpsilonFrame.lean`](https://github.com/leonardoalt/EVMYulLean/blob/main/EvmYul/Frame/UpsilonFrame.lean)).
  None of it is WETH-specific; any future EVM bytecode proof
  inherits it for free. See
  [`FRAME_LIBRARY.md`](https://github.com/leonardoalt/EVMYulLean/blob/main/FRAME_LIBRARY.md)
  for the full surface.
- **Relational-invariant closure**: ~5400 lines in
  [`EvmSmith/Demos/Weth/InvariantClosure.lean`](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/InvariantClosure.lean):
  the `storageSum ≤ balanceOf` predicate plus the mutual closure that
  preserves it across Υ. Generic in shape (no WETH-bytecode refs);
  lives consumer-side only because we have one consumer. The
  natural next step once a second consumer demonstrates the same
  shape is lifting it back into the framework as a parametric
  module over the invariant.
- **WETH-specific**: ~6800 lines, dominated by
  [`BytecodeFrame.lean`](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/BytecodeFrame.lean)
  (~6000 lines of per-PC walks through the bytecode trace), plus
  the headline theorem composition
  ([`Solvency.lean`](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Solvency.lean)),
  the `WethInv` abbreviation
  ([`Invariant.lean`](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Invariant.lean)),
  and the bytecode definition
  ([`Program.lean`](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Program.lean)).

For this 86-byte contract that's ~80 lines of WETH-specific Lean per byte of
bytecode. Framework cost is one-time and amortizes across every future
contract. The per-contract cost is large today but impressive for a first
attempt and clearly improvable.

## How did Claude do?

I provided high-level goals ("prove WETH is solvent"), the
framework (EVMYulLean), and iterative review when stuck. Claude
wrote everything: bytecode, executable tests, Foundry tests, and
the Lean proofs.

Code and testing were one-shot. The proofs took 30-50 sessions
across different prompting styles (Claude Code directly, parallel
sub-agents, single hyperfocused sub-agent, pep talks). Claude
bailed many times calling steps "multi-day sessions". I still don't
know how to handle that besides telling it to keep grinding.

## Conclusion: this is harder than it looks

Proving inductive invariants for smart contracts is not an easy
feat. A one-line property like `storageSum σ C ≤ balanceOf σ C` has
to survive arbitrary reentrancy, nested CALLs into untrusted code, a
non-zero outbound CALL where the contract pays out exactly the
amount it just decremented from storage, and the EVM's full
execution semantics: precompiles, CREATE/CREATE2, SELFDESTRUCT, gas
accounting. The proof crosses every layer of the spec from individual
opcodes up to the transaction processor, with no exceptions allowed
at any layer.

For a human team, this is weeks of expert proof engineering. Claude
landed it across a few weeks of guided sessions, with the human (me)
doing only spec review and direction. That's the part I find
genuinely impressive: not the framework, not the WETH bytecode, but
the fact that the model can carry an inductive proof of this shape
at all.

What this means going forward:

- Smart contracts are deployed as bytecode + Lean proof of safety
  properties.
- The "audit" is reading the Lean theorem statements and confirming
  they capture the right invariants.
- Compilers become debugging tools, not part of the trusted base:
  compile from Solidity/Vyper to check your bytecode matches your
  intent, but the deployed artifact is bytecode + proof.
- Compilers may still be needed for gas performance, but autoopt
  could solve that for AI-generated code.
- The proof is generated by AI, supervised by humans who read the
  spec.
- And probably none of this is specific to smart contracts; the same
  pattern likely applies to all software where the cost of bugs
  justifies the cost of proof.

The bottleneck moves from building a safe and performant compiler to
humans reading formal specs in Lean.

## Artifacts

The framework: [evm-smith](https://github.com/leonardoalt/evm-smith),
which depends on
[the EVMYulLean fork](https://github.com/leonardoalt/EVMYulLean)
carrying the Frame library
([`FRAME_LIBRARY.md`](https://github.com/leonardoalt/EVMYulLean/blob/main/FRAME_LIBRARY.md)).

For WETH specifically:

- [Program.lean](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Program.lean):
  the EVM assembly + the 86-byte
  [bytecode hex](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/foundry/test/Weth.bytecode.hex).
- [Invariant.lean](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Invariant.lean):
  the solvency predicate.
- [BytecodeFrame.lean](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/BytecodeFrame.lean):
  the per-PC bytecode walk.
- [InvariantClosure.lean](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/InvariantClosure.lean):
  the relational-invariant closure chain.
- [Solvency.lean](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Solvency.lean):
  the headline theorem + assumptions bundle.
- [Foundry tests](https://github.com/leonardoalt/evm-smith/tree/main/EvmSmith/Demos/Weth/foundry):
  fuzz + integration tests against the deployed bytecode.

Reports for deeper reading:

- [REPORT_WETH.md](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/REPORT_WETH.md):
  what's proved, what's assumed, theorem call graphs.
- [REPORT_FRAMEWORK.md](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/REPORT_FRAMEWORK.md):
  framework infrastructure landed for this experiment.
- [AXIOMS.md](https://github.com/leonardoalt/evm-smith/blob/main/AXIOMS.md)
  and
  [TRUST_ASSUMPTIONS.md](https://github.com/leonardoalt/evm-smith/blob/main/TRUST_ASSUMPTIONS.md):
  the trust base in detail.

Contributions welcome!
