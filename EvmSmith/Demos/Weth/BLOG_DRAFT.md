# evm-smith: formally verified Ethereum smart contracts, without a compiler

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
This is of course not a feasible practice for humans, shown by our move from
assembly to HLLs decades ago. However, we are not the ones writing code
anymore.

My first thought then was: can we do the same for Ethereum smart contracts? I
was immediately convinced AIs can write EVM assembly quite well, but can they
write the proofs too? Can they prove inductive invariants in the presence of
potential reentrancy, over any callstack length, considering every possible
malicious external contract?

To test this, I asked Claude to write EVM assembly and Lean proofs for
increasingly harder problems, such as contracts that "read 3 numbers and add
them" and that "let any account set the value of storage slot `msg.sender`",
with different properties being proved for each contract. I used
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean) to get formal and
executable semantics for EVM bytecode.

My requirements were:

- I will describe what the smart contract should do, but I shouldn't write bytecode.
- I will read the bytecode.
- I will describe the properties that should be proven, but I shouldn't write theorems nor proofs.
- I will read the main theorems and check for sorries and new axioms.

Claude was quite efficient at proving properties for the simpler contracts, and
we quickly got to the final boss of this experiment, a WETH-clone solvency
proof.

The result is [evm-smith](https://github.com/leonardoalt/evm-smith), a new
framework that provides the machinery for AI to write combined EVM bytecode and
Lean proofs.

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
  If you are a smart contract dev, I invite you to read the bytecode to get an
  idea that this _should_ be correct.
- [Foundry
  tests](https://github.com/leonardoalt/evm-smith/tree/main/EvmSmith/Demos/Weth/foundry)
  for our contract. Useful for integration, fuzzing and deployment.
- [Solvency
  theorem/proof](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Solvency.lean#L338).
  The final goal.

This article explains what we (Claude and I) built, what's actually been
proved, what's still assumed, and what I think the experiment means for how
smart-contract development might evolve.

## What's the property?

**Solvency**: at every moment in the contract's life, the sum of all
users' stored token balances is at most the contract's actual ETH
balance.

[In Lean](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Invariant.lean) (using the types from `EVMYulLean`):

```lean
def WethInv (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  storageSum σ C ≤ balanceOf σ C
```

Reading this:

- `σ` is the **EVM state** — a snapshot of all accounts on the chain
  (their balances, code, and storage).
- `C` is **WETH's contract address** — a specific account in σ.
- `storageSum σ C` is the **sum over every storage slot at C's account
  in σ**. For our WETH layout, each slot holds a single user's token
  balance, so this sum equals the total of all users' tokens.
- `balanceOf σ C` is **C's actual ETH balance in σ** — the wei held by
  the contract.
- `≤` is the standard ≤ on natural numbers.

So `WethInv σ C` says: in state σ, the total of users' token balances
at WETH (C) is at most the actual ETH balance of WETH (C).

If solvency holds, every user can always withdraw their full balance, i.e., the
contract never owes more tokens than it has ETH to back them.

## What's a "proof" here?

A Lean theorem. Lean is a dependently-typed proof assistant: every proof is a
program that the type checker mechanically verifies.  If the file compiles, the
theorem holds.

Our [headline theorem](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Solvency.lean) says, roughly:

> **For any well-formed EVM state σ where solvency holds, after
> running any single Ethereum transaction through `EVM.Υ` (the EVM's
> transaction processor, formalized in EVMYulLean), solvency still
> holds in the post-state σ'.**

In Lean syntax (the actual signature, lightly reflowed):

```lean
theorem weth_solvency_invariant
    (fuel : ℕ) (σ : AccountMap .EVM) (H_f : ℕ)
    (H H_gen : BlockHeader) (blocks : ProcessedBlocks)
    (tx : Transaction) (S_T C : AccountAddress)
    (hWF      : StateWF σ)                            -- total ETH < 2^255
    (hInv     : WethInv σ C)                          -- pre-state solvency
    (hS_T     : C ≠ S_T)                              -- WETH is not the tx sender
    (hBen     : C ≠ H.beneficiary)                    -- WETH is not the miner
    (_hValid  : TxValid σ S_T tx H H_f)               -- standard tx-validity
    (hAssumptions : WethAssumptions σ fuel H_f H H_gen blocks tx S_T C) :
    match EVM.Υ fuel σ H_f H H_gen blocks tx S_T with
    | .ok (σ', _, _, _) => WethInv σ' C               -- post-state solvency
    | .error _          => True                       -- vacuous on failure
```

The first batch of arguments are the parameters Υ itself takes (the
fuel bound, the pre-state σ, the gas counter, two block headers, the
processed-blocks list, the transaction, and the sender + WETH
addresses). `hWF` / `hS_T` / `hBen` / `_hValid` are the standard
transaction-boundary hypotheses any single-contract proof of this
shape needs. `hAssumptions` packages the five WETH-specific
structural facts, discussed in the next section.

So the theorem says: **starting from a state that satisfies WETH's
solvency invariant, after the EVM does whatever it does for a
transaction, the state still satisfies solvency**.

### Partial correctness: what about failures?

The conclusion has two branches: on `.ok` (success) the post-state
satisfies solvency; on `.error` (out-of-gas, REVERT, invalid opcode,
stack underflow, etc.) the conclusion is vacuous. This is **partial
correctness**: we can prove safety on successful runs, not that the
contract always succeeds. The EVM's error semantics (gas tracked per
Yellow Paper Appendix G; failures roll back state) are fully modeled
in EVMYulLean, so failure paths are handled by the model, not by my
theorem.

The headline claim, plainly: **any execution path through any opcode
sequence reachable from any caller, including malicious reentrant
ones, can't violate solvency**. That's the whole point.

Notice the proof captures checks-effects-interactions correctly even
on the failure path: WETH decrements the user's balance *before* the
outbound CALL, so if the CALL reverts, the user's balance went down
and they didn't get paid, so the accounting still adds up.

## What are Θ, Λ, Ξ, Υ?

Before we go further, a quick glossary. The EVM's Yellow Paper uses
Greek letters for the layered execution functions, and the Lean
formalization keeps the same names:

- **Υ** (Upsilon) — *transaction processor*. Takes an EVM state and a
  transaction, returns the post-transaction state. The outermost
  layer.
- **Θ** (Theta) — *call frame*. Handles a CALL/CALLCODE/DELEGATECALL/
  STATICCALL. Transfers value, sets up an execution environment, and
  invokes Ξ.
- **Λ** (Lambda) — *contract-creation frame*. Handles CREATE/CREATE2.
  Computes the new address, transfers value, runs the init code via
  Ξ, and writes the resulting code to the new account.
- **Ξ** (Xi) — *code execution*. Runs a sequence of EVM opcodes
  starting from a given program counter and stack. Internally drives
  the X loop (the per-instruction iteration).

WETH's `withdraw` does an outbound CALL which goes through Θ. WETH
itself is invoked by some outer transaction processed by Υ, which
calls Θ to invoke Ξ on WETH's bytecode.

Whenever we say "WETH's invariant is preserved by Θ" or "the CALL
goes through Λ", these are the layers we mean.

## How is this proved?

The proof has to walk through WETH's bytecode instruction-by-instruction and
track what happens to the EVM state at the proposition level. Concretely, the
proof:

1. **Models the bytecode as a control-flow graph**. WETH has 86 bytes
   spanning **58 distinct program counter (PC) positions**. The proof
   builds a predicate `WethTrace` enumerating every reachable
   `(PC, stack-length)` combination.

2. **Threads structural data through the trace**. At each PC, the proof carries
   witnesses about what's on the stack and what storage facts hold. For
   instance: at PC 60 (the SSTORE in `withdraw`), the trace carries
   `(slot=sender, oldVal=balance, newVal=balance−x, bound x ≤ balance)`. The
   bound comes from the JUMPI gate at PC 55, and the proof formally verifies
   that path.

3. **Per-PC walks**. For each PC, a Lean theorem walks one instruction
   forward, showing the post-state still satisfies the trace
   predicate. 61 such walks across the 58 PCs — the revert block
   (PCs 80, 81, 83) is reached from two different paths
   (insufficient-balance and failed-CALL) with different stack shapes,
   so those PCs need a walk per disjunct. All aggregated into a
   single `weth_step_closure` theorem.

4. **Bridges to the EVM's transaction processor**. A
   relational-invariant top-level theorem `Υ_invariant_preserved`
   says: if your contract's invariant is preserved by every internal
   step, then it's preserved by the transaction. We feed it the
   per-step preservation, and it gives us the headline theorem.
   This bridge is itself a worked-example pattern (in
   `EvmSmith/Demos/Weth/InvariantClosure.lean`, alongside the WETH
   proof) built on top of generic frame primitives carried by the
   underlying EVMYulLean framework: the framework supplies the
   contract-agnostic Ξ/Θ/Λ/X preservation closures and Υ-tail
   helpers, and this WETH-style relational-invariant bridge sits on
   top.

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

Four are about how the contract is set up at the chain level, and one
is a chain-state bound:

1. **`deployed`**: WETH's specific 86-byte bytecode is installed at
   address C. (Real-world: someone deployed it.)

2. **`sd_excl`**: across the entire transaction's call tree (which
   may include arbitrary other contracts called by WETH or calling
   WETH), no `SELFDESTRUCT` instruction targets C, i.e., C is not
   added to the transaction's self-destruct set.

   Note that this is a claim about *every* contract in the call tree,
   not just WETH. SELFDESTRUCT only inserts the *executing-frame*
   address into the self-destruct set, so for some other contract D ≠
   C to add C, D would have to be running *as* C, which can't happen
   unless C's deployed code is D, which `deployed` rules out.

   **An aside on real Ethereum**: post-Cancun (EIP-6780, activated
   March 2024), `SELFDESTRUCT` no longer deletes contracts that
   weren't created in the same transaction. So on current mainnet,
   `sd_excl` is essentially moot: a pre-existing WETH deployment
   simply cannot be SELFDESTRUCT-ed by anyone. The EVM model in
   EVMYulLean (which our proof uses) is the older, more conservative
   pre-Cancun semantics where SELFDESTRUCT could remove an arbitrary
   contract. Our proof handles that stricter case; on real
   post-Cancun chains the assumption is automatically satisfied.

3. **`dead_at_σP`**: after the EVM dispatches the transaction's
   value transfer and contract call (the Θ/Λ step that happens before
   actual code execution), C still has non-empty code at the
   dispatched state. In other words: WETH's deployment isn't undone
   mid-transaction.

4. **`inv_at_σP`**: after that same dispatch step (still before
   actual code execution begins), the solvency invariant
   `storageSum σ C ≤ balanceOf σ C` still holds. The dispatch step
   transfers value to C (deposit) or from C (withdraw return), and
   this assumption says those bookkeeping moves don't break solvency
   in the way they update balances.

5. **`call_no_wrap`**: when WETH transfers ETH back to a withdrawing
   user, the user's balance plus the transfer amount is < 2^256.
   (Real-world: total ETH supply is bounded; UInt256 arithmetic doesn't
   overflow on real chain state.)

Items 1–4 are standard transaction-boundary facts: they describe the state of
the chain at the moment WETH's code begins executing, and how value transfers
get bookkept before the code runs. Item 5 is an irreducible fact about the
chain's balance state.

**Crucially, there are no assumptions _about WETH's bytecode behavior_**.  The
"interesting" parts of the proof, what the SSTOREs do, what the CALL does, how
the LT/JUMPI gate enforces solvency, are all Lean theorems, mechanically
checked.

## What's the trust boundary?

To trust the WETH solvency theorem, we trust:

1. **Lean's type checker**: that the proof compiles.

2. **EVMYulLean's modeling choices**. EVMYulLean is a Lean
   formalization of the EVM. Most of its content is *theorems*
   (mechanically proved in Lean).
   But two facts are stated (by us) as **explicit axioms**:

   - `precompile_preserves_accountMap` (paper section T2): every EVM precompile
     (SHA256, ECRECOVER, etc.) returns a state whose `accountMap` is either
     unchanged or empty. Provable by case inspection of the ten precompile
     bodies if they were actual EVM precompiles.
   - `lambda_derived_address_ne_C` (paper section T5): the address
     derived by CREATE/CREATE2 (computed via Keccak) never collides
     with C. Equivalent to Keccak's collision-resistance, a
     cryptographic assumption.

   Beyond these two axioms, you also trust the **definitions** in
   EVMYulLean: that `EVM.Υ`, `EVM.step`, etc. accurately model the
   actual EVM behavior. Bugs in those definitions would invalidate
   the proof.

3. **The 5 `WethAssumptions` fields** above.

## Do we still need compilers?

Smart contracts today are written in a high-level language (Solidity,
Vyper, ...), compiled to bytecode, and deployed. The compiler sits in
the trusted base: a bug in the compiler can introduce a vulnerability
invisible to high-level source review, potentially leading to loss of
funds.

This experiment skips the compiler entirely. The AI:

- Writes the bytecode directly.
- Writes a Lean proof that the bytecode satisfies the safety property.

Both artifacts live at the same level of abstraction (machine code +
machine-checked proof about machine code), minimizing the translation gap where
bugs often hide.

Of course this isn't theoretically novel, as formal verification of EVM bytecode has
existed for years. What I personally find groundbreaking in this approach is:

- Compilers are large pieces of software and cost a lot of money. We can potentially bypass them entirely.
- Minimal effort required from the human:
    - I supervised the AI and tried to guide it.
    - I read the bytecode which makes sense to me.
    - I verified the trust boundaries, axioms, and theorems.
    - I didn't write any code.
    - I didn't need to read the proofs — the type checker did.

## What does the human still need to do?

This is the question that decides whether any of this matters. If
the AI writes the bytecode and writes the proof, what's left for
humans?

**Reading the spec.** Lean theorem statements are the specification.

```lean
def WethInv (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  storageSum σ C ≤ balanceOf σ C
```

A human auditor can read the property above and confirm that this is what
"solvency" means. The token balances shouldn't exceed the ETH balance. If you
can read this Lean definition, you understand the property being proved.

```lean
call_no_wrap : WethCallNoWrapAt72 C
```

**Reading the assumptions.** The same auditor reads the assumption above and
confirms that this is a chain-state bound on UInt256 wrapping, which is true in
practice on Ethereum and acceptable to assume.

If they don't understand a Lean expression, they can't verify the claim. The
thing humans **must** be able to read is Lean theorem statements.

It is possible or likely that this will take a while to become common.  An
alternative to that are thin higher level eDSLs built in Lean itself that serve
as a "human readable IR" and have a verified compiler to EVM bytecode.

## What's the scale?

The cost splits in three tiers, in decreasing order of reusability:

- **Generic framework infrastructure** — ~12500 lines of new Lean
  in EVMYulLean's `EvmYul/Frame/` library: mutual-induction
  preservation results for Ξ/Θ/Λ/X, account-presence preservation,
  the universal Ξ-preservation theorem, generic Υ-tail helpers.
  None of it is WETH-specific; any future EVM bytecode proof
  inherits it for free.
- **Relational-invariant closure** — ~5400 lines in
  `EvmSmith/Demos/Weth/InvariantClosure.lean`: the
  `storageSum ≤ balanceOf` predicate plus the mutual closure that
  preserves it across Υ. Generic in shape (no WETH-bytecode refs);
  lives consumer-side only because we have one consumer. The
  natural next step once a second consumer demonstrates the same
  shape is lifting it back into the framework as a parametric
  module over the invariant.
- **WETH-specific** — ~6800 lines, dominated by `BytecodeFrame.lean`
  (~6000 lines of per-PC walks through the bytecode trace), plus
  the headline theorem composition (`Solvency.lean`), the `WethInv`
  abbreviation (`Invariant.lean`), and the bytecode definition
  (`Program.lean`).

For this 86-byte contract that's ~80 lines of WETH-specific Lean
per byte of bytecode. Framework cost is one-time and amortizes
across every future contract; per-contract cost is large today but
impressive for a first attempt and clearly improvable.

## How did Claude do?

I used Claude as the proof engineer. I provided:

- The high-level goals (e.g. "prove WETH is solvent").
- The framework (EVMYulLean): an existing formalization.
- Iterative review and direction when the AI got stuck.

Claude wrote all code: EVM bytecode, executable tests, compile-time tests,
Foundry integration for fuzzing and Solidity tests, and the Lean proofs.  All
the code and testing parts were one-shot. The proofs took several (probably >=
20 and <= 100) sessions and different prompt styles, including Claude code
directly trying, parallel sub-agents, "hyperfocused" single sub-agent, and pep
talks. Claude bailed many times saying some steps were "multi-day sessions",
which I still don't know how to get out of besides by repeatedly telling it to
keep grinding.

## The Potential Future

- Smart contracts are deployed as bytecode + Lean proof of safety
  properties.
- The "audit" is reading the Lean theorem statements and confirming
  they capture the right invariants.
- Compilers are debugging tools, not part of the trusted base: you
  can compile from Solidity to check your bytecode matches your
  intent, but the deployed artifact is the bytecode + proof.
- The proof is generated by AI, supervised by humans who read the
  spec.

The bottleneck moves from building a safe and performant compiler to humans
reading formal specs in Lean.

## Artifacts

The full proof lives at [evm-smith](https://github.com/leonardoalt/evm-smith),
and depends on [the framework fork of EVMYulLean](https://github.com/leonardoalt/EVMYulLean).

The headline theorem is in [EvmSmith/Demos/Weth/Solvency.lean](https://github.com/leonardoalt/evm-smith/blob/main/EvmSmith/Demos/Weth/Solvency.lean).
The framework infrastructure landed in this experiment is documented in the [framework report](EvmSmith/Demos/Weth/REPORT_FRAMEWORK.md).

Contributions welcome!
