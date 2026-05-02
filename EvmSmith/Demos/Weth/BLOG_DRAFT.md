# What if AI wrote both the smart contract and the proof?

## A WETH solvency proof, end-to-end, in Lean — with an AI doing all the heavy lifting

We did an experiment. We let an AI:

1. Write a smart contract directly in raw EVM bytecode (no Solidity, no
   compiler).
2. Write a Lean 4 formal proof that the bytecode is solvent — meaning
   the contract's stored token balances never exceed its actual ETH
   balance.

The result: 86 bytes of bytecode, and a machine-checked proof that
those 86 bytes satisfy the solvency property — under explicit, narrow
assumptions about chain state and standard EVM execution boundaries.

This blog post explains what we built, what's actually been proved,
what's still assumed, and what we think the experiment means for how
smart-contract development might evolve.

---

## What's the contract?

A minimal Wrapped-ETH (WETH) clone. Two functions:

- `deposit()` payable: when a user sends ETH to the contract, their
  token balance increases by the same amount.
- `withdraw(amount)`: if the user has enough tokens, decrement the
  user's balance and send back the corresponding ETH.

That's it. Real WETH on Ethereum is more complicated (events, ERC-20
boilerplate, allowances), but this minimal version captures the
critical solvency property.

In our setup, the contract is **86 bytes of raw EVM bytecode**, written
directly. No Solidity. No compiler in the trust path.

## What's the property?

**Solvency**: at every moment in the contract's life, the sum of all
users' stored token balances is at most the contract's actual ETH
balance.

In Lean:

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

If solvency holds, every user can always withdraw their full balance —
the contract never owes more tokens than it has ETH to back them.

## What's a "proof" here?

A Lean theorem. Lean is a dependently-typed proof assistant: every
proof is a program that the type checker mechanically verifies. There's
no manual checking, no human reviewer making errors. If the file
compiles, the theorem holds.

Our headline theorem says, roughly:

> **For any well-formed EVM state σ where solvency holds, after running
> any single Ethereum transaction through the standard transaction
> processor, solvency still holds in the post-state σ'.**

In Lean syntax:

```lean
theorem weth_solvency_invariant
    (... boundary hypotheses ...)
    (hInv : WethInv σ C)              -- pre-state solvency
    (hAssumptions : WethAssumptions ...) :
    match EVM.Υ ... σ ... with
    | .ok (σ', _, _, _) => WethInv σ' C   -- post-state solvency
    | .error _ => True
```

`EVM.Υ` is the EVM's transaction-processing function — the formal
specification of "run a transaction". We didn't write this. It's part
of EVMYulLean, an open-source Lean formalization of Ethereum's Yellow
Paper.

So the theorem says: **starting from a state that satisfies WETH's
solvency invariant, after the EVM does whatever it does for a
transaction, the state still satisfies solvency**.

### Partial correctness — what about failures?

Note the two-branch structure of the conclusion:

- `.ok (σ', _, _, _) => WethInv σ' C` — if the transaction *succeeded*,
  the post-state still satisfies solvency.
- `.error _ => True` — if the transaction *errored*, we claim nothing.

The error branches include: out-of-gas, REVERT, invalid opcode, stack
underflow, and any of the EVM's other halt conditions. EVMYulLean
models all of these — gas is fully tracked (Yellow Paper Appendix G:
the per-instruction schedule, memory-expansion cost, the dynamic
call-gas computation), and any step that runs out of gas, hits an
invalid op, or reverts produces an `.error` result that propagates up
through Ξ, Θ, Λ, Υ.

This is the **partial correctness** framing common to formal proofs
of real-world programs: we prove safety on successful runs, not
termination or liveness. We don't claim "the contract always
succeeds" — only "if it succeeds, it doesn't break solvency".

This matters for understanding what the theorem rules out (and what
it doesn't). Things it **rules out**:

- Any successful execution that ends with the user's stored balance
  having grown beyond the ETH backing it.
- Any successful execution where reentrancy or sequence-of-calls
  could leave the contract owing more tokens than it has ETH.

Things it **doesn't rule out** (and doesn't need to):

- A user calling `withdraw` and the CALL failing — that produces
  `.error`, and the conclusion is vacuous. (But notice: WETH writes
  the state update *before* the CALL, so even on `.error` the
  pre-failure state is consistent. The user's balance is decremented;
  they didn't get paid. The accounting still adds up. This is the
  standard "checks-effects-interactions" pattern, and it matters
  here.)
- Out-of-gas conditions partway through deposit or withdraw — same
  story: the conclusion is vacuous on `.error`, and the EVM's
  state-rollback semantics (also modeled in EVMYulLean) handle it.

So when we say the proof is "complete," we mean: every reachable
post-state of a successful transaction satisfies solvency. Failures
fall into the EVM's normal error-handling, which the model accurately
represents.

## Aside: Θ, Λ, Ξ, Υ — what are these?

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

WETH's `withdraw` does an outbound CALL — which goes through Θ. WETH
itself is invoked by some outer transaction processed by Υ, which
calls Θ to invoke Ξ on WETH's bytecode.

Whenever we say "WETH's invariant is preserved by Θ" or "the CALL
goes through Λ", these are the layers we mean.

## How is this proved?

The proof has to walk through WETH's bytecode instruction-by-instruction
and track what happens to the EVM state at the proposition level. Not
"this code seems to work"; not "this code passes tests"; but "we have a
formal Lean proof that for every possible input, the math works out".

Concretely, the proof:

1. **Models the bytecode as a control-flow graph**. WETH has 86 bytes
   spanning **59 distinct program counter (PC) positions**. The proof
   builds a predicate `WethTrace` enumerating every reachable
   `(PC, stack-length)` combination.

2. **Threads structural data through the trace**. At each PC, the proof
   carries witnesses about what's on the stack and what storage facts
   hold. For instance: at PC 60 (the SSTORE in `withdraw`), the trace
   carries `(slot=sender, oldVal=balance, newVal=balance−x, bound x ≤
   balance)`. The bound comes from the JUMPI gate at PC 55 — the proof
   formally verifies that path.

3. **Per-PC walks**. For each PC, a Lean theorem walks one instruction
   forward, showing the post-state still satisfies the trace
   predicate. **61 such per-PC walks**, aggregated into a single
   `weth_step_closure` theorem.

4. **Bridges to the EVM's transaction processor**. A
   relational-invariant top-level theorem `Υ_invariant_preserved`
   says: if your contract's invariant is preserved by every internal
   step, then it's preserved by the transaction. We feed it the
   per-step preservation, and it gives us the headline theorem.
   This bridge is itself a worked-example pattern (in
   `EvmSmith/Demos/Weth/InvariantClosure.lean`, alongside the WETH
   proof) built on top of generic frame primitives carried by the
   underlying EVMYulLean framework — the framework supplies the
   contract-agnostic Ξ/Θ/Λ/X preservation closures and Υ-tail
   helpers, and this WETH-style relational-invariant bridge sits on
   top.

## What's still assumed?

The proof isn't complete in vacuum. There are five structural
assumptions, packaged in a `WethAssumptions` bundle:

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

1. **`deployed`** — WETH's specific 86-byte bytecode is installed at
   address C. (Real-world: someone deployed it.)

2. **`sd_excl`** — across the entire transaction's call tree (which
   may include arbitrary other contracts called by WETH or calling
   WETH), no `SELFDESTRUCT` instruction targets C — i.e., C is not
   added to the transaction's self-destruct set.

   Note that this is a claim about *every* contract in the call tree,
   not just WETH. SELFDESTRUCT only inserts the *executing-frame*
   address into the self-destruct set, so for some other contract D ≠
   C to add C, D would have to be running *as* C — which can't happen
   unless C's deployed code is D, which `deployed` rules out.

   **An aside on real Ethereum**: post-Cancun (EIP-6780, activated
   March 2024), `SELFDESTRUCT` no longer deletes contracts that
   weren't created in the same transaction. So on current mainnet,
   `sd_excl` is essentially moot — a pre-existing WETH deployment
   simply cannot be SELFDESTRUCT-ed by anyone. The EVM model in
   EVMYulLean (which our proof uses) is the older, more conservative
   pre-Cancun semantics where SELFDESTRUCT could remove an arbitrary
   contract. Our proof handles that stricter case; on real
   post-Cancun chains the assumption is automatically satisfied.

3. **`dead_at_σP`** — after the EVM dispatches the transaction's
   value transfer and contract call (the Θ/Λ step that happens before
   actual code execution), C still has non-empty code at the
   dispatched state. In other words: WETH's deployment isn't undone
   mid-transaction.

4. **`inv_at_σP`** — after that same dispatch step (still before
   actual code execution begins), the solvency invariant
   `storageSum σ C ≤ balanceOf σ C` still holds. The dispatch step
   transfers value to C (deposit) or from C (withdraw return), and
   this assumption says those bookkeeping moves don't break solvency
   in the way they update balances.

5. **`call_no_wrap`** — when WETH transfers ETH back to a withdrawing
   user, the user's balance plus the transfer amount is < 2^256.
   (Real-world: total ETH supply is bounded; UInt256 arithmetic doesn't
   overflow on real chain state.)

Items 1–4 are standard transaction-boundary facts: they describe the
state of the chain at the moment WETH's code begins executing, and
how value transfers get bookkept before the code runs. Item 5 is
genuinely irreducible: it's a fact about the chain's balance state,
not derivable from any bytecode reasoning.

**Crucially, every assumption that was *about WETH's bytecode behavior*
has been eliminated**. The "interesting" parts of the proof — what the
SSTOREs do, what the CALL does, how the LT/JUMPI gate enforces
solvency — are all Lean theorems, mechanically checked.

## What's the trust boundary?

To trust the WETH solvency theorem, you trust:

1. **Lean's type checker** — that the proof compiles.

2. **EVMYulLean's modeling choices**. EVMYulLean is a Lean
   formalization of the EVM. Most of its content is *theorems*
   (mechanically proved in Lean — these you don't trust, you check).
   But two facts are stated as **explicit axioms** because formally
   proving them is out of scope:

   - `precompile_preserves_accountMap` (paper section T2): every
     EVM precompile (SHA256, ECRECOVER, etc.) returns a state whose
     accountMap is either unchanged or empty. Provable by case
     inspection of the ten precompile bodies; not yet done.
   - `lambda_derived_address_ne_C` (paper section T5): the address
     derived by CREATE/CREATE2 (computed via Keccak) never collides
     with C. Equivalent to Keccak's collision-resistance, a
     cryptographic assumption.

   Beyond these two axioms, you also trust the **definitions** in
   EVMYulLean — that `EVM.Υ`, `EVM.step`, etc. accurately model the
   actual EVM behavior. Bugs in those definitions would invalidate
   the proof.

3. **The 5 `WethAssumptions` fields** above.

That's everything. No "trust me" predicates about what the bytecode
does. No appeal to compiler correctness. No "we ran a million tests".

## What's the experiment really about?

The deeper question: **do we still need compilers?**

Smart contracts today are written in a high-level language (Solidity,
Vyper, Move, …), compiled to bytecode, and deployed. The compiler is
a load-bearing piece of trusted infrastructure: a bug in the compiler
can introduce a vulnerability invisible to the high-level source
review.

Our experiment skips the compiler entirely. The AI:

- Writes the bytecode directly.
- Writes a Lean proof that the bytecode satisfies the safety property.

Both artifacts live at the same level of abstraction (machine code +
machine-checked proof about machine code). There's no translation gap
where bugs hide.

This isn't theoretically novel — formal verification of bytecode has
existed for years. What's new is the **scale of effort** required from
the human. We didn't write any of the proof. We didn't write the
bytecode. We supervised the AI, redirected it when it got stuck, and
verified the trust boundaries at the end.

## What does the human still need to do?

This is the load-bearing question. If the AI writes the bytecode and
writes the proof, what's left for humans?

**Reading the spec.** Lean theorem statements *are* the specification.
A human auditor can read:

```lean
def WethInv (σ : AccountMap .EVM) (C : AccountAddress) : Prop :=
  storageSum σ C ≤ balanceOf σ C
```

…and confirm: yes, this is what "solvency" means. The token balances
shouldn't exceed the ETH balance. If you can read this Lean
definition, you understand the property being proved.

**Reading the assumptions.** The same auditor reads:

```lean
call_no_wrap : WethCallNoWrapAt72 C
```

…and confirms: yes, this is a chain-state bound on UInt256 wrapping.
True in practice on Ethereum. Acceptable to assume.

If they don't understand a Lean expression, they can't verify the
claim. **The thing humans must be able to read is Lean theorem
statements**, not Solidity, not bytecode, not test results.

## What's the scale?

There are three cost categories, in decreasing order of reusability:

**Generic framework infrastructure** (reusable by *any* future EVM
bytecode proof, regardless of invariant shape): ~3500 lines of new
Lean added to EVMYulLean's `EvmYul/Frame/` tree this session,
sitting on top of an earlier ~9000-line balance-monotonicity chain.
This is the most amortizable layer — mutual induction proofs of
Ξ/Θ/Λ/X properties (account-presence preservation,
accountMap-preservation strong shape lemmas, the universal
Ξ-preservation result, generic Υ-tail helpers, pres-step variants
for invariant-aware Reachable closures). None of it is WETH-specific.
A second contract proof on the same framework inherits all of it
for free.

**Relational-invariant closure** (reusable by future proofs of the
same `S ≤ β` shape, *and* generalisable): ~5400 lines of Lean in
`EvmSmith/Demos/Weth/InvariantClosure.lean` — the
`StorageSumLeBalance` predicate, the parallel mutual closure that
preserves it across Θ/Λ/Ξ, and the transaction-level
`Υ_invariant_preserved` entry point. None of these theorems
reference WETH's bytecode; the closure is generic in shape and
lives consumer-side only because we currently have one consumer.
A future contract with the *same* shape inherits it directly. A
future contract with a *different* relational invariant (say
`Σ supply ≤ totalSupply`) would either copy and specialise this
file or — the eventual right move — trigger the lift into the
frame library as a parametric module over `I : AccountMap →
AccountAddress → Prop`. We deliberately deferred that
parameterisation: premature with one consumer, a small refactor
once a second consumer establishes the pattern.

**WETH-specific** (the per-contract proof): ~6800 lines of Lean —
dominated by `BytecodeFrame.lean` (~6000 lines: 61 per-PC walks
through the bytecode trace, plus cascade threading for the deposit
and withdraw blocks and dischargers for each cascade-fact
predicate), with `Solvency.lean` (~380 lines: the headline theorem
composition + assumptions bundle), `Invariant.lean` (~160 lines:
the `WethInv` abbreviation + transit lemmas), and `Program.lean`
(~200 lines: the bytecode definition + the symbolic block-list
forms used by the walk).

So for *this* 86-byte contract: ~6800 lines of WETH-specific proof,
roughly 80 lines of Lean per byte of bytecode (heavily front-loaded
in the per-PC walk machinery).
For a *future* contract with WETH-style solvency on the same
framework: dominated by bytecode-specific cascade threading and
per-PC walks — likely a few hundred lines of Lean per hundred bytes
of bytecode, plus whatever contract-specific invariants need their
own dischargers, and the relational-invariant closure inherited
directly. For a future contract with a *different* relational
invariant: add the cost of porting the closure pattern.

The framework investment is steep but one-time. The per-contract
cost is what matters going forward.

## What does "AI did it" actually mean?

We used Claude — Anthropic's LLM — as the proof engineer. We provided:

- The high-level goal ("prove WETH is solvent").
- The framework (EVMYulLean) — an existing formalization.
- Iterative review and direction when the AI got stuck.

The AI did the actual proof engineering: writing the bytecode trace,
threading cascade data through PCs, navigating Lean's elaboration
quirks, designing the framework infrastructure (mutual induction over
Ξ/Θ/Λ/X for account-presence preservation), refactoring assumptions
to narrow them.

When the AI encountered a wall — like a 600-line proof with
elaboration friction — it sometimes bogged down. We redirected it,
spawned focused sub-agents for specific tasks, and eventually got
through. The final proof's structure emerged from a long iterative
process, not a one-shot generation.

Claude also bailed many times saying some steps were "multi-day
sessions", which we corrected only by repeatedly telling it to keep
grinding. Calibrating the AI's sense of "this is too much work" to
match the actual scope is its own meta-challenge.

## What does this experiment *not* prove?

**It doesn't prove that AI can replace auditors.** A human still has
to read the spec (the Lean theorem statement) and confirm it captures
the right property.

**It doesn't prove that AI can write any bytecode.** WETH is a small
contract with simple logic. Larger contracts with intricate state
machines, reentrancy patterns, or upgradability would be much harder.

**It doesn't prove the EVM model is faithful.** EVMYulLean is a
substantial formalization of EVM semantics, with 2 explicit axioms
(see "What's the trust boundary?" above) and a much larger body of
*definitions* whose faithfulness to the real EVM is itself a
modeling claim. Bugs in those definitions would invalidate the
proof. (This is the same modeling-fidelity question shared by any
Lean-based EVM verification.)

## Where this might go

A future where:

- Smart contracts are deployed as bytecode + Lean proof of safety
  properties.
- The "audit" is reading the Lean theorem statements and confirming
  they capture the right invariants.
- Compilers are debugging tools, not load-bearing infrastructure: you
  can compile from Solidity to check your bytecode matches your
  intent, but the deployed artifact is the bytecode + proof.
- The proof is generated by AI, supervised by humans who read the
  spec.

The bottleneck moves from "can we compile correctly?" to "can humans
read the spec?" That seems like a more honest place for the
trust boundary to sit.

---

## Try it yourself

The full proof lives at `github.com/leonardoalt/evm-smith` (this
repo) and depends on `github.com/leonardoalt/EVMYulLean` (the framework
fork).

Build instructions in the README. The headline theorem is in
`EvmSmith/Demos/Weth/Solvency.lean`. The framework infrastructure
landed in this experiment is documented in
`EvmSmith/Demos/Weth/REPORT_FRAMEWORK.md`.

The proof compiles. The theorem holds. We hope it's useful.
