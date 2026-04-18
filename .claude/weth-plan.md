# Plan — `Weth` contract (wrapped-ETH token in raw EVM bytecode) — v2

**Changes vs v1** (per `weth-review-1.md`):

1. **Bytecode fix**: removed phantom `POP` at withdraw entry (stack is
   `[]` after its dispatch JUMPI, not `[selector]`); fixed deposit
   block signature to `hs : s0.stack = [selector]`.
2. **Conservation invariant**: dropped from Lean statement. Replaced
   with narrower per-call storage-delta theorems in Lean; Foundry
   invariant testing takes full responsibility for the
   multi-transaction cross-user claim.
3. **Invariant 4 weakened** from equality to `≤`: `Σ storage[a] ≤
   accountMap[C].balance` — handles force-fed ETH (SELFDESTRUCT,
   coinbase) while still expressing the real safety property (user
   funds never lost).
4. **Foundry handler-contract pattern** specified explicitly:
   `WethHandler.sol` with `deposit`/`withdraw` methods + ghost
   variables, `targetContract(handler)` in setUp, invariant iterates
   over a tracked actor set.
5. **Reentrancy test promoted to mandatory** with a concrete attacker
   contract.
6. **Spike plan**: prove `runOp_dup3`, `runOp_dup5`, `runOp_swap2`
   before chaining through the withdraw-block proof.
7. **Block-pc parametrization**: block proofs take arbitrary
   starting `pc` because JUMPI-taken targets are absolute, not
   offsets from block start.
8. **REVERT chain termination**: `runSeq_cons_ok` only handles `.ok`;
   for the revert block we either (a) write a `runSeq_cons_err`
   fusion, or (b) stop chaining one step before REVERT and conclude
   with a direct equation. Chose (b) — simpler.
9. **Gas-unaware disclaimer** on the Lean side (Foundry covers gas).
10. **Contract funding**: starts with 0 ETH; all ETH comes from
    deposits.

Third worked example. Substantially more ambitious than Add3 / Register:
first one with **function dispatch**, **control flow** (JUMP/JUMPI/
JUMPDEST), **state-mutating CALL** (for the ETH refund on withdraw),
and genuinely **inductive invariants** over state transitions.

## The contract

Minimal WETH-style wrapper. Exactly two entry points distinguished by
a 4-byte function selector in `calldata[0:4]` (Solidity ABI convention):

| Solidity signature | Selector | Args | Behaviour |
|--------------------|----------|------|-----------|
| `deposit()`        | `0xd0e30db0` | none | `balance[msg.sender] += msg.value` |
| `withdraw(uint256)`| `0x2e1a7d4d` | `x` at offset 4 | if `balance[msg.sender] ≥ x`: `balance[msg.sender] -= x`, send `x` wei to `msg.sender`; else revert |

Storage layout: `storage[msg.sender]` (address as `uint256` slot key)
holds the user's token balance in wei. Same convention as `Register`,
so the existing `addressSlot` / `storageAt` helpers apply.

No events, no name/symbol/decimals views, no approvals, no transfers
to other addresses. Minimal but real.

### Why two selectors is the minimum

`deposit()` takes no args but must exist as an externally-callable
entry point to be useful (otherwise users can't call it without
sending raw value + hitting a fallback — more machinery). `withdraw`
needs an argument. So two selectors is the minimum viable API.

## Bytecode layout

Approximate byte counts; final bytecode is pinned during
implementation.

### Dispatch (PCs 0..31, ~32 bytes)

```
  PUSH1 0x00        ; [0]
  CALLDATALOAD      ; [calldata[0:32]]        — treat the first word
  PUSH1 0xe0        ; [224, …]                — shift right by 28*8
  SHR               ; [selector]              — top 4 bytes only
  DUP1              ; [selector, selector]
  PUSH4 0xd0e30db0  ; [depositSel, selector, selector]
  EQ                ; [isDeposit, selector]
  PUSH2 <depositLbl>; [depositLbl, isDeposit, selector]
  JUMPI             ; → if match go to depositLbl; stack [selector]
  PUSH4 0x2e1a7d4d  ; [withdrawSel, selector]
  EQ                ; [isWithdraw]
  PUSH2 <withdrawLbl>
  JUMPI             ; → if match go to withdrawLbl; stack []
  PUSH1 0 PUSH1 0 REVERT  ; no match: revert
```

### Deposit block (PCs 32..~41, ~10 bytes)

Entry stack: `[selector]` (leftover from DUP1; pop it).

```
  JUMPDEST          ; depositLbl
  POP               ; pop stale selector
  CALLER            ; [sender]
  DUP1              ; [sender, sender]
  SLOAD             ; [balance, sender]       — storage[sender]
  CALLVALUE         ; [value, balance, sender]
  ADD               ; [balance + value, sender]
  SWAP1             ; [sender, newBalance]
  SSTORE            ; storage[sender] = newBalance; stack: []
  STOP
```

No overflow check — `balance + value > 2^256 - 1` would require the
sum of all wei deposited to exceed the total ETH supply in wei (~10^26),
infeasible. If the bytecode ever lands in a pathological environment
with adversarial balance seeding, the write wraps modulo 2^256 and
the invariant breaks; the Foundry test `testFuzz_overflow_invariant`
documents this boundary.

### Withdraw block (PCs ~42..~90, ~50 bytes)

Entry stack: `[]` (the dispatch's second EQ consumed the sole
remaining selector copy; nothing leftover at this label).

```
  JUMPDEST          ; withdrawLbl
  PUSH1 0x04
  CALLDATALOAD      ; [x]                    — calldata[4:36]
  CALLER            ; [sender, x]
  DUP1              ; [sender, sender, x]
  SLOAD             ; [balance, sender, x]

  -- Check balance ≥ x, else revert
  DUP3              ; [x, balance, sender, x]
  DUP2              ; [balance, x, balance, sender, x]
  LT                ; [balance<x, balance, sender, x]
  PUSH2 <revertLbl>
  JUMPI             ; → if balance<x, revert; stack [balance, sender, x]

  -- Subtract and store
  DUP3              ; [x, balance, sender, x]
  SWAP1             ; [balance, x, sender, x]
  SUB               ; [newBalance, sender, x]
  SWAP1             ; [sender, newBalance, x]
  SSTORE            ; stack: [x]             — storage[sender] = newBalance

  -- Send x wei to sender via CALL
  PUSH1 0x00        ; retSize
  PUSH1 0x00        ; retOff
  PUSH1 0x00        ; argsSize
  PUSH1 0x00        ; argsOff
  DUP5              ; [x, 0, 0, 0, 0, x]
  CALLER            ; [sender, x, 0, 0, 0, 0, x]
  GAS               ; [gas, sender, x, 0, 0, 0, 0, x]
  CALL              ; [success, x]

  -- Check call succeeded, else revert
  ISZERO
  PUSH2 <revertLbl>
  JUMPI             ; → if !success, revert
  POP               ; [] — pop x
  STOP

  JUMPDEST          ; revertLbl
  PUSH1 0x00 PUSH1 0x00 REVERT
```

**Ordering**: state is updated (`SSTORE`) **before** the external
`CALL`. This is the checks-effects-interactions pattern — necessary
to prevent reentrancy, which is the classic WETH-class vulnerability.
A reentrant call landing back in our `withdraw` sees the already-
decremented balance, so the balance-check would fail on the nested
attempt.

### Total size

~90-100 bytes. Final count pinned after assembly.

## Invariants to state

Four invariants, tiered by provability:

### 1. Balance monotonicity under sufficient funds (per-call, provable)

For a deposit: `post.balance[sender] = pre.balance[sender] + msg.value`.
For a withdraw with `pre.balance[sender] ≥ x`:
`post.balance[sender] = pre.balance[sender] - x`.

These are straightforward block-level theorems; directly provable in
Lean against the straight-line deposit/withdraw blocks (no dispatch
reasoning, no CALL reasoning required, since we reason before CALL).

### 2. Frame rule (per-call, provable)

`deposit` and `withdraw` only modify `storage[sender]` and the
contract's ETH balance. All other storage slots and all other
accounts' state is unchanged. Stated in the same form as
`Register.program_preserves_other_accounts` — account-map-level.

### 3. Withdrawal safety (per-call, provable)

If `pre.balance[sender] < x`, the withdraw block reverts and the
post-state's storage is unchanged (revert restores state). Provable
via the branch on `LT` → `JUMPI` → `revertLbl`.

### 4. Conservation (Foundry-only, weakened to ≤)

**The main safety invariant**. For any reachable state `s` (starting
from the deploy-time all-zero state and stepping through any
sequence of deposit/withdraw calls by any senders):

    sum over all addresses a of storageAt(s, C, addressSlot(a))
      ≤ s.accountMap[C].balance

where `C` is the contract's address. In English: **user funds are
never lost** — the contract always holds at least enough ETH to
honor all recorded token balances.

Weakened from equality to `≤` because of **force-fed ETH**: anyone
can `SELFDESTRUCT` into `C` (or make `C` a coinbase beneficiary)
and increase its balance without invoking our bytecode.
`Σ storage[a]` tracks only voluntary deposits. `≤` still expresses
the solvency property we actually care about; equality is not
achievable against an adversarial world.

**Provability**: Not stated in Lean. Relies on the Foundry
invariant test. Reasons:

- The storage-half needs `RBMap.foldl_insert` / `foldl_erase`
  lemmas that Batteries doesn't expose (verified by grep — same
  gap as Register's slot-level theorems).
- The ETH-balance-half needs CALL-level reasoning through Θ,
  which is out of reach for a worked example of this scope.
- Even if both were achievable, the quantification over *all
  reachable states* is transaction-level modeling we haven't
  built.

Foundry invariant testing is the perfect tool for this: it generates
long sequences of random `deposit`/`withdraw` calls from arbitrary
senders and checks the invariant after every transition. If the
invariant can be violated, it finds a counterexample.

What Lean *does* prove instead — a narrower per-call delta claim:

### 5. Per-call storage delta (provable)

For `deposit`:
```
storageAt post C (addressSlot u) = storageAt pre C (addressSlot u) + msg.value
∀ a ≠ u, storageAt post C (addressSlot a) = storageAt pre C (addressSlot a)
∀ addr ≠ C, accountMap[addr] unchanged
```

For `withdraw(x)` on the success path (`pre.balance ≥ x`), up to
but not including the `CALL`:
```
storageAt post C (addressSlot u) = storageAt pre C (addressSlot u) - x
(frames identical to above)
```

These are the same shape as Register's proved theorems, just
applied to the Weth program's blocks. Provable against the
block-level `runSeq` chain. The slot-level frame claim has the
same Batteries-API blocker as Register; state at account-map level
and accept the restriction.

## Proof strategy

### The problem with `runSeq`

Our existing `runSeq` walks a concrete list of opcodes sequentially;
it does **not** simulate JUMP/JUMPI/JUMPDEST. A program with control
flow cannot be faithfully executed with `runSeq`.

### Block-level approach

Decompose Weth's bytecode into straight-line **basic blocks**, each
ending in `JUMP` / `JUMPI` / `STOP` / `REVERT` / `RETURN`. Prove
per-block effects using `runSeq`-style chaining. At the contract
level, state behaviour as "assume calldata selector = deposit → the
deposit block ran". We don't attempt to prove the top-level dispatch
in Lean; Foundry tests cover end-to-end behaviour.

Blocks identified:

- **B0 (dispatch)** — not proved in Lean; tested in Foundry.
- **B1 (deposit)** — straight line from `depositLbl` through `STOP`.
  Provable: `program_result`-style equation for the deposit path,
  starting from a state with stack `[selector]` and calldata whose
  selector matches deposit.
- **B2_pre_call (withdraw up to `CALL`)** — straight line from
  `withdrawLbl` up to but not including `CALL`. Provable.
- **B2_revert_subpath** — from `LT → JUMPI → revertLbl → REVERT`.
  Provable via a dedicated lemma for `JUMPI` + a straight-line
  revert block.
- **B3 (revert)** — one-liner.

This gives us Invariants 1–3 directly; Invariant 4 (the cross-txn
conservation) is a theorem schema, proved partially.

### New opcode lemmas needed in `EvmSmith/Lemmas.lean`

- `runOp_callvalue` — pushes `executionEnv.weiValue`, pc+1. Trivial;
  mirror of `runOp_caller`.
- `runOp_sload` — pops key, pushes `EvmYul.State.sload toState key`.
  Plus a characterisation `sload_reads` that says what it returns
  when storage has a given value. Like `runOp_sstore` +
  `sstore_accountMap`, paired.
- `runOp_lt` / `runOp_iszero` — trivial, binary-op / unary-op
  families.
- `runOp_dup` for DUP1..DUP5 and `runOp_swap` for SWAP1..SWAP2 — the
  generic `dup`/`swap` transformers in upstream. These pop the
  correct-depth stack and push the duplicated/swapped value. Already
  defined in `EvmYul.step`; we just need our `rfl`-style wrappers.
- `runOp_jumpi_taken` / `runOp_jumpi_not_taken` — `JUMPI` with a
  non-zero second arg jumps to the pc on top; with zero, falls
  through. Branching is the only semantic novelty — straightforward
  but a new pattern.
- `runOp_jumpdest` — no-op (just increments pc). Trivial.
- `runOp_sub` — binary op, mirror of `runOp_add`.
- `runOp_call` — **not provided**. `CALL` routes through the deep
  `Θ` iterator in upstream; out of scope. Withdraw's proof stops
  before `CALL`.
- `runOp_stop`, `runOp_revert` — already have `runOp_stop` from
  Register. Add `runOp_revert` if needed (likely needed for the
  revert block).

### What the block-level theorems look like

```lean
theorem deposit_block_result
    (s0 : EVM.State)
    (selector : UInt256)
    (hs  : s0.stack = [selector])                -- exactly one element
    (acc : Account .EVM)
    (hacct : s0.accountMap.find? s0.executionEnv.codeOwner = some acc)
    : runSeq depositBlock s0 = .ok <post-state with
        accountMap[C] = some (acc.updateStorage (addressSlot sender)
                                                (oldBal + value))>
```

Similarly `withdraw_block_precall_result` with hypothesis
`hs : s0.stack = []`, plus a case split on `pre.balance < x`
(goes to revert) vs `≥ x` (goes through SSTORE + CALL setup).

### PC parametrization across JUMPI

Register's block proofs accumulated `pc` offsets linearly
(`s0.pc + 2 + 1 + 2 + …`). Weth's blocks **can't** do that —
after JUMPI-taken, the new pc is the destination (an absolute
address), not the old pc + offset. Block proofs take
`hpc : s0.pc = <blockStartPc>` as a hypothesis and produce
post-states where `pc = <blockEndPc>` (also absolute). Offsets
only accumulate *within* a block, not across JUMPI boundaries.

### REVERT chain termination

`runSeq_cons_ok` only handles `.ok`-producing steps. REVERT
produces `.error`. For the revert-block proof, terminate the
chain one step before REVERT and conclude with a direct equation:

```lean
-- Chain through LT; JUMPI-taken; JUMPDEST (revertLbl); PUSH1 0; PUSH1 0;
-- then directly:
have : runOp .REVERT state = .error <revert result>
```

No new fusion lemma needed; just a direct `runOp_revert` claim at
the block tail.

### Spike before chaining: DUP3, DUP5, SWAP2

The withdraw-precall block has a chain of ~17 ops including
`DUP3`, `DUP5`, `SWAP1`, `SWAP2`. Upstream `dup n` / `swap n`
at `EvmYul/Semantics.lean:119-134` use partial list ops
(`getLast!`, `tail!.dropLast`, `head!`). For concrete-shape
inputs these should reduce by `rfl`, but the normal form grows
with depth. **Action**: prove `runOp_dup3`, `runOp_dup5`,
`runOp_swap1`, `runOp_swap2` as standalone lemmas before wiring
them into the withdraw proof. If `rfl` falters on any, use
`unfold; simp`.

## Foundry tests (`foundry/test/Weth.t.sol`)

Mirror Add3 / Register structure. `vm.etch(WETH, runtime)` at setup;
use `vm.prank` + `vm.deal` to fund senders.

### Concrete tests

- `test_Weth_deposit_credits_sender` — deposit from A with value
  `v`, then `storage[A]` = v.
- `test_Weth_deposit_accumulates` — two deposits, balance = sum.
- `test_Weth_withdraw_succeeds` — deposit then withdraw full,
  balance = 0, recipient's ETH back.
- `test_Weth_withdraw_partial` — deposit v, withdraw w < v,
  balance = v - w, recipient got w.
- `test_Weth_withdraw_insufficient_reverts` — no deposit, withdraw
  attempts revert (low-level call returns false).
- `test_Weth_withdraw_zero` — withdraw 0 is a no-op + succeeds
  (a valid trivial case).
- `test_Weth_senders_are_independent` — A deposits, B deposits,
  A's balance unchanged after B's ops.
- `test_Weth_bad_selector_reverts` — calldata with unknown
  selector reverts.
- `test_Weth_empty_calldata_reverts` — no selector, reverts.
- **`test_Weth_reentrancy_does_not_drain`** — deploy an attacker
  contract whose fallback calls `withdraw` again; deposit x from
  the attacker; attempt to withdraw x; on the reentrant CALL the
  attacker's fallback calls `withdraw(x)` a second time. Must
  revert the inner call (balance already decremented to 0).
  **Mandatory, not aspirational.**

### Invariant fuzz test (handler pattern)

Foundry's invariant testing needs an ABI to dispatch against. The
Weth contract is deployed as raw bytecode via `vm.etch`, so the
fuzzer can't discover its selectors directly. Standard workaround:
a **handler contract** with public methods that do the low-level
`.call{value:…}(selector)`. The handler is what
`targetContract(handler)` points at.

```solidity
// foundry/test/WethHandler.sol
contract WethHandler is Test {
    address public immutable weth;
    address[] public actors;        // ghost: senders we've used
    mapping(address => bool) seen;
    uint256 public ghostTotalDeposited;
    uint256 public ghostTotalWithdrawn;

    constructor(address _weth) { weth = _weth; _addActor(address(0xA)); _addActor(address(0xB)); _addActor(address(0xC)); }

    function deposit(uint256 actorSeed, uint256 amtRaw) public {
        address a = actors[actorSeed % actors.length];
        uint256 amt = _bound(amtRaw, 0, 100 ether);
        vm.deal(a, amt);
        vm.prank(a);
        (bool ok,) = weth.call{value: amt}(hex"d0e30db0");
        if (ok) { ghostTotalDeposited += amt; _addActor(a); }
    }

    function withdraw(uint256 actorSeed, uint256 amtRaw) public {
        address a = actors[actorSeed % actors.length];
        uint256 bal = uint256(vm.load(weth, bytes32(uint256(uint160(a)))));
        uint256 amt = _bound(amtRaw, 0, bal);
        vm.prank(a);
        (bool ok,) = weth.call(abi.encodeWithSelector(bytes4(0x2e1a7d4d), amt));
        if (ok) ghostTotalWithdrawn += amt;
    }

    function _addActor(address a) internal { if (!seen[a]) { seen[a] = true; actors.push(a); } }
    function actorCount() external view returns (uint256) { return actors.length; }
}
```

And in the invariant test:
```solidity
function invariant_user_funds_never_lost() public view {
    uint256 sum;
    for (uint256 i = 0; i < handler.actorCount(); i++) {
        sum += uint256(vm.load(WETH, bytes32(uint256(uint160(handler.actors(i))))));
    }
    assertLe(sum, WETH.balance);    // weakened to ≤
}

function invariant_ghost_accounting_consistent() public view {
    // Weakened (≥, not =) because WETH may receive force-fed ETH
    // via SELFDESTRUCT or coinbase rewards outside our bytecode.
    assertGe(WETH.balance, handler.ghostTotalDeposited() - handler.ghostTotalWithdrawn());
}
```

Setup:
```solidity
function setUp() public {
    vm.etch(WETH, runtime);
    handler = new WethHandler(WETH);
    targetContract(address(handler));
}
```

Run with `forge test --match-test invariant_ --runs 1000 --depth 50`
or similar; tuned during implementation.

### Fuzz tests

- `testFuzz_deposit_invariant(sender, value)` — any non-zero sender
  depositing any value → balance correctly set.
- `testFuzz_withdraw_after_deposit(sender, depositValue, withdrawAmount)`
  — deposit `depositValue`, then `withdraw(withdrawAmount)`:
  if `withdrawAmount ≤ depositValue`, succeed; else revert.
- `testFuzz_multi_sender_conservation(...)` — two-sender scenario,
  balance conservation.

## File layout

```
EvmSmith/Demos/Weth/
├── Program.lean          # selectors, block definitions, bytecode
├── Proofs.lean           # per-block theorems + Invariant 4 schema
├── DumpBytecode.lean
└── foundry/
    ├── foundry.toml
    ├── lib/forge-std     # submodule
    ├── src/.gitkeep
    └── test/
        ├── Weth.bytecode.hex
        └── Weth.t.sol    # concrete + invariant + fuzz
```

## Work order

1. **Selectors sanity-check** — compute `keccak256("deposit()")[:4]`
   and `keccak256("withdraw(uint256)")[:4]` via a scratch Lean or
   shell command; confirm `0xd0e30db0` and `0x2e1a7d4d`.

2. **Bytecode assembly** — write `Program.lean` with the three
   basic blocks (`dispatch`, `depositBlock`, `withdrawBlock`) and
   the raw `bytecode` `ByteArray`. Pin exact PCs by hand and encode
   the `PUSH2 <label>` operands. Double-check by decoding via
   `EVM.decode` in a `#eval` (defensive check).

3. **Foundry scaffolding** — `forge init` the `foundry/`
   subdirectory, register the submodule, write the hex dumper exe,
   write `Weth.t.sol` with concrete tests. Run `forge test` to
   confirm the bytecode is behaviourally correct before tackling
   any proofs. **This is the first-pass signal** — if the contract
   doesn't work in Foundry, no amount of Lean effort matters.

4. **Invariant test** — add the Foundry invariant test. This is the
   main safety demonstration. Ensure the fuzzer runs the invariant
   test deeply (>= 1000 runs, depth >= 50).

5. **Lean step lemmas** — extend `EvmSmith/Lemmas.lean` with the
   new opcode lemmas (`runOp_callvalue`, `runOp_sload`, `runOp_lt`,
   `runOp_iszero`, `runOp_dup{1..5}`, `runOp_swap{1..2}`,
   `runOp_jumpi_{taken,not_taken}`, `runOp_jumpdest`, `runOp_sub`,
   `runOp_revert`). Build check.

6. **Block-level proofs** — `Proofs.lean`:
   - `deposit_block_result` — structural post-state of the
     straight-line deposit block.
   - `deposit_updates_sender_balance` — storage update claim.
   - `withdraw_block_precall_result` — structural post-state
     through the `SSTORE` (before `CALL`).
   - `withdraw_block_sufficient_balance` — case analysis on
     `balance ≥ x`.
   - `withdraw_block_insufficient_reverts` — case analysis on
     `balance < x`.

7. (removed — Invariant 4 lives only in Foundry, not Lean)

8. **Size guards** + `#guard`s for block lengths and selector
   positions.

9. **Update README + AGENTS.md**.

10. **Commit locally; do not push**.

## Risks

- **JUMPI lemma complexity**. `JUMPI` semantics in upstream pops two
  operands and branches. Our lemma form needs to case-split on the
  second operand. Should be provable by `rfl` for concrete
  condition values; provable with slightly more work for symbolic
  ones.

- **DUPn / SWAPn rigour**. Upstream uses `dup n` / `swap n`
  transformers parameterised by depth. Our wrappers for DUP3, DUP5,
  SWAP2 should mirror Register's `runOp_caller` pattern; `rfl`
  likely closes each. Potential pitfall: the concrete-shape
  rewriting might require deeper stack patterns (4-5 cons cells).

- **Selector correctness**. If I get a selector byte wrong the
  Foundry tests will fail on bad-selector-reverts. Easy to diagnose;
  not a blocker.

- **`PUSH2 <label>` operand computation**. Need absolute PC of
  `depositLbl`, `withdrawLbl`, `revertLbl`. Compute by hand, verify
  by assembly round-trip.

- **Bytecode size overrun PUSH2 operand limits**. `PUSH2` operand
  is two bytes = up to 65535. Our total size is ~100 bytes, well
  within range.

- **CALL gas forwarding edge cases**. Using `GAS` to forward all
  remaining gas is simple but in real deployments one often uses
  `gas - 2300` (the "stipend" pattern). For MVP we use all gas;
  document this as a simplification in the README.

- **Reentrancy guard not needed because of ordering**. The
  checks-effects-interactions ordering makes a separate guard
  unnecessary. Worth explicitly testing with a Foundry test that
  deploys a malicious receiver attempting reentrancy.

## Out of scope

- **Events** (`Deposit`, `Withdrawal`) — standard WETH emits these.
  Our minimal version doesn't; mention in the file docstring.
- **View functions** (`balanceOf(address)`) — can be added later;
  not needed for the core mechanic.
- **Approvals / transfers** — full ERC-20 surface is out of scope.
- **CALL semantics in Lean proofs** — see above; Foundry tests
  cover the behaviour.
- **Reentrancy invariant in Lean** — requires Θ modeling.

## Gas-unaware Lean disclaimer

All `runSeq`-based proofs in this repo ignore gas. The step
lemmas unfold `EvmYul.step` (the pure semantics) rather than
`EVM.step` (which deducts gas and tracks `execLength`). Gas
behaviour is covered by Foundry, which runs through the real
gas-accounting code path.

## Acceptance

Done when:
- `lake build` clean, no `sorry` / `admit` in the files we own.
- `forge test` in `Weth/foundry/` passes all concrete, fuzz, and
  invariant tests (including reentrancy test and
  `invariant_user_funds_never_lost`).
- Invariants 1–3 and 5 are stated and proved in Lean
  `Proofs.lean`. Invariant 4 (conservation) lives only in the
  Foundry invariant test; the plan documents why.
- Spike lemmas `runOp_dup{3,5}`, `runOp_swap{1,2}` close by `rfl`
  (or documented fallback).
- The AGENTS.md / README.md updates land.
- Commit is local; **no push** pending user's explicit go-ahead.
