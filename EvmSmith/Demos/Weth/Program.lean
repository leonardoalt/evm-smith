import EvmSmith.Framework

/-!
# The `Weth` program — wrapped-ETH token in raw EVM bytecode

A minimal WETH-style contract. Two entry points distinguished by the
standard 4-byte function selector prefix in `calldata[0:4]`:

| Solidity signature  | Selector     | Behaviour                                      |
|---------------------|--------------|------------------------------------------------|
| `deposit()` payable | `0xd0e30db0` | `balance[msg.sender] += msg.value`             |
| `withdraw(uint256)` | `0x2e1a7d4d` | if `balance ≥ x`: decrement + CALL sender, x; else revert |

Storage layout: `storage[msg.sender]` (address used directly as a
`UInt256` slot key) holds the user's token balance in wei.

Safety design:
- `withdraw` updates state **before** the external CALL
  (checks-effects-interactions). A reentrant call sees the
  already-decremented balance and hits the `LT` gate on any further
  withdrawal attempt.
- Gas forwarding via `GAS` passes all remaining gas; simple, not
  EIP-150 stipend-based.
- No overflow check in `deposit` — `balance + value` wrapping
  requires the sum of deposits to exceed `2^256 - 1` wei, infeasible
  given total ETH supply. The Foundry tests document this boundary.

Assembly:

```
pc  bytes           mnemonic                  comment
-----------------------------------------------------------------
; Dispatch
0   60 00           PUSH1 0x00
2   35              CALLDATALOAD              calldata[0:32]
3   60 e0           PUSH1 0xe0
5   1c              SHR                       selector in low 4 bytes
6   80              DUP1
7   63 d0 e3 0d b0  PUSH4 0xd0e30db0          deposit selector
12  14              EQ
13  61 00 20        PUSH2 0x0020              depositLbl = 32
16  57              JUMPI
17  63 2e 1a 7d 4d  PUSH4 0x2e1a7d4d          withdraw selector
22  14              EQ
23  61 00 2a        PUSH2 0x002a              withdrawLbl = 42
26  57              JUMPI
27  60 00
29  60 00
31  fd              REVERT                    no-selector-match revert

; Deposit (stack at entry: [selector])
32  5b              JUMPDEST
33  50              POP                       pop stale selector
34  33              CALLER
35  80              DUP1
36  54              SLOAD                     [balance, sender]
37  34              CALLVALUE
38  01              ADD                       [newBal, sender]
39  90              SWAP1                     [sender, newBal]
40  55              SSTORE
41  00              STOP

; Withdraw (stack at entry: [] — second EQ consumed the selector)
42  5b              JUMPDEST
43  60 04           PUSH1 0x04
45  35              CALLDATALOAD              [x]
46  33              CALLER
47  80              DUP1
48  54              SLOAD                     [balance, sender, x]
49  82              DUP3                      [x, balance, sender, x]
50  81              DUP2                      [balance, x, balance, sender, x]
51  10              LT                        [balance < x ?, balance, sender, x]
52  61 00 50        PUSH2 0x0050              revertLbl = 80
55  57              JUMPI                     branch to revert if underfunded
56  82              DUP3                      [x, balance, sender, x]
57  90              SWAP1                     [balance, x, sender, x]
58  03              SUB                       [newBal, sender, x]
59  90              SWAP1                     [sender, newBal, x]
60  55              SSTORE                    state update before external CALL
61  60 00                                     retSize
63  60 00                                     retOff
65  60 00                                     argsSize
67  60 00                                     argsOff
69  84              DUP5                      value = x
70  33              CALLER                    to
71  5a              GAS                       gas
72  f1              CALL
73  15              ISZERO                    check success
74  61 00 50        PUSH2 0x0050
77  57              JUMPI                     revert if CALL failed
78  50              POP                       pop x
79  00              STOP

; Revert (shared by insufficient-balance and CALL-failed branches)
80  5b              JUMPDEST
81  60 00
83  60 00
85  fd              REVERT
```

Total: 86 bytes.
-/

namespace EvmSmith.Weth
open EvmYul EvmYul.EVM

/-! ## Selectors -/

def depositSelector  : UInt256 := UInt256.ofNat 0xd0e30db0
def withdrawSelector : UInt256 := UInt256.ofNat 0x2e1a7d4d

/-! ## Control-flow destinations (absolute PCs) -/

def depositLbl  : UInt256 := UInt256.ofNat 32
def withdrawLbl : UInt256 := UInt256.ofNat 42
def revertLbl   : UInt256 := UInt256.ofNat 80

/-! ## Basic blocks as `Program` lists

These are used for block-level Lean proofs (via `runSeq`), not for
execution on-chain. The `bytecode` below is the on-chain form. -/

/-- The **deposit block**: entry at `depositLbl` with stack `[selector]`.
    Increments `storage[msg.sender]` by `msg.value`, then halts. -/
def depositBlock : EvmSmith.Program :=
  [ (.JUMPDEST,     none)
  , (.POP,          none)
  , (.CALLER,       none)
  , (.DUP1,         none)
  , (.SLOAD,        none)
  , (.CALLVALUE,    none)
  , (.ADD,          none)
  , (.SWAP1,        none)
  , (.SSTORE,       none)
  , (.STOP,         none)
  ]

/-- The **withdraw block, up to but not including CALL** (i.e. the
    state-update prefix that we can reason about without Θ-level
    CALL semantics). Entry stack: `[]`, entry pc = `withdrawLbl`. -/
def withdrawPreCallBlock : EvmSmith.Program :=
  [ (.JUMPDEST,     none)
  , (.Push .PUSH1,  some (UInt256.ofNat 4, 1))
  , (.CALLDATALOAD, none)
  , (.CALLER,       none)
  , (.DUP1,         none)
  , (.SLOAD,        none)
  , (.DUP3,         none)
  , (.DUP2,         none)
  , (.LT,           none)
  , (.Push .PUSH2,  some (revertLbl, 2))
  , (.JUMPI,        none)
  , (.DUP3,         none)
  , (.SWAP1,        none)
  , (.SUB,          none)
  , (.SWAP1,        none)
  , (.SSTORE,       none)
  ]

/-! ## Raw bytecode (on-chain form) -/

def bytecode : ByteArray := ⟨#[
  -- Dispatch
  0x60, 0x00,                      -- 0:    PUSH1 0
  0x35,                            -- 2:    CALLDATALOAD
  0x60, 0xe0,                      -- 3:    PUSH1 0xe0
  0x1c,                            -- 5:    SHR
  0x80,                            -- 6:    DUP1
  0x63, 0xd0, 0xe3, 0x0d, 0xb0,    -- 7:    PUSH4 depositSelector
  0x14,                            -- 12:   EQ
  0x61, 0x00, 0x20,                -- 13:   PUSH2 depositLbl
  0x57,                            -- 16:   JUMPI
  0x63, 0x2e, 0x1a, 0x7d, 0x4d,    -- 17:   PUSH4 withdrawSelector
  0x14,                            -- 22:   EQ
  0x61, 0x00, 0x2a,                -- 23:   PUSH2 withdrawLbl
  0x57,                            -- 26:   JUMPI
  0x60, 0x00, 0x60, 0x00, 0xfd,    -- 27:   PUSH1 0; PUSH1 0; REVERT
  -- Deposit block (pc 32..41)
  0x5b,                            -- 32:   JUMPDEST
  0x50,                            -- 33:   POP
  0x33, 0x80, 0x54,                -- 34:   CALLER; DUP1; SLOAD
  0x34, 0x01,                      -- 37:   CALLVALUE; ADD
  0x90, 0x55,                      -- 39:   SWAP1; SSTORE
  0x00,                            -- 41:   STOP
  -- Withdraw block (pc 42..79)
  0x5b,                            -- 42:   JUMPDEST
  0x60, 0x04, 0x35,                -- 43:   PUSH1 4; CALLDATALOAD
  0x33, 0x80, 0x54,                -- 46:   CALLER; DUP1; SLOAD
  0x82, 0x81, 0x10,                -- 49:   DUP3; DUP2; LT
  0x61, 0x00, 0x50, 0x57,          -- 52:   PUSH2 revertLbl; JUMPI
  0x82, 0x90, 0x03, 0x90, 0x55,    -- 56:   DUP3; SWAP1; SUB; SWAP1; SSTORE
  0x60, 0x00, 0x60, 0x00,          -- 61:   PUSH1 0; PUSH1 0       (retSize, retOff)
  0x60, 0x00, 0x60, 0x00,          -- 65:   PUSH1 0; PUSH1 0       (argsSize, argsOff)
  0x84, 0x33, 0x5a,                -- 69:   DUP5; CALLER; GAS      (value, to, gas)
  0xf1,                            -- 72:   CALL
  0x15,                            -- 73:   ISZERO
  0x61, 0x00, 0x50, 0x57,          -- 74:   PUSH2 revertLbl; JUMPI
  0x50, 0x00,                      -- 78:   POP; STOP
  -- Revert block (pc 80..85)
  0x5b,                            -- 80:   JUMPDEST
  0x60, 0x00, 0x60, 0x00, 0xfd     -- 81:   PUSH1 0; PUSH1 0; REVERT
]⟩

end EvmSmith.Weth
