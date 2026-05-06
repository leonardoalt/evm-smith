// SPDX-License-Identifier: MIT
pragma solidity 0.8.20;

import "forge-std/Test.sol";
import {WethSolidity} from "../src/WethSolidity.sol";

/// @title Per-tx gas comparison: original vs PUSH0-opt vs CALLER-trick-opt vs Solidity
/// @notice Loads four implementations of the same WETH semantics:
///
///           * `WETH_ORIG` (86 bytes): the hand-rolled bytecode the Lean
///             solvency proof targets.
///           * `WETH_OPT`  (77 bytes): the PUSH0-optimized bytecode,
///             observably equivalent per `OptimizedProgram.lean`'s
///             block-level proofs.
///           * `WETH_OPT2` (74 bytes): layered on top of `WETH_OPT`,
///             swaps `DUP1+SWAP1` patterns for double-`CALLER` (BASE
///             vs VERYLOW) in the deposit and withdraw bodies, and
///             drops the dead `POP` before `STOP` on withdraw success.
///             Equivalence proved in `OptimizedProgramV2.lean`.
///           * `WETH_SOL`  (deployed Solidity contract): an idiomatic
///             Solidity implementation compiled by `solc 0.8.20`. Uses
///             a `mapping(address => uint256)` rather than
///             address-as-slot, so storage layout differs.
///
///         The gas-comparison rows below run identical deposit /
///         withdraw / revert flows on all four and emit the deltas.
///         Bytecode-orig vs bytecode-opt: PUSH0-vs-PUSH1-zero (1 gas
///         per swap site reached). Opt vs OptV2: BASE-vs-VERYLOW on
///         the CALLER reload, plus the saved `POP`. Bytecode-orig vs
///         Solidity: the Solidity bill is dominated by compiler-
///         emitted dispatcher overhead, calldata length checks,
///         function-selector matching, the keccak-derived mapping-
///         slot lookup, etc.
contract WethGasCompareTest is Test {
    address constant WETH_ORIG = address(uint160(0x5c00));
    address constant WETH_OPT  = address(uint160(0x5c01));
    address constant WETH_OPT2 = address(uint160(0x5c02));

    WethSolidity wethSol;
    address WETH_SOL;

    function setUp() public {
        bytes memory orig = vm.parseBytes(_trim(vm.readFile("test/Weth.bytecode.hex")));
        bytes memory opt  = vm.parseBytes(_trim(vm.readFile("test/Weth.optimized.bytecode.hex")));
        bytes memory opt2 = vm.parseBytes(_trim(vm.readFile("test/Weth.optimizedV2.bytecode.hex")));
        vm.etch(WETH_ORIG, orig);
        vm.etch(WETH_OPT,  opt);
        vm.etch(WETH_OPT2, opt2);
        wethSol = new WethSolidity();
        WETH_SOL = address(wethSol);

        // Sanity: deployed sizes match the Lean-side claim.
        assertEq(WETH_ORIG.code.length, 86, "orig runtime is 86 bytes");
        assertEq(WETH_OPT.code.length,  77, "opt runtime is 77 bytes");
        assertEq(WETH_OPT2.code.length, 74, "opt-v2 runtime is 74 bytes");
        emit log_named_uint("solidity runtime size (bytes)", WETH_SOL.code.length);
    }

    /// Solidity stores `balances[addr]` at `keccak256(abi.encode(addr, 0))`.
    function _solSlot(address a) internal pure returns (bytes32) {
        return keccak256(abi.encode(a, uint256(0)));
    }

    /// The hand-rolled bytecodes store `balances[addr]` directly at slot `addr`.
    function _rawSlot(address a) internal pure returns (bytes32) {
        return bytes32(uint256(uint160(a)));
    }

    // ------------- helpers -------------

    function _trim(string memory s) internal pure returns (string memory) {
        bytes memory b = bytes(s);
        uint256 n = b.length;
        while (n > 0 &&
               (b[n - 1] == 0x0a || b[n - 1] == 0x0d ||
                b[n - 1] == 0x09 || b[n - 1] == 0x20)) {
            n--;
        }
        bytes memory r = new bytes(n);
        for (uint256 i = 0; i < n; i++) r[i] = b[i];
        return string(r);
    }

    /// Measure the gas a single `WETH.call{value:v}(data)` consumes,
    /// as reported by the EVM (gasleft() delta around the call).
    /// Uses an isolated sender so prior-state warmth doesn't leak
    /// between original / optimized measurements.
    function _measure(address WETH, address sender, uint256 v, bytes memory data)
        internal returns (uint256 gasUsed, bool ok)
    {
        vm.deal(sender, sender.balance + v);
        vm.prank(sender);
        uint256 g0 = gasleft();
        (ok,) = WETH.call{value: v}(data);
        uint256 g1 = gasleft();
        gasUsed = g0 - g1;
    }

    // ------------- per-path comparisons -------------

    /// Deposit on all four.
    function test_gas_deposit() public {
        bytes memory data = hex"d0e30db0";
        (uint256 gOrig,) = _measure(WETH_ORIG, address(0xAA01), 1 ether, data);
        (uint256 gOpt,)  = _measure(WETH_OPT,  address(0xAA02), 1 ether, data);
        (uint256 gOpt2,) = _measure(WETH_OPT2, address(0xAA04), 1 ether, data);
        (uint256 gSol,)  = _measure(WETH_SOL,  address(0xAA03), 1 ether, data);
        emit log_named_uint("deposit gas: original   ",  gOrig);
        emit log_named_uint("deposit gas: optimized  ",  gOpt);
        emit log_named_uint("deposit gas: opt-v2     ",  gOpt2);
        emit log_named_uint("deposit gas: solidity   ",  gSol);
        emit log_named_int ("deposit delta opt-orig  ",  int256(gOpt)  - int256(gOrig));
        emit log_named_int ("deposit delta opt2-orig ",  int256(gOpt2) - int256(gOrig));
        emit log_named_int ("deposit delta opt2-opt  ",  int256(gOpt2) - int256(gOpt));
        emit log_named_int ("deposit delta sol-orig  ",  int256(gSol)  - int256(gOrig));
        assertLe(gOpt,  gOrig, "optimized deposit must not cost more gas");
        assertLe(gOpt2, gOpt,  "opt-v2 deposit must not cost more than opt");
    }

    /// Withdraw success on all four.
    function test_gas_withdraw_success() public {
        // Pre-fund so the withdraw can pay out.
        _measure(WETH_ORIG, address(0xBB01), 1 ether, hex"d0e30db0");
        _measure(WETH_OPT,  address(0xBB02), 1 ether, hex"d0e30db0");
        _measure(WETH_OPT2, address(0xBB04), 1 ether, hex"d0e30db0");
        _measure(WETH_SOL,  address(0xBB03), 1 ether, hex"d0e30db0");

        bytes memory data = abi.encodeWithSelector(bytes4(0x2e1a7d4d), uint256(1 ether));
        (uint256 gOrig, bool okO) = _measure(WETH_ORIG, address(0xBB01), 0, data);
        (uint256 gOpt,  bool okP) = _measure(WETH_OPT,  address(0xBB02), 0, data);
        (uint256 gOpt2, bool okQ) = _measure(WETH_OPT2, address(0xBB04), 0, data);
        (uint256 gSol,  bool okS) = _measure(WETH_SOL,  address(0xBB03), 0, data);
        assertTrue(okO); assertTrue(okP); assertTrue(okQ); assertTrue(okS);
        emit log_named_uint("withdraw-success gas: original   ", gOrig);
        emit log_named_uint("withdraw-success gas: optimized  ", gOpt);
        emit log_named_uint("withdraw-success gas: opt-v2     ", gOpt2);
        emit log_named_uint("withdraw-success gas: solidity   ", gSol);
        emit log_named_int ("withdraw-success delta opt-orig  ", int256(gOpt)  - int256(gOrig));
        emit log_named_int ("withdraw-success delta opt2-orig ", int256(gOpt2) - int256(gOrig));
        emit log_named_int ("withdraw-success delta opt2-opt  ", int256(gOpt2) - int256(gOpt));
        emit log_named_int ("withdraw-success delta sol-orig  ", int256(gSol)  - int256(gOrig));
        assertLe(gOpt,  gOrig, "optimized withdraw must not cost more gas");
        assertLe(gOpt2, gOpt,  "opt-v2 withdraw must not cost more than opt");
    }

    /// Withdraw with insufficient balance on all four.
    function test_gas_withdraw_insufficient() public {
        bytes memory data = abi.encodeWithSelector(bytes4(0x2e1a7d4d), uint256(1));
        (uint256 gOrig, bool okO) = _measure(WETH_ORIG, address(0xCC01), 0, data);
        (uint256 gOpt,  bool okP) = _measure(WETH_OPT,  address(0xCC02), 0, data);
        (uint256 gOpt2, bool okQ) = _measure(WETH_OPT2, address(0xCC04), 0, data);
        (uint256 gSol,  bool okS) = _measure(WETH_SOL,  address(0xCC03), 0, data);
        assertFalse(okO); assertFalse(okP); assertFalse(okQ); assertFalse(okS);
        emit log_named_uint("withdraw-revert gas: original   ", gOrig);
        emit log_named_uint("withdraw-revert gas: optimized  ", gOpt);
        emit log_named_uint("withdraw-revert gas: opt-v2     ", gOpt2);
        emit log_named_uint("withdraw-revert gas: solidity   ", gSol);
        emit log_named_int ("withdraw-revert delta opt-orig  ", int256(gOpt)  - int256(gOrig));
        emit log_named_int ("withdraw-revert delta opt2-orig ", int256(gOpt2) - int256(gOrig));
        emit log_named_int ("withdraw-revert delta opt2-opt  ", int256(gOpt2) - int256(gOpt));
        emit log_named_int ("withdraw-revert delta sol-orig  ", int256(gSol)  - int256(gOrig));
        assertLe(gOpt,  gOrig, "optimized withdraw-revert must not cost more gas");
        assertLe(gOpt2, gOpt,  "opt-v2 withdraw-revert must not cost more than opt");
    }

    /// Unknown selector on all four. The bytecode versions revert via
    /// their explicit no-selector-match path; the Solidity contract
    /// reverts via the compiler-generated dispatcher fallback.
    function test_gas_bad_selector() public {
        bytes memory data = hex"deadbeef";
        (uint256 gOrig, bool okO) = _measure(WETH_ORIG, address(0xDD01), 0, data);
        (uint256 gOpt,  bool okP) = _measure(WETH_OPT,  address(0xDD02), 0, data);
        (uint256 gOpt2, bool okQ) = _measure(WETH_OPT2, address(0xDD04), 0, data);
        (uint256 gSol,  bool okS) = _measure(WETH_SOL,  address(0xDD03), 0, data);
        assertFalse(okO); assertFalse(okP); assertFalse(okQ); assertFalse(okS);
        emit log_named_uint("bad-selector gas: original   ", gOrig);
        emit log_named_uint("bad-selector gas: optimized  ", gOpt);
        emit log_named_uint("bad-selector gas: opt-v2     ", gOpt2);
        emit log_named_uint("bad-selector gas: solidity   ", gSol);
        emit log_named_int ("bad-selector delta opt-orig  ", int256(gOpt)  - int256(gOrig));
        emit log_named_int ("bad-selector delta opt2-orig ", int256(gOpt2) - int256(gOrig));
        emit log_named_int ("bad-selector delta opt2-opt  ", int256(gOpt2) - int256(gOpt));
        emit log_named_int ("bad-selector delta sol-orig  ", int256(gSol)  - int256(gOrig));
        assertLe(gOpt,  gOrig, "optimized bad-selector must not cost more gas");
        assertLe(gOpt2, gOpt,  "opt-v2 bad-selector must not cost more than opt");
    }

    /// Behavioral parity: all four end up at the same accounting
    /// state after a deposit + partial withdraw round, modulo storage
    /// layout (Solidity uses keccak-derived slot, bytecodes use the
    /// raw address as slot).
    function test_behavior_parity_deposit_withdraw() public {
        address sender = address(0xEE01);
        // Deposit on all four.
        (, bool dO) = _measure(WETH_ORIG, sender, 3 ether, hex"d0e30db0");
        (, bool dP) = _measure(WETH_OPT,  sender, 3 ether, hex"d0e30db0");
        (, bool dQ) = _measure(WETH_OPT2, sender, 3 ether, hex"d0e30db0");
        (, bool dS) = _measure(WETH_SOL,  sender, 3 ether, hex"d0e30db0");
        assertTrue(dO); assertTrue(dP); assertTrue(dQ); assertTrue(dS);
        assertEq(vm.load(WETH_ORIG, _rawSlot(sender)), bytes32(uint256(3 ether)));
        assertEq(vm.load(WETH_OPT,  _rawSlot(sender)), bytes32(uint256(3 ether)));
        assertEq(vm.load(WETH_OPT2, _rawSlot(sender)), bytes32(uint256(3 ether)));
        assertEq(vm.load(WETH_SOL,  _solSlot(sender)), bytes32(uint256(3 ether)));

        // Partial withdraw on all four.
        bytes memory wdata = abi.encodeWithSelector(bytes4(0x2e1a7d4d), uint256(1 ether));
        (, bool wO) = _measure(WETH_ORIG, sender, 0, wdata);
        (, bool wP) = _measure(WETH_OPT,  sender, 0, wdata);
        (, bool wQ) = _measure(WETH_OPT2, sender, 0, wdata);
        (, bool wS) = _measure(WETH_SOL,  sender, 0, wdata);
        assertTrue(wO); assertTrue(wP); assertTrue(wQ); assertTrue(wS);
        assertEq(vm.load(WETH_ORIG, _rawSlot(sender)), bytes32(uint256(2 ether)));
        assertEq(vm.load(WETH_OPT,  _rawSlot(sender)), bytes32(uint256(2 ether)));
        assertEq(vm.load(WETH_OPT2, _rawSlot(sender)), bytes32(uint256(2 ether)));
        assertEq(vm.load(WETH_SOL,  _solSlot(sender)), bytes32(uint256(2 ether)));
    }
}
