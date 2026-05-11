// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {ERC20} from "solady/tokens/ERC20.sol";
import {MockERC20Original} from "../src/MockERC20Original.sol";
import {MockERC20Optimized} from "../src/MockERC20Optimized.sol";

/// @notice Per-operation gas comparison between the keccak-balance and
///         address-as-slot ERC-20 backends.
///
///         Each row mints / transfers / burns on freshly-allocated
///         senders so cold-slot warming is consistent across runs.
///         The output is printed via `log_named_uint` / `log_named_int`
///         so the deltas are obvious in `forge test -vvv` output.
contract ERC20GasCompareTest is Test {
    MockERC20Original orig;
    MockERC20Optimized opt;

    address constant _PERMIT2 = 0x000000000022D473030F116dDEE9F6B43aC78BA3;

    function setUp() public {
        orig = new MockERC20Original("Token", "TKN", 18);
        opt  = new MockERC20Optimized("Token", "TKN", 18);
    }

    function _measureCall(address target, bytes memory data) internal returns (uint256 gasUsed, bool ok) {
        uint256 g0 = gasleft();
        (ok,) = target.call(data);
        uint256 g1 = gasleft();
        gasUsed = g0 - g1;
    }

    /// @dev Fresh-slot mint (zero → non-zero, SSTORE cold-to-set).
    function test_gas_mint_fresh() public {
        bytes memory data = abi.encodeWithSignature("mint(address,uint256)", address(0xAA01), 1 ether);
        (uint256 gO,) = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeWithSignature("mint(address,uint256)", address(0xAA02), 1 ether);
        (uint256 gP,) = _measureCall(address(opt),  data2);
        emit log_named_uint("mint(fresh) keccak-layout (gas)", gO);
        emit log_named_uint("mint(fresh) addr-as-slot  (gas)", gP);
        emit log_named_int ("delta                          ", int256(gP) - int256(gO));
        assertLe(gP, gO, "optimized must not cost more for mint");
    }

    /// @dev Hot-slot mint (additional credit, slot already warm).
    function test_gas_mint_warm() public {
        // Warm up: first credit.
        orig.mint(address(0xAA01), 1 ether);
        opt.mint(address(0xAA02),  1 ether);

        bytes memory data = abi.encodeWithSignature("mint(address,uint256)", address(0xAA01), 1 ether);
        (uint256 gO,) = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeWithSignature("mint(address,uint256)", address(0xAA02), 1 ether);
        (uint256 gP,) = _measureCall(address(opt),  data2);
        emit log_named_uint("mint(warm)  keccak-layout (gas)", gO);
        emit log_named_uint("mint(warm)  addr-as-slot  (gas)", gP);
        emit log_named_int ("delta                          ", int256(gP) - int256(gO));
        assertLe(gP, gO, "optimized must not cost more for warm mint");
    }

    function test_gas_burn() public {
        orig.mint(address(0xAA01), 1 ether);
        opt.mint(address(0xAA02),  1 ether);

        bytes memory data = abi.encodeWithSignature("burn(address,uint256)", address(0xAA01), 0.4 ether);
        (uint256 gO,) = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeWithSignature("burn(address,uint256)", address(0xAA02), 0.4 ether);
        (uint256 gP,) = _measureCall(address(opt),  data2);
        emit log_named_uint("burn         keccak-layout (gas)", gO);
        emit log_named_uint("burn         addr-as-slot  (gas)", gP);
        emit log_named_int ("delta                           ", int256(gP) - int256(gO));
        assertLe(gP, gO, "optimized must not cost more for burn");
    }

    function test_gas_transfer_fresh_to() public {
        // Both senders pre-funded; recipients are fresh.
        orig.mint(address(this), 10 ether);
        opt.mint(address(this),  10 ether);

        bytes memory data = abi.encodeWithSignature("transfer(address,uint256)", address(0xBB01), 1 ether);
        (uint256 gO,) = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeWithSignature("transfer(address,uint256)", address(0xBB02), 1 ether);
        (uint256 gP,) = _measureCall(address(opt),  data2);
        emit log_named_uint("transfer(fresh-to) keccak-layout (gas)", gO);
        emit log_named_uint("transfer(fresh-to) addr-as-slot  (gas)", gP);
        emit log_named_int ("delta                                ", int256(gP) - int256(gO));
        assertLe(gP, gO, "optimized must not cost more for transfer(fresh)");
    }

    function test_gas_transfer_warm_to() public {
        // Both recipients pre-funded so the SSTORE on credit hits a non-zero slot.
        orig.mint(address(this),    10 ether);
        opt.mint(address(this),     10 ether);
        orig.mint(address(0xBB01),  1 ether);
        opt.mint(address(0xBB02),   1 ether);

        bytes memory data = abi.encodeWithSignature("transfer(address,uint256)", address(0xBB01), 1 ether);
        (uint256 gO,) = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeWithSignature("transfer(address,uint256)", address(0xBB02), 1 ether);
        (uint256 gP,) = _measureCall(address(opt),  data2);
        emit log_named_uint("transfer(warm-to)  keccak-layout (gas)", gO);
        emit log_named_uint("transfer(warm-to)  addr-as-slot  (gas)", gP);
        emit log_named_int ("delta                                ", int256(gP) - int256(gO));
        assertLe(gP, gO, "optimized must not cost more for transfer(warm)");
    }

    function test_gas_transferFrom() public {
        address from = address(0xABCD);
        orig.mint(from, 10 ether);
        opt.mint(from,  10 ether);
        vm.prank(from);
        orig.approve(address(this), 10 ether);
        vm.prank(from);
        opt.approve(address(this),  10 ether);

        bytes memory data = abi.encodeWithSignature(
            "transferFrom(address,address,uint256)", from, address(0xBB01), 1 ether
        );
        (uint256 gO,) = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeWithSignature(
            "transferFrom(address,address,uint256)", from, address(0xBB02), 1 ether
        );
        (uint256 gP,) = _measureCall(address(opt),  data2);
        emit log_named_uint("transferFrom keccak-layout (gas)", gO);
        emit log_named_uint("transferFrom addr-as-slot  (gas)", gP);
        emit log_named_int ("delta                            ", int256(gP) - int256(gO));
        assertLe(gP, gO, "optimized must not cost more for transferFrom");
    }

    function test_gas_balanceOf_warm() public {
        orig.mint(address(0xAA01), 1 ether);
        opt.mint(address(0xAA02),  1 ether);
        // Prime the slot to be warm for both reads. The first balanceOf
        // call below will pay the cold-load cost; we measure the second.
        orig.balanceOf(address(0xAA01));
        opt.balanceOf(address(0xAA02));

        bytes memory data = abi.encodeWithSignature("balanceOf(address)", address(0xAA01));
        (uint256 gO,) = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeWithSignature("balanceOf(address)", address(0xAA02));
        (uint256 gP,) = _measureCall(address(opt),  data2);
        emit log_named_uint("balanceOf(warm) keccak-layout (gas)", gO);
        emit log_named_uint("balanceOf(warm) addr-as-slot  (gas)", gP);
        emit log_named_int ("delta                             ", int256(gP) - int256(gO));
        assertLe(gP, gO, "optimized must not cost more for balanceOf(warm)");
    }

    function test_runtime_size() public {
        emit log_named_uint("runtime size keccak-layout (bytes)", address(orig).code.length);
        emit log_named_uint("runtime size addr-as-slot  (bytes)", address(opt).code.length);
    }
}
