// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {IERC20Like} from "./IERC20Like.sol";
import {BytecodePatcher} from "./BytecodePatcher.sol";

/// @notice Per-operation gas comparison between the Vyper / Snekmate
///         ERC-20 with and without the balance-slot peephole. The
///         optimization is bytecode-level: vm.etch of the patched
///         runtime onto an already-deployed (constructor-initialised)
///         instance, length-preserving so jumpdests stay valid.
contract ERC20VyperGasCompareTest is Test {
    IERC20Like orig;
    IERC20Like opt;

    function setUp() public {
        orig = IERC20Like(_deployOrig());
        opt  = IERC20Like(_deployOptimized());
    }

    function _deployOrig() internal returns (address) {
        bytes memory creation = vm.getCode("mock.vy:mock");
        address a;
        assembly {
            a := create(0, add(creation, 0x20), mload(creation))
        }
        require(a != address(0), "deploy failed");
        return a;
    }

    function _deployOptimized() internal returns (address) {
        bytes memory creation = vm.getCode("mock.vy:mock");
        address a;
        assembly {
            a := create(0, add(creation, 0x20), mload(creation))
        }
        require(a != address(0), "deploy failed");
        bytes memory code = a.code;
        BytecodePatcher.patch(code);
        vm.etch(a, code);
        return a;
    }

    function _measureCall(address target, bytes memory data) internal returns (uint256 gasUsed) {
        uint256 g0 = gasleft();
        (bool ok, ) = target.call(data);
        require(ok, "call failed");
        return g0 - gasleft();
    }

    function test_gas_mint_fresh() public {
        bytes memory data = abi.encodeCall(IERC20Like.mint, (address(0xAA01), 1 ether));
        uint256 gO = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeCall(IERC20Like.mint, (address(0xAA02), 1 ether));
        uint256 gP = _measureCall(address(opt),  data2);
        emit log_named_uint("mint(fresh)   keccak (gas)", gO);
        emit log_named_uint("mint(fresh)   patched(gas)", gP);
        emit log_named_int ("delta                     ", int256(gP) - int256(gO));
    }

    function test_gas_mint_warm() public {
        orig.mint(address(0xAA01), 1 ether);
        opt.mint(address(0xAA02), 1 ether);
        bytes memory data = abi.encodeCall(IERC20Like.mint, (address(0xAA01), 1 ether));
        uint256 gO = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeCall(IERC20Like.mint, (address(0xAA02), 1 ether));
        uint256 gP = _measureCall(address(opt),  data2);
        emit log_named_uint("mint(warm)    keccak (gas)", gO);
        emit log_named_uint("mint(warm)    patched(gas)", gP);
        emit log_named_int ("delta                     ", int256(gP) - int256(gO));
    }

    function test_gas_burn() public {
        orig.mint(address(this), 1 ether);
        opt.mint(address(this),  1 ether);
        bytes memory data = abi.encodeCall(IERC20Like.burn, (0.4 ether));
        uint256 gO = _measureCall(address(orig), data);
        uint256 gP = _measureCall(address(opt),  data);
        emit log_named_uint("burn          keccak (gas)", gO);
        emit log_named_uint("burn          patched(gas)", gP);
        emit log_named_int ("delta                     ", int256(gP) - int256(gO));
    }

    function test_gas_transfer_fresh() public {
        orig.mint(address(this), 10 ether);
        opt.mint(address(this),  10 ether);
        bytes memory data = abi.encodeCall(IERC20Like.transfer, (address(0xBB01), 1 ether));
        uint256 gO = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeCall(IERC20Like.transfer, (address(0xBB02), 1 ether));
        uint256 gP = _measureCall(address(opt),  data2);
        emit log_named_uint("transfer      keccak (gas)", gO);
        emit log_named_uint("transfer      patched(gas)", gP);
        emit log_named_int ("delta                     ", int256(gP) - int256(gO));
    }

    function test_gas_transfer_warm() public {
        orig.mint(address(this),    10 ether);
        opt.mint(address(this),     10 ether);
        orig.mint(address(0xBB01),  1 ether);
        opt.mint(address(0xBB02),   1 ether);
        bytes memory data = abi.encodeCall(IERC20Like.transfer, (address(0xBB01), 1 ether));
        uint256 gO = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeCall(IERC20Like.transfer, (address(0xBB02), 1 ether));
        uint256 gP = _measureCall(address(opt),  data2);
        emit log_named_uint("transfer(warm)keccak (gas)", gO);
        emit log_named_uint("transfer(warm)patched(gas)", gP);
        emit log_named_int ("delta                     ", int256(gP) - int256(gO));
    }

    function test_gas_transferFrom() public {
        address from = address(0xABCD);
        orig.mint(from, 10 ether);
        opt.mint(from,  10 ether);
        vm.prank(from);
        orig.approve(address(this), 10 ether);
        vm.prank(from);
        opt.approve(address(this),  10 ether);
        bytes memory data = abi.encodeCall(IERC20Like.transferFrom, (from, address(0xBB01), 1 ether));
        uint256 gO = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeCall(IERC20Like.transferFrom, (from, address(0xBB02), 1 ether));
        uint256 gP = _measureCall(address(opt),  data2);
        emit log_named_uint("transferFrom  keccak (gas)", gO);
        emit log_named_uint("transferFrom  patched(gas)", gP);
        emit log_named_int ("delta                     ", int256(gP) - int256(gO));
    }

    function test_gas_balanceOf_warm() public {
        orig.mint(address(0xAA01), 1 ether);
        opt.mint(address(0xAA02),  1 ether);
        orig.balanceOf(address(0xAA01)); // prime warm slot
        opt.balanceOf(address(0xAA02));
        bytes memory data = abi.encodeCall(IERC20Like.balanceOf, (address(0xAA01)));
        uint256 gO = _measureCall(address(orig), data);
        bytes memory data2 = abi.encodeCall(IERC20Like.balanceOf, (address(0xAA02)));
        uint256 gP = _measureCall(address(opt),  data2);
        emit log_named_uint("balanceOf(W)  keccak (gas)", gO);
        emit log_named_uint("balanceOf(W)  patched(gas)", gP);
        emit log_named_int ("delta                     ", int256(gP) - int256(gO));
    }

    function test_runtime_size() public {
        emit log_named_uint("runtime size keccak (bytes)", address(orig).code.length);
        emit log_named_uint("runtime size patched(bytes)", address(opt).code.length);
        require(address(orig).code.length == address(opt).code.length, "length-preserved");
    }
}
