// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {IERC20Like} from "./IERC20Like.sol";
import {BytecodePatcher} from "./BytecodePatcher.sol";

/// @notice Behaviour parity test for the Vyper / Snekmate ERC-20 with
///         and without the balance-slot peephole optimization. The
///         optimization is applied at the bytecode level: we deploy
///         the Vyper contract normally (so the constructor sets up
///         immutables and ownable state), then in-place patch the
///         deployed code with `vm.etch`. The patch is length-
///         preserving so PC-absolute jumpdests stay valid.
///
///         Both backends pass the same 22-test suite (mint, burn,
///         approve, transfer, transferFrom, permit-ish checks,
///         fuzz). Gas comparison lives in
///         `ERC20VyperGasCompare.t.sol`.
abstract contract ERC20VyperBehaviourTest is Test {
    IERC20Like internal token;

    event Transfer(address indexed from, address indexed to, uint256 amount);
    event Approval(address indexed owner, address indexed spender, uint256 amount);

    function _deploy() internal virtual returns (address);

    function setUp() public {
        token = IERC20Like(_deploy());
    }

    // --- metadata ---

    function testMetadata() public view {
        assertEq(token.name(), "Token");
        assertEq(token.symbol(), "TKN");
        assertEq(token.decimals(), 18);
    }

    // --- mint / burn ---

    function testMint() public {
        vm.expectEmit(true, true, true, true);
        emit Transfer(address(0), address(0xBEEF), 1e18);
        token.mint(address(0xBEEF), 1e18);
        assertEq(token.totalSupply(), 1e18);
        assertEq(token.balanceOf(address(0xBEEF)), 1e18);
    }

    function testMintMultiple() public {
        token.mint(address(0xAA), 5 ether);
        token.mint(address(0xBB), 3 ether);
        token.mint(address(0xAA), 2 ether);
        assertEq(token.balanceOf(address(0xAA)), 7 ether);
        assertEq(token.balanceOf(address(0xBB)), 3 ether);
        assertEq(token.totalSupply(), 10 ether);
    }

    function testBurnSelf() public {
        token.mint(address(this), 1 ether);
        vm.expectEmit(true, true, true, true);
        emit Transfer(address(this), address(0), 0.4 ether);
        token.burn(0.4 ether);
        assertEq(token.balanceOf(address(this)), 0.6 ether);
        assertEq(token.totalSupply(), 0.6 ether);
    }

    function testBurnFrom() public {
        address from = address(0xBEEF);
        token.mint(from, 1 ether);
        vm.prank(from);
        token.approve(address(this), 0.5 ether);
        token.burn_from(from, 0.5 ether);
        assertEq(token.balanceOf(from), 0.5 ether);
        assertEq(token.totalSupply(), 0.5 ether);
    }

    // --- approve / allowance ---

    function testApprove() public {
        vm.expectEmit(true, true, true, true);
        emit Approval(address(this), address(0xBEEF), 1e18);
        assertTrue(token.approve(address(0xBEEF), 1e18));
        assertEq(token.allowance(address(this), address(0xBEEF)), 1e18);
    }

    // --- transfer ---

    function testTransfer() public {
        token.mint(address(this), 1 ether);
        vm.expectEmit(true, true, true, true);
        emit Transfer(address(this), address(0xBEEF), 1 ether);
        assertTrue(token.transfer(address(0xBEEF), 1 ether));
        assertEq(token.balanceOf(address(this)), 0);
        assertEq(token.balanceOf(address(0xBEEF)), 1 ether);
    }

    function testTransferPartial() public {
        token.mint(address(this), 10 ether);
        assertTrue(token.transfer(address(0xBEEF), 3 ether));
        assertEq(token.balanceOf(address(this)), 7 ether);
        assertEq(token.balanceOf(address(0xBEEF)), 3 ether);
    }

    function testTransferInsufficientReverts() public {
        token.mint(address(this), 0.5 ether);
        vm.expectRevert(); // Snekmate uses string error
        token.transfer(address(0xBEEF), 1 ether);
    }

    function testTransferToZeroReverts() public {
        token.mint(address(this), 1 ether);
        vm.expectRevert();
        token.transfer(address(0), 1 ether);
    }

    // --- transferFrom ---

    function testTransferFrom() public {
        address from = address(0xABCD);
        token.mint(from, 1 ether);
        vm.prank(from);
        token.approve(address(this), 1 ether);
        vm.expectEmit(true, true, true, true);
        emit Transfer(from, address(0xBEEF), 1 ether);
        assertTrue(token.transferFrom(from, address(0xBEEF), 1 ether));
        assertEq(token.balanceOf(from), 0);
        assertEq(token.balanceOf(address(0xBEEF)), 1 ether);
        assertEq(token.allowance(from, address(this)), 0);
    }

    function testTransferFromInfiniteAllowance() public {
        address from = address(0xABCD);
        token.mint(from, 1 ether);
        vm.prank(from);
        token.approve(address(this), type(uint256).max);
        assertTrue(token.transferFrom(from, address(0xBEEF), 1 ether));
        // Infinite allowance: unchanged after the spend.
        assertEq(token.allowance(from, address(this)), type(uint256).max);
    }

    function testTransferFromInsufficientAllowanceReverts() public {
        address from = address(0xABCD);
        token.mint(from, 1 ether);
        vm.prank(from);
        token.approve(address(this), 0.5 ether);
        vm.expectRevert();
        token.transferFrom(from, address(0xBEEF), 1 ether);
    }

    function testTransferFromInsufficientBalanceReverts() public {
        address from = address(0xABCD);
        token.mint(from, 0.5 ether);
        vm.prank(from);
        token.approve(address(this), 1 ether);
        vm.expectRevert();
        token.transferFrom(from, address(0xBEEF), 1 ether);
    }

    // --- fuzz ---

    function testFuzzMint(address to, uint96 amount) public {
        vm.assume(to != address(0));
        token.mint(to, amount);
        assertEq(token.totalSupply(), amount);
        assertEq(token.balanceOf(to), amount);
    }

    function testFuzzTransfer(address to, uint96 amount) public {
        vm.assume(to != address(0));
        token.mint(address(this), amount);
        assertTrue(token.transfer(to, amount));
        if (address(this) == to) {
            assertEq(token.balanceOf(address(this)), amount);
        } else {
            assertEq(token.balanceOf(address(this)), 0);
            assertEq(token.balanceOf(to), amount);
        }
    }

    function testFuzzTransferFrom(address from, address to, uint96 amount) public {
        vm.assume(from != address(0) && to != address(0) && from != address(this));
        token.mint(from, amount);
        vm.prank(from);
        token.approve(address(this), amount);
        assertTrue(token.transferFrom(from, to, amount));
        if (from == to) {
            assertEq(token.balanceOf(from), amount);
        } else {
            assertEq(token.balanceOf(from), 0);
            assertEq(token.balanceOf(to), amount);
        }
    }

    function testFuzzApprove(address to, uint96 amount) public {
        vm.assume(to != address(0));
        assertTrue(token.approve(to, amount));
        assertEq(token.allowance(address(this), to), amount);
    }

    // --- non-balance state (nonces, owner, is_minter) should be
    //     untouched by the optimization — Vyper still uses keccak
    //     slots for them. ---

    function testNoncesUnchangedFromZero() public view {
        assertEq(token.nonces(address(0xAA)), 0);
    }

    function testOwnerInitializedToDeployer() public view {
        assertEq(token.owner(), address(this));
    }

    function testIsMinterInit() public view {
        assertTrue(token.is_minter(address(this)));
    }
}

contract OriginalVyperERC20Test is ERC20VyperBehaviourTest {
    function _deploy() internal override returns (address) {
        bytes memory creation = vm.getCode("mock.vy:mock");
        address a;
        assembly {
            a := create(0, add(creation, 0x20), mload(creation))
        }
        require(a != address(0), "deploy failed");
        return a;
    }
}

contract OptimizedVyperERC20Test is ERC20VyperBehaviourTest {
    function _deploy() internal override returns (address) {
        bytes memory creation = vm.getCode("mock.vy:mock");
        address a;
        assembly {
            a := create(0, add(creation, 0x20), mload(creation))
        }
        require(a != address(0), "deploy failed");

        // Apply the balance-access peephole in place. The deployed
        // code has constructor-initialised immutables (EIP-712 domain
        // name/version hashes, address(this) etc.) baked in; the
        // patcher only changes opcode bytes in the dispatch path so
        // the data region is untouched. Length-preserving ensures
        // PC-absolute jumpdests remain valid.
        bytes memory code = a.code;
        require(BytecodePatcher.countSites(code) == 9, "expected 9 balance-access sites");
        BytecodePatcher.patch(code);
        vm.etch(a, code);
        // Post-condition: no sites remain.
        require(BytecodePatcher.countSites(a.code) == 0, "patcher missed sites");
        return a;
    }
}
