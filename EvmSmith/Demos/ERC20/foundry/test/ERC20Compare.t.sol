// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {ERC20} from "solady/tokens/ERC20.sol";
import {MockERC20Original} from "../src/MockERC20Original.sol";
import {MockERC20Optimized} from "../src/MockERC20Optimized.sol";

/// @notice One abstract test contract; instantiated twice — once against
///         the keccak-balance backend, once against the address-as-slot
///         backend. Each subclass overrides `_makeToken()` to wire in its
///         backend. Both must pass the same suite of tests.
abstract contract ERC20BehaviourTest is Test {
    ERC20 token;
    address constant _PERMIT2 = 0x000000000022D473030F116dDEE9F6B43aC78BA3;

    event Transfer(address indexed from, address indexed to, uint256 amount);
    event Approval(address indexed owner, address indexed spender, uint256 amount);

    function _makeToken() internal virtual returns (ERC20);

    function _mint(address to, uint256 amount) internal {
        // Both backends expose `mint(address,uint256)` on the mock.
        (bool ok,) = address(token).call(abi.encodeWithSignature("mint(address,uint256)", to, amount));
        require(ok, "mint failed");
    }

    function _burn(address from, uint256 amount) internal {
        (bool ok,) = address(token).call(abi.encodeWithSignature("burn(address,uint256)", from, amount));
        require(ok, "burn failed");
    }

    function setUp() public {
        token = _makeToken();
    }

    // -------- metadata --------

    function testMetadata() public {
        assertEq(token.name(), "Token");
        assertEq(token.symbol(), "TKN");
        assertEq(token.decimals(), 18);
    }

    // -------- mint --------

    function testMint() public {
        vm.expectEmit(true, true, true, true);
        emit Transfer(address(0), address(0xBEEF), 1e18);
        _mint(address(0xBEEF), 1e18);
        assertEq(token.totalSupply(), 1e18);
        assertEq(token.balanceOf(address(0xBEEF)), 1e18);
    }

    function testMintMultiple() public {
        _mint(address(0xAA), 5 ether);
        _mint(address(0xBB), 3 ether);
        _mint(address(0xAA), 2 ether);
        assertEq(token.balanceOf(address(0xAA)), 7 ether);
        assertEq(token.balanceOf(address(0xBB)), 3 ether);
        assertEq(token.totalSupply(), 10 ether);
    }

    function testMintOverflowReverts() public {
        _mint(address(this), type(uint256).max);
        // Use a try/catch via raw call here because `mint` is exposed
        // only by the concrete Mock contracts (not the abstract ERC20
        // base we typed `token` as), but we still want to assert the
        // exact revert reason rather than just "non-success".
        (bool ok, bytes memory ret) = address(token).call(
            abi.encodeWithSignature("mint(address,uint256)", address(this), 1)
        );
        assertFalse(ok, "should have reverted");
        assertEq(bytes4(ret), ERC20.TotalSupplyOverflow.selector);
    }

    // -------- burn --------

    function testBurn() public {
        _mint(address(0xBEEF), 1e18);
        vm.expectEmit(true, true, true, true);
        emit Transfer(address(0xBEEF), address(0), 0.9e18);
        _burn(address(0xBEEF), 0.9e18);
        assertEq(token.totalSupply(), 0.1e18);
        assertEq(token.balanceOf(address(0xBEEF)), 0.1e18);
    }

    function testBurnInsufficientReverts() public {
        _mint(address(0xBEEF), 0.5e18);
        (bool ok, bytes memory ret) = address(token).call(
            abi.encodeWithSignature("burn(address,uint256)", address(0xBEEF), 1e18)
        );
        assertFalse(ok, "should have reverted");
        assertEq(bytes4(ret), ERC20.InsufficientBalance.selector);
    }

    // -------- approve --------

    function testApprove() public {
        vm.expectEmit(true, true, true, true);
        emit Approval(address(this), address(0xBEEF), 1e18);
        assertTrue(token.approve(address(0xBEEF), 1e18));
        assertEq(token.allowance(address(this), address(0xBEEF)), 1e18);
    }

    function testPermit2InfiniteAllowance() public view {
        assertEq(token.allowance(address(0xAA), _PERMIT2), type(uint256).max);
    }

    // -------- transfer --------

    function testTransfer() public {
        _mint(address(this), 1e18);
        vm.expectEmit(true, true, true, true);
        emit Transfer(address(this), address(0xBEEF), 1e18);
        assertTrue(token.transfer(address(0xBEEF), 1e18));
        assertEq(token.balanceOf(address(this)), 0);
        assertEq(token.balanceOf(address(0xBEEF)), 1e18);
        assertEq(token.totalSupply(), 1e18);
    }

    function testTransferPartial() public {
        _mint(address(this), 10 ether);
        assertTrue(token.transfer(address(0xBEEF), 3 ether));
        assertEq(token.balanceOf(address(this)), 7 ether);
        assertEq(token.balanceOf(address(0xBEEF)), 3 ether);
    }

    function testTransferInsufficientBalanceReverts() public {
        _mint(address(this), 0.9e18);
        vm.expectRevert(ERC20.InsufficientBalance.selector);
        token.transfer(address(0xBEEF), 1e18);
    }

    function testTransferToSelf() public {
        _mint(address(this), 5 ether);
        assertTrue(token.transfer(address(this), 3 ether));
        assertEq(token.balanceOf(address(this)), 5 ether);
        assertEq(token.totalSupply(), 5 ether);
    }

    function testTransferZero() public {
        _mint(address(0xAA), 1 ether);
        vm.prank(address(0xAA));
        assertTrue(token.transfer(address(0xBB), 0));
        assertEq(token.balanceOf(address(0xAA)), 1 ether);
        assertEq(token.balanceOf(address(0xBB)), 0);
    }

    // -------- transferFrom --------

    function testTransferFrom() public {
        address from = address(0xABCD);
        _mint(from, 1e18);
        vm.prank(from);
        token.approve(address(this), 1e18);

        vm.expectEmit(true, true, true, true);
        emit Transfer(from, address(0xBEEF), 1e18);
        assertTrue(token.transferFrom(from, address(0xBEEF), 1e18));
        assertEq(token.allowance(from, address(this)), 0);
        assertEq(token.balanceOf(from), 0);
        assertEq(token.balanceOf(address(0xBEEF)), 1e18);
        assertEq(token.totalSupply(), 1e18);
    }

    function testInfiniteApproveTransferFrom() public {
        address from = address(0xABCD);
        _mint(from, 1e18);
        vm.prank(from);
        token.approve(address(this), type(uint256).max);
        assertTrue(token.transferFrom(from, address(0xBEEF), 1e18));
        assertEq(token.allowance(from, address(this)), type(uint256).max);
        assertEq(token.balanceOf(from), 0);
        assertEq(token.balanceOf(address(0xBEEF)), 1e18);
    }

    function testTransferFromInsufficientAllowanceReverts() public {
        address from = address(0xABCD);
        _mint(from, 1e18);
        vm.prank(from);
        token.approve(address(this), 0.9e18);
        vm.expectRevert(ERC20.InsufficientAllowance.selector);
        token.transferFrom(from, address(0xBEEF), 1e18);
    }

    function testTransferFromInsufficientBalanceReverts() public {
        address from = address(0xABCD);
        _mint(from, 0.9e18);
        vm.prank(from);
        token.approve(address(this), 1e18);
        vm.expectRevert(ERC20.InsufficientBalance.selector);
        token.transferFrom(from, address(0xBEEF), 1e18);
    }

    function testPermit2NoAllowanceNeeded() public {
        address from = address(0xABCD);
        _mint(from, 1e18);
        vm.prank(_PERMIT2);
        assertTrue(token.transferFrom(from, address(0xBEEF), 1e18));
        assertEq(token.balanceOf(from), 0);
        assertEq(token.balanceOf(address(0xBEEF)), 1e18);
        // Permit2 allowance is fixed at infinity, unchanged.
        assertEq(token.allowance(from, _PERMIT2), type(uint256).max);
    }

    // -------- fuzz --------

    function testFuzzMint(address to, uint96 amount) public {
        _mint(to, amount);
        assertEq(token.totalSupply(), amount);
        assertEq(token.balanceOf(to), amount);
    }

    function testFuzzBurn(address from, uint96 mintAmount, uint96 burnAmount) public {
        vm.assume(burnAmount <= mintAmount);
        _mint(from, mintAmount);
        _burn(from, burnAmount);
        assertEq(token.totalSupply(), uint256(mintAmount) - uint256(burnAmount));
        assertEq(token.balanceOf(from), uint256(mintAmount) - uint256(burnAmount));
    }

    function testFuzzTransfer(address to, uint96 amount) public {
        _mint(address(this), amount);
        assertTrue(token.transfer(to, amount));
        if (address(this) == to) {
            assertEq(token.balanceOf(address(this)), amount);
        } else {
            assertEq(token.balanceOf(address(this)), 0);
            assertEq(token.balanceOf(to), amount);
        }
        assertEq(token.totalSupply(), amount);
    }

    function testFuzzTransferFrom(address from, address to, uint96 amount) public {
        vm.assume(from != address(this));
        _mint(from, amount);
        vm.prank(from);
        token.approve(address(this), amount);
        assertTrue(token.transferFrom(from, to, amount));
        assertEq(token.allowance(from, address(this)), 0);
        if (from == to) {
            assertEq(token.balanceOf(from), amount);
        } else {
            assertEq(token.balanceOf(from), 0);
            assertEq(token.balanceOf(to), amount);
        }
    }

    function testFuzzApprove(address to, uint96 amount) public {
        // Solady's approve has a special case for the Permit2 address
        // (infinite-only). Excluded from this fuzz path.
        vm.assume(to != _PERMIT2);
        assertTrue(token.approve(to, amount));
        assertEq(token.allowance(address(this), to), amount);
    }
}

contract OriginalERC20Test is ERC20BehaviourTest {
    function _makeToken() internal override returns (ERC20) {
        return new MockERC20Original("Token", "TKN", 18);
    }
}

contract OptimizedERC20Test is ERC20BehaviourTest {
    function _makeToken() internal override returns (ERC20) {
        return new MockERC20Optimized("Token", "TKN", 18);
    }
}
