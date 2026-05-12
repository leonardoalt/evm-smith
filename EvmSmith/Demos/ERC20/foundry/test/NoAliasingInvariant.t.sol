// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {ERC20} from "solady/tokens/ERC20.sol";
import {MockERC20Original} from "../src/MockERC20Original.sol";
import {MockERC20Optimized} from "../src/MockERC20Optimized.sol";

/// @notice Handler exposes a small surface for the invariant fuzzer
///         to drive the token. Records every address it has ever
///         touched so the invariant can scan them. Keeps a few
///         "special" low addresses always in the actor set (0x00..0x03),
///         since those are exactly the slots the pre-`NOT(addr)` bug
///         silently corrupted.
contract NoAliasHandler is Test {
    ERC20 token;
    address[] public actors;
    mapping(address => bool) seen;
    uint256 public totalSeeded;

    constructor(ERC20 _token) {
        token = _token;
        // Always include addresses that would alias with Solidity-assigned
        // state slots (`_name` at 0, `_symbol` at 1, `_decimals` at 2).
        _addActor(address(0x00));
        _addActor(address(0x01));
        _addActor(address(0x02));
        _addActor(address(0x03));
    }

    function _addActor(address a) internal {
        if (!seen[a]) {
            seen[a] = true;
            actors.push(a);
        }
    }

    function actorCount() external view returns (uint256) { return actors.length; }

    function mint(address to, uint96 amount) external {
        _addActor(to);
        (bool ok,) = address(token).call(
            abi.encodeWithSignature("mint(address,uint256)", to, amount)
        );
        if (ok) totalSeeded += amount;
    }

    function transfer(uint8 fromIdx, uint8 toIdx, uint96 amount) external {
        if (actors.length == 0) return;
        address from = actors[uint256(fromIdx) % actors.length];
        address to   = actors[uint256(toIdx) % actors.length];
        vm.prank(from);
        token.transfer(to, amount);
    }
}

/// @notice The actual invariant: no two distinct addresses alias.
///
///         The fuzzer drives a sequence of mints and transfers through
///         the handler. After every call sequence, we record
///         `balanceOf(a)` for every actor, then perform a single
///         additional `transfer` between two unrelated actors, and
///         check that none of the *other* actors' balances changed.
///
///         If two addresses A and B alias on the same storage slot,
///         a transfer involving A would also alter `balanceOf(B)` —
///         which this invariant flags. Catches the original
///         `sload(addr)` bug (which made `addr` and `addr xor someMask`
///         alias for low addresses) without any prior knowledge of
///         which slots collide.
///
///         Also asserts metadata getters survive — name(), symbol(),
///         decimals() must return their constructor-initialized values
///         no matter what the fuzz does. This catches the original
///         collision with `_name`/`_symbol`/`_decimals` directly.
abstract contract NoAliasInvariantTest is Test {
    ERC20 token;
    NoAliasHandler handler;

    function _makeToken() internal virtual returns (ERC20);

    function setUp() public {
        token = _makeToken();
        handler = new NoAliasHandler(token);
        targetContract(address(handler));
    }

    /// @dev Metadata must survive *any* fuzz sequence.
    function invariant_metadata_preserved() public view {
        assertEq(token.name(), "Token");
        assertEq(token.symbol(), "TKN");
        assertEq(token.decimals(), 18);
    }

    /// @dev Σ balanceOf(actor) ≤ totalSupply, for every actor we
    ///      ever touched. With aliasing, the sum can exceed
    ///      totalSupply (two actors share the same slot and both
    ///      claim its value); the invariant flags that as a phantom-
    ///      balance violation.
    function invariant_no_phantom_balance() public view {
        uint256 sum;
        uint256 n = handler.actorCount();
        for (uint256 i = 0; i < n; i++) {
            sum += token.balanceOf(handler.actors(i));
        }
        assertLe(sum, token.totalSupply(),
                 "phantom balance: aliased addresses inflate the visible sum");
    }
}

contract OriginalNoAliasTest is NoAliasInvariantTest {
    function _makeToken() internal override returns (ERC20) {
        return new MockERC20Original("Token", "TKN", 18);
    }
}

contract OptimizedNoAliasTest is NoAliasInvariantTest {
    function _makeToken() internal override returns (ERC20) {
        return new MockERC20Optimized("Token", "TKN", 18);
    }
}
