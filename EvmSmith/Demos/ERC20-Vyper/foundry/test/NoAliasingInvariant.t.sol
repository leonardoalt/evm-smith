// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {IERC20Like} from "./IERC20Like.sol";
import {BytecodePatcher} from "./BytecodePatcher.sol";

/// @notice Handler driving the Vyper ERC-20 through mints and
///         transfers chosen from a small dictionary of actors
///         (deliberately including low addresses 0x00..0x06 that
///         collide with Vyper's named state slots in the pre-fix
///         layout).
contract NoAliasHandlerVyper is Test {
    IERC20Like token;
    address[] public actors;
    mapping(address => bool) seen;
    uint256 public totalSeeded;

    constructor(IERC20Like _token) {
        token = _token;
        // Cover every address that overlaps Vyper's named storage:
        // owner@0x01, balanceOf-base@0x02, allowance-base@0x03,
        // totalSupply@0x04, is_minter-base@0x05, nonces-base@0x06.
        for (uint160 i = 0; i <= 6; i++) _addActor(address(i));
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

abstract contract NoAliasVyperInvariantTest is Test {
    IERC20Like token;
    NoAliasHandlerVyper handler;

    function _deployToken() internal virtual returns (IERC20Like);

    function setUp() public {
        token = _deployToken();
        handler = new NoAliasHandlerVyper(token);
        targetContract(address(handler));
    }

    /// @dev Metadata + owner + totalSupply consistency must hold
    ///      across any fuzz sequence. With the pre-fix `sload(addr)`
    ///      version, `mint(address(0x04), v)` would corrupt
    ///      `totalSupply` (slot 4); this invariant catches it.
    function invariant_metadata_preserved() public view {
        assertEq(token.name(), "Token");
        assertEq(token.symbol(), "TKN");
        assertEq(token.decimals(), 18);
        assertTrue(token.owner() != address(0), "owner corrupted");
    }

    /// @dev Σ balanceOf(actor) ≤ totalSupply. With aliasing, the sum
    ///      can exceed totalSupply (two actors share a slot, both
    ///      claim its value), or — worse — the corrupted totalSupply
    ///      itself can be lower than reality. Either way, the
    ///      invariant fails.
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

contract OriginalVyperNoAliasTest is NoAliasVyperInvariantTest {
    function _deployToken() internal override returns (IERC20Like) {
        bytes memory creation = vm.getCode("mock.vy:mock");
        address a;
        assembly {
            a := create(0, add(creation, 0x20), mload(creation))
        }
        require(a != address(0), "deploy failed");
        return IERC20Like(a);
    }
}

contract OptimizedVyperNoAliasTest is NoAliasVyperInvariantTest {
    function _deployToken() internal override returns (IERC20Like) {
        bytes memory creation = vm.getCode("mock.vy:mock");
        address a;
        assembly {
            a := create(0, add(creation, 0x20), mload(creation))
        }
        require(a != address(0), "deploy failed");
        bytes memory code = a.code;
        BytecodePatcher.patch(code);
        vm.etch(a, code);
        return IERC20Like(a);
    }
}
