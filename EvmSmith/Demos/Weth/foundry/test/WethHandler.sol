// SPDX-License-Identifier: MIT
pragma solidity 0.8.20;

import "forge-std/Test.sol";

/// @title WethHandler — fuzz handler for Weth's invariant tests
/// @notice Exposes `deposit`/`withdraw` to Foundry's invariant fuzzer. The
///         fuzzer cannot call the etched bytecode directly (no ABI), so we
///         dispatch via low-level `.call` and track a ghost actor set.
contract WethHandler is Test {
    address public immutable weth;

    /// Actors we've seen — iterated by the invariant checks.
    address[] public actors;
    mapping(address => bool) private seen;

    /// Ghost accounting: total wei ever deposited / withdrawn successfully.
    uint256 public ghostTotalDeposited;
    uint256 public ghostTotalWithdrawn;

    constructor(address _weth) {
        weth = _weth;
        // Seed actor pool so the fuzzer has addresses to pick even
        // before any ghost deposits/withdrawals have happened.
        _addActor(address(uint160(0xAAAA)));
        _addActor(address(uint160(0xBBBB)));
        _addActor(address(uint160(0xCCCC)));
    }

    function deposit(uint256 actorSeed, uint256 amtRaw) public {
        address a = actors[actorSeed % actors.length];
        uint256 amt = bound(amtRaw, 0, 100 ether);
        vm.deal(a, amt);
        vm.prank(a);
        (bool ok,) = weth.call{value: amt}(hex"d0e30db0");
        if (ok) {
            ghostTotalDeposited += amt;
            _addActor(a);
        }
    }

    function withdraw(uint256 actorSeed, uint256 amtRaw) public {
        address a = actors[actorSeed % actors.length];
        uint256 bal = uint256(vm.load(weth, bytes32(uint256(uint160(a)))));
        uint256 amt = bound(amtRaw, 0, bal);
        vm.prank(a);
        (bool ok,) = weth.call(abi.encodeWithSelector(bytes4(0x2e1a7d4d), amt));
        if (ok) ghostTotalWithdrawn += amt;
    }

    function actorCount() external view returns (uint256) {
        return actors.length;
    }

    function _addActor(address a) internal {
        if (a == address(0)) return;
        if (seen[a]) return;
        seen[a] = true;
        actors.push(a);
    }
}
