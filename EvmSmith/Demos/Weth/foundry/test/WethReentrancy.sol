// SPDX-License-Identifier: MIT
pragma solidity 0.8.20;

/// @title WethReentrancyAttacker — calls back into Weth.withdraw from
///        its receive fallback, to prove the checks-effects-interactions
///        ordering blocks the classic reentrancy drain.
contract WethReentrancyAttacker {
    address public immutable weth;
    uint256 public reentries;

    constructor(address _weth) { weth = _weth; }

    function deposit() external payable {
        (bool ok,) = weth.call{value: msg.value}(hex"d0e30db0");
        require(ok, "deposit failed");
    }

    function attack(uint256 x) external {
        (bool ok,) = weth.call(abi.encodeWithSelector(bytes4(0x2e1a7d4d), x));
        require(ok, "outer withdraw failed");
    }

    /// When Weth.CALL sends ETH here, this fires. We attempt to withdraw
    /// again — the inner call should revert because our balance has
    /// already been decremented by the outer withdraw.
    receive() external payable {
        reentries++;
        if (reentries < 3) {
            // Attempt to drain more. Not `require(ok)` — we WANT this
            // to fail silently so the outer withdraw still succeeds.
            weth.call(abi.encodeWithSelector(bytes4(0x2e1a7d4d), msg.value));
        }
    }
}
