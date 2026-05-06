// SPDX-License-Identifier: MIT
pragma solidity 0.8.20;

/// @title WethSolidity
/// @notice An idiomatic Solidity port of the minimal WETH semantics
///         proved in Lean against `EvmSmith/Demos/Weth/Program.lean`.
///         Same observable behaviour: deposit credits the sender's
///         tracked balance with `msg.value`; withdraw decrements that
///         tracked balance and sends the corresponding ETH back via a
///         low-level `call` (CEI: state update before the external
///         call). On insufficient balance or failed call, revert.
///
///         Storage layout differs from the hand-rolled bytecode: this
///         version uses `mapping(address => uint256)`, which Solidity
///         lowers to `keccak256(abi.encode(addr, slot))` lookups; the
///         hand-rolled version uses the raw address as the slot key.
///         Compare gas costs in `test/WethGasCompare.t.sol`.
contract WethSolidity {
    mapping(address => uint256) public balances;

    function deposit() external payable {
        balances[msg.sender] += msg.value;
    }

    function withdraw(uint256 x) external {
        uint256 bal = balances[msg.sender];
        if (bal < x) revert();
        balances[msg.sender] = bal - x;
        (bool ok,) = msg.sender.call{value: x}("");
        if (!ok) revert();
    }
}
