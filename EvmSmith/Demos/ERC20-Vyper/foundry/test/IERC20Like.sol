// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Common interface for both backends (orig + patched), with
///         the few extra Snekmate-y entry points the tests need:
///         mint, burn, set_minter, transfer_ownership, etc.
interface IERC20Like {
    // ERC-20
    function name() external view returns (string memory);
    function symbol() external view returns (string memory);
    function decimals() external view returns (uint8);
    function totalSupply() external view returns (uint256);
    function balanceOf(address) external view returns (uint256);
    function allowance(address, address) external view returns (uint256);
    function transfer(address, uint256) external returns (bool);
    function approve(address, uint256) external returns (bool);
    function transferFrom(address, address, uint256) external returns (bool);

    // Snekmate extras
    function mint(address, uint256) external;
    function burn(uint256) external;
    function burn_from(address, uint256) external;
    function set_minter(address, bool) external;
    function transfer_ownership(address) external;
    function renounce_ownership() external;
    function nonces(address) external view returns (uint256);
    function is_minter(address) external view returns (bool);
    function owner() external view returns (address);
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}
