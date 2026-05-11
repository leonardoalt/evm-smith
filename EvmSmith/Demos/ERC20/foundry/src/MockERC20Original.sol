// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC20} from "solady/tokens/ERC20.sol";

/// @title MockERC20Original
/// @notice A Solady-based ERC-20 used as the *original* layout in the
///         storage-layout-optimization comparison. Inherits Solady's
///         ERC-20 unchanged: balance slots are keccak-derived
///         (`keccak256(addr ++ 0x87a211a2)` per the seed-mstore trick),
///         allowance slots are keccak-derived (separate seed), nonces
///         likewise, and totalSupply is at a fixed slot.
///
///         Pairs with `MockERC20Optimized.sol` whose balance slots are
///         the raw `uint256(uint160(addr))` of the holder. Functional
///         equivalence between the two layouts is proved at the
///         bytecode level under `../../Equivalence.lean`.
contract MockERC20Original is ERC20 {
    string private _name;
    string private _symbol;
    uint8 private _decimals;

    constructor(string memory name_, string memory symbol_, uint8 decimals_) {
        _name = name_;
        _symbol = symbol_;
        _decimals = decimals_;
    }

    function name() public view virtual override returns (string memory) {
        return _name;
    }

    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    function decimals() public view virtual override returns (uint8) {
        return _decimals;
    }

    function mint(address to, uint256 value) external {
        _mint(to, value);
    }

    function burn(address from, uint256 value) external {
        _burn(from, value);
    }
}
