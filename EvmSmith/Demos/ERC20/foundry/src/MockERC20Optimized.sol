// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC20} from "solady/tokens/ERC20.sol";

/// @title MockERC20Optimized
/// @notice Solady's ERC-20 with the **balance storage layout** changed
///         from keccak-derived slots to the raw address (`uint256(uint160(addr))`).
///         Allowances, nonces, and totalSupply are unchanged.
///
///         Behavioural equivalence with `MockERC20Original` (the
///         keccak-balance backend) is proved bytecode-level in
///         `EvmSmith/Demos/ERC20/Equivalence.lean`.
///
///         Six functions override Solady's keccak-mapped balance access:
///         `balanceOf`, `transfer`, `transferFrom`, `_mint`, `_burn`,
///         `_transfer`. Each is rewritten so the balance slot is
///         `sload(addr)` directly, no `mstore+keccak256` prefix.
///
///         The `log3` topic for the address (`to` or `from`) is sourced
///         from the parameter / `caller()` directly, rather than reading
///         memory that Solady's path conveniently happens to have
///         written for the keccak prefix.
contract MockERC20Optimized is ERC20 {
    /// @dev `keccak256(bytes("Transfer(address,address,uint256)"))`.
    uint256 private constant _TRANSFER_EVENT_SIGNATURE =
        0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef;

    /// @dev `keccak256(bytes("Approval(address,address,uint256)"))`.
    uint256 private constant _APPROVAL_EVENT_SIGNATURE =
        0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925;

    /// @dev See Solady's ERC20.sol.
    uint256 private constant _TOTAL_SUPPLY_SLOT = 0x05345cdf77eb68f44c;

    /// @dev Allowance seed; Solady's original layout (keccak-mapped).
    uint256 private constant _ALLOWANCE_SLOT_SEED = 0x7f5e9f20;

    /// @dev Canonical Permit2 address. Same as in Solady; participates
    ///      in Solady's allowance-infinity escape hatch.
    address internal constant _PERMIT2_OPT = 0x000000000022D473030F116dDEE9F6B43aC78BA3;

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

    /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
    /*               OVERRIDDEN BALANCE FUNCTIONS                 */
    /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

    /// @dev The balance slot for `addr` is `not(addr)`, not `addr` itself.
    ///      `not(addr)` for any 160-bit address has the high 96 bits all
    ///      one, putting the slot at >= 2^160 — strictly above every
    ///      named state slot in this contract (`_name` at slot 0,
    ///      `_symbol` at 1, `_decimals` at 2, plus `_TOTAL_SUPPLY_SLOT`
    ///      which is a high constant anyway) and well clear of every
    ///      keccak-derived slot from the allowance / nonce buckets.
    ///      `not` is bijective so injectivity per address is preserved.
    function balanceOf(address owner) public view virtual override returns (uint256 result) {
        /// @solidity memory-safe-assembly
        assembly {
            result := sload(not(shr(96, shl(96, owner))))
        }
    }

    function transfer(address to, uint256 amount) public virtual override returns (bool) {
        _beforeTokenTransfer(msg.sender, to, amount);
        /// @solidity memory-safe-assembly
        assembly {
            let fromSlot := not(caller())
            let toSlot := not(shr(96, shl(96, to)))
            let fromBal := sload(fromSlot)
            if gt(amount, fromBal) {
                mstore(0x00, 0xf4d678b8) // `InsufficientBalance()`.
                revert(0x1c, 0x04)
            }
            sstore(fromSlot, sub(fromBal, amount))
            sstore(toSlot, add(sload(toSlot), amount))
            // Emit Transfer(from=caller, to, amount). Topics are the raw
            // addresses, not the negated slots — the event log must
            // remain identical to the original.
            mstore(0x00, amount)
            log3(0x00, 0x20, _TRANSFER_EVENT_SIGNATURE,
                 caller(), shr(96, shl(96, to)))
        }
        _afterTokenTransfer(msg.sender, to, amount);
        return true;
    }

    function transferFrom(address from, address to, uint256 amount)
        public
        virtual
        override
        returns (bool)
    {
        _beforeTokenTransfer(from, to, amount);
        // Allowance handling stays exactly as Solady: keccak-mapped,
        // with the Permit2-infinity escape hatch.
        bool permit2Infinite = _givePermit2InfiniteAllowance();
        if (permit2Infinite && msg.sender == _PERMIT2_OPT) {
            // Allowance is infinite; skip the allowance debit entirely.
        } else {
            /// @solidity memory-safe-assembly
            assembly {
                let from_ := shl(96, from)
                // Solady's allowance slot computation, unchanged.
                mstore(0x20, caller())
                mstore(0x0c, or(from_, _ALLOWANCE_SLOT_SEED))
                let allowanceSlot := keccak256(0x0c, 0x34)
                let allowance_ := sload(allowanceSlot)
                if not(allowance_) {
                    if gt(amount, allowance_) {
                        mstore(0x00, 0x13be252b) // `InsufficientAllowance()`.
                        revert(0x1c, 0x04)
                    }
                    sstore(allowanceSlot, sub(allowance_, amount))
                }
            }
        }
        /// @solidity memory-safe-assembly
        assembly {
            let fromAddr := shr(96, shl(96, from))
            let toAddr := shr(96, shl(96, to))
            let fromSlot := not(fromAddr)
            let toSlot := not(toAddr)
            let fromBal := sload(fromSlot)
            if gt(amount, fromBal) {
                mstore(0x00, 0xf4d678b8) // `InsufficientBalance()`.
                revert(0x1c, 0x04)
            }
            sstore(fromSlot, sub(fromBal, amount))
            sstore(toSlot, add(sload(toSlot), amount))
            mstore(0x00, amount)
            log3(0x00, 0x20, _TRANSFER_EVENT_SIGNATURE, fromAddr, toAddr)
        }
        _afterTokenTransfer(from, to, amount);
        return true;
    }

    function _mint(address to, uint256 amount) internal virtual override {
        _beforeTokenTransfer(address(0), to, amount);
        /// @solidity memory-safe-assembly
        assembly {
            let totalSupplyBefore := sload(_TOTAL_SUPPLY_SLOT)
            let totalSupplyAfter := add(totalSupplyBefore, amount)
            if lt(totalSupplyAfter, totalSupplyBefore) {
                mstore(0x00, 0xe5cfe957) // `TotalSupplyOverflow()`.
                revert(0x1c, 0x04)
            }
            sstore(_TOTAL_SUPPLY_SLOT, totalSupplyAfter)
            let toAddr := shr(96, shl(96, to))
            let toSlot := not(toAddr)
            sstore(toSlot, add(sload(toSlot), amount))
            mstore(0x00, amount)
            log3(0x00, 0x20, _TRANSFER_EVENT_SIGNATURE, 0, toAddr)
        }
        _afterTokenTransfer(address(0), to, amount);
    }

    function _burn(address from, uint256 amount) internal virtual override {
        _beforeTokenTransfer(from, address(0), amount);
        /// @solidity memory-safe-assembly
        assembly {
            let fromAddr := shr(96, shl(96, from))
            let fromSlot := not(fromAddr)
            let fromBal := sload(fromSlot)
            if gt(amount, fromBal) {
                mstore(0x00, 0xf4d678b8) // `InsufficientBalance()`.
                revert(0x1c, 0x04)
            }
            sstore(fromSlot, sub(fromBal, amount))
            sstore(_TOTAL_SUPPLY_SLOT, sub(sload(_TOTAL_SUPPLY_SLOT), amount))
            mstore(0x00, amount)
            log3(0x00, 0x20, _TRANSFER_EVENT_SIGNATURE, fromAddr, 0)
        }
        _afterTokenTransfer(from, address(0), amount);
    }

    function _transfer(address from, address to, uint256 amount) internal virtual override {
        _beforeTokenTransfer(from, to, amount);
        /// @solidity memory-safe-assembly
        assembly {
            let fromAddr := shr(96, shl(96, from))
            let toAddr := shr(96, shl(96, to))
            let fromSlot := not(fromAddr)
            let toSlot := not(toAddr)
            let fromBal := sload(fromSlot)
            if gt(amount, fromBal) {
                mstore(0x00, 0xf4d678b8) // `InsufficientBalance()`.
                revert(0x1c, 0x04)
            }
            sstore(fromSlot, sub(fromBal, amount))
            sstore(toSlot, add(sload(toSlot), amount))
            mstore(0x00, amount)
            log3(0x00, 0x20, _TRANSFER_EVENT_SIGNATURE, fromAddr, toAddr)
        }
        _afterTokenTransfer(from, to, amount);
    }
}
