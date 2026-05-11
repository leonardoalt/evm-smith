// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @notice Solidity in-place bytecode patcher mirroring `script/patch.py`.
///         Used in tests to take an already-deployed Vyper contract's
///         runtime (which has constructor-initialised immutables baked
///         into the bytecode) and apply the balance-access peephole
///         transformation, then `vm.etch` the patched bytes back onto
///         the *same address* — so the immutables stay valid.
///
///         The peephole pattern (15 bytes):
///           PUSH1 <slot> PUSH1 <P> MLOAD PUSH1 0x20 MSTORE PUSH0
///           MSTORE PUSH1 0x40 PUSH0 KECCAK256 <SLOAD|SSTORE>
///
///         The slot immediate (byte 1) discriminates which storage
///         bucket; we patch only those with slot == BALANCE_SLOT.
///         Replacement (also 15 bytes):
///           11 × JUMPDEST  ; no-op padding
///           PUSH1 <P> MLOAD <SLOAD|SSTORE>  ; key-as-slot access
library BytecodePatcher {
    /// @dev Vyper-emitted balance-slot id for `balanceOf` in the
    ///      Snekmate ERC-20 (verified empirically; see patch.py).
    uint8 internal constant BALANCE_SLOT = 0x02;

    /// @dev Patches `code` in place. Returns `code` (memory reference)
    ///      for convenience.
    function patch(bytes memory code) internal pure returns (bytes memory) {
        // Walk the bytecode, treating PUSH<n> immediates as data and
        // skipping them. At each non-data byte, check whether a 15-
        // byte balance-access prefix starts there.
        uint256 i = 0;
        while (i + 15 <= code.length) {
            uint8 b0 = uint8(code[i]);
            // First byte must be PUSH1.
            if (b0 == 0x60) {
                uint8 slot = uint8(code[i + 1]);
                uint8 b2 = uint8(code[i + 2]);
                uint8 b3 = uint8(code[i + 2]);
                if (slot == BALANCE_SLOT && b2 == 0x60) {
                    // The fixed tail of the prefix.
                    bool match_ =
                        uint8(code[i + 4])  == 0x51 &&  // MLOAD
                        uint8(code[i + 5])  == 0x60 &&  // PUSH1
                        uint8(code[i + 6])  == 0x20 &&
                        uint8(code[i + 7])  == 0x52 &&  // MSTORE
                        uint8(code[i + 8])  == 0x5f &&  // PUSH0
                        uint8(code[i + 9])  == 0x52 &&  // MSTORE
                        uint8(code[i + 10]) == 0x60 &&  // PUSH1
                        uint8(code[i + 11]) == 0x40 &&
                        uint8(code[i + 12]) == 0x5f &&  // PUSH0
                        uint8(code[i + 13]) == 0x20;    // KECCAK256
                    uint8 op = uint8(code[i + 14]);
                    if (match_ && (op == 0x54 || op == 0x55)) {
                        uint8 keyOffset = uint8(code[i + 3]);
                        // Replacement (15 bytes, length-preserving):
                        //   10 × JUMPDEST, PUSH1 keyOffset, MLOAD, NOT, op
                        // NOT (0x19) maps addr -> ~addr (slot above
                        // 2^160-ish), avoiding collisions with Vyper's
                        // named-slot storage (owner at 1, totalSupply
                        // at 4, etc.).
                        for (uint256 j = 0; j < 10; j++) {
                            code[i + j] = bytes1(uint8(0x5b));
                        }
                        code[i + 10] = bytes1(uint8(0x60));
                        code[i + 11] = bytes1(keyOffset);
                        code[i + 12] = bytes1(uint8(0x51));
                        code[i + 13] = bytes1(uint8(0x19));  // NOT
                        code[i + 14] = bytes1(op);
                        // Skip past the patched region.
                        i += 15;
                        continue;
                    }
                }
                // Not a balance access; skip the PUSH1 (1 imm byte).
                i += 2;
                // Unused; pacify the compiler.
                b3;
            } else if (b0 >= 0x61 && b0 <= 0x7f) {
                // PUSH2..PUSH32: skip opcode + (b0 - 0x5f) immediate bytes.
                i += 1 + (b0 - 0x5f);
            } else {
                i += 1;
            }
        }
        return code;
    }

    /// @dev Count the number of balance-access sites in `code`. Used
    ///      by tests to assert the expected 9 sites are present before
    ///      patching.
    function countSites(bytes memory code) internal pure returns (uint256 n) {
        uint256 i = 0;
        while (i + 15 <= code.length) {
            uint8 b0 = uint8(code[i]);
            if (b0 == 0x60 && uint8(code[i + 1]) == BALANCE_SLOT
                && uint8(code[i + 2]) == 0x60
                && uint8(code[i + 4]) == 0x51
                && uint8(code[i + 5]) == 0x60
                && uint8(code[i + 6]) == 0x20
                && uint8(code[i + 7]) == 0x52
                && uint8(code[i + 8]) == 0x5f
                && uint8(code[i + 9]) == 0x52
                && uint8(code[i + 10]) == 0x60
                && uint8(code[i + 11]) == 0x40
                && uint8(code[i + 12]) == 0x5f
                && uint8(code[i + 13]) == 0x20
            ) {
                uint8 op = uint8(code[i + 14]);
                if (op == 0x54 || op == 0x55) {
                    n++;
                    i += 15;
                    continue;
                }
            }
            if (b0 >= 0x60 && b0 <= 0x7f) {
                i += 1 + (b0 - 0x5f);
            } else {
                i += 1;
            }
        }
    }
}
