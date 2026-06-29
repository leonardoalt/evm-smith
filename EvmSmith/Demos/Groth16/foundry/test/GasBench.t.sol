// SPDX-License-Identifier: MIT
pragma solidity 0.8.20;

import "forge-std/Test.sol";
import "circuit/verifier_reference.sol";

/// @title Gas benchmark: hand-assembled bytecode vs. snarkjs's reference,
///        against a theoretical floor
/// @notice Run with `forge test --match-contract GasBenchTest -vv` to see
///         the logged gas figures; `-vv` is needed for `emit log_named_uint`
///         to print. Both contracts are called with the same real proof
///         (see `Groth16.t.sol`'s docstring for its provenance) so the
///         comparison is apples-to-apples.
///
///         The theoretical floor (`THEORETICAL_MIN_GAS`) is the sum of the
///         three precompile costs this verifier cannot avoid, fixed since
///         EIP-1108/EIP-197 and unchanged through Cancun/Prague:
///           ECADD (0x06):                                            150
///           ECMUL (0x07):                                          6,000
///           ECPAIRING (0x08), 4 pairs: 45,000 + 4 * 34,000 =       181,000
///                                                          -------------
///                                                                 187,150
///         Neither contract can get below this; both pay some overhead on
///         top of it (`CALL`/`STATICCALL` opcode cost, memory expansion,
///         calldata decode, `checkField`'s range check, dispatch). What
///         differs is how much.
contract GasBenchTest is Test {
    address constant VERIFIER = address(uint160(0x6701));
    Groth16Verifier ref;

    uint256 constant THEORETICAL_MIN_GAS = 187_150;

    uint256 constant Ax  = 0x1436394a7a720743fd709443ec3bddee84b5d15af72f7b30de99429458466987;
    uint256 constant Ay  = 0x145fd6737532999f6f7e54238225c1edfd97893e98ffe3ece5569da53573709f;
    uint256 constant Bx1 = 0x0000201a8505badf54f5f17a02eff349ea1d225aabc09eae27a3f3fcabe3b4fe;
    uint256 constant Bx0 = 0x2dc9aa285aeff75b29eb74e000546f235d9c10cd493006470fa990fba592eba7;
    uint256 constant By1 = 0x2aa9b607e9fbf7ce7d26c48d7910fd123d00e91a91edc2a1282f8e0bab0392ed;
    uint256 constant By0 = 0x00a5d72782da85a80edb669cb34dd0471f175ef4f2016502c33873f366efeba4;
    uint256 constant Cx  = 0x14de0c4e98c6abfefabd35e18f31e60d6f8477b2317817b5db49495928f4ffef;
    uint256 constant Cy  = 0x1c2eec5c65a2bbd28d9d83c46c50effa12e3e56ca243935c72341375b2e53685;
    uint256 constant INPUT = 9;

    function setUp() public {
        string memory raw = vm.readFile("test/Groth16.bytecode.hex");
        bytes memory runtime = vm.parseBytes(_trim(raw));
        vm.etch(VERIFIER, runtime);
        ref = new Groth16Verifier();
    }

    function _trim(string memory s) internal pure returns (string memory) {
        bytes memory b = bytes(s);
        uint256 n = b.length;
        while (n > 0 &&
               (b[n - 1] == 0x0a || b[n - 1] == 0x0d ||
                b[n - 1] == 0x09 || b[n - 1] == 0x20)) {
            n--;
        }
        bytes memory r = new bytes(n);
        for (uint256 i = 0; i < n; i++) r[i] = b[i];
        return string(r);
    }

    /// The hand-assembled bytecode's call-only gas (excludes the 21,000
    /// transaction base cost -- this measures the message call, not a
    /// standalone top-level transaction).
    function test_gas_lean_bytecode() public {
        bytes memory calldata_ = abi.encodePacked(
            bytes4(0x43753b4d), Ax, Ay, Bx1, Bx0, By1, By0, Cx, Cy, INPUT
        );
        uint256 g0 = gasleft();
        (bool ok, bytes memory ret) = VERIFIER.call(calldata_);
        uint256 used = g0 - gasleft();
        assertTrue(ok);
        assertEq(abi.decode(ret, (uint256)), 1);
        emit log_named_uint("lean bytecode call gas", used);
        emit log_named_uint("  vs. theoretical floor (+gas)", used - THEORETICAL_MIN_GAS);
    }

    /// snarkjs's own generated Solidity verifier (`circuit/verifier_reference.sol`),
    /// same proof, same floor.
    function test_gas_reference_solidity() public {
        uint256[2] memory pA = [Ax, Ay];
        uint256[2][2] memory pB = [[Bx1, Bx0], [By1, By0]];
        uint256[2] memory pC = [Cx, Cy];
        uint256[1] memory pubSignals = [INPUT];
        uint256 g0 = gasleft();
        bool ok = ref.verifyProof(pA, pB, pC, pubSignals);
        uint256 used = g0 - gasleft();
        assertTrue(ok);
        emit log_named_uint("reference solidity call gas", used);
        emit log_named_uint("  vs. theoretical floor (+gas)", used - THEORETICAL_MIN_GAS);
    }
}
