# pragma version ~=0.5.0a1
# pragma nonreentrancy off
"""
@title ERC-20 Mock for the Vyper / Snekmate storage-layout optimization demo
@notice Imports snekmate's ERC-20 module unchanged. The mock just initialises
        a name/symbol/decimals and grants the deployer the minter role.

        Pairs with `mock_optimized.runtime.hex` (a peephole-patched copy of
        this contract's runtime bytecode) deployed via vm.etch in the
        Foundry tests. The patcher (script/patch.py) replaces every
        balanceOf-keccak-prefix site with a direct address-as-slot access.
"""

from ethereum.ercs import IERC20
from ethereum.ercs import IERC20Detailed
implements: IERC20
implements: IERC20Detailed

from snekmate.tokens.interfaces import IERC20Permit
implements: IERC20Permit

from snekmate.utils.interfaces import IERC5267
implements: IERC5267

from snekmate.auth import ownable
initializes: ownable

from snekmate.tokens import erc20
initializes: erc20[ownable := ownable]

# @notice Export every external entry-point from erc20 + the ownable
#         module's owner getter + EIP-5267 metadata. This is what the
#         test suite calls.
exports: (
    erc20.balanceOf,
    erc20.allowance,
    erc20.totalSupply,
    erc20.is_minter,
    erc20.nonces,
    erc20.name,
    erc20.symbol,
    erc20.decimals,
    erc20.transfer,
    erc20.approve,
    erc20.transferFrom,
    erc20.burn,
    erc20.burn_from,
    erc20.permit,
    erc20.DOMAIN_SEPARATOR,
    erc20.mint,
    erc20.set_minter,
    erc20.transfer_ownership,
    erc20.renounce_ownership,
    ownable.owner,
    erc20.eip712Domain,
)


@deploy
@payable
def __init__():
    """
    @notice Hard-coded metadata: name "Token", symbol "TKN", 18 decimals.
            EIP-712 domain name "Token", version "1". Same on both
            backends so log emission and permit derivations match.
    """
    ownable.__init__()
    erc20.__init__("Token", "TKN", 18, "Token", "1")
