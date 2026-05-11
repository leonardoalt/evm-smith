#!/usr/bin/env python3
"""
Vyper ERC-20 balance-access bytecode peephole patcher.

Reads the compiled runtime of `src/mock.vy` and replaces every site
matching Vyper's `self.balanceOf[addr]` keccak prefix with a direct
`SLOAD(addr) / SSTORE(addr, value)` access. Allowance, nonce, and
is_minter accesses (which use different slot-id immediates) are left
untouched. The patch is length-preserving so JUMPDEST addresses and
the deploy-code-embedded runtime length immediate stay valid.

## The peephole

Original (15 bytes, slot=BALANCE_SLOT, key-mem-offset=P, op in
{SLOAD, SSTORE}):

    60 <slot>          PUSH1 slot
    60 <P>             PUSH1 P
    51                 MLOAD          ; load address from mem[P]
    60 20              PUSH1 0x20
    52                 MSTORE         ; mem[0x20] = address
    5f                 PUSH0
    52                 MSTORE         ; mem[0x00] = slot
    60 40              PUSH1 0x40
    5f                 PUSH0
    20                 KECCAK256      ; keccak256(slot ++ address)
    <op>               SLOAD or SSTORE

Patched (15 bytes, length-preserved):

    5b 5b 5b 5b 5b     10 × JUMPDEST  ; no-op padding
    5b 5b 5b 5b 5b
    60 <P>             PUSH1 P
    51                 MLOAD          ; load address from mem[P]
    19                 NOT            ; addr -> ~addr (avoids slot collision)
    <op>               SLOAD or SSTORE

Why `NOT`? Vyper's storage layout puts named state variables at low
slots: `ownable.owner` is at slot 0x01, `totalSupply` at 0x04, etc.
Using the raw address as a slot would collide with these for tiny
addresses (the original failure mode: `mint(0x01, v)` overwriting
the contract owner). `NOT(addr)` maps any 160-bit address to a slot
above 2^160 - 2^160 = (2^256 - 1) - addr, which never collides with
Vyper's named slots (max ~16) or with any keccak-derived slot (a
keccak hash that high-bits-collides with `~addr` requires breaking
cryptographic preimage resistance). It's one byte and just-as-
injective.

JUMPDEST is the cheapest legal no-op (1 gas, doesn't touch stack/
memory/storage, doesn't halt). Padding is at the start, so the
optimization's real work happens last.

## Discrimination

We don't pattern-match purely on shape — the allowance / nonce /
is_minter buckets emit the same shape with a different slot id. The
slot id immediate (byte 1 of the pattern) is the discriminator: only
sites where it matches the configured `BALANCE_SLOT` are patched.

The expected site count is computed from the source AST by counting
every `self.balanceOf[...]` access in the Vyper input. The patcher
fails closed if the bytecode-side count doesn't match the AST count.

## Where the balance-slot id comes from

Vyper's `-f layout` JSON reports `balanceOf.slot: 1`, but the bytecode
actually emits slot id `0x02` — a known +1 offset (Vyper accounts for
the implicit ownable module's slot before erc20's). We resolve it by
reading the `balanceOf` getter's PUSH1 immediate directly from the
bytecode.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Vyper's balanceOf-via-public-getter selector.
BALANCE_OF_SELECTOR = "70a08231"

# The 15-byte keccak prefix pattern with `<slot>`, `<P>`, and `<op>`
# captured. The constants embedded are Vyper's exact emission:
#   PUSH1 <slot>; PUSH1 <P>; MLOAD; PUSH1 0x20; MSTORE; PUSH0; MSTORE;
#   PUSH1 0x40; PUSH0; KECCAK256; <op>
KECCAK_PREFIX_RE = re.compile(
    r"60([0-9a-f]{2})"           # PUSH1 slot
    r"60([0-9a-f]{2})"           # PUSH1 P (memory offset for key)
    r"516020525f5260405f20"      # MLOAD; PUSH1 0x20; MSTORE; PUSH0; MSTORE;
                                 # PUSH1 0x40; PUSH0; KECCAK256
    r"([0-9a-f]{2})"             # op (SLOAD = 54, SSTORE = 55, or other)
)

JUMPDEST = "5b"


def find_balance_slot_id(rt_hex: str) -> int:
    """Find the slot id Vyper emits for `balanceOf` by inspecting the
    public getter's prologue.

    Vyper's selector dispatcher uses `XOR + JUMPI` where a non-zero
    XOR (selector mismatch) jumps to the *next* case; matched selectors
    fall through to the function body. After the balanceOf selector
    check, the prologue has a calldata-length JUMPI revert-guard, then
    `PUSH1 0x04; CALLDATALOAD; DUP1; PUSH1 0xa0; SHR; PUSH2 <bad>; JUMPI;
    PUSH1 0x40; MSTORE` (an address-padding clean-up that stores the
    argument at mem[0x40]). Right after, the balance-slot keccak prefix
    starts with `PUSH1 <slot>` — that's the slot id we want.
    """
    idx = rt_hex.find("63" + BALANCE_OF_SELECTOR)
    if idx < 0:
        raise RuntimeError(f"balanceOf selector {BALANCE_OF_SELECTOR} not found")
    # Walk the fall-through prologue: skip the XOR/JUMPI mismatch
    # branch, the calldatasize guard, the arg loading, and the
    # mstore-at-mem[0x40]. The next byte is `60 <slot>`.
    # In practice that's "60 40 52 60 <slot>" right before the
    # keccak prefix.
    tail = rt_hex[idx * 1 :]
    m = re.search(r"6040525260([0-9a-f]{2})60[0-9a-f]{2}51", tail)
    if not m:
        # Alternative shape: just look for the first keccak prefix that
        # appears anywhere after the balanceOf selector — its slot
        # immediate is the balanceOf slot id.
        m2 = KECCAK_PREFIX_RE.search(tail)
        if not m2:
            raise RuntimeError("no keccak prefix found after balanceOf selector")
        return int(m2.group(1), 16)
    return int(m.group(1), 16)


def count_balance_accesses_in_source(src_path: Path) -> int:
    """Count `self.balanceOf[...]` access sites in the Vyper source.
    The patcher cross-checks this against the bytecode-side site count
    and fails closed on mismatch.

    Includes accesses across all imported Vyper modules — we walk the
    `import` graph by following `from <pkg>.<mod> import <name>` lines
    and recursing into each module file. For Snekmate this finds
    `lib/snekmate/src/snekmate/tokens/erc20.vy`.
    """
    # Naive: count all `self.balanceOf[` in the main source.
    # For the snekmate-imported balance accesses, recurse manually.
    seen = set()
    pending = [src_path]
    total = 0
    while pending:
        p = pending.pop()
        if p in seen or not p.exists():
            continue
        seen.add(p)
        text = p.read_text()
        # Count `self.balanceOf[` and (the public getter generated by Vyper
        # also counts as one access — but it shares the same pattern
        # site with `self.balanceOf[...]` in the source).
        total += text.count("self.balanceOf[")
        # Follow imports.
        for m in re.finditer(r"from\s+(\S+)\s+import\s+(\w+)", text):
            mod = m.group(1)
            # Two layout cases:
            #   .interfaces           -> ../interfaces.vy ?
            #   ..utils               -> ../utils.vy ?
            #   ethereum.ercs         -> built-in, skip
            #   snekmate.tokens       -> needs to traverse the symlinked tree
            if mod.startswith("ethereum."):
                continue
            mod_path = _resolve_import(p, mod, m.group(2))
            if mod_path:
                pending.append(mod_path)
    # Vyper auto-generates the public getter for `balanceOf` which
    # internally does `return self.balanceOf[arg]`. That's an
    # additional access site we don't count in source (it's compiler-
    # synthesized). Add 1 for it.
    return total + 1


def _resolve_import(src_path: Path, mod: str, name: str) -> Path | None:
    """Best-effort: resolve a Vyper `from <mod> import <name>` to a
    file path. Returns None if not resolvable."""
    parts = mod.split(".")
    candidates = []
    if mod.startswith("."):
        # Relative import: count leading dots, walk up that many parents.
        leading_dots = len(mod) - len(mod.lstrip("."))
        rel = parts[leading_dots:]
        base = src_path.parent
        for _ in range(leading_dots - 1):
            base = base.parent
        candidates.append(base.joinpath(*rel, f"{name}.vy"))
        candidates.append(base.joinpath(*rel, f"{name}.vyi"))
    else:
        # Absolute under src/. Try a few roots.
        for root in (src_path.parent.parent, src_path.parent):
            candidates.append(root.joinpath(*parts, f"{name}.vy"))
            candidates.append(root.joinpath(*parts, f"{name}.vyi"))
    for c in candidates:
        if c.exists():
            return c
    return None


def patch_runtime(rt_hex: str, balance_slot: int) -> tuple[str, list[dict]]:
    """Apply the peephole to every balance-access site. Returns
    `(patched_rt_hex, [site_descriptors])`. Fails closed (raises) if
    the resulting bytecode would change length.
    """
    out: list[str] = []
    cursor = 0
    sites: list[dict] = []
    for m in KECCAK_PREFIX_RE.finditer(rt_hex):
        slot = int(m.group(1), 16)
        offset = int(m.group(2), 16)
        op = m.group(3)
        if slot != balance_slot:
            continue
        if op not in ("54", "55"):
            # Only SLOAD/SSTORE are real balance accesses; DUP1 etc.
            # are the allowance-style nested-keccak chain head.
            continue
        # Emit unchanged bytes up to the start of this site.
        out.append(rt_hex[cursor : m.start()])
        # Replacement: 10 JUMPDESTs (20 hex chars) + PUSH1 P (4) +
        # MLOAD (2) + NOT (2) + op (2) = 30 hex chars total = 15 bytes.
        replacement = (JUMPDEST * 10) + "60" + m.group(2) + "51" + "19" + op
        assert len(replacement) == 30, "replacement must be 15 bytes"
        out.append(replacement)
        sites.append(
            dict(
                pc=m.start() // 2,
                op="SLOAD" if op == "54" else "SSTORE",
                key_mem_offset=offset,
            )
        )
        cursor = m.end()
    out.append(rt_hex[cursor:])
    patched = "".join(out)
    if len(patched) != len(rt_hex):
        raise RuntimeError(
            f"length-preservation violated: orig={len(rt_hex)//2} "
            f"bytes, patched={len(patched)//2} bytes"
        )
    return patched, sites


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--artifact", required=True, help="Foundry artifact JSON (out/mock.vy/mock.json)")
    ap.add_argument("--source", required=True, help="The Vyper source (src/mock.vy)")
    ap.add_argument("--out-orig", required=True, help="Where to write the original runtime hex")
    ap.add_argument("--out-opt", required=True, help="Where to write the patched runtime hex")
    args = ap.parse_args()

    artifact = json.loads(Path(args.artifact).read_text())
    rt = artifact["deployedBytecode"]["object"]
    if rt.startswith("0x"):
        rt = rt[2:]

    balance_slot = find_balance_slot_id(rt)
    print(f"balance slot id (from bytecode-side balanceOf getter): 0x{balance_slot:02x}")

    expected_count = count_balance_accesses_in_source(Path(args.source))
    print(f"expected balance-access sites from source AST: {expected_count}")

    patched, sites = patch_runtime(rt, balance_slot)
    print(f"patched {len(sites)} sites:")
    for s in sites:
        print(f"  pc=0x{s['pc']:04x} {s['op']:7s} key_mem=0x{s['key_mem_offset']:02x}")

    if len(sites) != expected_count:
        print(
            f"\nFATAL: site-count mismatch. bytecode found {len(sites)}, "
            f"source counted {expected_count}.\nRefusing to write a "
            f"possibly-corrupt patch — fix the discriminator first.",
            file=sys.stderr,
        )
        sys.exit(2)

    Path(args.out_orig).write_text(rt + "\n")
    Path(args.out_opt).write_text(patched + "\n")
    print(f"\nwrote original  -> {args.out_orig} ({len(rt)//2} bytes)")
    print(f"wrote optimized -> {args.out_opt} ({len(patched)//2} bytes)")
    if len(rt) == len(patched):
        print("length-preserved: ✓")


if __name__ == "__main__":
    main()
