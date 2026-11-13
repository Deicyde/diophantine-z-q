"""frob-pieces: check that each Prop copied into a frob-pieces file is verbatim (docstring + def,
up to the next blank line) in its owner file. Run from the repository root:
    python3 scratch/frob-pieces/py/verbatim_check.py"""
import re, sys
PAIRS = [
    # (name, owner file, copy file)
    ("SmoothGeomConnIntegral", "scratch/alg-frob-red/part_red.lean",
     "ZInQKernel/Contrib/FrobPieces/SmoothGeomConnIntegral.lean"),
    ("HasAbelianSchemeAway", "scratch/neron-lg/NeronLG.lean", "scratch/frob-pieces/part_neron.lean"),
    ("AbVarSpreadsOut", "scratch/neron-lg/NeronLG.lean", "scratch/frob-pieces/part_neron.lean"),
    ("GoodRedCofinite", "scratch/alg-frob-red/part_red.lean", "scratch/frob-pieces/FrobPieces.lean"),
    ("SmoothGeomConnIntegral", "scratch/alg-frob-red/part_red.lean", "scratch/frob-pieces/FrobPieces.lean"),
]
EXTRA = [l.split('|') for l in sys.argv[1:]]  # name|owner|copy
ok = True
for name, owner, copy in PAIRS + [tuple(e) for e in EXTRA]:
    src = open(owner, encoding='utf-8').read()
    dst = open(copy, encoding='utf-8').read()
    m = re.search(r"/--(?:(?!-/).)*?-/\ndef " + name + r"\b.*?(?=\n\n)", src, re.S)
    if m is None:
        print(name, "NOT FOUND in", owner); ok = False; continue
    blk = m.group(0)
    # keep only the last docstring (the one directly before the def)
    blk = blk[blk.rfind("/--", 0, blk.find("\ndef ")):]
    v = blk in dst
    print(f"{name}: docstring+def ({len(blk.splitlines())} lines) verbatim in {copy}: {v}")
    ok &= v
print("ALL VERBATIM" if ok else "MISMATCH")
