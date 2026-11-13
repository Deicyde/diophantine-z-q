"""zariski-conn: check that each Prop copied into a zariski-conn file is verbatim (docstring + def,
up to the next blank line) in its owner file, and that the set_option line above the copy is the
owner's. Run from the repository root:
    python3 scratch/zariski-conn/py/verbatim_check.py"""
import re, sys
PAIRS = [
    # (name, owner file, copy file)
    ("ProperSmoothGenConnected", "scratch/frob-pieces/part_neron.lean",
     "ZInQKernel/Contrib/ZariskiConn/Basic.lean"),
    ("ProperSmoothGenConnected", "scratch/frob-pieces/part_neron.lean",
     "scratch/zariski-conn/ZariskiConnFull.lean"),
]
ok = True
for name, owner, copy in PAIRS:
    src = open(owner, encoding='utf-8').read()
    dst = open(copy, encoding='utf-8').read()
    m = re.search(r"(set_option [^\n]*\n)?/--(?:(?!-/).)*?-/\ndef " + name + r"\b.*?(?=\n\n)", src, re.S)
    if m is None:
        print(name, "NOT FOUND in", owner); ok = False; continue
    blk = m.group(0)
    so = m.group(1) or ""
    body = blk[blk.rfind("/--", 0, blk.find("\ndef ")):]
    v = (so + body) in dst
    print(f"{name}: set_option+docstring+def ({len((so+body).splitlines())} lines) verbatim in {copy}: {v}")
    ok &= v
print("ALL VERBATIM" if ok else "MISMATCH")
