"""coeff-ext: move dsThm966's locator from Diamond-Shurman 9.6.6 to Deligne-Serre 1974 Thm 4.1 (4.1.1), p. 514,
in the Lean docstrings (comment-only edits; no declaration changes). Run from the repository root."""
H = 'ZInQKernel/OneProof/H/'
EDITS = [
 ('TailS.lean',
  "/-- **LEAF (Deligne–Serre, in Diamond–Shurman's form).** Deligne–Serre, *Formes modulaires de\n"
  "poids 1*, Ann. Sci. ÉNS 7 (1974), Thm 4.1; Diamond–Shurman Thm 9.6.6 (numbering UNVERIFIED): for a\n",
  "/-- **LEAF (Deligne–Serre 1974 Thm 4.1).** Deligne–Serre, *Formes modulaires de\n"
  "poids 1*, Ann. Sci. ÉNS (4) 7 (1974), Thm 4.1, display (4.1.1), p. 514 (UNVERIFIED; Diamond–Shurman\n"
  "Thm 9.6.6 restates it): for a\n"),
 ('TailT.lean',
  "`DSThm966` (Deligne–Serre, via Diamond–Shurman Thm 9.6.6) only. -/",
  "`DSThm966` (Deligne–Serre 1974 Thm 4.1 (4.1.1), p. 514) only. -/"),
 ('TailT.lean',
  "Diamond–Shurman 9.6.5 and 9.6.6); H-10 also from",
  "Diamond–Shurman 9.6.5 and Deligne–Serre 1974 Thm 4.1 (4.1.1)); H-10 also from"),
 ('TailX.lean',
  "`r14` from Diamond–Shurman's Thms 9.6.5-9.6.6, `t23` from",
  "`r14` from Diamond–Shurman's Thm 9.6.5 and Deligne–Serre 1974 Thm 4.1 (4.1.1), `t23` from"),
 ('TailX.lean',
  "/-- hodge-split, H-22: Diamond–Shurman Thm 9.6.6 (`k = 1`, Deligne–Serre Thm 4.1). -/",
  "/-- hodge-split, H-22: Deligne–Serre 1974 Thm 4.1 (4.1.1), p. 514 (`k = 1`; Diamond–Shurman Thm 9.6.6\n"
  "  restates it). -/"),
 ('TailZ6.lean',
  "(Deligne–Serre 1974 Thm 4.1; Diamond–Shurman Thm 9.6.6).** A semisimple",
  "(Deligne–Serre 1974 Thm 4.1 (4.1.1), p. 514).** A semisimple"),
]
for f, old, new in EDITS:
    p = H + f
    s = open(p).read()
    assert s.count(old) == 1, (f, old[:60])
    open(p, 'w').write(s.replace(old, new))
print('applied', len(EDITS), 'edits')
