# Hand repairs of wrap.py's line breaks that Lean rejects (run after adopt5b.py and wrap.py).
# Each is (module, old text, new text); only whitespace changes.
D = 'ZInQKernel/HDecomp/Textbook/'
FIX = [
 ('Different.lean',
  "  rw [Ideal.ramificationIdx'_spec (n := j) (by rw [hj]) (by rw [hj, maximalIdeal_pow_le_iff];\n"
  "      omega)]",
  "  rw [Ideal.ramificationIdx'_spec (n := j) (by rw [hj])\n"
  "    (by rw [hj, maximalIdeal_pow_le_iff]; omega)]"),
]
for m, old, new in FIX:
    s = open(D + m).read()
    if old in s: s = s.replace(old, new); open(D + m, 'w').write(s)
    else: assert new in s, (m, old)
