"""Generate ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Heegner.lean from scratch/gz-heegner/Heegner.lean."""
import re, sys
s = open('scratch/gz-heegner/Heegner.lean').read()
s = s[:s.index("#print axioms")].rstrip() + "\n"
header = open('scratch/gz-heegner/header.txt').read()
s = header + s[s.index("noncomputable section"):]
s = s.replace("/-! gz-heegner development file (single file; see log.md). -/\n", "")
s += open('scratch/gz-heegner/footer.txt').read()
open('ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Heegner.lean', 'w').write(s)
print(len(s.encode()))
