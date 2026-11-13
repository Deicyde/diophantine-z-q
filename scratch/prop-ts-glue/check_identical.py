# 1. The first part of PropTSGlue.lean must be scratch/prop-ts/PropTS.lean, byte for byte.
# 2. The t-purity3 proof (PurityDim2.lean from origin/wip/t-purity3, saved as
#    t-purity3-PurityDim2.orig.txt) must be contained verbatim, minus `import Mathlib` and the
#    trailing `#print axioms` lines.
a=open("scratch/prop-ts/PropTS.lean").read()
b=open("scratch/prop-ts-glue/PropTSGlue.lean").read()
print("PREFIX IDENTICAL" if b.startswith(a) else "DIFFERENT", len(a))
c=open("scratch/prop-ts-glue/t-purity3-PurityDim2.orig.txt").read().split("\n")[1:]
c="\n".join(l for l in c if not l.startswith("#print axioms")).rstrip()
print("PURITY COPY CONTAINED" if c in b else "PURITY COPY DIFFERENT", len(c))
