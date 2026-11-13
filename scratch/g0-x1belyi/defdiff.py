# Compare the declarations X1BelyiOnModel depends on: Split.lean copy vs kernel modules.
import re, sys
names = ["structure AbVar", "abbrev Qj", "def Ej ", "abbrev Kbar", "def EjBar", "def xCoord",
         "def fieldX1", "class IsCurve", "abbrev SpecQ", "def IsX1Model", "abbrev RatPt",
         "structure IsJacobian", "def IsJ1", "def IsBelyiFunction", "def BelyiX1",
         "noncomputable def ffStructMap", "noncomputable def ffAlgebra", "def dim "]
def grab(text, key):
    out = []
    lines = text.split("\n")
    for i, l in enumerate(lines):
        if key in l and not l.lstrip().startswith("--"):
            blk = [l]
            for m in lines[i+1:]:
                if m.strip() == "" or m.startswith("/--") or m.startswith("theorem") or m.startswith("instance") or m.startswith("def ") or m.startswith("@[") or m.startswith("end ") or m.startswith("abbrev") or m.startswith("namespace") or m.startswith("attribute"):
                    break
                blk.append(m)
            out.append("\n".join(blk))
    return out
split = open(sys.argv[1]).read()
kern = "".join(open(f).read() + "\n" for f in sys.argv[2:])
for k in names:
    a, b = grab(split, k), grab(kern, k)
    same = [x for x in a if x in b]
    print(f"{k!r}: split {len(a)}, kernel {len(b)}, identical blocks {len(same)}")
