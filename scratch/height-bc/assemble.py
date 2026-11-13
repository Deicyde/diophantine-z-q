"""Assemble the two integration checks from Final.lean (run from the repository root).
H5WithBC.lean = scratch/h5-glue/H5Final.lean (verbatim, #print lines dropped) + Final.lean body + Part D.
G0WithBC.lean = Final.lean body + one alias + scratch/g0-stablebc/Main.part (verbatim, #print lines
dropped) + Part E."""

def body(path):
    s = open(path).read().split("\n", 1)[1]
    return "\n".join(l for l in s.split("\n") if not l.startswith("#print axioms"))

fin = body('scratch/height-bc/Final.lean')

h5 = open('scratch/h5-glue/H5Final.lean').read()
h5 = h5[:h5.index("end ZInQ.H5Glue\n\n#print axioms ZInQ.H5Glue.heightAntitone")] + "end ZInQ.H5Glue\n"
partD = open('scratch/height-bc/PartD.lean.part').read()
open('scratch/height-bc/H5WithBC.lean', 'w').write(
    h5 + "\n/-! # height-bc (`scratch/height-bc/Final.lean`, copied) -/\n"
    + fin.replace("\nend ZInQ.HeightBC\n", "\n") + partD)

mp = "\n".join(l for l in open('scratch/g0-stablebc/Main.part').read().split("\n")
               if not l.startswith("#print axioms"))
partE = open('scratch/height-bc/PartE.lean.part').read()
open('scratch/height-bc/G0WithBC.lean', 'w').write(
    "import ZInQKernel.HDecomp.Faltings.Leaves\n\n/-! # height-bc's `Final.lean`, then g0-stablebc's "
    "`Main.part` (verbatim) over the kernel's\nobjects through one alias, then the bridge to g0-split's "
    "piece `StableHeightBaseChange` -/\n" + fin + partE.split("%%MAINPART%%")[0] + mp
    + partE.split("%%MAINPART%%")[1])
