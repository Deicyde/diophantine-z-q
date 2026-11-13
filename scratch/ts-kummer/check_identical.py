# KummerTS.lean must be PropTSGlue.lean verbatim (two extra import lines after its imports),
# followed by the ts-kummer appendix.
orig = open("scratch/prop-ts-glue/PropTSGlue.lean").read()
fin = open("scratch/ts-kummer/KummerTS.lean").read()
EXTRA = "import Mathlib.RingTheory.Localization.AtPrime.Extension\nimport Mathlib.RingTheory.Flat.TorsionFree\n"
ol = orig.split("\n")
expected = "\n".join(ol[:2]) + "\n" + EXTRA + "\n".join(ol[2:])
print("PREFIX IDENTICAL" if fin.startswith(expected) else "DIFFERENT", len(expected))
