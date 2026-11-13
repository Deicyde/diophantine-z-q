# Builds scratch/ts-kummer/KummerTS.lean = PropTSGlue.lean (verbatim, with two extra Mathlib imports
# inserted after its two import lines) + the appendix taken from Core.lean (dev-only verbatim copies
# of the PropTSGlue definitions removed; the appendix uses the prefix's definitions).
orig = open("scratch/prop-ts-glue/PropTSGlue.lean").read()
core = open("scratch/ts-kummer/Core.lean").read()
EXTRA = "import Mathlib.RingTheory.Localization.AtPrime.Extension\nimport Mathlib.RingTheory.Flat.TorsionFree\n"
ol = orig.split("\n")
assert ol[0].startswith("import") and ol[1].startswith("import") and not ol[2].startswith("import")
head = "\n".join(ol[:2]) + "\n" + EXTRA
body = "\n".join(ol[2:])
# appendix: drop Core's import lines, drop dev copies section
cl = core.split("\n")
i = 0
while cl[i].startswith("import"):
    i += 1
app = "\n".join(cl[i:])
a = app.index("/-! ## Verbatim copies (dev only) -/")
b = app.index("end TsKummer", a)
app = app[:a] + app[b:]
app = app.replace("open scoped TensorProduct\n", "open scoped TensorProduct\nopen PropTSRed PropTSGlue\n", 1)
app = "\n/-! # ts-kummer appendix (namespace `TsKummer`) -/\n" + app
TAIL = open("scratch/ts-kummer/FinalTail.lean.part").read()
open("scratch/ts-kummer/KummerTS.lean", "w").write(head + body + "\n" + app + "\n" + TAIL)
print("written")
