# Builds scratch/kummer-comp/KummerComp.lean = scratch/ts-kummer/KummerTS.lean (verbatim)
# + the appendix taken from Core.lean (imports and the dev-only verbatim copies removed;
# `Qbar` written out as `AlgebraicClosure ℚ`, which is what every `Qbar` abbrev unfolds to)
# + FinalTail.lean.part.
orig = open("scratch/ts-kummer/KummerTS.lean").read()
core = open("scratch/kummer-comp/Core.lean").read()
cl = core.split("\n")
i = 0
while cl[i].startswith("import"):
    i += 1
app = "\n".join(cl[i:])
a = app.index("namespace KummerComp\n\n/-! ## Verbatim copies (dev only) -/")
b = app.index("end KummerComp", a) + len("end KummerComp")
app = app[:a] + app[b:]
# drop the dev #print axioms lines (re-printed in the tail)
app = "\n".join(l for l in app.split("\n") if not l.startswith("#print axioms"))
app = app.replace("open Polynomial IntermediateField\n", "open Polynomial IntermediateField\nopen PropTSGlue\n", 1)
app = app.replace("Qbar", "(AlgebraicClosure ℚ)")
app = "\n/-! # kummer-comp appendix (namespace `KummerComp`) -/\n" + app
TAIL = open("scratch/kummer-comp/FinalTail.lean.part").read()
open("scratch/kummer-comp/KummerComp.lean", "w").write(orig.rstrip("\n") + "\n" + app + "\n" + TAIL)
print("written")
