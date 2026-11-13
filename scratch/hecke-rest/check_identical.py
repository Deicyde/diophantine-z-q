"""Check that the verbatim line ranges copied into scratch/hecke-rest/*.lean equal their sources.
Run from the repository root: ~/pyenv/bin/python -I scratch/hecke-rest/check_identical.py"""
src = open("scratch/ts-hecke/TSHecke.lean", encoding="utf-8").read().split("\n")
ip = open("scratch/image-plane/AlgDepProof.lean", encoding="utf-8").read().split("\n")
def block(lines, a, b):
    return "\n".join(lines[a - 1:b])
checks = {
    "FibreSizes.lean": [(src, 3563, 4606), (src, 5511, 5717), (src, 6132, 6135), (src, 6154, 6213),
                        (src, 6215, 6227), (src, 6553, 6577)],
    "NoVert.lean": [(src, 6, 889), (src, 3427, 3437)],
    "CurveChart.lean": [(src, 6, 889), (ip, 15, 171), (ip, 277, 322), (src, 4613, 5002),
                        (src, 5010, 5173), (src, 5725, 5858), (src, 6444, 6455), (src, 6526, 6551)],
    "HeckeRestAll.lean": [(src, 1, 7109), (ip, 15, 171), (ip, 277, 322)],
}
ok = True
for f, rs in checks.items():
    text = open("scratch/hecke-rest/" + f, encoding="utf-8").read()
    for (lines, a, b) in rs:
        if block(lines, a, b) not in text:
            ok = False
            print("MISSING", f, a, b)
# the targets, verbatim
for name in ["def HeckeFibreSizes", "def HeckeNoVertRam", "def CurveNormChart", "def CurveChartInf",
             "def CurveGaloisChart"]:
    i = next(k for k, l in enumerate(src) if l.startswith(name))
    j = i
    while src[j].strip():
        j += 1
    tgt = "\n".join(src[i:j])
    found = [f for f in checks if tgt in open("scratch/hecke-rest/" + f, encoding="utf-8").read()]
    print(name, "found verbatim in", found)
print("ALL OK" if ok else "FAILED")
