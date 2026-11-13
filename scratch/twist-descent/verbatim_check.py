"""twist-descent: mechanical verbatim checks for scratch/twist-descent/TwistDescent.lean.
Run from the repository root: python3 scratch/twist-descent/verbatim_check.py"""
import re
out = open('scratch/twist-descent/TwistDescent.lean').read()
kf = open('scratch/kf-glue/KfGlue.lean').read()
new = open('scratch/kf-glue/New.lean').read()
# 1. KfGlue.lean minus its import lines is a verbatim block of the output
kf_lines = kf.split('\n')
n = max(i for i, l in enumerate(kf_lines) if l.startswith('import '))
body = '\n'.join(kf_lines[n + 1:])
print("KfGlue.lean body (after its imports) verbatim in TwistDescent.lean:", body in out)
print("KfGlue.lean imports all present:", all(l in out.split('\n') for l in kf_lines[:n + 1] if l.startswith('import ')))
# 2. New.lean (owner file of TwistDescent) is verbatim inside KfGlue.lean
print("scratch/kf-glue/New.lean verbatim in KfGlue.lean:", new in kf)
# 3. the statements: owner text == text in the checked file
for name in ["TwistDescent", "SemilinearTwistAt", "bcEnd"]:
    m = re.search(r"/--(?:(?!/--).)*?-/\n(?:noncomputable )?def " + name + r"\b.*?(?=\n\n)", new, re.S)
    print(name, "found in owner New.lean:", m is not None,
          "| verbatim in TwistDescent.lean:", m is not None and m.group(0) in out,
          "| occurrences of 'def %s' in TwistDescent.lean:" % name,
          len(re.findall(r"\ndef " + name + r"\b|\nnoncomputable def " + name + r"\b", out)))
# 4. the theorem has exactly the Prop as its type
print("theorem twistDescent : TwistDescent present:", "theorem twistDescent : TwistDescent :=" in out)
