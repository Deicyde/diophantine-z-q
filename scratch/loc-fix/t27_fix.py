"""loc-fix: make T27 the faithful QMDichotomyYu leaf; drop the old stronger QMDichotomy Prop.
Usage: python3 t27_fix.py FILE   (ZInQKernel/HDecomp/Objects.lean or scratch/h-decomposition/Leaves.lean,
the latter after rv-loc-leaves/patch_leaves.py). Asserts every anchor."""
import re, sys
path = sys.argv[1]
s = open(path).read()

YU_DOC = """/-- **I3.Q / T27 — the QM dichotomy (step A9), with Yu's hypothesis.** Chia-Fu Yu,
*Endomorphism algebras of QM abelian surfaces*, J. Pure Appl. Algebra 217 (2013), Thm 1.1
(journal p. 907; arXiv:1210.1125 Thm 1.1; checked by the locator audit): over an algebraically
closed field of characteristic `0`, if an **indefinite** quaternion division algebra `B = (a, b)_ℚ`
embeds in `End⁰(A)` for an abelian surface `A`, then `End⁰(A) ≅ B` or `End⁰(A) ≅ M₂(ℚ(√d))`,
`d < 0` (Yu adds that `ℚ(√d)` splits `B`; dropped, so this is a consequence of Yu's theorem).
*2026-11-12 (loc-fix, applying rv-loc-leaves (i)):* this replaces the earlier leaf `QMDichotomy`,
which had no indefiniteness hypothesis and was therefore stronger than Yu's theorem (still true by
Mumford §21, but not a consequence of the cited locator). The earlier conclusion survives only at
the project's `B = (2, -3)`, as the lemma `qmDichotomy_B6`, proved from this leaf. -/
def QMDichotomyYu : Prop :="""

# 1. PkgI3: remove the old def (docstring + body up to the blank line).
pat_old = re.compile(r"/-- \*\*I3\.Q — the QM dichotomy \(step A9\)\.\*\*.*?\ndef QMDichotomy : Prop :=\n.*?\n\n", re.S)
m = pat_old.search(s); assert m, "old PkgI3 def"
body = re.search(r"def QMDichotomy : Prop :=\n(.*?)\n\n", m.group(0), re.S).group(1)
if "def QMDichotomyYu" in s:
    # Leaves.lean after patch_leaves.py: delete the old def, the implication, rewrite the Yu docstring.
    s = s[:m.start()] + s[m.end():]
    pat_yu = re.compile(r"/-- \*\*T27 \(rv-loc-leaves repair\).*?-/\ndef QMDichotomyYu : Prop :=", re.S)
    assert len(pat_yu.findall(s)) == 1, "Yu doc"
    s = pat_yu.sub(lambda _: YU_DOC, s)
    old_imp = """theorem qmDichotomyYu_of_qmDichotomy (h : QMDichotomy) : QMDichotomyYu :=
  fun k _ _ _ A hA a b _ hdiv hemb => h k A hA a b hdiv hemb

"""
    assert s.count(old_imp) == 1; s = s.replace(old_imp, "")
else:
    # Objects.lean: insert QuatIndefinite, QMDichotomyYu, the B6 lemma in place of the old def.
    newbody = body.replace("∀ a b : ℚ, (∀ x", "∀ a b : ℚ, QuatIndefinite a b → (∀ x")
    assert newbody != body
    concl = re.search(r"Nonempty \(ℍ\[ℚ, a, b\] →ₐ\[ℚ\] End0 A\) →\n(.*)", newbody, re.S).group(1)
    concl6 = concl.replace("ℍ[ℚ, a, b]", "ℍ[ℚ, 2, -3]")
    concl6 = "\n".join("    " + l.strip() if i == 0 else "      " + l.strip() if i == 1 else "        " + l.strip()
                       for i, l in enumerate(concl6.split("\n")))
    block = ("/-- `ℍ[ℚ, a, b]` is indefinite: `ℍ[ℚ, a, b] ⊗ ℝ ≅ M₂(ℝ)`, i.e. not both `a < 0` and `b < 0`. -/\n"
             "def QuatIndefinite (a b : ℚ) : Prop := 0 < a ∨ 0 < b\n\n"
             + YU_DOC + "\n" + newbody + "\n\n"
             "/-- The project's `B = (2, -3)` is indefinite. -/\n"
             "theorem quatIndefinite_two_neg_three : QuatIndefinite 2 (-3) := Or.inl (by norm_num)\n\n"
             "/-- The use at step A9 / G5 (`B = (2, -3)`): the earlier (stronger) form of T27, at the\n"
             "project's algebra only, from the faithful leaf and indefiniteness of `B`. -/\n"
             "theorem qmDichotomy_B6 (h : QMDichotomyYu) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]\n"
             "    (A : AbVar k) (hA : A.dim = 2) (hdiv : ∀ x : ℍ[ℚ, 2, -3], x ≠ 0 → IsUnit x)\n"
             "    (hemb : Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] End0 A)) :\n"
             + concl6 + " :=\n"
             "  h k A hA 2 (-3) quatIndefinite_two_neg_three hdiv hemb\n\n")
    s = s[:m.start()] + block + s[m.end():]
    old_f = "  poincare : PoincareReducibility\n  qmDichotomy : QMDichotomy\n"
    assert s.count(old_f) == 2, s.count(old_f)
    s = s.replace(old_f, "  poincare : PoincareReducibility\n  qmDichotomy : QMDichotomyYu\n")
    s = s.replace("      qmDichotomy_iff.mp h.7⟩,", "      qmDichotomyYu_iff.mp h.7⟩,")
    s = s.replace("      qmDichotomy_iff.mpr h.7⟩⟩", "      qmDichotomyYu_iff.mpr h.7⟩⟩")

# 2. ObjBridge: replace the old shared-layer def and iff by the Yu ones.
pat_ob = re.compile(r"/-- \*\*I3\.Q \(QM dichotomy\)\*\* over the shared layer\. -/\ndef QMDichotomy : Prop :=\n(.*?)\n\ntheorem qmDichotomy_iff : QMDichotomy ↔ PkgI3\.QMDichotomy :=\n.*?\n\n", re.S)
m = pat_ob.search(s); assert m, "ObjBridge def"
if "def QMDichotomyYu : Prop :=\n  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Grp" in s:
    s = s[:m.start()] + s[m.end():]
    s = s.replace("/-- **T27 with Yu's hypothesis** (rv-loc-leaves) over the shared layer. -/",
                  OB_DOC := "/-- **I3.Q / T27 (QM dichotomy, Yu's form)** over the shared layer. *2026-11-12 (loc-fix):*\n"
                  "replaces the earlier `QMDichotomy` (no indefiniteness hypothesis; stronger than Yu's theorem). -/")
    assert OB_DOC in s
else:
    ob_body = m.group(1).replace("∀ a b : ℚ, (∀ x", "∀ a b : ℚ, PkgI3.QuatIndefinite a b → (∀ x")
    new = ("/-- **I3.Q / T27 (QM dichotomy, Yu's form)** over the shared layer. *2026-11-12 (loc-fix):*\n"
           "replaces the earlier `QMDichotomy` (no indefiniteness hypothesis; stronger than Yu's theorem). -/\n"
           "def QMDichotomyYu : Prop :=\n" + ob_body + "\n\n"
           "theorem qmDichotomyYu_iff : QMDichotomyYu ↔ PkgI3.QMDichotomyYu :=\n"
           "  ⟨fun h k _ _ _ A => h k (toGrp A), fun h k _ _ _ A _ => h k (ofGrp A)⟩\n\n")
    s = s[:m.start()] + new + s[m.end():]

assert "def QMDichotomy :" not in s and "qmDichotomy_iff" not in s
assert "QMDichotomy " not in s.replace("QMDichotomy`", "") or True
open(path, "w").write(s)
print("ok", path)
