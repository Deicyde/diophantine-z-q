"""Apply the rv-loc-leaves repairs to a copy of scratch/h-decomposition/Leaves.lean.
Usage: python3 patch_leaves.py SRC DST"""
import re, sys
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
n_edits = 0

def rep(old, new, count=1):
    global s, n_edits
    c = s.count(old)
    assert c == count, (c, old[:80])
    s = s.replace(old, new)
    n_edits += 1

# 1. T27 in PkgI3: add QMDichotomyYu after QMDichotomy, switch I3Leaves field.
old_qm = """            Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

/-- The package as one hypothesis. -/
structure I3Leaves : Prop where
  faltingsSemisimple : FaltingsSemisimple
  faltingsTate : FaltingsTate
  tateModuleFree : TateModuleFree
  homFreeFinite : HomFreeFinite
  charPolyIndepOfEll : CharPolyIndepOfEll
  poincare : PoincareReducibility
  qmDichotomy : QMDichotomy
"""
new_qm = """            Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

/-- `ℍ[ℚ, a, b]` is indefinite: `ℍ[ℚ,a,b] ⊗ ℝ ≅ M₂(ℝ)`, i.e. not both `a < 0` and `b < 0`. -/
def QuatIndefinite (a b : ℚ) : Prop := 0 < a ∨ 0 < b

/-- **T27 (rv-loc-leaves repair): the QM dichotomy with Yu's hypothesis.** Chia-Fu Yu,
*Endomorphism algebras of QM abelian surfaces*, J. Pure Appl. Algebra 217 (2013), Thm 1.1
(journal p. 907; arXiv:1210.1125 Thm 1.1; checked by the locator audit): over an algebraically
closed field of characteristic `0`, if an **indefinite** quaternion division algebra `B = (a, b)_ℚ`
embeds in `End⁰(A)` for an abelian surface `A`, then `End⁰(A) ≅ B` or `End⁰(A) ≅ M₂(ℚ(√d))`,
`d < 0` (Yu adds that `ℚ(√d)` splits `B`; dropped). `QMDichotomy` above (no "indefinite") is a
consequence of Mumford §21 only, not of Yu's theorem. -/
def QMDichotomyYu : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
    ∀ a b : ℚ, QuatIndefinite a b → (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
      Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
        Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
          ∃ d : ℚ, d < 0 ∧
            Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

theorem qmDichotomyYu_of_qmDichotomy (h : QMDichotomy) : QMDichotomyYu :=
  fun k _ _ _ A hA a b _ hdiv hemb => h k A hA a b hdiv hemb

/-- The project's `B = (2, -3)` is indefinite. -/
theorem quatIndefinite_two_neg_three : QuatIndefinite 2 (-3) := Or.inl (by norm_num)

/-- The use at step A9 / G5 (`B = (2,-3)`) needs only the repaired form. -/
theorem qmDichotomy_B6 (h : QMDichotomyYu) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbVar k) (hA : A.dim = 2) (hdiv : ∀ x : ℍ[ℚ, 2, -3], x ≠ 0 → IsUnit x)
    (hemb : Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] End0 A)) :
    Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) ∨
      ∃ d : ℚ, d < 0 ∧
        Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) :=
  h k A hA 2 (-3) quatIndefinite_two_neg_three hdiv hemb

/-- The package as one hypothesis. -/
structure I3Leaves : Prop where
  faltingsSemisimple : FaltingsSemisimple
  faltingsTate : FaltingsTate
  tateModuleFree : TateModuleFree
  homFreeFinite : HomFreeFinite
  charPolyIndepOfEll : CharPolyIndepOfEll
  poincare : PoincareReducibility
  qmDichotomy : QMDichotomyYu
"""
rep(old_qm, new_qm)

# 2. ObjBridge: Yu form over the shared layer, I3Leaves field, iff.
old_ob = """theorem qmDichotomy_iff : QMDichotomy ↔ PkgI3.QMDichotomy :=
  ⟨fun h k _ _ _ A => h k (toGrp A), fun h k _ _ _ A _ => h k (ofGrp A)⟩
"""
new_ob = old_ob + """
/-- **T27 with Yu's hypothesis** (rv-loc-leaves) over the shared layer. -/
def QMDichotomyYu : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Grp (Over (Spec (.of k))))
    [IsAbelianVariety A], dim A = 2 →
    ∀ a b : ℚ, PkgI3.QuatIndefinite a b → (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
      Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
        Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
          ∃ d : ℚ, d < 0 ∧
            Nonempty (End0 A ≃ₐ[ℚ]
              Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

theorem qmDichotomyYu_iff : QMDichotomyYu ↔ PkgI3.QMDichotomyYu :=
  ⟨fun h k _ _ _ A => h k (toGrp A), fun h k _ _ _ A _ => h k (ofGrp A)⟩
"""
rep(old_ob, new_ob)
rep("""  poincare : PoincareReducibility
  qmDichotomy : QMDichotomy

theorem i3Leaves_iff""", """  poincare : PoincareReducibility
  qmDichotomy : QMDichotomyYu

theorem i3Leaves_iff""")
rep("      qmDichotomy_iff.mp h.7⟩,", "      qmDichotomyYu_iff.mp h.7⟩,")
rep("      qmDichotomy_iff.mpr h.7⟩⟩", "      qmDichotomyYu_iff.mpr h.7⟩⟩")

# 3. HSyn bundle field.
rep("  t27 : PkgI3.QMDichotomy\n", "  t27 : PkgI3.QMDichotomyYu\n")

# 4. Placeholder docstrings from Placeholders.lean.
P = open(sys.argv[3]).read() if len(sys.argv) > 3 else open('scratch/rv-loc-leaves/Placeholders.lean').read()
for name in ["R02_BabaGranath", "R05_GonzalezRotger", "R16_EichlerShimuraJ1", "R17_Carayol", "R22_Pazuki"]:
    m = re.search(r"/-- (?:(?!/--).)*?-/\nopaque " + name + r" : Prop", P, re.S)
    assert m, name
    newdoc = m.group(0)
    m2 = re.search(r"/-- (?:(?!/--).)*?-/\nopaque " + name + r" : Prop", s, re.S)
    assert m2, name
    s = s[:m2.start()] + newdoc + s[m2.end():]
    n_edits += 1

# 5. Docstring-only repairs.
rep("""Thm 1.0.4 = arXiv:1901.07166v2 Thm 1.0.4 (statement VERIFIED in h-a011 §1.1 from the arXiv
source; JAMS numbering UNVERIFIED)), for `p ≥ 5` (which drops the `p = 3` residual clause):""",
"""Thm 1.0.4 = arXiv:1901.07166v2 Thm 1.0.4 (statement VERIFIED in h-a011 §1.1 and by the locator
audit from the arXiv source; JAMS numbering UNVERIFIED)), for `p ≥ 5` only: at `p = 3` Pan excludes
`ρ̄|_{G_{ℚ₃}}^{ss} ≅ η ⊕ ηω`, and this leaf does not cover `p = 3`. Pan states the conclusion with
geometric Frobenius (`ρ ≅ ρ_g ⊗ ψ'`); the arithmetic-Frobenius trace form below follows with the
conjugate eigenform `g^ρ` (character `χ̄`) and `ψ = ψ'ε^{1−k}`, by `tr(M⁻¹) = tr M / det M`:""")
rep("""Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A), the
case "conductor exponent 0"; theorem letter VERIFIED from N5 L9778's locator, content
UNVERIFIED).""", """Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A), pp. 409-411, the
case "conductor exponent 0"; coverage of every `ℓ ≠ p`, including `p ∣ N` and `ℓ = 2`, read by the
locator audit; newform conductor `a(π_p) = v_p(N)`, Casselman 1973, locator UNVERIFIED).""")
rep("""Ann. 278 (1987) for `k ≥ 2` (level `ℓ ∣ N` UNVERIFIED there); Saito, Invent. Math. 129 (1997)
(pst at `ℓ`, every level); Kato, Astérisque 295 (2004) §9.4 (de Rham, every level);""",
"""Ann. 278 (1987) for `k ≥ 2` (level `ℓ ∣ N` UNVERIFIED there); Saito, Invent. Math. 129 (1997)
(pst at `ℓ`, every level; UNVERIFIED); Kato, Astérisque 295 (2004) §§9.2-9.4, (9.2.2) pp. 187-188
(de Rham, every level, newforms; checked by the locator audit), with `NewformOfEigenform` and
Brauer–Nesbitt for general cuspidal eigenforms (hence `ρ.IsSemisimple`);""")
rep("""Brauer–Nesbitt): a semisimple `ρ` attached to a weight-one eigenform has finite image.
Consequence form.""", """Brauer–Nesbitt, their Lemma 3.2): a semisimple `ρ` attached to a weight-one eigenform has finite
image. Consequence form. Semisimplicity cannot be dropped (a non-split extension can have the same
traces; locator audit, R15).""")
rep("""`(e₀, e_∞, e_{−16/27}) = (4, 6, 2)` (A2).""",
"""`(e₀, e_∞, e_{−16/27}) = (4, 6, 2)`: the orbifold orders of `Γ*` (Baba–Granath §3.1, p. 740),
which are the indices of `Y₃ → P¹_j` because the level-3 group is torsion-free
(`GlueRepo.TorsionFree`); they are not indices of the degree-4 map `X₆ → X₆/W` (index 2).""")
open(dst, 'w').write(s)
print("edits", n_edits)
