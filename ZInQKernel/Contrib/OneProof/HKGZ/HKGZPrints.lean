import ZInQKernel.Contrib.OneProof.HKRefereed.HKRefereedPrintDrafts
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.BFH

/-!
# Printed candidates for the pole rank-one input

These are page-reading drafts in the existing analytic parametrization and
Heegner-trace dictionary. None has a LEAF rating.
-/

namespace ZInQ.Manuscript.HKGZ

open NumberField WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST

/-- The split Heegner hypothesis, with the discriminants with extra units excluded.
The level is the one used by the stage-one parametrization dictionary. -/
def SplitHeegnerField (E : WeierstrassCurve ℚ) (K : Type) [Field K] [NumberField K] : Prop :=
  Module.finrank ℚ K = 2 ∧ IsTotallyComplex K ∧ discr K ≠ -3 ∧ discr K ≠ -4 ∧
    0 < newformLevel E ∧ (∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p)

open Classical in
/-- **Printed candidate; locator UNVERIFIED.** Gross–Zagier, *Heegner points and derivatives
of L-series*, Invent. Math. 84 (1986), 225–320, elliptic-curve consequence of the height formula
for the trivial class character. In the odd-discriminant split case, a nonzero derivative of the entire
continuation of `L(E/K,s)` forces the specified conductor-one trace to have infinite order.
Check the precise hypotheses on the quotient, the discriminant, and the trace normalization. -/
def GrossZagierTraceDraft : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (P : (E.baseChange K).toAffine.Point),
    SplitHeegnerField E K → Odd (discr K) → HKRefereed.IsHeegnerTrace E K P →
    ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ s : ℂ, 3 / 2 < s.re → F s = (E.baseChange K).LSeries s) →
      deriv F 1 ≠ 0 → ¬ IsOfFinAddOrder P

/-- **Reused printed candidate; locator UNVERIFIED for this reading.**
Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990), §0, pp. 543–544, clause (ii).
The base's statement includes both clauses; only the central nonvanishing clause is read here. -/
abbrev BFHTwistNonvanishingDraft : Prop := RC.PrintsAnalytic.BFHTheorem

open Classical in
/-- **Printed candidate; locator UNVERIFIED.** Gross–Zagier (1986), or Gross,
*Kolyvagin's work on modular elliptic curves*, LMS Lecture Note Ser. 153 (1991),
comparison of the conductor-one Heegner trace with its complex conjugate.
For root number `-1`, the eigenvalue should be `+1` modulo torsion. Check the
Atkin–Lehner/cusp correction and the hypotheses of the stated comparison. -/
def HeegnerTraceConjugationDraft : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (P : (E.baseChange K).toAffine.Point),
    SplitHeegnerField E K → Odd (discr K) → HKRefereed.IsHeegnerTrace E K P → RootNumber E (-1) →
    ∀ σ : K ≃ₐ[ℚ] K, σ ≠ 1 →
      IsOfFinAddOrder (Affine.Point.map (W' := E.toAffine) σ.toAlgHom P - P)

open Classical in
/-- Open GLUE: the algebraic CM image and trace, in the dictionary used by the two
drafts. This includes the comparison of the level and analytic map with the
conductor and algebraic parametrization of the print. No rank or height assertion
is part of this input. -/
def PoleCMTraceDictionary : Prop :=
  ∀ (ℓ : ℕ) (hℓ : 0 < ℓ),
    letI : (curve (ℓ : ℚ)).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
    Squarefree ℓ → ℓ % 12 = 11 → PoleS12.IsModular (curve (ℓ : ℚ)) →
    ∀ (K : Type) [Field K] [NumberField K], SplitHeegnerField (curve (ℓ : ℚ)) K →
      Odd (discr K) →
      ∃ P : ((curve (ℓ : ℚ)).baseChange K).toAffine.Point,
        HKRefereed.IsHeegnerTrace (curve (ℓ : ℚ)) K P

end ZInQ.Manuscript.HKGZ
