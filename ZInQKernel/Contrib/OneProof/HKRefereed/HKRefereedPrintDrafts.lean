import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
import ZInQKernel.Contrib.OneProof.HKRefereed.HKRefereedConsumed

/-!
# Two candidate arithmetic rank statements, pending a reading

Neither draft is a verified printed theorem. The algebraic parametrization and CM point are
represented by the existing analytic model; the comparison with the printed objects remains
glue. The proposed statements retain only the rank conclusion over the Heegner field.
-/

noncomputable section

namespace ZInQ.Manuscript.HKRefereed

open NumberField TauCeti.ClassFieldTheory WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST

open Classical in
/-- A conductor-one Heegner trace over `K`, in the existing analytic parametrization model.
The input in the Hilbert class field is pinned to the image of a CM point of discriminant
`discr K`. The point over `K` is pinned to the sum of its actual Galois conjugates. -/
def IsHeegnerTrace (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (P : (E.baseChange K).toAffine.Point) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (c : ℚ),
    (∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) ∧
    IsLatticeOf E Lat ∧ IsNonCMLattice Lat ∧ IsParamScale (newformLevel E) f Lat (c : ℂ) ∧
    ∃ (A B C : ℤ) (ι : hilbertClassField K →ₐ[ℚ] ℂ)
      (y : (E.baseChange (hilbertClassField K)).toAffine.Point),
      IsHeegnerForm (newformLevel E) (discr K) A B C ∧
      Affine.Point.map (W' := E.toAffine) ι y = phiAn E f Lat c (cmPoint A B (discr K)) ∧
      Affine.Point.map (W' := E.toAffine) (IsScalarTower.toAlgHom ℚ K (hilbertClassField K)) P =
        ∑ σ : hilbertClassField K ≃ₐ[K] hilbertClassField K,
          Affine.Point.map (W' := E.toAffine) (σ.toAlgHom.restrictScalars ℚ) y

open Classical in
/-- The split Heegner setting and the arithmetic non-torsion hypothesis, restricted to the
non-CM parametrization model and fields without extra units. -/
def HeegnerRankInput (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (P : (E.baseChange K).toAffine.Point) : Prop :=
  Module.finrank ℚ K = 2 ∧ IsTotallyComplex K ∧ discr K ≠ -3 ∧ discr K ≠ -4 ∧
  0 < newformLevel E ∧ (∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p) ∧
  IsHeegnerTrace E K P ∧ ¬ IsOfFinAddOrder P

open Classical in
/-- Common candidate rank conclusion over the Heegner field, with Sha omitted. -/
def HeegnerRankStatement : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (P : (E.baseChange K).toAffine.Point),
    HeegnerRankInput E K P → Module.rank ℤ (E.baseChange K).toAffine.Point = 1

/-- **Draft pending a reading; locator UNVERIFIED.** Kolyvagin, *Euler systems*, in
*The Grothendieck Festschrift*, Vol. II, Progr. Math. 87 (1990), arithmetic rank-one theorem
(exact page and numbering unverified). Check the parametrization, the trace, and whether this
conclusion is stated in this generality or only via a theorem with extra prime hypotheses. -/
def KolyvaginEulerSystemsRankDraft : Prop := HeegnerRankStatement

/-- **Draft pending a reading; locator UNVERIFIED.** Gross, *Kolyvagin's work on modular elliptic
curves*, in *L-functions and Arithmetic*, LMS Lecture Note Ser. 153 (1991), opening arithmetic
theorem (possibly Theorem 1.1, UNVERIFIED). Check the stated rank or finite-index conclusion
and distinguish it from the prime-by-prime result proved in the exposition. -/
def GrossHeegnerRankDraft : Prop := HeegnerRankStatement

/-- GLUE, open: at a headline call, supply the actual split imaginary quadratic field, modular
parametrization, CM point and non-torsion trace required by the arithmetic theorem. -/
def PoleNonTorsionHeegnerTrace : Prop :=
  ∀ (ℓ : ℕ) (hℓ : 0 < ℓ),
    letI : (curve (ℓ : ℚ)).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
    Squarefree ℓ → ℓ % 12 = 11 → (PoleRC.SelM ℓ).ncard = 8 →
    PoleS12.IsModular (curve (ℓ : ℚ)) → AnalyticRankOne (curve (ℓ : ℚ)) →
    ∃ (K : Type) (hK : Field K), letI : Field K := hK
      ∃ hNF : NumberField K, letI : NumberField K := hNF
        ∃ P : ((curve (ℓ : ℚ)).baseChange K).toAffine.Point, HeegnerRankInput (curve (ℓ : ℚ)) K P

open Classical in
/-- GLUE, open: the rank-one line over the Heegner field contributes to the untwisted curve
over `ℚ`. A comparison of the Heegner trace with its conjugate modulo torsion would give this
orientation. Rank one after quadratic base change does not specify it by itself. -/
def PoleHeegnerRankDescent : Prop :=
  ∀ (ℓ : ℕ) (hℓ : 0 < ℓ),
    letI : (curve (ℓ : ℚ)).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
    Squarefree ℓ → ℓ % 12 = 11 → (PoleRC.SelM ℓ).ncard = 8 →
    AnalyticRankOne (curve (ℓ : ℚ)) →
    ∀ (K : Type) [Field K] [NumberField K] (P : ((curve (ℓ : ℚ)).baseChange K).toAffine.Point),
      HeegnerRankInput (curve (ℓ : ℚ)) K P →
      Module.rank ℤ ((curve (ℓ : ℚ)).baseChange K).toAffine.Point = 1 →
      Module.rank ℤ (curve (ℓ : ℚ)).toAffine.Point = 1

/-- Conditional wiring shared by the two drafts. The two application gaps are explicit. -/
theorem hkConsumed_of_heegnerRank (hRank : HeegnerRankStatement)
    (hTrace : PoleNonTorsionHeegnerTrace) (hDescent : PoleHeegnerRankDescent) : HKConsumed := by
  intro ℓ hℓ hsf h12 h8 hM hA
  obtain ⟨K, hK, hNF, P, hP⟩ := hTrace ℓ hℓ hsf h12 h8 hM hA
  let _ : Field K := hK
  let _ : NumberField K := hNF
  have : (curve (ℓ : ℚ)).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  have hr := hRank (curve (ℓ : ℚ)) K P hP
  exact PoleRC.exists_not_isOfFinAddOrder_of_rank (hDescent ℓ hℓ hsf h12 h8 hA K P hP hr)

end ZInQ.Manuscript.HKRefereed

#print axioms ZInQ.Manuscript.HKRefereed.hkConsumed_of_heegnerRank
