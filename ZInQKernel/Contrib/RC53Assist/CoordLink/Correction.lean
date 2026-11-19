import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1aG

/-!
# Correction in the fraction field

The manuscript's correction belongs to the completed coefficient group algebra,
not necessarily to the power-series group algebra.  The relevant locators are
ex:arith-common-coordinate, TeX 4196–4229, especially 4155 and 4229 for poles,
and ex:arith-coordinate, TeX 3877–3892, for the original coordinate.

The correction factors have unit sign evaluations in the completed coefficient
ring.  This is enough for cancellation in its fraction field.  It gives no
power-series-unit lift.  The equivalences below isolate the original-coordinate
identification; they do not assert that this identification follows from
correction data alone.  No additional printed proposition is used.
-/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.CoordLink

open Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Contrib.CloudB3RC53.CoordLink
open ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.Wiring (UTildeRep OrigCoordLink)
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)
open ZInQ.Manuscript.RC.SelmerComplex (NewPlaces)

/-- The manuscript's factors are units after sign evaluation in the completed
coefficient ring (TeX 4219–4224), even if their coefficients have poles. -/
theorem signEval_eta_isUnit {b : ℕ} {ι : Type} [DecidableEq ι]
    (Q : Finset ι) (v g : ι → MonoidAlgebra OO (SignGroup b)) (x : Addr b)
    (hsign : ∀ q ∈ Q, Determinant.signEval (sgnChar x) (g q) = 1 ∨
      Determinant.signEval (sgnChar x) (g q) = -1) :
    IsUnit (Determinant.signEval (sgnChar x) (Central.eta Q v g)) := by
  classical
  have h := Central.map_eta
    (Determinant.signEval (O := OO) (sgnChar x)).toRingHom Q v g hsign
  change IsUnit ((Determinant.signEval (O := OO) (sgnChar x)).toRingHom
    (Central.eta Q v g))
  rw [h]
  exact IsUnit.prod_iff.mpr fun q _ => Determinant.isUnit_one_add_two_mul_OO _

/-- Consequently the correction can be cancelled in the fraction field. -/
theorem evK_eta_ne_zero {b : ℕ} {ι : Type} [DecidableEq ι]
    (Q : Finset ι) (v g : ι → MonoidAlgebra OO (SignGroup b)) (x : Addr b)
    (hsign : ∀ q ∈ Q, Determinant.signEval (sgnChar x) (g q) = 1 ∨
      Determinant.signEval (sgnChar x) (g q) = -1) :
    evK (sgnChar x) (Central.eta Q v g) ≠ 0 := by
  rw [Determinant.evK_apply]
  exact ((signEval_eta_isUnit Q v g x hsign).map
    (algebraMap OO (FractionRing OO))).ne_zero

/-- A correction-shaped factor with a pole is still a unit of the completed ring. -/
theorem poleFactor_isUnit : IsUnit (1 + 2 * Determinant.tInv) :=
  Determinant.isUnit_one_add_two_mul_OO _

/-- A concrete obstruction to a power-series lift: modulo four the coefficient
of degree minus one is two.  This illustrates the scope of TeX 4155 and 4229;
it does not claim that every unused-prime factor has this particular value. -/
theorem poleFactor_not_in_powerSeries :
    ¬ ∃ a : Lam, algebraMap Lam OO a = 1 + 2 * Determinant.tInv := by
  rintro ⟨a, ha⟩
  have h := congrArg (fun y : OO => (Determinant.proj 2 y).coeff (-1)) ha
  rw [Determinant.proj_algebraMap, map_add, map_mul, map_one, map_ofNat,
    Determinant.proj_tInv] at h
  norm_num [HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_mul_single, PowerSeries.coeff_coe] at h
  change (0 : ZMod 4) = (2 : LaurentSeries (ZMod 4)).coeff 0 at h
  rw [show (2 : LaurentSeries (ZMod 4)) = HahnSeries.single 0 (2 : ZMod 4) by
    rw [← HahnSeries.C_apply, map_ofNat], HahnSeries.coeff_single_same] at h
  exact (by decide : (0 : ZMod 4) ≠ 2) h

/-- There is no coefficient-compatible homomorphism from the completed ring to
rational power series: the variable is a unit in the former and not in the latter.
Comparisons therefore have to use a common localization or fraction field. -/
theorem no_completed_to_powerSeries :
    ¬ ∃ f : OO →+* PowerSeries ℚ_[2],
      ∀ a : Lam, f (algebraMap Lam OO a) = ιQ a := by
  rintro ⟨f, hf⟩
  have h := Determinant.isUnit_t.map f
  rw [hf] at h
  have hX : ιQ (PowerSeries.X : Lam) = PowerSeries.X := by simp [ιQ]
  rw [hX, PowerSeries.isUnit_iff_constantCoeff] at h
  simp at h

/-- The fraction-field coordinate pinned by a representation of the corrected
coordinate and by a nonzero evaluated correction.  No integral-unit lift is used. -/
def relaxedFromCorrection {b : ℕ} (η : MonoidAlgebra OO (SignGroup b))
    (e : Addr b → ℕ) (g : Addr b → Lam) (x : Addr b) : FractionRing OO :=
  uK (e x) (g x) / evK (sgnChar x) η

/-- The pinned fraction-field coordinate is independent of the representation. -/
theorem relaxedFromCorrection_independent {ℓ : ℕ} {D : RCData ℓ} {F : Family}
    (η : MonoidAlgebra OO (SignGroup F.b)) {e e' : Addr F.b → ℕ}
    {g g' : Addr F.b → Lam} (h : UTildeRep D F e g) (h' : UTildeRep D F e' g') :
    relaxedFromCorrection η e g = relaxedFromCorrection η e' g' := by
  funext x
  unfold relaxedFromCorrection
  rw [uK_rep_indep h h' x]

/-- Multiplication by the original correction recovers every representation.
This pins a fraction-field value, not its provenance as a Selmer coordinate. -/
theorem correctedIsEta_fraction {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (η : MonoidAlgebra OO (SignGroup F.b)) (e₀ : Addr F.b → ℕ)
    (g₀ : Addr F.b → Lam) (h₀ : UTildeRep D F e₀ g₀)
    (hη : ∀ x, evK (sgnChar x) η ≠ 0) :
    CorrectedIsEta D F η (relaxedFromCorrection η e₀ g₀) := by
  intro e g hrep x
  rw [uK_rep_indep hrep h₀ x]
  unfold relaxedFromCorrection
  rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ (hη x), mul_one]

section Original

variable {K : Type} [Field K] [NumberField K]
  {S S' : Set (HeightOneSpectrum (𝓞 K))} {hS : S ⊆ S'}
  [Fintype (NewPlaces K S S')] [DecidableEq (NewPlaces K S S')]
  {b dK hK cE tK : ℕ}

/-- Without nonvanishing of the correction, the corrected comparison detects
exactly the unmasked original-coordinate equality.  A representation is required
because the corrected comparison alone is vacuous when there are no representations. -/
theorem origCoordLink_iff_masked {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (urel : Addr F.b → FractionRing OO)
    (hη : CorrectedIsEta D F η urel) (e₀ : Addr F.b → ℕ) (g₀ : Addr F.b → Lam)
    (h₀ : UTildeRep D F e₀ g₀) :
    OrigCoordLink D F M z lam hz hlam η ↔
      ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
        evK (sgnChar x) η = 0 ∨ urel x = kmOrig M z lam hz hlam x := by
  constructor
  · intro h x hΔ
    by_cases he : evK (sgnChar x) η = 0
    · exact Or.inl he
    · right
      exact mul_left_cancel₀ he ((hη e₀ g₀ h₀ x).symm.trans (h e₀ g₀ h₀ x hΔ))
  · intro h e g hrep x hΔ
    change uK (e x) (g x) = evK (sgnChar x) η * kmOrig M z lam hz hlam x
    rw [hη e g hrep x]
    rcases h x hΔ with he | hu
    · rw [he, zero_mul, zero_mul]
    · rw [hu]

/-- The exact residual gap after the corrected-coordinate comparison: the
relaxed coordinate is the original determinant coordinate.  Only fraction-field
nonvanishing at the relevant addresses is needed, not a power-series unit. -/
theorem relIsKMG_iff_origCoordLink {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (urel : Addr F.b → FractionRing OO)
    (hη : CorrectedIsEta D F η urel) (e₀ : Addr F.b → ℕ) (g₀ : Addr F.b → Lam)
    (h₀ : UTildeRep D F e₀ g₀)
    (hne : ∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 → evK (sgnChar x) η ≠ 0) :
    ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M urel z lam hz hlam ↔
      OrigCoordLink D F M z lam hz hlam η := by
  rw [origCoordLink_iff_masked D F M z lam hz hlam η urel hη e₀ g₀ h₀]
  constructor
  · intro h x hΔ
    exact Or.inr (h x hΔ)
  · intro h x hΔ
    exact (h x hΔ).resolve_left (hne x hΔ)

/-- The unit-free (4.7) route leaves exactly the original-coordinate comparison.
The hypotheses are the already-proved correction bridge's ratio, inverse,
support-triangle, and common-coordinate identities.  The correction's
fraction-field nonvanishing is proved from its original completed-ring factors. -/
theorem relIsKMG_iff_origCoordLink_of_47 {ℓ : ℕ} (D : RCData ℓ) (F : Family)
    (M : Identification2G K S S' hS F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    {ι : Type} [DecidableEq ι] (Q : Finset ι)
    (v gq l eq ei : ι → MonoidAlgebra OO (SignGroup F.b))
    (ε : Addr F.b → ι → FractionRing OO) (urel uprim : Addr F.b → FractionRing OO)
    [∀ x : Addr F.b, DecidablePred fun q => evK (sgnChar x) (gq q) = 1]
    (hsign : ∀ x, ∀ q ∈ Q, evK (sgnChar x) (gq q) = 1 ∨ evK (sgnChar x) (gq q) = -1)
    (hratio : ∀ x, ∀ q ∈ Q, evK (sgnChar x) (l q) * evK (sgnChar x) (ei q) ^ 2 =
      1 + 2 * evK (sgnChar x) (v q))
    (hinv : ∀ x, ∀ q ∈ Q, evK (sgnChar x) (eq q) * evK (sgnChar x) (ei q) = 1)
    (h47 : ∀ x, (∏ q ∈ Q with evK (sgnChar x) (gq q) = 1, evK (sgnChar x) (l q)) * urel x =
      (∏ q ∈ Q with evK (sgnChar x) (gq q) = 1, evK (sgnChar x) (eq q) ^ 2 * ε x q) * uprim x)
    (hcommon : ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep D F e g → ∀ x,
      uK (e x) (g x) = (∏ q ∈ Q with evK (sgnChar x) (gq q) = 1, ε x q) * uprim x)
    (e₀ : Addr F.b → ℕ) (g₀ : Addr F.b → Lam) (h₀ : UTildeRep D F e₀ g₀) :
    ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M urel z lam hz hlam ↔
      OrigCoordLink D F M z lam hz hlam (Central.eta Q v gq) := by
  have hsignO : ∀ x, ∀ q ∈ Q, Determinant.signEval (sgnChar x) (gq q) = 1 ∨
      Determinant.signEval (sgnChar x) (gq q) = -1 := by
    intro x q hq
    rcases hsign x q hq with h | h
    · left
      apply IsFractionRing.injective OO (FractionRing OO)
      simpa only [Determinant.evK_apply, map_one] using h
    · right
      apply IsFractionRing.injective OO (FractionRing OO)
      simpa only [Determinant.evK_apply, map_neg, map_one] using h
  exact relIsKMG_iff_origCoordLink D F M z lam hz hlam _ urel
    (correctedIsEta_of_47 D F Q v gq l eq ei ε urel uprim hsign hratio hinv h47 hcommon)
    e₀ g₀ h₀ (fun x _ => evK_eta_ne_zero Q v gq x (hsignO x))

end Original

set_option pp.universes false

end ZInQ.Contrib.RC53Assist.CoordLink
