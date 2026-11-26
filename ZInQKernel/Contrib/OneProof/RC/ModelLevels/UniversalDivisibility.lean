import ZInQKernel.Contrib.OneProof.RC.ModelLevels.AffineDivisor
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Specialization from a domain to an arbitrary coefficient ring -/

namespace WeierstrassCurve.ModelLevels

open Polynomial ModelTorsion

private abbrev Coefficients := MvPolynomial (Fin 5) ℤ

private noncomputable def universalEquation : WeierstrassCurve Coefficients :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
    MvPolynomial.X 3, MvPolynomial.X 4⟩

private theorem universal_discriminant_ne_zero : universalEquation.Δ ≠ 0 := by
  let f := MvPolynomial.eval₂Hom (RingHom.id ℤ) ![0, 0, 0, 1, 0]
  intro hz
  have h : (universalEquation.map f).Δ = 0 := by rw [WeierstrassCurve.map_Δ, hz, map_zero]
  norm_num [universalEquation, f, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] at h

/-- The two divisor-level equations over an arbitrary base ring are obtained by
specializing divisibility over the universal integer domain with the level and
discriminant inverted. -/
theorem divisor_polynomials_dvd {A : Type*} [CommRing A] (W : WeierstrassCurve A)
    [W.IsElliptic] {d N : ℕ} (hN : IsUnit (N : A)) (hdN : d ∣ N) :
    xPolynomial W d ∣ xPolynomial W N ∧ W.preΨ' d ∣ W.preΨ' N := by
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    exact ⟨⟨1, Subsingleton.elim _ _⟩, ⟨1, Subsingleton.elim _ _⟩⟩
  | inr _ =>
    have hN0 : N ≠ 0 := by
      rintro rfl
      exact hN.ne_zero (by simp)
    let z : Coefficients := (N : Coefficients) * universalEquation.Δ
    let U := Localization.Away z
    have hz : z ≠ 0 := by
      apply mul_ne_zero _ universal_discriminant_ne_zero
      exact_mod_cast hN0
    haveI : IsDomain U := Localization.Away.isDomain hz
    let i : Coefficients →+* U := algebraMap _ _
    have hUnitProduct : IsUnit (i (N : Coefficients) * i universalEquation.Δ) := by
      rw [← map_mul]
      exact IsLocalization.Away.algebraMap_isUnit z
    let V := universalEquation.map i
    haveI : V.IsElliptic := ⟨by
      rw [WeierstrassCurve.map_Δ]
      exact isUnit_of_mul_isUnit_right hUnitProduct⟩
    have hu : IsUnit (N : U) := by
      simpa using isUnit_of_mul_isUnit_left hUnitProduct
    let f : Coefficients →+* A :=
      MvPolynomial.eval₂Hom (Int.castRingHom A) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
    have hf : universalEquation.map f = W := by
      ext <;> simp [universalEquation, f]
    have hfz : IsUnit (f z) := by
      dsimp only [z]
      rw [map_mul, map_natCast, ← WeierstrassCurve.map_Δ, hf]
      exact hN.mul W.isUnit_Δ
    let g : U →+* A := IsLocalization.Away.lift z hfz
    have hg : V.map g = W := by
      change (universalEquation.map i).map g = W
      rw [WeierstrassCurve.map_map]
      have hcomp : g.comp i = f := IsLocalization.Away.lift_comp (S := U) z hfz
      rwa [hcomp]
    constructor
    · rw [← hg, map_xPolynomial V g d, map_xPolynomial V g N]
      exact Polynomial.map_dvd g (xPolynomial_dvd V hu hdN)
    · rw [← hg, V.map_preΨ' g d, V.map_preΨ' g N]
      exact Polynomial.map_dvd g (prePsi_dvd V hu hdN)

/-- The closed inclusion of nonidentity torsion at a divisor level, written as
a restriction on coordinate algebras. -/
noncomputable def restrictAffineTorsion {A : Type*} [CommRing A] (W : WeierstrassCurve A)
    [W.IsElliptic] {d N : ℕ} (hN : IsUnit (N : A)) (hdN : d ∣ N) :
    AffineTorsionAlgebra W N →ₐ[A] AffineTorsionAlgebra W d :=
  affineDivisorMap W hdN (divisor_polynomials_dvd W hN hdN).2

/-- Restriction to the divisor level is a closed immersion on spectra. -/
theorem restrictAffineTorsion_surjective {A : Type*} [CommRing A] (W : WeierstrassCurve A)
    [W.IsElliptic] {d N : ℕ} (hN : IsUnit (N : A)) (hdN : d ∣ N) :
    Function.Surjective (restrictAffineTorsion W hN hdN) :=
  affineDivisorMap_surjective W hdN _

#print axioms universal_discriminant_ne_zero
#print axioms divisor_polynomials_dvd
#print axioms restrictAffineTorsion_surjective

end WeierstrassCurve.ModelLevels
