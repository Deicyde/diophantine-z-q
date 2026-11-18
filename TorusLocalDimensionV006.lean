import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Scheme

/-!
# The local dimension of the split torus at the identity

* Every maximal ideal of `k[X_1, …, X_n]` has height `n` (induction on `n`: a maximal ideal of
  `A[X]` contracts to a maximal ideal of the Jacobson ring `A`, and then its height grows by one).
* The coordinate ring of `𝔾_m^r` is `k[X_i^{±1}] = k[X][(∏ X_i)^{-1}]`; its identity character
  `X_i ↦ 1` has maximal kernel `𝔪₁` of height `r`, so the local ring of `𝔾_m^r` at the identity,
  i.e. the stalk of `Spec k[X_i^{±1}]` at `𝔪₁`, has Krull dimension `r`.
-/

noncomputable section
set_option autoImplicit false

open Ideal

namespace TorusDimension

/-- **Every maximal ideal of `k[X_1, …, X_n]` has height `n`.** -/
theorem height_maximal_mvPolynomial (k : Type*) [Field k] :
    ∀ (n : ℕ) (P : Ideal (MvPolynomial (Fin n) k)) [P.IsMaximal], P.height = n
  | 0, P, _ => by
    have h1 : (P.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 0) k) :=
      Ideal.height_le_ringKrullDim_of_isPrime
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
      at h1
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_zero, add_zero] at h1
    have h2 : P.height ≤ 0 := by exact_mod_cast h1
    rw [Nat.cast_zero]
    exact nonpos_iff_eq_zero.mp h2
  | n + 1, P, _ => by
    let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let P' : Ideal (Polynomial (MvPolynomial (Fin n) k)) := P.map e
    have hP' : P'.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hh : P'.height = P.height := RingEquiv.height_map e P
    let p : Ideal (MvPolynomial (Fin n) k) := P'.comap Polynomial.C
    have hp : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P'
    have hlo : P'.LiesOver p := ⟨by
      show P'.comap Polynomial.C =
        P'.comap (algebraMap (MvPolynomial (Fin n) k) (Polynomial (MvPolynomial (Fin n) k)))
      rw [Polynomial.algebraMap_eq]⟩
    have h := Polynomial.height_eq_height_add_one p P'
    rw [height_maximal_mvPolynomial k n p] at h
    rw [← hh, h, Nat.cast_succ]

variable (k : Type) [Field k] (r : ℕ)

/-- `∏ X_i`. -/
abbrev torusProd : MvPolynomial (Fin r) k := ∏ i, MvPolynomial.X i

/-- The coordinate ring `k[X_i^{±1}]` of the split torus `𝔾_m^r`. -/
abbrev TorusRing : Type := Localization.Away (torusProd k r)

/-- The evaluation of a coordinate family of units, on polynomials. -/
def evalUnits {R : Type} [CommRing R] [Algebra k R] (t : Fin r → Rˣ) :
    MvPolynomial (Fin r) k →ₐ[k] R :=
  MvPolynomial.aeval (fun i => (t i : R))

theorem evalUnits_prod_isUnit {R : Type} [CommRing R] [Algebra k R] (t : Fin r → Rˣ) :
    IsUnit (evalUnits k r t (torusProd k r)) := by
  rw [map_prod]
  refine isUnit_iff_exists_inv.mpr ⟨∏ i, ((t i)⁻¹ : Rˣ), ?_⟩
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [evalUnits]

/-- **The torus coordinate character** `X_i ↦ t_i` for units `t_i` of a `k`-algebra. -/
def torusLift {R : Type} [CommRing R] [Algebra k R] (t : Fin r → Rˣ) :
    TorusRing k r →ₐ[k] R :=
  IsLocalization.Away.liftAlgHom (torusProd k r) (evalUnits_prod_isUnit k r t)

theorem torusLift_X {R : Type} [CommRing R] [Algebra k R] (t : Fin r → Rˣ) (i : Fin r) :
    torusLift k r t (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r) (MvPolynomial.X i)) =
      t i := by
  rw [torusLift, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  simp [evalUnits]

/-- The identity character `X_i ↦ 1`. -/
def oneChar : TorusRing k r →ₐ[k] k := torusLift k r (fun _ => 1)

theorem oneChar_surjective : Function.Surjective (oneChar k r) :=
  fun c => ⟨algebraMap k (TorusRing k r) c, (oneChar k r).commutes c⟩

/-- The maximal ideal of the identity of `𝔾_m^r`. -/
def idealOne : Ideal (TorusRing k r) := RingHom.ker (oneChar k r).toRingHom

instance idealOne_isMaximal : (idealOne k r).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (oneChar_surjective k r)

/-- **The identity ideal of `𝔾_m^r` has height `r`**, from the polynomial heights. -/
theorem height_idealOne : (idealOne k r).height = r := by
  rw [← IsLocalization.height_under (Submonoid.powers (torusProd k r)) (idealOne k r)]
  have hsurj : Function.Surjective
      ((oneChar k r).toRingHom.comp (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r))) :=
    fun c => ⟨MvPolynomial.C c, by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact (oneChar k r).commutes c⟩
  have hmax : ((idealOne k r).under (MvPolynomial (Fin r) k)).IsMaximal := by
    show (Ideal.comap (algebraMap (MvPolynomial (Fin r) k) (TorusRing k r))
      (RingHom.ker (oneChar k r).toRingHom)).IsMaximal
    rw [RingHom.comap_ker]
    exact RingHom.ker_isMaximal_of_surjective _ hsurj
  exact height_maximal_mvPolynomial k r _

/-- **The local ring of `𝔾_m^r` at the identity has dimension `r`** (any localization at the
identity ideal). -/
theorem ringKrullDim_localization_one (A : Type) [CommRing A] [Algebra (TorusRing k r) A]
    [IsLocalization.AtPrime A (idealOne k r)] : ringKrullDim A = r := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (idealOne k r) A, height_idealOne]
  rfl

/-- The identity point of `Spec k[X_i^{±1}]`. -/
def onePoint : PrimeSpectrum (TorusRing k r) := ⟨idealOne k r, inferInstance⟩

/-- **The stalk of `Spec k[X_i^{±1}]` at the identity has Krull dimension `r`.** -/
theorem ringKrullDim_stalk_one :
    ringKrullDim ((AlgebraicGeometry.Spec (CommRingCat.of (TorusRing k r))).presheaf.stalk
      (onePoint k r)) = r := by
  have hloc : IsLocalization.AtPrime
      ((AlgebraicGeometry.structurePresheafInCommRingCat (TorusRing k r)).stalk (onePoint k r))
      (onePoint k r).asIdeal := inferInstance
  have hloc' : IsLocalization.AtPrime
      ((AlgebraicGeometry.structurePresheafInCommRingCat (TorusRing k r)).stalk (onePoint k r))
      (idealOne k r) := hloc
  have h : ringKrullDim ((AlgebraicGeometry.structurePresheafInCommRingCat (TorusRing k r)).stalk
      (onePoint k r)) = r := ringKrullDim_localization_one k r _
  exact h

end TorusDimension
