/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.Global.RayClass.Integral), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.RayClass.Integral`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.RayClass.Integral

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Factoring through the ray class map -/

/-- **A homomorphism killing the trivial ray classes is constant on ray classes.**  If `φ` kills
every integral ideal of trivial ray class, then it takes the same value on any two integral ideals
in the same ray class: an ideal `J''` in the inverse class makes `φ J''` inverse to both. -/
theorem apply_eq_of_idealClass_eq {𝔪 : Modulus K} {M : Type*} [Monoid M]
    (φ : integralIdealsPrimeTo 𝔪 →* M) (hφ : ∀ J, idealClass 𝔪 J = 1 → φ J = 1)
    {J J' : integralIdealsPrimeTo 𝔪} (h : idealClass 𝔪 J = idealClass 𝔪 J') : φ J = φ J' := by
  obtain ⟨J'', hJ''⟩ := idealClass_surjective 𝔪 (idealClass 𝔪 J')⁻¹
  have h₁ : φ J * φ J'' = 1 := by
    rw [← map_mul]
    exact hφ _ (by rw [map_mul, hJ'', h, mul_inv_cancel])
  have h₂ : φ J'' * φ J' = 1 := by
    rw [← map_mul]
    exact hφ _ (by rw [map_mul, hJ'', inv_mul_cancel])
  exact left_inv_eq_right_inv h₁ h₂

/-- **Factoring through the ray class map.**  A homomorphism out of the integral ideals prime to
`𝔪` that kills every integral ideal of trivial ray class factors through `idealClass 𝔪`, which is
surjective by the moving lemma. -/
noncomputable def idealClassLift {𝔪 : Modulus K} {M : Type*} [Monoid M]
    (φ : integralIdealsPrimeTo 𝔪 →* M) (hφ : ∀ J, idealClass 𝔪 J = 1 → φ J = 1) :
    RayClassGroup 𝔪 →* M :=
  (Con.lift (Con.ker (idealClass 𝔪)) φ fun {_ _} h =>
      (Con.ker_rel _).mpr (apply_eq_of_idealClass_eq φ hφ ((Con.ker_rel _).mp h))).comp
    (Con.quotientKerEquivOfSurjective _ (idealClass_surjective 𝔪)).symm.toMonoidHom

/-- The factorization `idealClassLift φ hφ` sends the ray class of `J` to `φ J`. -/
@[simp]
theorem idealClassLift_idealClass {𝔪 : Modulus K} {M : Type*} [Monoid M]
    (φ : integralIdealsPrimeTo 𝔪 →* M) (hφ : ∀ J, idealClass 𝔪 J = 1 → φ J = 1)
    (J : integralIdealsPrimeTo 𝔪) : idealClassLift φ hφ (idealClass 𝔪 J) = φ J := by
  have hJ : (Con.quotientKerEquivOfSurjective _ (idealClass_surjective 𝔪)).symm
      (idealClass 𝔪 J) = J :=
    -- Mathlib states no evaluation lemma for `Con.quotientKerEquivOfSurjective`; on the class of
    -- `J` it is `Con.kerLift`, which evaluates to `idealClass _ J` by definition.
    (MulEquiv.symm_apply_eq _).mpr (rfl)
  rw [idealClassLift, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hJ, Con.lift_coe]

/-- Composing `idealClassLift φ hφ` with the ray class map gives back `φ`. -/
theorem idealClassLift_comp_idealClass {𝔪 : Modulus K} {M : Type*} [Monoid M]
    (φ : integralIdealsPrimeTo 𝔪 →* M) (hφ : ∀ J, idealClass 𝔪 J = 1 → φ J = 1) :
    (idealClassLift φ hφ).comp (idealClass 𝔪) = φ :=
  MonoidHom.ext (idealClassLift_idealClass φ hφ)

/-- **Homomorphisms out of the ray class group are determined on ideals.**  Two homomorphisms out
of `RayClassGroup 𝔪` that agree on the ray classes of the integral ideals prime to `𝔪` are equal,
since every ray class is such a class by the moving lemma. -/
@[ext]
theorem RayClassGroup.hom_ext {𝔪 : Modulus K} {M : Type*} [Monoid M]
    {f g : RayClassGroup 𝔪 →* M} (h : f.comp (idealClass 𝔪) = g.comp (idealClass 𝔪)) : f = g :=
  MonoidHom.ext fun c ↦ by
    obtain ⟨J, rfl⟩ := idealClass_surjective 𝔪 c
    exact DFunLike.congr_fun h J

/-- **Uniqueness of the factorization through the ray class map.**  A homomorphism out of
`RayClassGroup 𝔪` whose composite with `idealClass 𝔪` is `φ` is `idealClassLift φ hφ`. -/
theorem idealClassLift_unique {𝔪 : Modulus K} {M : Type*} [Monoid M]
    {φ : integralIdealsPrimeTo 𝔪 →* M} (hφ : ∀ J, idealClass 𝔪 J = 1 → φ J = 1)
    {f : RayClassGroup 𝔪 →* M} (h : f.comp (idealClass 𝔪) = φ) : f = idealClassLift φ hφ :=
  RayClassGroup.hom_ext (by rw [h, idealClassLift_comp_idealClass])

/-- The factorization of a surjective homomorphism through the ray class map is surjective. -/
theorem idealClassLift_surjective {𝔪 : Modulus K} {M : Type*} [Monoid M]
    {φ : integralIdealsPrimeTo 𝔪 →* M} (hφ : ∀ J, idealClass 𝔪 J = 1 → φ J = 1)
    (hsurj : Function.Surjective φ) : Function.Surjective (idealClassLift φ hφ) := by
  intro c
  obtain ⟨J, rfl⟩ := hsurj c
  exact ⟨_, idealClassLift_idealClass φ hφ J⟩

/-- **The kernel of the factorization through the ray class map** consists of the ray classes of
the integral ideals killed by `φ`. -/
theorem mem_ker_idealClassLift {𝔪 : Modulus K} {M : Type*} [Monoid M]
    {φ : integralIdealsPrimeTo 𝔪 →* M} (hφ : ∀ J, idealClass 𝔪 J = 1 → φ J = 1)
    {c : RayClassGroup 𝔪} :
    c ∈ (idealClassLift φ hφ).ker ↔
      ∃ J : integralIdealsPrimeTo 𝔪, idealClass 𝔪 J = c ∧ φ J = 1 := by
  constructor
  · intro hc
    obtain ⟨J, rfl⟩ := idealClass_surjective _ c
    rw [MonoidHom.mem_ker, idealClassLift_idealClass] at hc
    exact ⟨J, rfl, hc⟩
  · rintro ⟨J, rfl, hJ⟩
    rwa [MonoidHom.mem_ker, idealClassLift_idealClass]

end TauCeti.GlobalNumberFields
