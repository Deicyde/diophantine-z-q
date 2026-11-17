import Mathlib

/-!
# G9: lifting a finite separable extension through a Henselian residue map

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Let `θ : R → Ω` be a surjective `K`-algebra map from a domain `R`, Henselian along `ker θ`, with
every `y ∉ ker θ` a unit (so `R` is local with maximal ideal `ker θ`), and `K` of characteristic
`0`. Then every `K`-embedding `ι_Ω : L → Ω` of a finite extension `L/K` lifts to `ι₀ : L → R`
(`exists_hensel_lift`), and the lift is unique and natural: for a `K`-algebra map `s : R → R` and
`τ : L → L` with `θ(s(ι₀ x)) = ι_Ω(τ x)`, `s ∘ ι₀ = ι₀ ∘ τ` (`hensel_lift_natural`).

Applied in `BdREmb.lean` to `θ⁺ : B_dR^+ → ℂ_p`: the classical embedding `ℚ̄_p ⊆ B_dR^+`
(STANDARD: Fontaine, Astérisque 223, Exp. II, §1.5; Brinon–Conrad, CMI notes, §4.4;
numbering UNVERIFIED), compatible with the Galois action.
-/

namespace ZInQ.Contrib.G9

open Polynomial

section Hensel

variable {K R Ω : Type*} [Field K] [CommRing R] [Algebra K R] [Field Ω] [Algebra K Ω]

/-- Two roots of `P` with the same residue at which `P'` does not vanish are equal. -/
theorem root_eq_of_theta [IsDomain R] (θ : R →ₐ[K] Ω) (P : K[X]) {a b : R}
    (ha : aeval a P = 0) (hb : aeval b P = 0) (hab : θ a = θ b)
    (hd : aeval (θ b) (derivative P) ≠ 0) : a = b := by
  set Q := P.map (algebraMap K R)
  obtain ⟨k, hk⟩ := Q.binomExpansion b (a - b)
  rw [add_sub_cancel, eval_map_algebraMap, eval_map_algebraMap, ha, hb, derivative_map,
    eval_map_algebraMap, zero_add] at hk
  have hfac : (a - b) * (aeval b (derivative P) + k * (a - b)) = 0 := by
    linear_combination -hk
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    apply hd
    have := congrArg θ h
    rwa [map_add, map_mul, map_sub, hab, sub_self, mul_zero, add_zero, map_zero,
      ← Polynomial.aeval_algHom_apply] at this

variable [CharZero K] {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **Hensel lift** of `ι_Ω : L → Ω` through `θ`. -/
theorem exists_hensel_lift (θ : R →ₐ[K] Ω) (hsurj : Function.Surjective θ)
    [HenselianRing R (RingHom.ker θ.toRingHom)] (hunit : ∀ y, θ y ≠ 0 → IsUnit y) (ιΩ : L →ₐ[K] Ω) :
    ∃ ι₀ : L →ₐ[K] R, ∀ x, θ (ι₀ x) = ιΩ x := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  set P := minpoly K pb.gen
  have hP : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral pb.gen)
  have hsep : P.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hroot : aeval pb.gen P = 0 := minpoly.aeval K pb.gen
  have hd : aeval (ιΩ pb.gen) (derivative P) ≠ 0 := by
    rw [Polynomial.aeval_algHom_apply]
    exact (map_ne_zero ιΩ).mpr (hsep.aeval_derivative_ne_zero hroot)
  obtain ⟨a₀, ha₀⟩ := hsurj (ιΩ pb.gen)
  obtain ⟨a, haroot, hamem⟩ := HenselianRing.is_henselian (I := RingHom.ker θ.toRingHom) (P.map (algebraMap K R))
    (hP.map _) a₀ (by
      change θ _ = 0
      rw [eval_map_algebraMap, ← Polynomial.aeval_algHom_apply, ha₀,
        Polynomial.aeval_algHom_apply, hroot, map_zero])
    (by
      apply IsUnit.map
      apply hunit
      rwa [derivative_map, eval_map_algebraMap, ← Polynomial.aeval_algHom_apply, ha₀])
  have haP : aeval a P = 0 := by
    rw [← eval_map_algebraMap]; exact haroot
  have hθa : θ a = ιΩ pb.gen := by
    change θ (a - a₀) = 0 at hamem
    rw [map_sub, sub_eq_zero] at hamem
    rw [← ha₀]; exact hamem
  refine ⟨pb.lift a haP, ?_⟩
  have : θ.comp (pb.lift a haP) = ιΩ := pb.algHom_ext (by
    rw [AlgHom.comp_apply, PowerBasis.lift_gen, hθa])
  intro x
  rw [← this, AlgHom.comp_apply]

/-- **Naturality of the Hensel lift.** -/
theorem hensel_lift_natural [IsDomain R] (θ : R →ₐ[K] Ω) (ιΩ : L →ₐ[K] Ω) (ι₀ : L →ₐ[K] R)
    (hι₀ : ∀ x, θ (ι₀ x) = ιΩ x) (s : R →ₐ[K] R) (τ : L →ₐ[K] L)
    (hs : ∀ x, θ (s (ι₀ x)) = ιΩ (τ x)) (x : L) : s (ι₀ x) = ι₀ (τ x) := by
  let pb := Field.powerBasisOfFiniteOfSeparable K L
  set P := minpoly K pb.gen
  have hsep : P.Separable := Algebra.IsSeparable.isSeparable K pb.gen
  have hroot : aeval pb.gen P = 0 := minpoly.aeval K pb.gen
  have hτroot : aeval (τ pb.gen) P = 0 := by
    rw [Polynomial.aeval_algHom_apply, hroot, map_zero]
  have key : (s.comp ι₀) = ι₀.comp τ := by
    apply pb.algHom_ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    refine root_eq_of_theta θ P ?_ ?_ ?_ ?_
    · rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply, hroot, map_zero,
        map_zero]
    · rw [Polynomial.aeval_algHom_apply, hτroot, map_zero]
    · rw [hs, hι₀]
    · rw [hι₀, Polynomial.aeval_algHom_apply]
      exact (map_ne_zero ιΩ).mpr (hsep.aeval_derivative_ne_zero hτroot)
  exact congrArg (fun φ => φ x) key

end Hensel

end ZInQ.Contrib.G9
