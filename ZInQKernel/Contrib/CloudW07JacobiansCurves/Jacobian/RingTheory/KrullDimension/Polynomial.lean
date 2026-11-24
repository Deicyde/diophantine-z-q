-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.RingTheory.KrullDimension.Polynomial), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Heights of maximal ideals of polynomial rings over fields

Every maximal ideal of a polynomial ring in `dimension` variables over a field
has height `dimension`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open Ideal

theorem MvPolynomial.height_eq_of_isMaximal {baseField : Type*} [Field baseField] :
    ∀ (dimension : ℕ) (maximal : Ideal (MvPolynomial (Fin dimension) baseField)) [maximal.IsMaximal], maximal.height = dimension
  | 0, maximal, _ => by
    have dimension_bound := height_le_ringKrullDim_of_ne_top (IsMaximal.ne_top ‹maximal.IsMaximal›)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field] at dimension_bound
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_zero, add_zero] at dimension_bound
    exact_mod_cast le_antisymm (by exact_mod_cast dimension_bound) zero_le
  | dimension + 1, maximal, _ => by
    let equivalence := MvPolynomial.finSuccEquiv baseField dimension
    let M' : Ideal (Polynomial (MvPolynomial (Fin dimension) baseField)) := maximal.map equivalence.toRingEquiv
    have : M'.IsMaximal := map_isMaximal_of_equiv equivalence.toRingEquiv
    have hM : maximal.height = M'.height := (equivalence.toRingEquiv.height_map maximal).symm
    let prime := M'.comap Polynomial.C
    have : prime.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
    have : M'.LiesOver prime := ⟨rfl⟩
    rw [hM, Polynomial.height_eq_height_add_one prime M', MvPolynomial.height_eq_of_isMaximal dimension prime]
    norm_cast
