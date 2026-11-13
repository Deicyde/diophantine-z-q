import ZInQKernel.Contrib.DifferentBound.Monogenic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic

/-!
# The genuine degree comparison for a generating uniformizer

The finite-flat ramification/inertia identity is reduced to the unique maximal
prime of a DVR. A generating uniformizer makes the residue extension trivial,
so the ramification index is the genuine fraction-field degree. No power basis
is asserted to exist without constructing it or invoking its actual supplier.
-/

namespace ZInQ.Contrib.DifferentBound

open IsLocalRing

/-- Equality of the contracted maximal ideals proves that the algebra map is local. -/
theorem isLocalHom_of_maximalIdeal_liesOver
    {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [(maximalIdeal B).LiesOver (maximalIdeal A)] :
    IsLocalHom (algebraMap A B) := by
  refine ⟨fun a ha ↦ ?_⟩
  by_contra hn
  have ham : a ∈ maximalIdeal A := hn
  have hbm : algebraMap A B a ∈ maximalIdeal B :=
    (Ideal.mem_of_liesOver (maximalIdeal B) (maximalIdeal A) a).mp ham
  exact hbm ha

section LocalDegree

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)]

/-- The finite-flat fundamental identity for an extension of DVRs has one prime term. -/
theorem dvr_ramificationIdx_mul_residueDegree :
    (maximalIdeal B).ramificationIdx A *
      Module.finrank (ResidueField A) (ResidueField B) = Module.finrank A B := by
  classical
  let p := maximalIdeal A
  let q₀ : p.primesOver B := ⟨maximalIdeal B, ⟨inferInstance, inferInstance⟩⟩
  let : Unique (p.primesOver B) :=
    { default := q₀
      uniq := fun q ↦ by
        have hq0 : q.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
          (IsDiscreteValuationRing.not_a_field A) q.1
        have hqm : q.1.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hq0
        apply Subtype.ext
        exact IsLocalRing.eq_maximalIdeal hqm }
  have h := Ideal.sum_ramification_inertia_eq_finrank p B
  rw [Fintype.sum_unique] at h
  change (maximalIdeal B).ramificationIdx A * (maximalIdeal B).inertiaDeg A =
    Module.finrank A B at h
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal A) (maximalIdeal B)] at h
  exact h

omit [Module.Finite A B] [Module.IsTorsionFree A B] in
/-- Surjectivity onto the upper residue field makes its degree over the lower residue field one. -/
theorem residueDegree_eq_one_of_surjective
    (hres : Function.Surjective ((residue B).comp (algebraMap A B))) :
    Module.finrank (ResidueField A) (ResidueField B) = 1 := by
  have hsurj : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)) := by
    intro y
    obtain ⟨a, ha⟩ := hres y
    exact ⟨residue A a, by
      simpa only [ResidueField.algebraMap_residue, RingHom.comp_apply] using ha⟩
  let E : ResidueField A ≃ₗ[ResidueField A] ResidueField B :=
    LinearEquiv.ofBijective (Algebra.linearMap (ResidueField A) (ResidueField B))
      ⟨(algebraMap (ResidueField A) (ResidueField B)).injective, hsurj⟩
  simpa only [Module.finrank_self] using E.finrank_eq.symm

/-- The ramification index equals the ring-module rank when the residue extension is trivial. -/
theorem dvr_ramificationIdx_eq_finrank_of_surjective_residue
    (hres : Function.Surjective ((residue B).comp (algebraMap A B))) :
    (maximalIdeal B).ramificationIdx A = Module.finrank A B := by
  have h := dvr_ramificationIdx_mul_residueDegree A B
  rw [residueDegree_eq_one_of_surjective A B hres, mul_one] at h
  exact h

/-- The same comparison on actual fraction fields, with all structure maps explicit. -/
theorem dvr_ramificationIdx_eq_fractionField_finrank_of_surjective_residue
    (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    (hres : Function.Surjective ((residue B).comp (algebraMap A B))) :
    (maximalIdeal B).ramificationIdx A = Module.finrank K L :=
  (dvr_ramificationIdx_eq_finrank_of_surjective_residue A B hres).trans
    (IsFractionRing.finrank_eq A K B L).symm

end LocalDegree

/-- A supplied generating uniformizer proves residue-field surjectivity: reduce its representing
polynomial at the uniformizer, whose residue is zero. -/
theorem residue_surjective_of_generating_uniformizer
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] {π : B} (hπ : Irreducible π) (hgen : Algebra.adjoin A {π} = ⊤) :
    Function.Surjective ((residue B).comp (algebraMap A B)) := by
  have hπ0 : residue B π = 0 := (residue_eq_zero_iff π).mpr (by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π)
  intro y
  obtain ⟨b, rfl⟩ := residue_surjective y
  have hb : b ∈ Algebra.adjoin A {π} := hgen ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨f, rfl⟩ := hb
  refine ⟨f.coeff 0, ?_⟩
  have hcomp : (algebraMap A (ResidueField B)).comp (RingHom.id A) =
      (residue B).comp (algebraMap A B) := by
    ext a
    rfl
  have h := Polynomial.map_aeval_eq_aeval_map hcomp f π
  change algebraMap A (ResidueField B) (f.coeff 0) = residue B (Polynomial.aeval π f)
  simpa only [hπ0, Polynomial.map_id, ← Polynomial.coeff_zero_eq_aeval_zero'] using h.symm

/-- The degree hypothesis in the local Serre estimate is derivable for every finite extension
with a genuine generating uniformizer. No completeness or perfectness is needed for this step. -/
theorem minpoly_natDegree_eq_ramificationIdx_of_generating_uniformizer
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K]
    [IsIntegralClosure B A L] [Module.IsTorsionFree A B] [Module.Finite A B]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [(maximalIdeal B).LiesOver (maximalIdeal A)]
    {π : B} (hπ : Irreducible π) (hgen : Algebra.adjoin A {π} = ⊤) :
    (minpoly A π).natDegree = (maximalIdeal B).ramificationIdx A := by
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let := isLocalHom_of_maximalIdeal_liesOver (A := A) (B := B)
  have hdeg := minpoly_natDegree_eq_finrank_of_ring_adjoin_eq_top A K L B π hgen
  have he := dvr_ramificationIdx_eq_fractionField_finrank_of_surjective_residue A B K L
    (residue_surjective_of_generating_uniformizer hπ hgen)
  exact hdeg.trans he.symm

end ZInQ.Contrib.DifferentBound
