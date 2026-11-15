/-
Multiplication-etale construction: LocalCotangentCriterion.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.RingCotangentCriterion
import Mathlib.RingTheory.LocalRing.Module

open scoped TensorProduct

namespace H101DirectFieldRoute

private theorem surjective_of_lTensor_residueField_surjective
    {A M N : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A N] (l : M →ₗ[A] N)
    (h : Function.Surjective (l.lTensor (IsLocalRing.ResidueField A))) :
    Function.Surjective l := by
  let k := IsLocalRing.ResidueField A
  let P : Submodule A (k ⊗[A] N) :=
    (LinearMap.range l).map (TensorProduct.mk A k N 1)
  have hp : ∀ z : k ⊗[A] M, l.lTensor k z ∈ P := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using P.zero_mem
    | tmul r x =>
      obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective r
      change algebraMap A k a = r at ha
      refine ⟨l (a • x), ⟨a • x, rfl⟩, ?_⟩
      change (1 : k) ⊗ₜ[A] l (a • x) = l.lTensor k (r ⊗ₜ[A] x)
      rw [LinearMap.lTensor_tmul, map_smul, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
      simp only [Algebra.smul_def, mul_one, ha]
    | add x y hx hy =>
      simpa only [map_add] using P.add_mem hx hy
  have hP : P = ⊤ := by
    apply top_le_iff.mp
    intro y _
    obtain ⟨z, rfl⟩ := h y
    exact hp z
  have hrange : LinearMap.range l = ⊤ :=
    (IsLocalRing.map_tensorProduct_mk_eq_top (R := A) (M := N)).1 hP
  exact LinearMap.range_eq_top.mp hrange

/-- A residue-field bijection lifts to a bijection when the source is finite
and the target is finite free. No assumed flatness of the investigated ring
map, Noetherian base, dimension bound or char-zero hypothesis occurs. -/
theorem bijective_of_lTensor_residueField_bijective
    {A M N : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N] [Module.Free A N]
    (l : M →ₗ[A] N)
    (h : Function.Bijective (l.lTensor (IsLocalRing.ResidueField A))) :
    Function.Bijective l :=
  ⟨injective_of_lTensor_residueField_injective l h.1,
    surjective_of_lTensor_residueField_surjective l h.2⟩

/-- The local cotangent version suitable for a smooth field-fibre stalk.
`R`, `S`, `T` must be instantiated using the ACTUAL base/source/target local
rings and the actual multiplication stalk map. The residue-tensor bijection
is the explicit remaining geometric join, not a newly assumed H101 Fact. -/
theorem formallyEtale_of_residue_cotangent_bijective
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalRing T]
    [Algebra.EssFiniteType R S] [Algebra.EssFiniteType R T]
    [Algebra.FormallySmooth R S] [Algebra.FormallySmooth R T]
    (h : Function.Bijective
      ((KaehlerDifferential.mapBaseChange R S T).lTensor
        (IsLocalRing.ResidueField T))) :
    Algebra.FormallyEtale S T := by
  haveI : Module.Free T Ω[T⁄R] := Module.free_of_flat_of_isLocalRing
  apply formallyEtale_of_bijective_mapBaseChange R S T
  exact bijective_of_lTensor_residueField_bijective
    (KaehlerDifferential.mapBaseChange R S T) h

end H101DirectFieldRoute
