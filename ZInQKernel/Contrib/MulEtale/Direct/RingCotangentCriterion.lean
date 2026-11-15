/-
Multiplication-etale construction: RingCotangentCriterion.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.LocalRing.Module

open scoped TensorProduct

namespace H101DirectFieldRoute

/-- The native Jacobi-Zariski sequence gives formal etaleness without an
assumed flatness premise: the source algebra is formally smooth over R and
its relative differential map is bijective. The missing H101 join is deriving
this bijectivity for the ACTUAL multiplication stalk map, not assuming it. -/
theorem formallyEtale_of_bijective_mapBaseChange
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
    Algebra.FormallyEtale S T := by
  have hdelta : ∀ x : Algebra.H1Cotangent S T,
      Algebra.H1Cotangent.δ R S T x = 0 := by
    intro x
    apply h.1
    have hz := LinearMap.congr_fun
      (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T).linearMap_comp_eq_zero x
    change KaehlerDifferential.mapBaseChange R S T (Algebra.H1Cotangent.δ R S T x) = 0 at hz
    simpa only [map_zero] using hz
  refine ⟨?_, ?_⟩
  · refine (subsingleton_iff_forall_eq 0).2 ?_
    intro x
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R S T x
    obtain ⟨z, rfl⟩ := h.2 y
    exact LinearMap.congr_fun
      (KaehlerDifferential.exact_mapBaseChange_map R S T).linearMap_comp_eq_zero z
  · refine (subsingleton_iff_forall_eq 0).2 ?_
    intro x
    obtain ⟨z, hz⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp (hdelta x)
    rw [← hz, Subsingleton.elim z 0, map_zero]

/-- Native Nakayama/splitting input for lifting a residue-field cotangent
injection to the local ring. It needs finiteness and a finite free target,
which smooth stalks over a field supply. No Noetherian or flatness of the
morphism being investigated is an input. -/
theorem injective_of_lTensor_residueField_injective
    {A M N : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N] [Module.Free A N]
    (l : M →ₗ[A] N)
    (h : Function.Injective (l.lTensor (IsLocalRing.ResidueField A))) :
    Function.Injective l := by
  obtain ⟨s, hs⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).2 h
  exact Function.HasLeftInverse.injective ⟨s, LinearMap.congr_fun hs⟩

end H101DirectFieldRoute
