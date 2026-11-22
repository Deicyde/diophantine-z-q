import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Homotopy

/-!
# Acyclic bounded free complexes are universally split exact

This is an actual contraction, not just a homology-rank identity. Consequently
ANY additive change-of-scalars functor preserves acyclicity; flatness of the
new coefficients is not needed. This is the linear-algebra input in the B2
finite-free-model argument.
-/

open CategoryTheory Limits

namespace ZInQ.Contrib.CloudR2Poincare.L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A bounded-above acyclic complex of projectives has a contracting homotopy. -/
theorem nonempty_contraction_of_bounded_projective
    {C : Type*} [Category C] [Abelian C]
    (P : CochainComplex C ℤ) (d : ℤ) [P.IsStrictlyLE d]
    [∀ n : ℤ, Projective (P.X n)] (hP : P.Acyclic) :
    Nonempty (Homotopy (𝟙 P) 0) := by
  letI : P.IsKProjective := CochainComplex.isKProjective_of_projective P d
  exact ⟨CochainComplex.IsKProjective.homotopyZero (𝟙 P) hP⟩

/-- A contraction forces zero homology in every degree. -/
theorem isZero_homology_of_contraction
    {C : Type*} [Category C] [Abelian C]
    (P : CochainComplex C ℤ) (h : Homotopy (𝟙 P) 0) (q : ℤ) :
    IsZero (P.homology q) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  simpa only [HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero]
    using h.homologyMap_eq q

/-- Acyclic bounded-above projectives remain acyclic under ANY additive functor. -/
theorem isZero_homology_map_of_bounded_projective_acyclic
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (P : CochainComplex C ℤ) (d : ℤ) [P.IsStrictlyLE d]
    [∀ n : ℤ, Projective (P.X n)] (hP : P.Acyclic)
    (F : C ⥤ D) [F.Additive] (q : ℤ) :
    IsZero (((F.mapHomologicalComplex (.up ℤ)).obj P).homology q) := by
  obtain ⟨h⟩ := nonempty_contraction_of_bounded_projective P d hP
  have hm := F.mapHomotopy h
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at hm
  exact isZero_homology_of_contraction _ hm q

/-- In particular the statement holds for bounded free module complexes and
arbitrary extension of scalars. No flatness premise on R→S is introduced. -/
theorem isZero_homology_extendScalars_of_bounded_free_acyclic
    (R S : Type*) [CommRing R] [CommRing S] (φ : R →+* S)
    (P : CochainComplex (ModuleCat R) ℤ) (d : ℤ) [P.IsStrictlyLE d]
    [∀ n : ℤ, Module.Free R (P.X n)] (hP : P.Acyclic) (q : ℤ) :
    IsZero ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P).homology q) := by
  haveI : ∀ n : ℤ, Projective (P.X n) := fun n => by infer_instance
  letI : PreservesBinaryBiproducts (ModuleCat.extendScalars φ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  letI : (ModuleCat.extendScalars φ).Additive :=
    CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _
  exact isZero_homology_map_of_bounded_projective_acyclic P d hP
    (ModuleCat.extendScalars φ) q

end ZInQ.Contrib.CloudR2Poincare.L3
