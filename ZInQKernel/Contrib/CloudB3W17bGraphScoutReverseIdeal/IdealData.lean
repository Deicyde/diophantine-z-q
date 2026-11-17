import ZInQKernel.Contrib.CloudB3W17bGraphScoutReverseIdeal.AffineSections
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
Reverse algebraic ideal construction on the actual Mathlib scheme/module objects.
The input is a concrete morphism from a quasi-coherent module to the structure
sheaf, as obtained by GAGA-2 after algebraizing the analytic ideal module.
The output has the exact affine section images: ofIdeals/envelope is not used.
No analytic graph or GAGA conclusion is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u

namespace ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal

variable {X : Scheme.{u}} {M : X.Modules}

/-- The actual sectionwise linear map of a module morphism into the structure sheaf. -/
def sectionMapToRing (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  (i.val.app (op U)).hom

/-- The image is an actual ideal of the ring of regular sections, not an arbitrary set. -/
def sectionImageIdeal (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) :
    Ideal Γ(X, U) := LinearMap.range (sectionMapToRing i U)

lemma sectionMapToRing_res (i : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    {U V : X.Opens} (h : V ≤ U) (s : Γ(M, U)) :
    sectionMapToRing i V (TopCat.Presheaf.restrictOpen s V h) =
      TopCat.Presheaf.restrictOpen (sectionMapToRing i U s) V h :=
  TopCat.Presheaf.map_restrict i.mapPresheaf h s

/-- Quasi-coherence supplies the full basic-open localization identity for the image ideal. -/
theorem sectionImageIdeal_map_basicOpen [M.IsQuasicoherent]
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U)) :
    (sectionImageIdeal i U).map (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom =
      sectionImageIdeal i (X.basicOpen a) := by
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr ?_
    rintro r ⟨s, rfl⟩
    exact ⟨TopCat.Presheaf.restrictOpen s _ (X.basicOpen_le a),
      sectionMapToRing_res i (X.basicOpen_le a) s⟩
  · rintro r ⟨s, rfl⟩
    obtain ⟨k, t, ht⟩ := exists_restrictOpen_eq_pow_smul hU M a s
    have hd := congrArg (sectionMapToRing i (X.basicOpen a)) ht
    rw [sectionMapToRing_res, map_smul, smul_eq_mul] at hd
    letI := hU.isLocalization_basicOpen a
    have hd' : (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
        (sectionMapToRing i U t) =
        algebraMap Γ(X, U) Γ(X, X.basicOpen a) a ^ k *
          sectionMapToRing i (X.basicOpen a) s := hd
    have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen a) a ^ k) :=
      (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen a)) a).pow k
    obtain ⟨v, hv⟩ := hu
    have hmem : (v : Γ(X, X.basicOpen a)) * sectionMapToRing i (X.basicOpen a) s ∈
        (sectionImageIdeal i U).map (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom := by
      rw [hv, ← hd']
      exact Ideal.mem_map_of_mem _ ⟨t, rfl⟩
    have hi := ((sectionImageIdeal i U).map
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom).mul_mem_left
        (↑v⁻¹ : Γ(X, X.basicOpen a)) hmem
    simpa only [← mul_assoc, v.inv_mul, one_mul] using hi

/-- The actual native quasi-coherent ideal data associated to a morphism into O_X.
Every affine component is exactly its section image. No compatibility premise is added. -/
def idealSheafOfQuasicoherentHom [M.IsQuasicoherent]
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) : X.IdealSheafData where
  ideal U := sectionImageIdeal i U.1
  map_ideal_basicOpen U a := sectionImageIdeal_map_basicOpen i U.2 a

/-- Exact component membership; this is stronger than the envelope supplied by ofIdeals. -/
theorem mem_idealSheafOfQuasicoherentHom [M.IsQuasicoherent]
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.affineOpens) (r : Γ(X, U.1)) :
    r ∈ (idealSheafOfQuasicoherentHom i).ideal U ↔
      ∃ s : Γ(M, U.1), sectionMapToRing i U.1 s = r := Iff.rfl

/-- The associated native algebraic closed subscheme and closed immersion really exist. -/
theorem exists_closedSubscheme_of_quasicoherentHom [M.IsQuasicoherent]
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsClosedImmersion j ∧
      ∀ U : X.affineOpens, j.ker.ideal U = sectionImageIdeal i U.1 := by
  let J := idealSheafOfQuasicoherentHom i
  refine ⟨J.subscheme, J.subschemeι, inferInstance, ?_⟩
  intro U
  rw [Scheme.IdealSheafData.ker_subschemeι]
  rfl

end ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal
