import ZInQKernel.Contrib.CloudB3W17bGraphScoutReverseIdeal.StalkGerms
import ZInQKernel.Contrib.CloudB3W17bGraphScoutReverseIdeal.RangeLocalization
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
Native support of the actual exact-image ideal, measured by properness of its
actual stalk image. This is the algebraic input to the canonical stalk-surjectivity
comparison, and does not assume an analytic ideal or graph equality.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
universe u

namespace ZInQ.Contrib.CloudB3W17bCanonicalImage

open ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal

/-- Extension of an actual image ideal is proper in a local ring exactly when
all actual image generators are nonunits. -/
theorem map_linearRangeIdeal_ne_top_iff
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing S]
    [AddCommGroup M] [Module R M] (q : M →ₗ[R] R) (f : R →+* S) :
    (linearRangeIdeal q).map f ≠ ⊤ ↔ ∀ m : M, ¬ IsUnit (f (q m)) := by
  constructor
  · intro h m
    have hle := IsLocalRing.le_maximalIdeal h
    have hm : f (q m) ∈ (linearRangeIdeal q).map f :=
      Ideal.mem_map_of_mem f ⟨m, rfl⟩
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp (hle hm))
  · intro h
    have hle : (linearRangeIdeal q).map f ≤ IsLocalRing.maximalIdeal S := by
      refine Ideal.map_le_iff_le_comap.mpr ?_
      rintro r ⟨m, rfl⟩
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (h m))
    intro he
    have ht : (⊤ : Ideal S) ≤ IsLocalRing.maximalIdeal S := he ▸ hle
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_le_iff.mp ht)

/-- The constructed native ideal support is exactly the vanishing of its actual
section images at a point, in the local-ring nonunit sense. -/
theorem nativeIdeal_mem_support_iff_nonunit_sectionImages
    {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.affineOpens)
    (x : X) (hxU : x ∈ U.1) :
    x ∈ (idealSheafOfQuasicoherentHom i).support ↔
      ∀ s : Γ(M, U.1), ¬ IsUnit ((X.presheaf.germ U.1 x hxU).hom (sectionMapToRing i U.1 s)) := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h s
    have hs : sectionMapToRing i U.1 s ∈ (idealSheafOfQuasicoherentHom i).ideal U :=
      (mem_idealSheafOfQuasicoherentHom i U _).mpr ⟨s, rfl⟩
    exact (X.mem_basicOpen _ x hxU).not.mp (h _ hs)
  · intro h r hr
    obtain ⟨s, rfl⟩ := (mem_idealSheafOfQuasicoherentHom i U r).mp hr
    exact (X.mem_basicOpen _ x hxU).not.mpr (h s)

/-- The actual native closed support equals properness of the actual stalk-germ
image ideal. No arbitrary submodule or analytic vanishing premise is passed in. -/
theorem nativeIdeal_mem_support_iff_stalkImage_ne_top
    {X : Scheme.{u}} {M : X.Modules} [M.IsQuasicoherent]
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.affineOpens)
    (x : X) (hxU : x ∈ U.1) :
    x ∈ (idealSheafOfQuasicoherentHom i).support ↔ sectionImageGermIdeal i x ≠ ⊤ := by
  rw [nativeIdeal_mem_support_iff_nonunit_sectionImages i U x hxU,
    sectionImageGermIdeal_eq_map i U.2 x hxU]
  exact (map_linearRangeIdeal_ne_top_iff (sectionMapToRing i U.1)
    (X.presheaf.germ U.1 x hxU).hom).symm

end ZInQ.Contrib.CloudB3W17bCanonicalImage
