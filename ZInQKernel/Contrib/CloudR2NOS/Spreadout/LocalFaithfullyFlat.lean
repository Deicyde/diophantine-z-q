/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): local injective maps out of a DVR are faithfully flat

New glue (no vendored source in this file). Written at the H5 lead's request, coordinated with lane 5:
a general helper with no ind-étale, henselian or residue hypothesis.

For a DVR `C` and a local domain `P` (in particular a DVR) with a LOCAL and INJECTIVE algebra map
`C → P`:
* `P` is torsion-free over `C` (Mathlib `Module.isTorsionFree_iff_algebraMap_injective`), hence flat over the
  Dedekind domain `C` (Mathlib, Stacks 0AUW);
* flat + local is faithfully flat (Mathlib `Module.FaithfullyFlat.of_flat_of_isLocalHom`);
* therefore `Spec P → Spec C` is surjective, on prime spectra and as a morphism of schemes.
A ring-hom form `f : C →+* P` is included.
-/
import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Spreadout.LocalFaithfullyFlat

section Algebra

variable {C P : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  [CommRing P] [IsDomain P] [IsLocalRing P] [Algebra C P]

omit [IsLocalRing P] in
/-- An injective algebra map from a DVR to a domain makes the target flat. -/
theorem flat_of_injective (hinj : Function.Injective (algebraMap C P)) : Module.Flat C P := by
  haveI : Module.IsTorsionFree C P := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  infer_instance

/-- **A local injective algebra map from a DVR to a local domain is faithfully flat.** -/
theorem faithfullyFlat_of_injective [IsLocalHom (algebraMap C P)]
    (hinj : Function.Injective (algebraMap C P)) : Module.FaithfullyFlat C P := by
  haveI := flat_of_injective hinj
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The map on prime spectra is surjective. -/
theorem comap_surjective_of_injective [IsLocalHom (algebraMap C P)]
    (hinj : Function.Injective (algebraMap C P)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap C P)) := by
  haveI := faithfullyFlat_of_injective hinj
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

/-- The morphism of affine schemes is surjective. -/
theorem surjective_specMap_of_injective [IsLocalHom (algebraMap C P)]
    (hinj : Function.Injective (algebraMap C P)) :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap C P))) :=
  ⟨comap_surjective_of_injective hinj⟩

end Algebra

section RingHom

variable {C P : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  [CommRing P] [IsDomain P] [IsLocalRing P]

/-- Ring-hom form: a local injective ring map from a DVR to a local domain is faithfully flat. -/
theorem faithfullyFlat_of_ringHom (f : C →+* P) [IsLocalHom f] (hinj : Function.Injective f) :
    letI : Algebra C P := f.toAlgebra
    Module.FaithfullyFlat C P := by
  letI : Algebra C P := f.toAlgebra
  haveI : IsLocalHom (algebraMap C P) := ‹IsLocalHom f›
  exact faithfullyFlat_of_injective hinj

/-- Ring-hom form of Spec surjectivity. -/
theorem surjective_specMap_of_ringHom (f : C →+* P) [IsLocalHom f] (hinj : Function.Injective f) :
    Surjective (Spec.map (CommRingCat.ofHom f)) := by
  letI : Algebra C P := f.toAlgebra
  haveI : IsLocalHom (algebraMap C P) := ‹IsLocalHom f›
  exact surjective_specMap_of_injective (C := C) (P := P) hinj

end RingHom

end ZInQ.Contrib.CloudR2NOS.Spreadout.LocalFaithfullyFlat
