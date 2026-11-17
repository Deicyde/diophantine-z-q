/-
NEW EDITION (H5 lane4 a940f2af, 2026-11-17, Parent route (E)). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat.lean
  Source sha256  : 5ffbdaf7a4931c7ce3441af6f6f023fc28b9d018b931d1e102a28cb7fe1edb5a
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct"

namespace BenchQD1a
r2nos_namespace_dual

theorem flat_specMap {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.Flat S S'] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  show (algebraMap S S').Flat
  have h : (algebraMap S S').toAlgebra = ‹Algebra S S'› := Algebra.algebra_ext _ _ fun _ => rfl
  unfold RingHom.Flat
  rw [h]; infer_instance

theorem main
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    {Y : Scheme.{u}} (φ' : T' ⟶ Y) (hφ' : q₁ ≫ φ' = q₂ ≫ φ') :
    ∃! φ : T ⟶ Y, p ≫ φ = φ' := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap S S'))
  let ιL := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))
  let ιR := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)

  haveI : Flat ι := flat_specMap
  haveI : Surjective ι := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  haveI : QuasiCompact ι := inferInstance
  haveI : Flat p := MorphismProperty.of_isPullback hp.flip inferInstance
  haveI : Surjective p := MorphismProperty.of_isPullback hp.flip inferInstance
  haveI : QuasiCompact p := MorphismProperty.of_isPullback hp.flip inferInstance
  haveI : EffectiveEpi p := inferInstance

  have hSpec : IsPullback ιL ιR ι ι :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct S S' S')
  have hbig : IsPullback (t'' ≫ ιR) q₁ ι (t' ≫ ι) := hq₁.flip.paste_horiz hSpec.flip
  have hbig' : IsPullback (q₂ ≫ t') q₁ ι (p ≫ t) := by
    rw [hq₂.w, hp.w]; exact hbig
  have hPB : IsPullback q₂ q₁ p p := IsPullback.of_right hbig' hq.symm hp.flip

  have key : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ T'), g₁ ≫ p = g₂ ≫ p → g₁ ≫ φ' = g₂ ≫ φ' := by
    intro Z g₁ g₂ hg
    have h1 := hPB.lift_fst g₂ g₁ hg.symm
    have h2 := hPB.lift_snd g₂ g₁ hg.symm
    calc g₁ ≫ φ' = (hPB.lift g₂ g₁ hg.symm ≫ q₁) ≫ φ' := by rw [h2]
      _ = hPB.lift g₂ g₁ hg.symm ≫ (q₂ ≫ φ') := by rw [Category.assoc, hφ']
      _ = g₂ ≫ φ' := by rw [← Category.assoc, h1]
  refine ⟨EffectiveEpi.desc p φ' key, EffectiveEpi.fac p φ' key, fun φ hφ => EffectiveEpi.uniq p φ' key φ hφ⟩

end BenchQD1a

theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {T T' T'' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
    (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (t'' : T'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (q₁ q₂ : T'' ⟶ T')
    (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S' →+* S' ⊗[S] S'))))
    (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hq : q₁ ≫ p = q₂ ≫ p)
    {Y : Scheme.{u}} (φ' : T' ⟶ Y) (hφ' : q₁ ≫ φ' = q₂ ≫ φ') :
    ∃! φ : T ⟶ Y, p ≫ φ = φ' :=
  BenchQD1a.main t t' p hp t'' q₁ q₂ hq₁ hq₂ hq φ' hφ'
end S_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
