/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_Kmf2FiberSpecTensorStalkLeg1AffineDatum.lean
  Source sha256  : ed666f4b8b1c3ac4d5170e0397db697ffe9292bfd759c23440937cbd8ca1fba3
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 800000`; `set_option synthInstance.maxHeartbeats 400000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T2×5; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct"

noncomputable def kmf2_fiberSpecTensorIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p ≅
      Spec (CommRingCat.of (p.asIdeal.Fiber S)) :=
  pullbackSymmetry _ _ ≪≫
    (pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
        (CommRingCat.of R) p).symm rfl ≪≫
      asIso (pullback.map _ _ _ _
        (Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv) (𝟙 _) (𝟙 _)
        (by simp) (by simp))) ≪≫
    pullbackSpecIso R p.asIdeal.ResidueField S

theorem kmf2_fiberSpecTensorIso_hom_includeRight
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (kmf2_fiberSpecTensorIso R S p).hom ≫
        Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight
            (R := R) (A := p.asIdeal.ResidueField) (B := S)))) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p := by
  simp only [kmf2_fiberSpecTensorIso, Scheme.Hom.fiberι, Iso.trans_hom, asIso_hom,
    pullback.congrHom_hom, Category.assoc, pullbackSpecIso_hom_snd,
    pullback.lift_snd, Category.comp_id]
  exact pullbackSymmetry_hom_comp_snd _ _

theorem kmf2_fiberSpecTensorIso_point_comap
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R)
    (w : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) :
    (((kmf2_fiberSpecTensorIso R S p).hom w).asIdeal).comap
        (Algebra.TensorProduct.includeRight
          (R := R) (A := p.asIdeal.ResidueField) (B := S)).toRingHom =
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p w).asIdeal := by
  have h1 : Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight
        (R := R) (A := p.asIdeal.ResidueField) (B := S))))
        ((kmf2_fiberSpecTensorIso R S p).hom w) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiberι p w := by
    rw [← Scheme.Hom.comp_apply, kmf2_fiberSpecTensorIso_hom_includeRight]
  have h2 := congrArg PrimeSpectrum.asIdeal h1
  rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom] at h2
  exact h2

theorem kmf2_fiberStalk_localizationAtPrime
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R)
    (w : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) :
    Nonempty
      (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p).presheaf.stalk w ≃+*
        Localization.AtPrime ((kmf2_fiberSpecTensorIso R S p).hom w).asIdeal) :=
  ⟨(asIso ((kmf2_fiberSpecTensorIso R S p).hom.stalkMap w)).commRingCatIsoToRingEquiv.symm.trans
    ((StructureSheaf.stalkIso (p.asIdeal.Fiber S)
      ((kmf2_fiberSpecTensorIso R S p).hom w)).symm.toRingEquiv)⟩

theorem kmf2_fiberStalkLeg1_affineDatum
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (x : Spec (CommRingCat.of S)) :
    ∃ (Q : Ideal ((Spec.map (CommRingCat.ofHom (algebraMap R S))
        x).asIdeal.Fiber S)) (_ : Q.IsPrime),
      Q.comap (Algebra.TensorProduct.includeRight
        (R := R)
        (A := (Spec.map (CommRingCat.ofHom (algebraMap R S)) x).asIdeal.ResidueField)
        (B := S)).toRingHom = x.asIdeal ∧
      Nonempty
        (((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber
            (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).presheaf.stalk
          ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x) ≃+*
          Localization.AtPrime Q) := by
  refine ⟨((kmf2_fiberSpecTensorIso R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)).asIdeal,
    ((kmf2_fiberSpecTensorIso R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)).hom
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)).2, ?_, ?_⟩
  · rw [kmf2_fiberSpecTensorIso_point_comap]
    rw [Scheme.Hom.fiberι_asFiber]
  · exact kmf2_fiberStalk_localizationAtPrime R S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) x)
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).asFiber x)






end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
