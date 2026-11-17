/-
NEW EDITION CANDIDATE 002 (H5 lane4 a940f2af, 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso.lean
  Source sha256  : 03508f685c54f383b0e5c811128ebcf620f94a1e96a9e39ab89ab48b9652be10
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

namespace P0PushforwardStart
r2nos_namespace_dual

noncomputable def pullbackPushforwardIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : U.Modules) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pushforward j).obj M) ≅ M :=
  ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app _) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso j).app M

noncomputable def pullbackImageIsoUnit {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : U.Modules) (V : U.Opens)
    (eV : (Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    (Scheme.Modules.pullback (j ''ᵁ V).ι).obj ((Scheme.Modules.pushforward j).obj M) ≅
      SheafOfModules.unit (j ''ᵁ V).toScheme.ringCatSheaf :=
  let φ := j.isoImage V
  have hfact : (j ''ᵁ V).ι = φ.inv ≫ (V.ι ≫ j) := (Scheme.Hom.isoImage_inv_ι j V).symm
  (Scheme.Modules.pullbackCongr hfact).app _ ≪≫
    ((Scheme.Modules.pullbackComp φ.inv (V.ι ≫ j)).app _).symm ≪≫
    (Scheme.Modules.pullback φ.inv).mapIso
      (((Scheme.Modules.pullbackComp V.ι j).app _).symm ≪≫
        (Scheme.Modules.pullback V.ι).mapIso (pullbackPushforwardIso j M) ≪≫ eV) ≪≫
    Scheme.Modules.pullbackUnitIso φ.inv

end P0PushforwardStart

theorem solution
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {M : U.Modules} (hM : Scheme.Modules.IsInvertible M) :
    ∃ 𝓛 : X.Modules,
      (∀ x ∈ Scheme.Hom.opensRange j, ∃ U : X.Opens, x ∈ U ∧ U ≤ Scheme.Hom.opensRange j ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)) ∧
      Nonempty ((Scheme.Modules.pullback j).obj 𝓛 ≅ M) := by
  refine ⟨(Scheme.Modules.pushforward j).obj M, ?_,
    ⟨P0PushforwardStart.pullbackPushforwardIso j M⟩⟩
  intro x hx
  obtain ⟨u, rfl⟩ := Scheme.Hom.mem_opensRange.mp hx
  obtain ⟨V, huV, ⟨eV⟩⟩ := hM.exists_trivialization u
  exact ⟨j ''ᵁ V, ⟨u, huV, rfl⟩, Scheme.Hom.image_le_opensRange j V,
    ⟨P0PushforwardStart.pullbackImageIsoUnit j M V eV⟩⟩
end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_locallyTrivial_opensRange_nonempty_pullback_iso
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
