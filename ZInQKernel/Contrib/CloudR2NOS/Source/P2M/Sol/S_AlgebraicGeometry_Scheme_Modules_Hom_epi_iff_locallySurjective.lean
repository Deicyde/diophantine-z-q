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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective.lean
  Source sha256  : 623e061141aeaf88ffefec8469be60232f3380e7801c76d1a4bddafc34d4f17b
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 7 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
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

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective.AlgebraicGeometry Opposite TopologicalSpace"

universe v v' u'

namespace SheafOfModules
r2nos_namespace_dual
w03_export "SheafOfModules" "forget restrictScalars toSheaf sections"
w03_open "SheafOfModules"

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

theorem epi_toSheaf_map_of_epi {M N : SheafOfModules.{v} R} (φ : M ⟶ N) [Epi φ] :
    Epi ((toSheaf R).map φ) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)
  let G := SheafOfModules.forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let S := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
  let ψ := G.map φ
  haveI hcounit : IsIso adj.counit :=
    inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).counit)
  let εM : S.obj (G.obj M) ≅ M :=
    @asIso _ _ _ _ (adj.counit.app M) (NatIso.isIso_app_of_isIso adj.counit M)
  let εN : S.obj (G.obj N) ≅ N :=
    @asIso _ _ _ _ (adj.counit.app N) (NatIso.isIso_app_of_isIso adj.counit N)
  have hnat : S.map ψ ≫ εN.hom = εM.hom ≫ φ := adj.counit.naturality φ
  haveI : Epi (S.map ψ) := by
    have : S.map ψ = (εM.hom ≫ φ) ≫ εN.inv := (Iso.eq_comp_inv εN).2 hnat
    rw [this]; infer_instance
  have h0 : S.map (cokernel.π ψ) = 0 := by
    apply zero_of_epi_comp (S.map ψ)
    rw [← S.map_comp, cokernel.condition]
    exact S.map_zero _ _
  let T := PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{v}
  have hT : ∀ {P Q : PresheafOfModules.{v} R.obj} (f : P ⟶ Q),
      T.map f = (toSheaf R).map (S.map f) := fun f => rfl
  have h0' : T.map (cokernel.π ψ) = 0 := by
    rw [hT, h0]
    exact Functor.map_zero _ _ _
  have hc := isColimitOfHasCokernelOfPreservesColimit T ψ
  haveI hTψ : Epi (T.map ψ) := by
    refine Preadditive.epi_of_cancel_zero _ (fun g hg => ?_)
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hc g hg
    rw [← hd]
    change T.map (cokernel.π ψ) ≫ d = 0
    rw [h0', zero_comp]
  have h2 : T.map ψ ≫ ((toSheaf R).mapIso εN).hom =
      ((toSheaf R).mapIso εM).hom ≫ (toSheaf R).map φ := by
    change (toSheaf R).map (S.map ψ) ≫ (toSheaf R).map εN.hom =
      (toSheaf R).map εM.hom ≫ (toSheaf R).map φ
    rw [← Functor.map_comp, ← Functor.map_comp, hnat]
  have : (toSheaf R).map φ =
      ((toSheaf R).mapIso εM).inv ≫ T.map ψ ≫ ((toSheaf R).mapIso εN).hom :=
    (Iso.eq_inv_comp _).2 h2.symm
  rw [this]
  haveI h1 : Epi (T.map ψ ≫ ((toSheaf R).mapIso εN).hom) :=
    @epi_comp _ _ _ _ _ (T.map ψ) hTψ _ inferInstance
  exact @epi_comp _ _ _ _ _ _ inferInstance _ h1

end SheafOfModules

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Scheme.Modules"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Γ Modules Opens grothendieckTopology PresheafOfModules"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf presheaf"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective.solution {M N : X.Modules} (φ : M ⟶ N) :
    Epi φ ↔ ∀ (U : X.Opens) (s : Γ(N, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ N.presheaf.map (homOfLE i).op s ∈ Set.range (φ.app V) := by

  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have key : Epi φ ↔ Sheaf.IsLocallySurjective (F.map φ) := by
    constructor
    · intro hφ
      have hepi : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ M N φ :=
        ⟨fun g h w => (cancel_epi φ).1 w⟩
      haveI : Epi (F.map φ) :=
        @SheafOfModules.epi_toSheaf_map_of_epi _ _ _ X.ringCatSheaf _ _ M N φ hepi
      exact (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u}) (φ := F.map φ)).2 inferInstance
    · intro h
      haveI : Epi (F.map φ) := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u}) (φ := F.map φ)).1 h
      have hepi : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ M N φ := F.epi_of_epi_map inferInstance
      exact ⟨fun g h w => (@cancel_epi _ _ _ _ _ φ hepi _ _).1 w⟩
  rw [key]
  constructor
  · intro h U s x hx
    obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      (F.map φ).hom (U := op U) s x hx
    exact ⟨V, i.le, hxV, t, ht⟩
  · intro h
    refine ⟨fun {U} s x hx => ?_⟩
    obtain ⟨V, i, hxV, t, ht⟩ := h U s x hx
    exact ⟨V, homOfLE i, ⟨t, ht⟩, hxV⟩

#print axioms solution

end AlgebraicGeometry.Scheme.Modules
end S_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
