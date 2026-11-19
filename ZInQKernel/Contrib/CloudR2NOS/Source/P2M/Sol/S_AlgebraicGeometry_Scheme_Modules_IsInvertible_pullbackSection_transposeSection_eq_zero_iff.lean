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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff.lean
  Source sha256  : b0908d57e47566d8e84f4252cf0b10bc7d28dc4e337a25c490e2c32d3e26e6a1
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff
r2nos_namespace_dual

section E6Coev
set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff.AlgebraicGeometry"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.dual Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Modules.pullback mk Modules evaluation Modules.IsInvertible Modules.dual Modules.pullbackSection Modules.pullbackSection_def"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "pullback IsInvertible dual pullbackSection pullbackSection_def IsInvertible.dual"
namespace CoevAux
r2nos_namespace_dual
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {Y : Scheme.{u}}

def tensorLeftEquivalence {Z Z' : Y.Modules} (i : Z' ⊗ Z ≅ 𝟙_ Y.Modules) (j : Z ⊗ Z' ≅ 𝟙_ Y.Modules) :
    Y.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (tensorLeft Z) (tensorLeft Z')
    ((leftUnitorNatIso Y.Modules).symm ≪≫ (tensoringLeft Y.Modules).mapIso i.symm ≪≫ tensorLeftTensor Z' Z)
    ((tensorLeftTensor Z Z').symm ≪≫ (tensoringLeft Y.Modules).mapIso j ≪≫ leftUnitorNatIso Y.Modules)

def tensorRightEquivalence {Z Z' : Y.Modules} (i : Z' ⊗ Z ≅ 𝟙_ Y.Modules) (j : Z ⊗ Z' ≅ 𝟙_ Y.Modules) :
    Y.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (tensorRight Z) (tensorRight Z')
    ((rightUnitorNatIso Y.Modules).symm ≪≫ (tensoringRight Y.Modules).mapIso j.symm ≪≫ tensorRightTensor Z Z')
    ((tensorRightTensor Z' Z).symm ≪≫ (tensoringRight Y.Modules).mapIso i ≪≫ rightUnitorNatIso Y.Modules)

theorem isEquivalence_tensorLeft {Z : Y.Modules} (hZ : Scheme.Modules.IsInvertible Z) :
    (tensorLeft Z).IsEquivalence :=
  (tensorLeftEquivalence (β_ _ _ ≪≫ hZ.dual.2.some) hZ.dual.2.some).isEquivalence_functor

theorem isEquivalence_tensorRight {Z : Y.Modules} (hZ : Scheme.Modules.IsInvertible Z) :
    (tensorRight Z).IsEquivalence :=
  (tensorRightEquivalence (β_ _ _ ≪≫ hZ.dual.2.some) hZ.dual.2.some).isEquivalence_functor

theorem isIso_ev_app (X : Y.Modules) (hX : Scheme.Modules.IsInvertible X) (N : Y.Modules) :
    IsIso ((ihom.ev X).app N) := by
  haveI := isEquivalence_tensorLeft hX
  let e : ihom X ≅ (tensorLeft X).inv :=
    (ihom.adjunction X).rightAdjointUniq (tensorLeft X).asEquivalence.toAdjunction
  haveI : (ihom X).Full := Functor.Full.of_iso e.symm
  haveI : (ihom X).Faithful := Functor.Faithful.of_iso e.symm
  haveI : IsIso (ihom.adjunction X).counit := Adjunction.counit_isIso_of_R_fully_faithful _
  exact NatIso.isIso_app_of_isIso (ihom.adjunction X).counit N

theorem whiskerRight_eq_zero_iff {L M Z : Y.Modules} (hZ : Scheme.Modules.IsInvertible Z) (f : L ⟶ M) :
    f ▷ Z = 0 ↔ f = 0 := by
  haveI := isEquivalence_tensorRight hZ
  constructor
  · intro h
    apply (tensorRight Z).map_injective
    rw [Functor.map_zero]
    exact h
  · rintro rfl
    exact (tensorRight Z).map_zero _ _

theorem transposeSection_eq_zero_iff' {X M : Y.Modules} (hX : Scheme.Modules.IsInvertible X) (φ : X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.dual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.dual X) :
    s = 0 ↔ φ = 0 := by

  have hiso := isIso_ev_app X hX (𝟙_ Y.Modules)
  rw [← whiskerRight_eq_zero_iff hX.dual.1 φ, ← hs]
  exact (@Preadditive.IsIso.comp_left_eq_zero _ _ _ _ _ _ _ s hiso).symm

theorem pullbackSection_transposeSection_eq_zero_iff' {Y' : Scheme.{u}} (g : Y' ⟶ Y) {X M : Y.Modules}
    (hX : Scheme.Modules.IsInvertible X) (φ : X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.dual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.dual X) :
    Scheme.Modules.pullbackSection g s = 0 ↔ (Scheme.Modules.pullback g).map φ = 0 := by
  have hiso := isIso_ev_app X hX (𝟙_ Y.Modules)
  have hiso' : IsIso ((Scheme.Modules.pullback g).map ((ihom.ev X).app (𝟙_ Y.Modules))) :=
    let e := (Scheme.Modules.pullback g).mapIso (@asIso _ _ _ _ ((ihom.ev X).app (𝟙_ Y.Modules)) hiso)
    ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  have h1 : (Scheme.Modules.pullback g).map ((ihom.ev X).app (𝟙_ Y.Modules)) ≫ (Scheme.Modules.pullback g).map s
      = (Scheme.Modules.pullback g).map (φ ▷ Scheme.Modules.dual X) :=
    ((Scheme.Modules.pullback g).map_comp _ _).symm.trans (congrArg _ hs)
  calc Scheme.Modules.pullbackSection g s = 0
      ↔ (Scheme.Modules.pullback g).map s = 0 := by
        rw [Scheme.Modules.pullbackSection_def]
        exact Preadditive.IsIso.comp_left_eq_zero _ _
    _ ↔ (Scheme.Modules.pullback g).map ((ihom.ev X).app (𝟙_ Y.Modules)) ≫ (Scheme.Modules.pullback g).map s = 0 :=
        (@Preadditive.IsIso.comp_left_eq_zero _ _ _ _ _ _ _ _ hiso').symm
    _ ↔ (Scheme.Modules.pullback g).map (φ ▷ Scheme.Modules.dual X) = 0 :=
        iff_of_eq (congrArg (fun t => t = 0) h1)
    _ ↔ Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) X (Scheme.Modules.dual X) ≫
          ((Scheme.Modules.pullback g).map φ ▷ (Scheme.Modules.pullback g).obj (Scheme.Modules.dual X)) ≫
          Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) M (Scheme.Modules.dual X) = 0 :=
        iff_of_eq (congrArg (fun t => t = 0) (Functor.Monoidal.map_whiskerRight _ _ _))
    _ ↔ ((Scheme.Modules.pullback g).map φ ▷ (Scheme.Modules.pullback g).obj (Scheme.Modules.dual X)) ≫
          Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) M (Scheme.Modules.dual X) = 0 :=
        Preadditive.IsIso.comp_left_eq_zero _ _
    _ ↔ (Scheme.Modules.pullback g).map φ ▷ (Scheme.Modules.pullback g).obj (Scheme.Modules.dual X) = 0 :=
        Preadditive.IsIso.comp_right_eq_zero _ _
    _ ↔ (Scheme.Modules.pullback g).map φ = 0 := whiskerRight_eq_zero_iff (hX.dual.1.pullback g) _

end AlgebraicGeometry.Scheme.Modules.CoevAux

open CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff.AlgebraicGeometry in
r2nos_open_dual "CategoryTheory CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff.AlgebraicGeometry" in
theorem solution
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {X M : Y.Modules} (hX : Scheme.Modules.IsInvertible X) (φ : X ⟶ M)
    (s : 𝟙_ Y.Modules ⟶ M ⊗ Scheme.Modules.dual X)
    (hs : (ihom.ev X).app (𝟙_ Y.Modules) ≫ s = φ ▷ Scheme.Modules.dual X) :
    Scheme.Modules.pullbackSection g s = 0 ↔ (Scheme.Modules.pullback g).map φ = 0 :=
  AlgebraicGeometry.Scheme.Modules.CoevAux.pullbackSection_transposeSection_eq_zero_iff' g hX φ s hs

end
end E6Coev
end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_transposeSection_eq_zero_iff
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
