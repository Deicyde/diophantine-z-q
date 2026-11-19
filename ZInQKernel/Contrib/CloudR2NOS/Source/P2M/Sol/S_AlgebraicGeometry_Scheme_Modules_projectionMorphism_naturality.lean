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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_projectionMorphism_naturality.lean
  Source sha256  : ed072376dedd9b8b9a81d7125b052f3805bf27aa9cf4a84d5f630be644350177
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_projectionMorphism_naturality
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {Z X : Scheme.{u}} (i : Z ⟶ X) {F F' : X.Modules} (φ : F ⟶ F') :
    Scheme.Modules.projectionMorphism i F ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ) =
      ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ φ) ≫ Scheme.Modules.projectionMorphism i F' := by

  have hmate : Scheme.Modules.projectionMorphismMate i F ≫ (Scheme.Modules.pullback i).map φ =
      (Scheme.Modules.pullback i).map ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ φ) ≫
        Scheme.Modules.projectionMorphismMate i F' := by
    rw [Scheme.Modules.projectionMorphismMate_def, Scheme.Modules.projectionMorphismMate_def,
      Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_inv]
    simp only [Category.assoc]

    have s1 : ∀ {M M' : Z.Modules} (ψ : M ⟶ M') (W : Z.Modules) (c : W ⟶ 𝟙_ Z.Modules),
        c ▷ M ≫ (λ_ M).hom ≫ ψ = W ◁ ψ ≫ c ▷ M' ≫ (λ_ M').hom := by
      intro M M' ψ W c
      exact ((MonoidalCategory.whisker_exchange_assoc c ψ (λ_ M').hom).symm ▸
        congrArg (fun t => c ▷ M ≫ t) (MonoidalCategory.leftUnitor_naturality ψ).symm :)
    exact (congrArg (fun t => Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i) _ _ ≫ t) (s1 _ _ _)).trans
      (Functor.OplaxMonoidal.δ_natural_right_assoc (Scheme.Modules.pullback i) _ φ _)

  have e1 := Adjunction.homEquiv_naturality_right (Scheme.Modules.pullbackPushforwardAdjunction i)
    (Scheme.Modules.projectionMorphismMate i F) ((Scheme.Modules.pullback i).map φ)
  have e2 := Adjunction.homEquiv_naturality_left (Scheme.Modules.pullbackPushforwardAdjunction i)
    ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ φ) (Scheme.Modules.projectionMorphismMate i F')
  exact e1.symm.trans ((congrArg _ hmate).trans e2)
end S_AlgebraicGeometry_Scheme_Modules_projectionMorphism_naturality
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
