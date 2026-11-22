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
  Source file    : Definitions/Def_AlgebraicGeometry_ModulesTildePullback.lean
  Source sha256  : 3c4db8c92a0b6a8022c3854b303950ad4b168f63125c6e7fe219c7c1399d6914
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
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

universe u

open CategoryTheory AlgebraicGeometry Opposite
r2nos_open_dual "CategoryTheory AlgebraicGeometry Opposite"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency false in

def Scheme.Modules.pushforwardSpecCompΓIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents
    (fun N => LinearEquiv.toModuleIso
      (X₁ := (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).obj N)
      (X₂ := (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj N)
      { __ := AddEquiv.refl _
        map_smul' := fun r m => by
          change (ModuleCat.restrictScalars (StructureSheaf.globalSectionsIso R).hom.hom).obj _ at m
          erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
          erw [ModuleCat.restrictScalars.smul_def, ModuleCat.restrictScalars.smul_def]
          simp only [AddEquiv.toFun_eq_coe, AddEquiv.refl_apply, RingHom.id_apply]
          have h1 : (Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤) =
              𝟙 (op (⊤ : (Spec (.of R)).Opens)) :=
            (Limits.initialOpOfTerminal Limits.isTerminalTop).hom_ext _ _
          have h2 : (Limits.initialOpOfTerminal Limits.isTerminalTop).to (op ⊤) =
              𝟙 (op (⊤ : (Spec (.of S)).Opens)) :=
            (Limits.initialOpOfTerminal Limits.isTerminalTop).hom_ext _ _
          simp only [h1, h2, CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply]
          congr 1
          have key := congrArg (fun ψ : R ⟶ Γ(Spec S, ⊤) => ψ.hom r) (Scheme.ΓSpecIso_inv_naturality φ)
          simp only [Scheme.ΓSpecIso_inv, StructureSheaf.globalSectionsIso_hom] at key
          exact key.symm })
    (fun f => by ext; rfl)

def tilde.functorCompPullbackSpecIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  Adjunction.leftAdjointUniq
    ((tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
      (Scheme.Modules.pushforwardSpecCompΓIso φ).symm)

def tilde.pullbackSpecIso (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      tilde ((ModuleCat.extendScalars φ.hom).obj M) :=
  (tilde.functorCompPullbackSpecIso φ).app M

@[simp] theorem tilde.functorCompPullbackSpecIso_app (M : ModuleCat.{u} R) :
    (tilde.functorCompPullbackSpecIso φ).app M = tilde.pullbackSpecIso φ M := rfl

theorem tilde.pullbackSpecIso_hom_naturality {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (Scheme.Modules.pullback (Spec.map φ)).map ((tilde.functor R).map f) ≫
        (tilde.pullbackSpecIso φ M').hom =
      (tilde.pullbackSpecIso φ M).hom ≫ (tilde.functor S).map ((ModuleCat.extendScalars φ.hom).map f) :=
  (tilde.functorCompPullbackSpecIso φ).hom.naturality f

end AlgebraicGeometry

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
