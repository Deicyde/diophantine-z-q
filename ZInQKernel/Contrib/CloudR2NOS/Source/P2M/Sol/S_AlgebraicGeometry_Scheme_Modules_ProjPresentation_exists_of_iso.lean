/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import(s) of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (re-provides, under the port prefix, db584 API this file's source relies on and Mathlib 56a removed or moved).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (Lean closes these implicitly at EOF in the original; no-op).
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

open Opposite
r2nos_open_dual "Opposite"

namespace PresIso
r2nos_namespace_dual

variable {X : Scheme.{u}} {M M' : X.Modules}

theorem map_app (φ : M ⟶ M') {U V : X.Opens} (i : V ⟶ U) (s : Γ(M, U)) :
    M'.presheaf.map i.op (φ.app U s) = φ.app V (M.presheaf.map i.op s) := by
  have h := φ.mapPresheaf.naturality i.op
  have := congrArg (fun f => (ConcreteCategory.hom f) s) h
  simpa using this.symm

theorem app_bijective (e : M ≅ M') (U : X.Opens) : Function.Bijective (e.hom.app U) :=
  ConcreteCategory.bijective_of_isIso (e.hom.app U)

noncomputable def transport {R : Type u} [CommRing R] {f : X ⟶ Spec (.of R)} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (e : M ≅ M') : M'.ProjPresentation f N where
  σ := fun i => e.hom.app ⊤ (𝔓.σ i)
  toProj := 𝔓.toProj
  toProj_π := 𝔓.toProj_π
  frame := fun i V hV => by
    have key : (fun g : Γ(X, V) => g • M'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (e.hom.app ⊤ (𝔓.σ i)))
        = (e.hom.app V) ∘ (fun g : Γ(X, V) => g • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (𝔓.σ i)) := by
      funext g
      simp only [Function.comp_apply, map_app, Scheme.Modules.Hom.app_smul]
    rw [key]
    exact (app_bijective e V).comp (𝔓.frame i V hV)
  app_ratio_smul := fun i j => by
    rw [map_app, map_app, ← Scheme.Modules.Hom.app_smul, 𝔓.app_ratio_smul i j]

end PresIso

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M M' : X.Modules} {N : ℕ}
    (𝔓 : M.ProjPresentation f N) (e : M ≅ M') :
    ∃ 𝔓' : M'.ProjPresentation f N, 𝔓'.toProj = 𝔓.toProj ∧ ∀ i, 𝔓'.σ i = (e.hom.app ⊤) (𝔓.σ i) :=
  ⟨PresIso.transport 𝔓 e, rfl, fun _ => rfl⟩

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
