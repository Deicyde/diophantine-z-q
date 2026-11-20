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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.lean
  Source sha256  : 1653497bf28e432f7ace136aa509fb1bd4b9e3b17f90f042f9450a7c7f455358
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
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000`; `set_option synthInstance.maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSimpArgs false`; `set_option linter.unusedVariables false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective
r2nos_namespace_dual

set_option autoImplicit false

w03_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec Scheme Scheme.OrderedAffineCoverOf Scheme.OrderedAffineCoverOf.moduleSections"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Γ Opens OrderedAffineCoverOf OrderedAffineCoverOf.moduleSections"
namespace OrderedAffineCoverOf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.OrderedAffineCoverOf" "Idx inter inter_le_base moduleSections cochain aug iSup_eq ι"
namespace Acyclic
r2nos_namespace_dual
w03_open "AlgebraicGeometry.Scheme.OrderedAffineCoverOf AlgebraicGeometry.Scheme AlgebraicGeometry"

universe u
section ResHelpers

variable {V : Scheme.{u}}

theorem res_refl {O : V.Opens} (h : O ≤ O) (x : Γ(V, O)) :
    (V.presheaf.map (homOfLE h).op).hom x = x := by
  have : (homOfLE h : O ⟶ O) = 𝟙 O := rfl
  rw [this, op_id, V.presheaf.map_id]; rfl

theorem res_res {O₁ O₂ O₃ : V.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃)
    (x : Γ(V, O₃)) :
    (V.presheaf.map (homOfLE h12).op).hom ((V.presheaf.map (homOfLE h23).op).hom x)
      = (V.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem altC_at_eq {W : V.Opens} {K : Scheme.OrderedAffineCoverOf W}
    {n : ℕ} (z : K.cochain n) {σ τ : K.Idx n} (h : σ = τ)
    {O : V.Opens} (hσ : O ≤ K.inter σ) (hτ : O ≤ K.inter τ) :
    (V.presheaf.map (homOfLE hσ).op).hom (z σ)
      = (V.presheaf.map (homOfLE hτ).op).hom (z τ) := by
  subst h; rfl

end ResHelpers

section Idx0
variable {V : Scheme.{u}} {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W) (i₀ : K.ι)

def idx0 : K.Idx 0 :=
  ⟨fun _ => i₀, fun a b h => absurd (Subsingleton.elim (α := Fin 1) a b) (ne_of_lt h)⟩
end Idx0

section CoverOf
variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
include π

theorem aug_injective {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    Function.Injective (K.aug π) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  intro w₁ w₂ hw
  have hcov : W ≤ ⨆ σ : K.Idx 0, K.inter σ :=
    K.iSup_eq.ge.trans (iSup_le fun i => le_iSup_of_le (idx0 K i)
      (le_iInf fun _ => le_rfl))
  exact V.sheaf.eq_of_locally_eq' (K.inter (i := 0)) W
    (fun σ => homOfLE (K.inter_le_base σ)) hcov w₁ w₂ fun σ => congrFun hw σ
end CoverOf

end AlgebraicGeometry.Scheme.OrderedAffineCoverOf.Acyclic

end

universe u

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.AlgebraicGeometry in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.AlgebraicGeometry" in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {W : V.Opens}
    (K : V.OrderedAffineCoverOf W) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    Function.Injective (K.aug π) :=
  Scheme.OrderedAffineCoverOf.Acyclic.aug_injective π K
end S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
