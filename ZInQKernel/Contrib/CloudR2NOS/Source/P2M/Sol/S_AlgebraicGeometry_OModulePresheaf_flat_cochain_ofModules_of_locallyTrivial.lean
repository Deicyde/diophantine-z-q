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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial.lean
  Source sha256  : 6d8f256bb4bd0dabcf7acddca832cc36fb47165f1e8ee355f3f1616acb9b5f29
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
r2nos_namespace_dual

universe u

set_option autoImplicit false
section cechflat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace"

namespace CechFlatSol
r2nos_namespace_dual

theorem isAffineOpen_inter {V : Scheme.{u}} [V.IsSeparated] (K : V.OrderedAffineCover) :
    ∀ (n : ℕ) (s : K.Idx n), IsAffineOpen (K.inter s) := by
  intro n
  induction n with
  | zero =>
    intro s
    have : K.inter s = K.U (s.1 0) := by
      apply le_antisymm (K.inter_le s 0)
      exact le_iInf fun j => by rw [Subsingleton.elim (α := Fin 1) j 0]
    rw [this]
    exact K.isAffineOpen _
  | succ n ih =>
    intro s
    have : K.inter s = K.U (s.1 0) ⊓ K.inter (K.face s 0) := by
      apply le_antisymm
      · exact le_inf (K.inter_le s 0) (K.inter_le_inter_face s 0)
      · refine le_iInf fun j => ?_
        refine Fin.cases ?_ (fun k => ?_) j
        · exact inf_le_left
        · exact inf_le_right.trans (by
            have := K.inter_le (K.face s 0) k
            rw [K.face_val] at this
            simpa [Fin.succAbove_zero] using this)
    rw [this]
    exact (K.isAffineOpen _).inf (ih _)

end CechFlatSol

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [Flat π] [IsSeparated π] (M : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (K : V.OrderedAffineCover) (i : ℕ) :
    Module.Flat R ((OModulePresheaf.ofModules π M).cochain K i) := by
  classical
  haveI : V.IsSeparated := by
    constructor
    rw [show terminal.from V = π ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance
  haveI : ∀ s : K.Idx i, Module.Flat R ((OModulePresheaf.ofModules π M).obj (K.inter s)) := fun s => by
    have haff : IsAffineOpen (K.inter s) := CechFlatSol.isAffineOpen_inter K i s
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π (K.inter s)
    haveI : Module.Flat R Γ(V, K.inter s) := Scheme.TwoAffineOpenCover.flat_sections_of_flat π _ haff
    haveI : Module.Projective Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s)) :=
      Scheme.Modules.projective_sections_of_locallyTrivial M htriv ⟨K.inter s, haff⟩
    haveI : Module.Flat Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s)) :=
      Module.Flat.of_projective
    exact Module.Flat.trans R Γ(V, K.inter s) ((OModulePresheaf.ofModules π M).obj (K.inter s))
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype R (K.Idx i) fun s => (OModulePresheaf.ofModules π M).obj (K.inter s)).symm

end cechflat
end S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
