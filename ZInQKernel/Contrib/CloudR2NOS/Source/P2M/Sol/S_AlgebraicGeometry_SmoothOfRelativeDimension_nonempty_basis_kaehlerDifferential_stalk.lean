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
  Source file    : P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk.lean
  Source sha256  : 1d07a4e8660a0de61d60324933ef528038cad0e146c183d0bd0e5c7c0b6451c7
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
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

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

universe u

theorem solution
    {k : Type u} [Field k] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p] (y : Y) :
    letI : Algebra k (Y.presheaf.stalk y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.toAlgebra
    Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄k])) := by
  classical
  letI algk : Algebra k (Y.presheaf.stalk y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom.toAlgebra
  obtain ⟨U, hU, V, hV, hyV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := p) y

  have hUtop : U = ⊤ := by
    ext z
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have hz : z = p y := Subsingleton.elim _ _
    rw [hz]; exact e hyV
  subst hUtop
  set A := Γ(Y, V) with hA

  letI algA : Algebra k Γ(Y, V) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ V e).hom.toAlgebra
  letI algVs : Algebra Γ(Y, V) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hyV⟩
  haveI : IsScalarTower k Γ(Y, V) (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq fun r => by
    show ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom r =
      (Y.presheaf.germ V y hyV).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ V e).hom r)
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    rfl

  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(Y, V) := by
    have h := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso
      (Scheme.ΓSpecIso (.of k)).inv (p.appLE ⊤ V e) |>.mpr hf
    rw [← CommRingCat.hom_comp] at h
    exact h
  haveI := hstd
  haveI : Algebra.IsStandardSmooth k Γ(Y, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Nontrivial Γ(Y, V) := (algebraMap Γ(Y, V) (Y.presheaf.stalk y)).domain_nontrivial
  have hrank : Module.rank Γ(Y, V) Ω[Γ(Y, V)⁄k] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  haveI : Module.Finite Γ(Y, V) Ω[Γ(Y, V)⁄k] := Module.finite_of_rank_eq_nat hrank
  let bA : Module.Basis (Fin n) Γ(Y, V) Ω[Γ(Y, V)⁄k] :=
    Module.finBasisOfFinrankEq _ _ (Module.finrank_eq_of_rank_eq hrank)

  haveI := hV.isLocalization_stalk ⟨y, hyV⟩
  exact ⟨bA.ofIsLocalizedModule (Y.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl
    (KaehlerDifferential.map k k Γ(Y, V) (Y.presheaf.stalk y))⟩
end S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
