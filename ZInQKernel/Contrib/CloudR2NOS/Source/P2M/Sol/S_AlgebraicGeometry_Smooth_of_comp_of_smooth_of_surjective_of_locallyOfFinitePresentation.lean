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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation.lean
  Source sha256  : 7948a89f86358775739bee1212914b6d73877d963727ea586026b69ee0361472
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Algebra_IsSmoothAt_of_isSmoothAt_of_smooth
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation
r2nos_namespace_dual

set_option autoImplicit false

universe u

open TensorProduct
r2nos_open_dual "TensorProduct"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

theorem solution
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth f] [Surjective f] [QuasiCompact f]
    [Smooth (f ≫ g)] [LocallyOfFinitePresentation g] : Smooth g := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro y -
  obtain ⟨x, rfl⟩ := f.surjective y

  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (f x))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (U.2.preimage g.continuous)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hyV)
      (V.2.preimage f.continuous)
  have hWU : W ≤ (f ≫ g) ⁻¹ᵁ U := fun w hw => hVU (hWV hw)

  have hfp := g.finitePresentation_appLE hU hV hVU
  have hsm := f.smooth_appLE hV hW hWV
  letI algRS := (g.appLE U V hVU).hom.toAlgebra
  letI algST := (f.appLE V W hWV).hom.toAlgebra
  letI algRT := ((f ≫ g).appLE U W hWU).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, W) := IsScalarTower.of_algebraMap_eq fun r => by
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE f g U V W hVU hWV]
  haveI : Algebra.FinitePresentation Γ(Z, U) Γ(Y, V) := hfp
  haveI : Algebra.Smooth Γ(Y, V) Γ(X, W) := hsm

  have hx' : Algebra.IsSmoothAt Γ(Z, U) (hW.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    have H : ((f ≫ g).stalkMap x).hom.FormallySmooth :=
      (Scheme.Hom.mem_smoothLocus (f := f ≫ g)).mp (by rw [Scheme.Hom.smoothLocus_eq_top]; trivial)
    exact (formallySmooth_stalkMap_iff U hU W hW hWU hxW).mp H

  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff U hU V hV hVU hyV]

  have hunder : (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.under Γ(Y, V) = (hV.primeIdealOf ⟨f x, hyV⟩).asIdeal := by
    rw [Ideal.under_def]
    exact congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV W hW hWV hxW).1)
  exact Algebra.IsSmoothAt.of_isSmoothAt_of_smooth Γ(Z, U) Γ(Y, V) Γ(X, W) _ hx' _ hunder

#print axioms solution
end S_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
