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
  Source file    : Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.lean
  Source sha256  : 6483dd70c9e61690ee75d4961f642c36b2878e0a830ace0a3937df1c5f631143
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.LinearAlgebra.TensorProduct.Prod
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct"

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (e0 : (A ⊗[R] (𝒱.cover c).A0) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A0)
      (e1 : (A ⊗[R] (𝒱.cover c).A1) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A1)
      (e01 : (A ⊗[R] (𝒱.cover c).A01) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
      (eH0 : LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A) ≃ₗ[A]
          ((𝒱.pullback c A).structureSheafSections
            (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H0)
      (eH1 : ((A ⊗[R] (𝒱.cover c).A01) ⧸ LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange A))
          ≃ₗ[A] ((𝒱.pullback c A).structureSheafSections
            (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H1),
      (∀ s, e0 ((1 : A) ⊗ₜ[R] s) = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app 𝒱.U0).hom s) ∧
      (∀ s, e1 ((1 : A) ⊗ₜ[R] s) = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app 𝒱.U1).hom s) ∧
      (∀ s, e01 ((1 : A) ⊗ₜ[R] s)
          = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) ∧
      (∀ x, ((eH0 x : _ × _)) = (e0 (TensorProduct.prodRight R A A _ _ x.1).1,
          e1 (TensorProduct.prodRight R A A _ _ x.1).2)) ∧
      (∀ y, eH1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e01 y)) := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
