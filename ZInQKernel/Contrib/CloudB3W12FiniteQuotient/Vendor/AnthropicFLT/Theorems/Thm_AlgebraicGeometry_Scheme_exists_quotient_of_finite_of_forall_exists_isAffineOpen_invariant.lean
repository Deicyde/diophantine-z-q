/-
Vendored from the Fermat's Last Theorem Lean development (Anthropic).

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant.lean (1390 bytes, sha256 4fe420e08648ba7f6c4ac1947ab5090ff37163bf3f829de9d3d48173bdb9d24c)
  Copyright      : 2026 Anthropic, PBC
  Licence        : Apache License, Version 2.0 (see LICENSE, NOTICE and NOTICE.md in
                   ZInQKernel/Contrib/CloudB3W12FiniteQuotient/)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), 2026-11-16, cloud batch 3 worker 12: this file has
been changed from the original, mechanically, to build on Lean v4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 (the source builds on Lean v4.33.1 and Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d). No hypothesis or conclusion was weakened,
strengthened or omitted. Changes:
  * `import P2M.Util` removed; the import of the solution module retargeted to `ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant`
  * 6 occurrences of `(ρ g).hom` written `(ρ g).asIso.hom` (Mathlib 56a: `CategoryTheory.Aut X` is a structure with field `asIso`)
  * the proof `by p2m_exact_reverting @_root_.P2MW.S_….solution` replaced by the direct term `P2MW.S_….solution ρ hadm` (the same constant, now under the port prefix)
  * file-level `set_option`s reproducing the source lakefile `leanOptions` (autoImplicit false, maxHeartbeats 4000000, synthInstance.maxHeartbeats 400000, backward.isDefEq.respectTransparency.types false), plus `backward.isDefEq.respectTransparency.instanceSearchTypes false` (a Lean 4.35 option absent from Lean 4.33.1; `false` restores the 4.33.1 behaviour); the source file's own `set_option`s are kept and take precedence where they repeat one
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`, so every declaration of the source is isolated under that prefix (the convention of the existing port ZInQKernel/Contrib/CloudW03NeronSurj)
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

open AlgebraicGeometry CategoryTheory

universe u v

theorem AlgebraicGeometry.Scheme.exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
    {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)
    (hadm : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U) :
    ∃ (Y : Scheme.{u}) (π : X ⟶ Y) (hπ : ∀ g : G, (ρ g).asIso.hom ≫ π = π),
      IsIntegralHom π ∧ IsAffineHom π ∧ Function.Surjective π.base ∧
      (∀ x x' : X, π.base x = π.base x' ↔ ∃ g : G, (ρ g).asIso.hom.base x = x') ∧
      (∀ V : Y.Opens, Function.Injective (π.app V)) ∧
      (∀ V : Y.Opens, Set.range (π.app V) =
        {s | ∀ g : G, (ρ g).asIso.hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
          (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s}) ∧
      (∀ U : X.Opens, IsAffineOpen U → (∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U) →
        ∃ V : Y.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U) ∧
      (∀ (T : Scheme.{u}) (f : X ⟶ T), (∀ g : G, (ρ g).asIso.hom ≫ f = f) →
        ∃! f' : Y ⟶ T, π ≫ f' = f) :=
  P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant.solution ρ hadm

end ZInQ.Contrib.CloudW03NeronSurj.FLT
