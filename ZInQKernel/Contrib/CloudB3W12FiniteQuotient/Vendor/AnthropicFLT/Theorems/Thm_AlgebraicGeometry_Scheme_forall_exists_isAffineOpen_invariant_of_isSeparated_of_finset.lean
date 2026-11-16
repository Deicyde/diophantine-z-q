/-
Vendored from the Fermat's Last Theorem Lean development (Anthropic).

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset.lean (809 bytes, sha256 bfa0782482181655cd66372e23bc761f51d7acbc528b2fd7fc8dc5c6b7c092c6)
  Copyright      : 2026 Anthropic, PBC
  Licence        : Apache License, Version 2.0 (see LICENSE, NOTICE and NOTICE.md in
                   ZInQKernel/Contrib/CloudB3W12FiniteQuotient/)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), 2026-11-16, cloud batch 3 worker 12: this file has
been changed from the original, mechanically, to build on Lean v4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 (the source builds on Lean v4.33.1 and Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d). No hypothesis or conclusion was weakened,
strengthened or omitted. Changes:
  * `import P2M.Util` removed; the import of the solution module retargeted to `ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset`
  * 1 occurrences of `(ρ g).hom` written `(ρ g).asIso.hom` (Mathlib 56a: `CategoryTheory.Aut X` is a structure with field `asIso`)
  * the proof `by p2m_exact_reverting @_root_.P2MW.S_….solution` replaced by the direct term `P2MW.S_….solution πX hsep hAF ρ` (the same constant, now under the port prefix)
  * file-level `set_option`s reproducing the source lakefile `leanOptions` (autoImplicit false, maxHeartbeats 4000000, synthInstance.maxHeartbeats 400000, backward.isDefEq.respectTransparency.types false), plus `backward.isDefEq.respectTransparency.instanceSearchTypes false` (a Lean 4.35 option absent from Lean 4.33.1; `false` restores the 4.33.1 behaviour); the source file's own `set_option`s are kept and take precedence where they repeat one
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`, so every declaration of the source is isolated under that prefix (the convention of the existing port ZInQKernel/Contrib/CloudW03NeronSurj)
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u v

theorem AlgebraicGeometry.Scheme.forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset
    {B : Type u} [CommRing B] {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of B)) (hsep : IsSeparated πX)
    (hAF : ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X) :
    ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U :=
  P2MW.S_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset.solution πX hsep hAF ρ

end ZInQ.Contrib.CloudW03NeronSurj.FLT
