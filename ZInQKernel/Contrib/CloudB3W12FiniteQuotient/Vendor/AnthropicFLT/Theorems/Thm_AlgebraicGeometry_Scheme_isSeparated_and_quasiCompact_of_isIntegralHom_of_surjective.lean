/-
Vendored from the Fermat's Last Theorem Lean development (Anthropic).

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective.lean (779 bytes, sha256 81ef711f069bd51e0650ec51c96361367fac32ea2bebfff6bac95a5cb4ed5eaf)
  Copyright      : 2026 Anthropic, PBC
  Licence        : Apache License, Version 2.0 (see LICENSE, NOTICE and NOTICE.md in
                   ZInQKernel/Contrib/CloudB3W12FiniteQuotient/)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), 2026-11-16, cloud batch 3 worker 12: this file has
been changed from the original, mechanically, to build on Lean v4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 (the source builds on Lean v4.33.1 and Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d). No hypothesis or conclusion was weakened,
strengthened or omitted. Changes:
  * `import P2M.Util` removed; the import of the solution module retargeted to `ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective`
  * the proof `by p2m_exact_reverting @_root_.P2MW.S_….solution` replaced by the direct term `P2MW.S_….solution πM πX π hπX hint hsurj hsep hqc` (the same constant, now under the port prefix)
  * file-level `set_option`s reproducing the source lakefile `leanOptions` (autoImplicit false, maxHeartbeats 4000000, synthInstance.maxHeartbeats 400000, backward.isDefEq.respectTransparency.types false), plus `backward.isDefEq.respectTransparency.instanceSearchTypes false` (a Lean 4.35 option absent from Lean 4.33.1; `false` restores the 4.33.1 behaviour); the source file's own `set_option`s are kept and take precedence where they repeat one
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`, so every declaration of the source is isolated under that prefix (the convention of the existing port ZInQKernel/Contrib/CloudW03NeronSurj)
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W12FiniteQuotient.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.Scheme.isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective
    {B : Type u} [CommRing B] {M X : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of B))
    (πX : X ⟶ Spec (CommRingCat.of B)) (π : M ⟶ X) (hπX : π ≫ πX = πM)
    (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
    (hsep : IsSeparated πM) (hqc : QuasiCompact πM) :
    IsSeparated πX ∧ QuasiCompact πX :=
  P2MW.S_AlgebraicGeometry_Scheme_isSeparated_and_quasiCompact_of_isIntegralHom_of_surjective.solution πM πX π hπX hint hsurj hsep hqc

end ZInQ.Contrib.CloudW03NeronSurj.FLT
