/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Theorems/Thm_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField.lean
  Retrieved      : 2026-11-16 (local clone at revision above, byte-for-byte before modification)
  Licence        : Apache License, Version 2.0 (see LICENSE and NOTICE in
                   ZInQKernel/Contrib/CloudB3W12Tame/Vendor/AnthropicFLT/)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudB3W12Tame.Vendor.AnthropicFLT.*`.
  * 1 `import P2M.Util` removed.
  * `by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField.solution` (a custom tactic that reverts the context and applies the term) replaced by the direct term `P2MW.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField.solution K₀ 𝒪 u hu0 hu` (resolved inside the port namespace).
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudB3W12Tame.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT


set_option autoImplicit false

universe u v

open IsLocalRing Polynomial

theorem Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_isSeparable_residueField
    (K₀ : Type u) [Field K₀] (𝒪 : Type v) [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪]
    [Algebra K₀ 𝒪] [Algebra.EssFiniteType K₀ 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u})
    [Algebra.IsAlgebraic K₀ (ResidueField 𝒪)] [Algebra.IsSeparable K₀ (ResidueField 𝒪)] :
    Algebra.FormallySmooth K₀ 𝒪 :=
  P2MW.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_isSeparable_residueField.solution K₀ 𝒪 u hu0 hu

end ZInQ.Contrib.CloudW03NeronSurj.FLT
