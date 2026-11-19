/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WLight_levelOne_hauptmodul_package (git blob 1c3ef9c98320d907e3cc588eb2fbf993dc382353, sha256 fd7675ab7eefe412845f18a7235558440079b1952a9fdffc9623257ea3b2b4a3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.Notation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WLight_levelOne_hauptmodul_package

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Complex Real Polynomial
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

theorem WLight.levelOne_hauptmodul_package :

    (∀ (m : ℕ) (h : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
      (∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) →
      IsBoundedAtImInfty (h * ModularForm.discriminant ^ m) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
        h = fun τ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P) ∧

    (∀ (k : IntermediateField ℚ ℂ) (N : ℕ), N ≠ 0 → ∀ (m : ℕ) (h : ℍ → ℂ),
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
      (∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) →
      Function.Periodic ((h * ModularForm.discriminant ^ m) ∘ ofComplex) N →
      IsBoundedAtImInfty (h * ModularForm.discriminant ^ m) →
      (∀ n : ℕ, (qExpansion N (h * ModularForm.discriminant ^ m)).coeff n ∈ k) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ (∀ i, P.coeff i ∈ k) ∧
        h = fun τ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P) ∧

    Function.Surjective (fun τ : ℍ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) ∧

    (∀ (m : ℕ) (P : Polynomial ℂ), P.natDegree ≤ m →
      (∀ n : ℕ, ∃ q : ℚ, (∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (P.coeff i) * qExpansion 1 ⇑ModularForm.E₄ ^ (3 * i) *
            qExpansion 1 ModularForm.discriminant ^ (m - i)).coeff n = (q : ℂ)) →
      ∀ i : ℕ, ∃ q : ℚ, P.coeff i = (q : ℂ)) ∧

    (∀ (k : IntermediateField ℚ ℂ) (m : ℕ) (P : Polynomial ℂ), P.natDegree ≤ m →
      (∀ n : ℕ, (∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (P.coeff i) * qExpansion 1 ⇑ModularForm.E₄ ^ (3 * i) *
            qExpansion 1 ModularForm.discriminant ^ (m - i)).coeff n ∈ k) →
      ∀ i : ℕ, P.coeff i ∈ k) := @_root_.P2MW.S_WLight_levelOne_hauptmodul_package.solution
