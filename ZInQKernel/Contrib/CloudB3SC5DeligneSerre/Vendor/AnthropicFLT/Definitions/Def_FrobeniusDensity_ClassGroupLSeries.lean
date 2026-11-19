/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_FrobeniusDensity_ClassGroupLSeries (git blob 4d75a5fe47b8a243baf0deb3a8afa6f0e892b9f8, sha256 3f4f98fc8209bb008d5c0a54a4953a5b20a3b9342711cbcb2af6e9a3a7a9bc6b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Filter Ideal NumberField NumberField.InfinitePlace NumberField.Units Topology
  nonZeroDivisors

open scoped Real

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

def classZetaCoeff (C : ClassGroup (𝓞 K)) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C}

def classZeta (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ classZetaCoeff K C n) s

def classResidue : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
    (torsionOrder K * Real.sqrt |discr K|)

def classGroupLSeries (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℂ) : ℂ :=
  ∑ C : ClassGroup (𝓞 K), χ C * classZeta K C s

def LSeriesInheritsPole (χ : ClassGroup (𝓞 K) →* ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ s : ℝ in 𝓝[>] 1, c ≤ ‖(fun s : ℝ ↦ (s - 1) * classGroupLSeries K χ s) s‖

end

end FrobeniusDensity
