/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_NumberField_CompletedRayL (git blob c00c163ef467e387bbb4ce284bfb9fc8c605a034, sha256 77de528a686fea526ce3873c96914f496aca00f1cbfcdc58398290f70184b1b0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NarrowRayClassGroup
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace Complex Deep.NTSupply nonZeroDivisors

namespace M4aTorus

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def rayZetaCoeff (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧
    ∃ hc : FractionalIdeal.mk0 K I ∈ coprimeToModulus K 𝔣,
      NarrowRayClassGroup.mk K 𝔣 ⟨FractionalIdeal.mk0 K I, hc⟩ = C}

def rayZeta (𝔣 : Ideal (𝓞 K)) (C : NarrowRayClassGroup K 𝔣) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ rayZetaCoeff K 𝔣 C n) s

def rayClassLSeries (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (s : ℂ) : ℂ :=
  ∑' C : NarrowRayClassGroup K 𝔣, χ C * rayZeta K 𝔣 C s

def completedRayL (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) : ℝ) : ℂ) ^ (s / 2) *
    Gammaℝ s ^ (nrRealPlaces K - S.card) * Gammaℝ (s + 1) ^ S.card *
    Gammaℂ s ^ nrComplexPlaces K * rayClassLSeries K 𝔣 χ s

end

end M4aTorus
