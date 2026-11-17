/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_FrobeniusDensity_DegOneAsymptotic (git blob a43b42173f51ab8fc573798c7a43f3684395c900, sha256 3fa91cc61916676dd0c95fc1a691282e1437d24b71ca03b2bdd4e28c78ab3ef7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TaylorWiles_Primes
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Fixed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped NNReal
open Filter Topology Asymptotics

namespace FrobeniusDensity

open NumberField Ideal

section DegOneCount

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

noncomputable def degOneCount (ℓ : ℕ) : ℕ :=
  if ℓ.Prime then
    {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver (𝓞 K) | Nat.card ((𝓞 K) ⧸ 𝔮) = ℓ}.ncard
  else 0

end DegOneCount

section AnalyticInput

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

def DegOneAsymptotic : Prop :=
  ∀ (H : Subgroup (L ≃ₐ[ℚ] L)) (S₀ : Finset ℕ),
    (∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
        (degOneCount (FixedPoints.intermediateField H : IntermediateField ℚ L) ℓ : ℝ))
      * (ℓ : ℝ) ^ (-s))) ∧
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (degOneCount (FixedPoints.intermediateField H : IntermediateField ℚ L) ℓ : ℝ))
      * (ℓ : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ))

end AnalyticInput

end FrobeniusDensity
