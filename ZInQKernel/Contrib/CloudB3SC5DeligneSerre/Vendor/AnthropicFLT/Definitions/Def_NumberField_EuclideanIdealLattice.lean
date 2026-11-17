/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_NumberField_EuclideanIdealLattice (git blob 8abee5c2056317b201b28e8b9a0e0a3624d1dc06, sha256 019fb7c4fdc7a9161234fe45d44229656b0840dac1b0a0ee9b6a95350e004957).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding
open scoped nonZeroDivisors

noncomputable section

namespace Deep.Analytic

variable (K : Type*) [Field K] [NumberField K]

open Classical in

def euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I) (euclidean.toMixed K).toLinearMap

end Deep.Analytic

namespace M4aP2

variable (K : Type*) [Field K] [NumberField K]

def heckeScale (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  (|(discr K : ℝ)| * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2)
    ^ (-(1 : ℝ) / (Module.finrank ℚ K : ℝ))

end M4aP2

end
