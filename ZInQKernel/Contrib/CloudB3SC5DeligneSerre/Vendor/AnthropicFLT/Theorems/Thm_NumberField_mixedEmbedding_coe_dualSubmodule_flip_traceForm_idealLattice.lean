/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice (git blob 7f8d819091a6c695061cb65dea4c88a63ce743e0, sha256 564a46694796bc0fd5b861d74011a1d9bff1676c7dfe98f7874d751dc27ca25b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors
theorem NumberField.mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice
    (K : Type*) [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ (mixedSpace K)).flip
        (mixedEmbedding.idealLattice K I) : Set (mixedSpace K))
      = mixedEmbedding K '' (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
  revert K I
  exact @_root_.P2MW.S_NumberField_mixedEmbedding_coe_dualSubmodule_flip_traceForm_idealLattice.solution
