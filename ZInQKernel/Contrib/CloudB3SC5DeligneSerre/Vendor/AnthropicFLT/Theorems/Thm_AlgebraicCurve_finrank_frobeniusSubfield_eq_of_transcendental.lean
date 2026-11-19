/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental (git blob 1b790d81da964822cc4b00a6943d957a50f95d01, sha256 ae19d6693f9ad754913f4b7c10ea3eeb4badee1675925a61dac495bbed08ca6c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.finrank_frobeniusSubfield_eq_of_transcendental {K M : Type*} [Field K] [Field M] [Algebra K M]
    [PerfectField K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (t : M) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M] :
    haveI : ExpChar M p := expChar_of_injective_algebraMap (algebraMap K M).injective p
    Module.finrank ↥(frobenius M p).fieldRange M = p := by
  revert K M p hp t htr
  exact @_root_.P2MW.S_AlgebraicCurve_finrank_frobeniusSubfield_eq_of_transcendental.solution
