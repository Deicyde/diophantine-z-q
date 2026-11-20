/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ValuationSubring_isAlgClosed_residueField (git blob a49772595181d139d48c2c6329bbb1fe4798a9df, sha256 043748dddc203657628be625798f4fdb39f91227903cde32ab33d36f75d53273).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.Polynomial.Lifts
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_exists_root_mem_of_monic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ValuationSubring_isAlgClosed_residueField

set_option autoImplicit false

open IsLocalRing

theorem solution {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro p hmonic hirr
  have hlift : p ∈ Polynomial.lifts (residue A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => residue_surjective _
  obtain ⟨f, hmap, hdeg, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  have hd : f.natDegree ≠ 0 := by
    rw [Polynomial.natDegree_eq_of_degree_eq hdeg]
    exact hirr.natDegree_pos.ne'
  obtain ⟨x, hx⟩ := ValuationSubring.exists_root_mem_of_monic A f hf hd
  refine ⟨residue A x, ?_⟩
  have hx0 : f.eval x = 0 := by
    have h1 : (algebraMap A K) (f.eval x) = 0 := by
      rw [← hx, Polynomial.aeval_def]
      exact (Polynomial.eval₂_at_apply (algebraMap A K) x).symm
    exact Subtype.coe_injective (by simpa using h1)
  rw [← hmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hx0, map_zero]
