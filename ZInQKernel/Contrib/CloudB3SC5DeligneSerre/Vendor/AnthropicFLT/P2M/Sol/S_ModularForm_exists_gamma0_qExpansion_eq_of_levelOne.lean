/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne (git blob 96dc9329a1957efbee5ed349fafd4e5ca69b450f, sha256 df4b0969d2a931706d77ea56b7fe7c05e3504be0e5a34c750dd26d4c77512099).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularForm_exists_degeneracy_Gamma0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne

open UpperHalfPlane
open scoped MatrixGroups

namespace SolRESTRAux

private theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private theorem gamma0_one_coe :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  simp [gamma0_one_eq_top, MonoidHom.range_eq_map]

private theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  simp [Matrix.one_fin_two]

end SolRESTRAux

theorem solution (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ∃ G : ModularForm (CongruenceSubgroup.Gamma0 N) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by
  obtain ⟨G, hG⟩ := ModularForm.exists_degeneracy_Gamma0 (show 1 * 1 ∣ N by simp)
    (ModularForm.mcast rfl F SolRESTRAux.gamma0_one_coe)
  refine ⟨G, ?_⟩
  rw [hG, SolRESTRAux.heckeDiagMatrix_one]
  funext τ
  rw [one_smul]
  rfl
