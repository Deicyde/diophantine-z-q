/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_TateGlobal_ideleNorm_uniformizerIdele (git blob 3a9c03de78d7e207e975949ff503951e71c77b57, sha256 6cfbcc904f2afd840b53b12f0da20c5f92d0a411be4d6064b38cc4560f4229c0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_HeckeEigenfunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_uniformizerIdele

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel NumberField.TateGlobal

private theorem norm_coe_uniformizerUnit (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ‖(uniformizerUnit F v : v.adicCompletion F)‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, ← WithZero.toAdd_unzero_eq_log WithZero.exp_ne_zero]
  simp only [WithZero.exp, WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv,
    NNReal.coe_natCast]

private theorem norm_one_apply_pow_mult (F : Type) [Field F] [NumberField F]
    (w : InfinitePlace F) : ‖(1 : InfiniteAdeleRing F) w‖ ^ w.mult = 1 := by
  rw [show (1 : InfiniteAdeleRing F) w = 1 from rfl, norm_one, one_pow]

theorem solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  have hfst : (uniformizerIdele F v : AdeleRing (𝓞 F) F).1 = 1 := rfl
  have hself : (uniformizerIdele F v : AdeleRing (𝓞 F) F).2 v
      = (uniformizerUnit F v : v.adicCompletion F) :=
    localUnit_apply_self (𝓞 F) F v (uniformizerUnit F v)
  have hne : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      (uniformizerIdele F v : AdeleRing (𝓞 F) F).2 w = 1 :=
    fun w hw => localUnit_apply_of_ne (𝓞 F) F v (uniformizerUnit F v) hw
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, hfst,
    Finset.prod_eq_one (fun w _ => norm_one_apply_pow_mult F w), one_mul,
    finprod_eq_single _ v (fun w hw => by simp only [hne w hw, norm_one]), hself,
    norm_coe_uniformizerUnit]
