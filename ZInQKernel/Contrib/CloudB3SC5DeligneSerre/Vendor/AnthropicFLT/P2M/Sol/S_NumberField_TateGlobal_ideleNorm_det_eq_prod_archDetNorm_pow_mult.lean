/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult (git blob 4f898a72d873a850fc6611e4758c16d21bb7aa5a, sha256 c0ef9855883dab23210f28461a58748e78d02c1e8ca24d5f11e89397eb359d47).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult

set_option autoImplicit false

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.NumberField
open _root_.NumberField.AdelicLevel
open _root_.NumberField.AdelicVolume
open _root_.NumberField.TateGlobal
namespace NumberField.TateGlobal
end NumberField.TateGlobal
open _root_.P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.NumberField.TateGlobal
open _root_.AutomorphicForm
open IsDedekindDomain
open scoped MatrixGroups

namespace NumberField
export _root_.NumberField (FinitePlace place InfinitePlace AdeleRing FinitePlace.norm_def AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm)
namespace TateGlobal
export _root_.NumberField.TateGlobal (ideleNorm)
namespace IdeleNormDetGlue
open _root_.NumberField.TateGlobal
open _root_.NumberField

variable {F : Type} [Field F] [NumberField F]

private theorem norm_eq_zpow_of_valued (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F} {m : ℤ}
    (hx : Valued.v x = WithZero.exp m) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, ← WithZero.toAdd_unzero_eq_log WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

private theorem valued_det_le_one (v : HeightOneSpectrum (𝓞 F)) {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (h : ∀ i j, Valued.v (M i j) ≤ 1) : Valued.v M.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
  · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

private theorem det_snd_apply (X : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
      = ((finComponent (𝓞 F) F v (glFin (𝓞 F) F X) : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)) (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

private theorem det_fst_apply (X : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = ((archComponent F w (glArch (𝓞 F) F X) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((archEval F w).comp (adeleArch (𝓞 F) F)) (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

private theorem valued_det_finComponent_eq_one (X : AdelicGL2 (𝓞 F) F)
    (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((finComponent (𝓞 F) F v (glFin (𝓞 F) F X) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
  set A := finComponent (𝓞 F) F v (glFin (𝓞 F) F X) with hA
  obtain ⟨h1, h2⟩ := mem_finiteIntegralGL2_iff.mp hX
  have ha : Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≤ 1 :=
    valued_det_le_one v fun i j =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h1 i j v)
  have hb : Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      ≤ 1 := by
    rw [hA, ← map_inv]
    exact valued_det_le_one v fun i j =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h2 i j v)
  have hab : (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      * ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hprod : Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      * Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
        = 1 := by
    rw [← map_mul, hab, map_one]
  refine le_antisymm ha ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
          * Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
              Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := hprod.symm
    _ ≤ Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det * 1 := mul_le_mul_right hb _
    _ = _ := mul_one _

private theorem ideleNorm_det_eq_prod_archDetNorm_pow (X : AdelicGL2 (𝓞 F) F)
    (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det X)
      = ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult := by
  have hS := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F
    (Matrix.GeneralLinearGroup.det X)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    intro v
    rw [det_snd_apply, norm_eq_zpow_of_valued v (m := 0)
      (by rw [valued_det_finComponent_eq_one X hX v, WithZero.exp_zero]), zpow_zero]
  have harch : ∀ w : InfinitePlace F,
      ‖((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖
        = archDetNorm w X := by
    intro w
    rw [det_fst_apply]
    rfl
  unfold ideleNorm
  rw [hS, finprod_eq_one_of_forall_eq_one hfin, mul_one]
  exact Finset.prod_congr rfl fun w _ => by rw [harch w]

end NumberField.TateGlobal.IdeleNormDetGlue

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.NumberField
open _root_.NumberField.AdelicLevel
open _root_.NumberField.AdelicVolume
open _root_.AutomorphicForm

open _root_.NumberField.TateGlobal _root_.P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.NumberField.TateGlobal NumberField.TateGlobal.IdeleNormDetGlue in

theorem solution (F : Type) [Field F] [NumberField F]
    (X : AdelicGL2 (𝓞 F) F) (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det X) = ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult :=
  ideleNorm_det_eq_prod_archDetNorm_pow X hX
