/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det (git blob eff3215b687f2aca3fe705d4f6c72dfb1e0d4de1, sha256 40c261f0fa93e72f437bfd6c7f91cf571268e8e9dd9cbaa165cf40a664468590).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 1}
    (hε : CuspForm.HasNebentypus ε F)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (ρ : Fin (p + 1) → GL (Fin 2) ℚ_[p])
    (hρ : ∀ i : Fin (p + 1), ((ρ i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      if (i : ℕ) < p then !![(1 : ℚ_[p]), ((i : ℕ) : ℚ_[p]); 0, (p : ℚ_[p])]
      else !![(p : ℚ_[p]), 0; 0, 1])
    {h : AdelicGL2 (𝓞 ℚ) ℚ}
    (hh : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    ∑ i : Fin (p + 1), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (h * AdelicDock.padicToAdelic p (ρ i)⁻¹) =
      (p : ℂ) *
        ((((ε (p : ZMod N))⁻¹ • ModularForm.heckeU 1 p ⇑F +
              (⇑F) ∣[(1 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(1 : ℤ)]
            LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I *
          (((LanglandsTunnell.ratArchGL2 h).det.val : ℝ) : ℂ)) := by
  revert N ε F hε p hpN ρ hρ h hh hpos
  exact @_root_.P2MW.S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det.solution
