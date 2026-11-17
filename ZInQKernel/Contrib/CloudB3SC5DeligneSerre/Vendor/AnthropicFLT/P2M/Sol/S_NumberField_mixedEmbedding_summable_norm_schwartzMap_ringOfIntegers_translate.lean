/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate (git blob baabe2eb2ad55ad65e312e580a2a5458726ea9b6, sha256 35b7ea3b3a11247bfff638b6f25208d10f78dcc5589ba9e2f7a4c889f4037829).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import Mathlib.Algebra.Module.ZLattice.Summable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate

open NumberField NumberField.mixedEmbedding
open scoped SchwartzMap Classical

noncomputable section

theorem solution
    (F : Type*) [Field F] [NumberField F]
    (g : 𝓢(NumberField.mixedEmbedding.mixedSpace F, ℂ))
    (x : NumberField.mixedEmbedding.mixedSpace F) :
    Summable fun a : 𝓞 F => ‖g (x + NumberField.mixedEmbedding F (a : F))‖ := by
  classical

  let e : 𝓞 F ≃ mixedEmbedding.integerLattice F :=
    Equiv.ofBijective
      (fun a => ⟨mixedEmbedding F (a : F), LinearMap.mem_range.mpr ⟨a, rfl⟩⟩)
      ⟨fun a b hab => RingOfIntegers.coe_injective
          ((mixedEmbedding_injective F) (Subtype.ext_iff.mp hab)),
        fun z => by
          obtain ⟨a, ha⟩ := LinearMap.mem_range.mp z.2
          exact ⟨a, Subtype.ext ha⟩⟩
  have hes : ∀ lam : mixedEmbedding.integerLattice F,
      mixedEmbedding F ((e.symm lam : 𝓞 F) : F) = (lam : mixedSpace F) := fun lam =>
    Subtype.ext_iff.mp (e.apply_symm_apply lam)
  have hfunc : (fun a : 𝓞 F => ‖g (x + mixedEmbedding F (a : F))‖) ∘ e.symm
      = fun lam : mixedEmbedding.integerLattice F => ‖g (x + (lam : mixedSpace F))‖ := by
    funext lam; simp only [Function.comp_apply, hes]
  rw [← Equiv.summable_iff e.symm, hfunc]

  set d : ℕ := Module.finrank ℤ (mixedEmbedding.integerLattice F) + 1 with hd
  have hd_lt : Module.finrank ℤ (mixedEmbedding.integerLattice F) < d := Nat.lt_succ_self _

  have hsum : Summable fun lam : mixedEmbedding.integerLattice F =>
      ‖(lam : mixedSpace F) - (-x)‖⁻¹ ^ d := by
    have hr : (-(d : ℝ)) < -(Module.finrank ℤ (mixedEmbedding.integerLattice F) : ℝ) := by
      simp only [neg_lt_neg_iff]; exact_mod_cast hd_lt
    have hZ := ZLattice.summable_norm_sub_rpow (L := mixedEmbedding.integerLattice F)
      (r := -(d : ℝ)) hr (-x)
    refine hZ.congr fun lam => ?_
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, inv_pow]

  refine Summable.of_norm_bounded_eventually
    (g := fun lam : mixedEmbedding.integerLattice F =>
      SchwartzMap.seminorm ℝ d 0 g * ‖(lam : mixedSpace F) - (-x)‖⁻¹ ^ d)
    (hsum.mul_left _) ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset
    (Set.Subsingleton.finite (s := {lam : mixedEmbedding.integerLattice F | (lam : mixedSpace F) = -x})
      fun a₁ h₁ a₂ h₂ => Subtype.coe_injective (h₁.trans h₂.symm)) ?_
  intro lam hlam
  simp only [Set.mem_setOf_eq] at hlam ⊢
  by_contra hne
  apply hlam

  have hne0 : x + (lam : mixedSpace F) ≠ 0 := by
    intro h0; exact hne ((neg_eq_of_add_eq_zero_right h0).symm)
  have hpos : (0 : ℝ) < ‖x + (lam : mixedSpace F)‖ ^ d := pow_pos (norm_pos_iff.mpr hne0) _
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ g d (x + (lam : mixedSpace F))

  have hnorm : ‖(lam : mixedSpace F) - (-x)‖ = ‖x + (lam : mixedSpace F)‖ := by
    rw [sub_neg_eq_add, add_comm]
  rw [norm_norm, hnorm, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
  exact hdecay
