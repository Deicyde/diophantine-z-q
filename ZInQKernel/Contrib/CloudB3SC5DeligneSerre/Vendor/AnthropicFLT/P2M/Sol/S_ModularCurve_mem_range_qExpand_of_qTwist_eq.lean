/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_mem_range_qExpand_of_qTwist_eq (git blob 94b72de88effd6990825a2e7d41859c076bf6234, sha256 e422d73730519271671a3e0dc5e8265483906bdb913cd862f6a1d47b9e98946f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_mem_range_qExpand_of_qTwist_eq

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (qTwist qTwist_coeff qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd)
open _root_.ModularCurve

theorem coeff_eq_zero_of_qTwist_eq {K : Type*} [Field K] (n : ℕ) [NeZero n] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) n) (f : LaurentSeries K) (h : qTwist ζ f = f) {k : ℤ}
    (hk : ¬ (n : ℤ) ∣ k) : f.coeff k = 0 := by
  have hc := congrArg (fun g : LaurentSeries K => g.coeff k) h
  simp only [qTwist_coeff] at hc

  have hne : ((ζ ^ k : Kˣ) : K) ≠ 1 := by
    rw [Units.val_zpow_eq_zpow_val]
    exact fun h1 => hk ((hζ.zpow_eq_one_iff_dvd k).mp h1)
  have : (((ζ ^ k : Kˣ) : K) - 1) * f.coeff k = 0 := by rw [sub_mul, one_mul, hc, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hne
  · exact h0

theorem mem_range_qExpand_of_qTwist_eq' {K : Type*} [Field K] (n : ℕ) [NeZero n] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) n) (f : LaurentSeries K) (h : qTwist ζ f = f) :
    f ∈ Set.range (qExpand K n) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

  have hbdd : BddBelow (Function.support fun m : ℤ => f.coeff ((n : ℤ) * m)) := by
    refine ⟨min f.order 0, fun m hm => ?_⟩
    have hm' : f.coeff ((n : ℤ) * m) ≠ 0 := hm
    have hord : f.order ≤ (n : ℤ) * m := HahnSeries.order_le_of_coeff_ne_zero hm'
    rcases le_or_gt 0 m with h0 | h0
    · exact (min_le_right _ _).trans h0
    · have : (n : ℤ) * m ≤ m := by nlinarith
      exact (min_le_left _ _).trans (hord.trans this)
  refine ⟨HahnSeries.ofSuppBddBelow _ hbdd, ?_⟩
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, HahnSeries.coeff_ofSuppBddBelow]
  · rw [qExpand_coeff_of_not_dvd n _ hk, coeff_eq_zero_of_qTwist_eq n ζ hζ f h hk]

end ModularCurve

theorem solution {K : Type*} [Field K] (n : ℕ) [NeZero n] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) n) (f : LaurentSeries K) (h : ModularCurve.qTwist ζ f = f) : f ∈ Set.range (ModularCurve.qExpand K n) :=
  ModularCurve.mem_range_qExpand_of_qTwist_eq' n ζ hζ f h
