/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward (git blob 9c16fd9b4566ef76b9ca78bbb6c0a358a00b0c5f, sha256 73ce2cfb2de730d788d8072e7a8ce7cfbecb978b601afb62ea4759e60983df7c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_of_ord_nonneg
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_support_pushforward_subset

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward

open AlgebraicCurve AlgebraicCurve.Divisor

private theorem zpow_finset_sum' {K : Type*} [Field K] {c : K} (hc : c ≠ 0) {ι : Type*}
    (s : Finset ι) (n : ι → ℤ) : ∏ i ∈ s, c ^ n i = c ^ (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : F} (hg : g ≠ 0) (D : Divisor K F') (hratw : ∀ w ∈ D.support, Place.IsRational w) (hratv : ∀ w ∈ D.support, (w.restrict F).IsRational) (hord : ∀ w ∈ D.support, (w.restrict F).ord g = 0) : Divisor.evalFun (algebraMap F F' g) D = Divisor.evalFun g (Divisor.pushforward F D) := by
  classical
  have hstep1 : evalFun (algebraMap F F' g) D
      = ∏ w ∈ D.support, (w.restrict F).evalAt g ^ D w := by
    rw [evalFun_def]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [w.evalAt_algebraMap_eq_evalAt_restrict (hratv w hw)
      ((w.restrict F).mem_of_ord_nonneg hg (hord w hw).ge)]
  have hne : ∀ w ∈ D.support, (w.restrict F).evalAt g ≠ 0 := fun w hw =>
    (w.restrict F).evalAt_ne_zero (hratv w hw) hg (hord w hw)
  have hstep2 : ∏ w ∈ D.support, (w.restrict F).evalAt g ^ D w
      = ∏ v ∈ D.support.image (fun w => w.restrict F),
          ∏ w ∈ D.support with w.restrict F = v, (w.restrict F).evalAt g ^ D w :=
    (Finset.prod_fiberwise_of_maps_to
      (fun w hw => Finset.mem_image.mpr ⟨w, hw, rfl⟩) _).symm
  have hstep3 : ∀ v ∈ D.support.image (fun w => w.restrict F),
      (∏ w ∈ D.support with w.restrict F = v, (w.restrict F).evalAt g ^ D w)
        = v.evalAt g ^ (pushforward F D v) := by
    intro v hv
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hv
    calc
      ∏ w ∈ D.support with w.restrict F = w₀.restrict F, (w.restrict F).evalAt g ^ D w
          = ∏ w ∈ D.support with w.restrict F = w₀.restrict F,
              (w₀.restrict F).evalAt g ^ (D w * (w.inertiaDeg F : ℤ)) := by
            refine Finset.prod_congr rfl fun w hw => ?_
            obtain ⟨hwD, hwv⟩ := Finset.mem_filter.mp hw
            rw [hwv, w.inertiaDeg_eq_one_of_isRational (hratw w hwD) (hratv w hwD),
              Nat.cast_one, mul_one]
      _ = (w₀.restrict F).evalAt g
            ^ (∑ w ∈ D.support with w.restrict F = w₀.restrict F,
                D w * (w.inertiaDeg F : ℤ)) :=
            zpow_finset_sum' (hne w₀ hw₀) _ _
      _ = (w₀.restrict F).evalAt g ^ (pushforward F D (w₀.restrict F)) := by
            rw [pushforward_apply, Finset.sum_filter]
  rw [hstep1, hstep2, Finset.prod_congr rfl hstep3]
  exact (Finsupp.prod_of_support_subset _ (support_pushforward_subset D)
    (fun v n => v.evalAt g ^ n) fun v _ => zpow_zero _).symm
