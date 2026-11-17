/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_weilReciprocity_algebraMap (git blob c52fc1485e3ce626f1ef5d855ab93020a30af0f5, sha256 4d2f96162eff16bb81a886b44e264c443ba0e652f19b95c3c55b37cd29c3bebd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_norm_eq_zero_of_forall_fiber
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_pushforward_div
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_evalFun_pullback
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_weilReciprocity_algebraMap

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F] [HasPrincipalDivisors K F] [HasPrincipalDivisors K F'] (hbase : WeilReciprocity K F) {f : F'} {g : F} (hf : f ≠ 0) (hg : g ≠ 0) (Df Dg : Divisor K F') (hDf : ∀ w : Place K F', Df w = w.ord f) (hDg : ∀ w : Place K F', Dg w = w.ord (algebraMap F F' g)) (hdisj : ∀ w : Place K F', w.ord f = 0 ∨ w.ord (algebraMap F F' g) = 0) (hratf : ∀ w ∈ Df.support, Place.IsRational w) (hratF : ∀ v : Place K F, v.IsRational) (hratfib : ∀ v : Place K F, v.ord g ≠ 0 → ∀ w ∈ v.fiber F', Place.IsRational w) : Divisor.evalFun f Dg = Divisor.evalFun (algebraMap F F' g) Df := by
  classical
  have hNf : Algebra.norm F f ≠ 0 := Algebra.norm_ne_zero_iff.mpr hf
  obtain ⟨Eg, hEg, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  obtain ⟨EN, hEN, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (Algebra.norm F f) hNf
  have hfib : ∀ v : Place K F, v.ord g ≠ 0 → ∀ w ∈ v.fiber F', w.ord f = 0 := by
    intro v hv w hw
    refine (hdisj w).resolve_right ?_
    rw [w.ord_restrict (F := F) g, Place.mem_fiber.mp hw]
    have hepos := w.ramificationIndex_pos (F := F)
    exact mul_ne_zero (by exact_mod_cast hepos.ne') hv
  have hres : ∀ w : Place K F', w.ord f ≠ 0 → (w.restrict F).ord g = 0 := by
    intro w hw
    have hzero := (hdisj w).resolve_left hw
    rw [w.ord_restrict (F := F) g] at hzero
    have hepos := w.ramificationIndex_pos (F := F)
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (by exact_mod_cast hepos.ne')
    · exact h
  have hdisjF : ∀ v : Place K F, v.ord (Algebra.norm F f) = 0 ∨ v.ord g = 0 := by
    intro v
    rcases eq_or_ne (v.ord g) 0 with h | h
    · exact Or.inr h
    · exact Or.inl (AlgebraicCurve.Place.ord_norm_eq_zero_of_forall_fiber hf v (hfib v h))
  have hstep1 : Dg = Divisor.pullback F' Eg := by
    ext w
    rw [hDg w, Divisor.pullback_apply_eq_ord (fun u => hEg u)]
  have hstep4 : Divisor.pushforward F Df = EN :=
    AlgebraicCurve.Divisor.pushforward_div hf hDf hEN
  have hstep2 : Divisor.evalFun f (Divisor.pullback F' Eg)
      = Divisor.evalFun (Algebra.norm F f) Eg := by
    refine AlgebraicCurve.Divisor.evalFun_pullback hf Eg (fun v _ => hratF v) (fun v hv w hw => ?_)
      (fun v hv w hw => ?_)
    · exact hratfib v (by rw [← hEg v]; exact Finsupp.mem_support_iff.mp hv) w hw
    · exact hfib v (by rw [← hEg v]; exact Finsupp.mem_support_iff.mp hv) w hw
  have hstep3 : Divisor.evalFun (Algebra.norm F f) Eg = Divisor.evalFun g EN :=
    hbase (Algebra.norm F f) g EN Eg hNf hg hEN hEg hdisjF
      (fun v _ => hratF v) (fun v _ => hratF v)
  have hstep5 : Divisor.evalFun (algebraMap F F' g) Df
      = Divisor.evalFun g (Divisor.pushforward F Df) := by
    refine AlgebraicCurve.Divisor.evalFun_algebraMap_pushforward hg Df (fun w hw => hratf w hw)
      (fun w _ => hratF _) (fun w hw => ?_)
    exact hres w (by rw [← hDf w]; exact Finsupp.mem_support_iff.mp hw)
  rw [hstep1, hstep2, hstep3, ← hstep4, ← hstep5]
