import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.MixedPeterssonRational
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ActualMixedSpanBridge

/-!
# Orthogonality of positive rational translates against mixed test products

Let `f` be a weight-three cusp form for `Γ(N)` (`N ≥ 3`) that is Petersson-orthogonal to the
same-level mixed space. For every `g ∈ GL(2, ℚ)` of positive determinant, every common level `L`
(`N ∣ L` and `g Γ(L) g⁻¹ ≤ Γ(N)`) and every test form `G` in the span of the mixed products
`x_U λ_V` at level `L`, the pairing `⟪f ∣ g, G⟫_{Γ(L)}` vanishes. The transport of `G ∣ g⁻¹` into
a mixed span at a level divisible by `L` is the positive-rational mixed transport theorem, applied
with `A = g⁻¹`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.MixedPeterssonRationalBinder

open MixedPeterssonTrace

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

theorem ratGL_eq_map (g : GL (Fin 2) ℚ) :
    ratGL g = Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g := by
  have h : (algebraMap ℚ ℝ) = Rat.castHom ℝ := RingHom.ext_rat _ _
  rw [ratGL, h]

theorem ratGL_det_pos (g : GL (Fin 2) ℚ) (hdetQ : 0 < ((g.det : ℚˣ) : ℚ)) :
    0 < ((ratGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  have h : ((ratGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
      ((((g.det : ℚˣ) : ℚ)) : ℝ) := by
    change ((Rat.castHom ℝ).mapMatrix (g : Matrix (Fin 2) (Fin 2) ℚ)).det = _
    rw [← RingHom.map_det]
    rfl
  rw [h]
  exact_mod_cast hdetQ

open ConjAct in
/-- **Rational-translate orthogonality against mixed test products**, with no transport
hypothesis. -/
theorem rational_translate_lowerMixed_orthogonal (g : GL (Fin 2) ℚ)
    (hdetQ : 0 < ((g.det : ℚˣ) : ℚ))
    (N L : ℕ) [NeZero N] [NeZero L] (h3 : 3 ≤ N) (hNL : N ∣ L)
    (hconj : toConjAct (ratGL g) • (ΓP L) ≤ ΓP N)
    (f : CuspForm (ΓP N) 3)
    (horth : ∀ G ∈ MixedAllLevelTrace.mixedSpace N (by omega), cuspModPairing f G = 0)
    (G : _root_.ModularForm (ΓP L) 3)
    (hG : G ∈ RepeatedPrimeMixedTrace.lowerMixedSpan L (Nat.pos_of_ne_zero (NeZero.ne L))) :
    cuspModPairing (CuspForm.restrict (translate_level_le g N L hconj)
      (CuspForm.translate f (ratGL g))) G = 0 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hGm : G ∈ RectangularMixedTransport.mixedSpan L hL := by
    rw [ActualMixedSpanBridge.mixedSpan_eq_lowerMixedSpan]
    exact hG
  have hdetInv : 0 < (((g⁻¹).det : ℚˣ) : ℚ) := by
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hdetQ
  obtain ⟨M, hM, hLM, F, hF, hFeq⟩ :=
    RationalMixedTransport.actual_positive_rational_mixed_transport L hL G hGm g⁻¹ hdetInv
  refine MixedPeterssonRational.rational_translate_mixed_orthogonal g (ratGL_det_pos g hdetQ)
    N L h3 hNL hconj f horth G ⟨M, hM, hLM, F, ?_, fun τ => ?_⟩
  · apply Submodule.mem_sup_left
    rw [← ActualMixedSpanBridge.mixedSpan_eq_lowerMixedSpan]
    exact hF
  · rw [hFeq τ, ratGL_eq_map, map_inv]

end ZInQ.Contrib.HeckePrimeRationality.MixedPeterssonRationalBinder
