import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Dilation
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Permutation

/-! The normalized `U_(p²)` preserves the half-integral comparison at
a level divisible by `4` and `p` (tex 9514–9542). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenMoving

open BlocksPerU EvenExpansion HalfIntegral CongruenceSubgroup Matrix Matrix.SpecialLinearGroup
open ModularGroup UpperHalfPlane PrintsAnalytic Filter Asymptotics
open scoped MatrixGroups Manifold BigOperators Topology

/-- The individual translate `(z+r)/n` occurring in the normalized sum. -/
def unscalePoint (n : ℕ) [NeZero n] (r : ZMod n) : ℍ → ℍ :=
  affinePoint (n : ℚ)⁻¹ (r.val / (n : ℚ)) (inv_pos.mpr (Nat.cast_pos.mpr (NeZero.pos n)))

theorem unscalePoint_coe (n : ℕ) [NeZero n] (r : ZMod n) (z : ℍ) :
    (unscalePoint n r z : ℂ) = ((z : ℂ) + (r.val : ℂ)) / n := by
  rw [unscalePoint, affinePoint_coe]
  push_cast
  ring

theorem Up_eq_affine (n : ℕ) [NeZero n] (g : ℍ → ℂ) (z : ℍ) :
    Up n g z = (n : ℂ)⁻¹ * ∑ r : ZMod n, g (unscalePoint n r z) := by
  unfold Up
  congr 1
  refine Finset.sum_congr rfl fun r _ => congrArg g (UpperHalfPlane.ext ?_)
  rw [coe_vadd, unscalePoint_coe]
  change (((r.val : ℝ) / n : ℝ) : ℂ) + ((n : ℝ)⁻¹ : ℝ) * (z : ℂ) = _
  push_cast
  ring

private theorem two_scale_unscale {p : ℕ} [NeZero (p ^ 2)] (hp : 0 < p)
    (r : ZMod (p ^ 2)) (z : ℍ) :
    scalePoint p hp (scalePoint p hp (unscalePoint (p ^ 2) r z)) = T ^ (r.val : ℤ) • z := by
  apply UpperHalfPlane.ext
  rw [scalePoint_coe, scalePoint_coe, unscalePoint_coe, modular_T_zpow_smul, coe_vadd]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hp.ne']
  exact add_comm _ _

private theorem scalePoint_inj (p : ℕ) (hp : 0 < p) : Function.Injective (scalePoint p hp) := by
  intro z w h
  apply UpperHalfPlane.ext
  have h' := congrArg ((↑) : ℍ → ℂ) h
  simp only [scalePoint_coe] at h'
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hp.ne') h'

/-- The actual transformed translate, its unchanged multiplier, and its
bottom-right residue all arise from the same permutation of the sum. -/
theorem upSquare_terms {m p : ℕ} [Fact p.Prime] [NeZero (p ^ 2)]
    (h4 : 4 ∣ m) (hpm : p ∣ m) (hodd : Odd p) (γ : ↥(Gamma0 m)) :
    ∃ e : Equiv.Perm (ZMod (p ^ 2)), ∀ r, ∃ δ : ↥(Gamma0 m),
      (((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod m) = (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod m) ∧
      (∀ z : ℍ,
        unscalePoint (p ^ 2) r ((γ : SL(2, ℤ)) • z) =
          (δ : SL(2, ℤ)) • unscalePoint (p ^ 2) (e r) z) ∧
      (∀ z : ℍ,
        thetaMultiplier δ (unscalePoint (p ^ 2) (e r) z) = thetaMultiplier γ z) := by
  let hp := (Fact.out : p.Prime)
  let A := (γ : SL(2, ℤ))
  let a := A 0 0
  let b := A 0 1
  let c := A 1 0
  let d := A 1 1
  have hcm : (m : ℤ) ∣ c := (mem_level_iff A).mp γ.property
  have hcp : (p : ℤ) ∣ c := (Int.natCast_dvd_natCast.mpr hpm).trans hcm
  obtain ⟨e, he⟩ := upSquare_conjugation hp (m : ℤ) a b c d (det_eq A) hcp hcm
  refine ⟨e, fun r => ?_⟩
  obtain ⟨u, hu, hdet, hcm', hdm'⟩ := he r
  let s := (r.val : ℤ)
  let t := ((e r).val : ℤ)
  let D : SL(2, ℤ) := ⟨!![a + s*c, u; (p : ℤ)^2*c, d-c*t], by
    simpa only [Matrix.det_fin_two, Fin.isValue, of_apply, cons_val_zero, cons_val_one,
      empty_val'] using hdet⟩
  have hDm : D ∈ Gamma0 m := (mem_level_iff D).mpr hcm'
  have hDp : (p : ℤ) ∣ D 1 0 := dvd_mul_of_dvd_left (dvd_pow_self _ (by decide : 2 ≠ 0)) _
  let B := scaleLower p D hDp
  obtain ⟨ha1, hb1, hc1, hd1⟩ := scaleLower_entries p D hDp
  have hcB : B 1 0 = (p : ℤ) * c := by
    apply mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)
    rw [hc1]
    change (p : ℤ)^2 * c = _
    ring
  have hBm : B ∈ Gamma0 m := (mem_level_iff B).mpr (hcB.symm ▸ dvd_mul_of_dvd_right hcm _)
  let E := T ^ s * A * T ^ (-t)
  obtain ⟨ha2, hb2, hc2, hd2⟩ := leftT_entries A s
  obtain ⟨ha3, hb3, hc3, hd3⟩ := rightT_entries (T ^ s * A) (-t)
  have hAE : E 0 0 = B 0 0 := by rw [ha3, ha2, ha1]; rfl
  have hBE : E 0 1 = (p : ℤ) * B 0 1 := by
    rw [hb3, ha2, hb2, hb1]
    change b + s*d + (a+s*c) * (-t) = (p : ℤ) * ((p : ℤ) * u)
    change b + s*d = (a+s*c)*t + (p : ℤ)^2*u at hu
    linear_combination hu
  have hCE : (p : ℤ) * E 1 0 = B 1 0 := by rw [hc3, hc2, hcB]
  have hDE : E 1 1 = B 1 1 := by
    rw [hd3, hc2, hd2, hd1]
    change d + c * (-t) = d - c*t
    ring
  have hEm : E ∈ Gamma0 m := (mem_level_iff E).mpr (by rwa [hc3, hc2])
  have h4B := (Int.natCast_dvd_natCast.mpr h4).trans ((mem_level_iff B).mp hBm)
  have h4E := (Int.natCast_dvd_natCast.mpr h4).trans ((mem_level_iff E).mp hEm)
  have hentry : ((D 1 1 : ℤ) : ZMod m) = ((A 1 1 : ℤ) : ZMod m) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by
      change (m : ℤ) ∣ d - (d - c*t)
      simpa only [neg_sub] using dvd_neg.mpr hdm')
  have hcancel (z : ℍ) : T ^ (-t) • (T ^ t • z) = z := by
    rw [← mul_smul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, one_smul]
  refine ⟨⟨D, hDm⟩, hentry, fun z => ?_, fun z => ?_⟩
  · let w := unscalePoint (p ^ 2) (e r) z
    apply (scalePoint_inj p hp.pos).comp (scalePoint_inj p hp.pos)
    change scalePoint p hp.pos (scalePoint p hp.pos (unscalePoint (p ^ 2) r (A • z))) =
      scalePoint p hp.pos (scalePoint p hp.pos (D • w))
    rw [two_scale_unscale hp.pos, ← scale_smul p hp.pos D B ha1 hb1 hc1 hd1,
      ← scale_smul p hp.pos B E hAE hBE hCE hDE]
    change T ^ s • (A • z) = E • (scalePoint p hp.pos (scalePoint p hp.pos
      (unscalePoint (p ^ 2) (e r) z)))
    rw [two_scale_unscale hp.pos]
    change T ^ s • (A • z) = (T ^ s * A * T ^ (-t)) • (T ^ t • z)
    rw [mul_smul, hcancel, mul_smul]
  · let w := unscalePoint (p ^ 2) (e r) z
    have hθ1 := thetaMultiplier_scale h4 hpm hodd D B hDm h4B ha1 hb1 hc1 hd1 w
    have hθ2 := thetaMultiplier_scale h4 hpm hodd B E hBm h4E hAE hBE hCE hDE
      (scalePoint p hp.pos w)
    rw [hd1, hθ1, ← mul_assoc, ← pow_two,
      primeCharacter_sq h4 hpm (AppE.isCoprime_d_of_mem_Gamma0 hDm), one_mul] at hθ2
    have hθ3 : thetaMultiplier E (scalePoint p hp.pos (scalePoint p hp.pos w)) =
        thetaMultiplier A z := by
      rw [show scalePoint p hp.pos (scalePoint p hp.pos w) = T ^ t • z from
        two_scale_unscale hp.pos (e r) z]
      simp only [E, thetaMultiplier_rightT, thetaMultiplier_leftT, hcancel]
    exact hθ2.symm.trans hθ3

/-- The cusp bound is stable under the normalized finite sum. -/
theorem Up_cusps {n : ℕ} [NeZero n] (k : ℝ) {g : ℍ → ℂ}
    (hg : ∀ γ : SL(2, ℤ), IsBoundedAtImInfty (cuspNorm k g γ)) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (cuspNorm k (Up n g) γ) := by
  classical
  let F (r : ZMod n) : ℍ → ℝ := cuspNorm k (fun z => g (unscalePoint n r z)) γ
  have hF (r : ZMod n) : F r ∈ boundedAtImInftySubalgebra ℝ :=
    affinePoint_cusps k hg _ _ _ γ
  have hsum : (∑ r : ZMod n, F r) ∈ boundedAtImInftySubalgebra ℝ :=
    (boundedAtImInftySubalgebra ℝ).sum_mem (fun r _ => hF r)
  have ht : BoundedAtFilter atImInfty ((‖(n : ℂ)⁻¹‖ : ℝ) • ∑ r : ZMod n, F r) :=
    BoundedAtFilter.smul _ hsum
  refine (isBigO_of_le atImInfty ?_).trans ht
  intro z
  have he : ∀ r, 0 ≤ F r z := fun r => by unfold F cuspNorm; positivity
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun r _ => he r))]
  rw [cuspNorm, Up_eq_affine, norm_mul, abs_of_nonneg (by positivity)]
  simp only [F, cuspNorm, ← Finset.sum_mul]
  rw [mul_assoc]
  gcongr
  exact norm_sum_le _ _

theorem Up_holo {n : ℕ} [NeZero n] {g : ℍ → ℂ} (hg : MDiff g) : MDiff (Up n g) := by
  have hf (r : ZMod n) : MDiff (fun z => g (unscalePoint n r z)) :=
    hg.comp (affinePoint_holo _ _ _)
  simpa only [show Up n g = (fun _ => (n : ℂ)⁻¹) * ∑ r : ZMod n, (fun z => g (unscalePoint n r z))
      from funext fun z => by simp [Up_eq_affine]] using
    mdifferentiable_const.mul (MDifferentiable.sum fun r _ => hf r)

/-- At a level divisible by both `4` and `p`, the actual normalized sum
preserves the character and the entire half-integral law. -/
theorem upSquare_threeHalves {m p : ℕ} [Fact p.Prime] [NeZero (p ^ 2)]
    (h4 : 4 ∣ m) (hpm : p ∣ m) (hodd : Odd p)
    {ξ : DirichletCharacter ℂ m} {g : ℍ → ℂ}
    (hg : HalfIntegralThreeHalves m ξ.toUnitHom g) :
    HalfIntegralThreeHalves m ξ.toUnitHom (Up (p ^ 2) g) := by
  refine ⟨Up_holo hg.holo, ?_, Up_cusps _ hg.cusps⟩
  intro γ z
  obtain ⟨e, he⟩ := upSquare_terms h4 hpm hodd γ
  rw [Up_eq_affine, Up_eq_affine, unitCharacter_d]
  let C := ξ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod m) * thetaMultiplier γ z ^ 3
  change _ = C * _
  rw [mul_left_comm]
  apply congrArg (fun s : ℂ => ((p ^ 2 : ℕ) : ℂ)⁻¹ * s)
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv e (fun r => g (unscalePoint (p ^ 2) r ((γ : SL(2, ℤ)) • z)))
    (fun r => C * g (unscalePoint (p ^ 2) r z)) fun r => ?_
  obtain ⟨δ, hd, hact, hθ⟩ := he r
  simp only [hact, hg.law δ, unitCharacter_d, hd, hθ, C]

end ZInQ.Manuscript.RC.EvenMoving
