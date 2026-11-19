import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Window
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.ThetaNonvanishing
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Waldspurger

/-! The first analytic stop is at the old level of the actual weighted
ternary series, before the level-raising operators and the theta product.
We use nonnegative, rather than strictly positive, cusp exponents. -/

noncomputable section

namespace ZInQ.Manuscript.RC.BlocksPerU

open ModularForm ThetaCoeff PrintsAnalytic UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups Manifold BigOperators ModularForm

def cuspNorm (r : ℝ) (g : ℍ → ℂ) (γ : SL(2, ℤ)) (z : ℍ) : ℝ :=
  ‖g (γ • z)‖ * ‖denom γ z‖ ^ (-r)

/-- Classical holomorphic weight `3/2`, including boundedness at every
cusp, with the manuscript's cubed theta multiplier. -/
structure HalfIntegralThreeHalves (m : ℕ) (ξ : (ZMod m)ˣ →* ℂˣ) (g : ℍ → ℂ) : Prop where
  holo : MDiff g
  law : ∀ (γ : ↥(Gamma0 m)) (z : ℍ),
    g ((γ : SL(2, ℤ)) • z) =
      (ξ ((Gamma0Map m).toHomUnits γ) : ℂ) * thetaMultiplier γ z ^ 3 * g z
  cusps : ∀ γ : SL(2, ℤ), IsBoundedAtImInfty (cuspNorm (3 / 2) g γ)

/-- Precisely the two ordinary theta facts used in passing from weight
`3/2` to weight two. No weighted theta transformation is asserted here. -/
structure OrdinaryThetaLaw : Prop where
  fourth : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 4 → ∀ z : ℍ,
    thetaMultiplier γ z ^ 4 = denom γ z ^ 2
  cusps : ∀ γ : SL(2, ℤ), IsBoundedAtImInfty (cuspNorm (1 / 2) thetaFun γ)

theorem thetaFun_holo : MDiff thetaFun := by
  intro z
  have h : 0 < (2 * (z : ℂ)).im := by
    rw [show (2 : ℂ) = (↑(2 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul]
    exact mul_pos (by norm_num) z.im_pos
  exact (differentiableAt_jacobiTheta h).mdifferentiableAt.comp z
    (mdifferentiableAt_const.mul z.mdifferentiable_coe)

private theorem thetaFun_ne_zero (z : ℍ) : thetaFun z ≠ 0 := by
  unfold thetaFun
  apply HalfIntegral.jacobiTheta_ne_zero_of_im_pos
  rw [show (2 : ℂ) = (↑(2 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul]
  exact mul_pos (by norm_num) z.im_pos

/-- The ordinary theta factor turns the cubed multiplier into the integral
weight automorphy factor and leaves the scalar character unchanged. -/
theorem theta_product_slash {m : ℕ} {ξ : (ZMod m)ˣ →* ℂˣ} {g : ℍ → ℂ}
    (hfour : 4 ∣ m) (hθ : OrdinaryThetaLaw) (hg : HalfIntegralThreeHalves m ξ g)
    (γ : ↥(Gamma0 m)) :
    (g * thetaFun) ∣[(2 : ℤ)] (γ : SL(2, ℤ)) =
      (ξ ((Gamma0Map m).toHomUnits γ) : ℂ) • (g * thetaFun) := by
  funext z
  rw [SL_slash_apply]
  have he : thetaFun ((γ : SL(2, ℤ)) • z) = thetaMultiplier γ z * thetaFun z :=
    (div_mul_cancel₀ _ (thetaFun_ne_zero z)).symm
  have hΓ := Gamma0_le_Gamma0_of_dvd hfour γ.property
  change (g ((γ : SL(2, ℤ)) • z) * thetaFun ((γ : SL(2, ℤ)) • z)) *
    denom (γ : SL(2, ℤ)) z ^ (-(2 : ℤ)) = _ * (g z * thetaFun z)
  rw [hg.law γ z, he]
  calc
    _ = (ξ ((Gamma0Map m).toHomUnits γ) : ℂ) * (g z * thetaFun z) *
        thetaMultiplier γ z ^ 4 * denom (γ : SL(2, ℤ)) z ^ (-(2 : ℤ)) := by ring
    _ = _ := by
      have hc : denom (γ : SL(2, ℤ)) z ^ 2 * denom (γ : SL(2, ℤ)) z ^ (-(2 : ℤ)) = 1 := by
        rw [zpow_neg]
        exact mul_inv_cancel₀ (pow_ne_zero _ (denom_ne_zero _ _))
      rw [hθ.fourth γ hΓ, mul_assoc, hc, mul_one]

private theorem theta_product_cusp {m : ℕ} {ξ : (ZMod m)ˣ →* ℂˣ} {g : ℍ → ℂ}
    (hθ : OrdinaryThetaLaw) (hg : HalfIntegralThreeHalves m ξ g) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty ((g * thetaFun) ∣[(2 : ℤ)] γ) := by
  obtain ⟨A, a, hA⟩ := isBoundedAtImInfty_iff.mp (hg.cusps γ)
  obtain ⟨B, b, hB⟩ := isBoundedAtImInfty_iff.mp (hθ.cusps γ)
  apply isBoundedAtImInfty_iff.mpr
  refine ⟨A * B, max a b, fun z hz => ?_⟩
  have he : ‖((g * thetaFun) ∣[(2 : ℤ)] γ) z‖ =
      cuspNorm (3 / 2) g γ z * cuspNorm (1 / 2) thetaFun γ z := by
    rw [SL_slash_apply, norm_mul, norm_zpow, Pi.mul_apply, norm_mul, cuspNorm, cuspNorm]
    have hr : ‖denom γ z‖ ^ (-(2 : ℤ)) =
        ‖denom γ z‖ ^ (-(3 / 2 : ℝ)) * ‖denom γ z‖ ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add (norm_pos_iff.mpr (denom_ne_zero _ _))]
      norm_num [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    rw [hr]
    ring
  rw [he, ← Real.norm_of_nonneg (by unfold cuspNorm; positivity : 0 ≤ cuspNorm (3 / 2) g γ z),
    ← Real.norm_of_nonneg (by unfold cuspNorm; positivity : 0 ≤ cuspNorm (1 / 2) thetaFun γ z)]
  exact mul_le_mul (hA z ((le_max_left _ _).trans hz)) (hB z ((le_max_right _ _).trans hz))
    (norm_nonneg _) ((norm_nonneg _).trans (hA z ((le_max_left _ _).trans hz)))

/-- Turn the half-integral block into a genuine weight-two modular form,
including cusp holomorphy. The action of diamonds is its prescribed scalar. -/
theorem theta_product_modular {m : ℕ} {ξ : (ZMod m)ˣ →* ℂˣ} {g : ℍ → ℂ}
    (hfour : 4 ∣ m) (hθ : OrdinaryThetaLaw) (hg : HalfIntegralThreeHalves m ξ g) :
    ∃ f : ModularForm ((Gamma1 m).map (mapGL ℝ)) 2,
      (⇑f : ℍ → ℂ) = g * thetaFun ∧ f ∈ modFormCharSpace 2 ξ := by
  let f : ModularForm ((Gamma1 m).map (mapGL ℝ)) 2 :=
    { toFun := g * thetaFun
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        let γ₀ : ↥(Gamma0 m) := ⟨γ, Gamma1_in_Gamma0 m hγ⟩
        have h1 : (Gamma0Map m).toHomUnits γ₀ = 1 := by
          apply Units.ext
          rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply]
          exact (mem_Gamma1_iff.mp hγ).2
        change (g * thetaFun) ∣[(2 : ℤ)] (γ₀ : SL(2, ℤ)) = g * thetaFun
        rw [theta_product_slash hfour hθ hg γ₀, h1, map_one, Units.val_one, one_smul]
      holo' := hg.holo.mul thetaFun_holo
      bdd_at_cusps' := by
        intro c hc
        have hSL : IsCusp c 𝒮ℒ := hc.mono (Subgroup.map_le_range (mapGL ℝ) (Gamma1 m))
        apply (OnePoint.isBoundedAt_iff_forall_SL2Z hSL).mpr
        intro γ _
        exact theta_product_cusp hθ hg γ }
  refine ⟨f, rfl, (mem_modFormCharSpace_iff_nebentypus 2 ξ f).mpr ?_⟩
  intro γ
  exact theta_product_slash hfour hθ hg γ

/-- Classical expansion with nonnegative exponents; convergence is part
of the statement, so assigning zero to a divergent theta sum cannot
satisfy it. -/
def HasThreeHalvesExpansion {O : Type} [CommRing O] (ι : O →+* ℂ)
    (m : ℕ) (ξ : (ZMod m)ˣ →* ℂˣ) (a : ℕ → O) : Prop :=
  ∃ g : ℍ → ℂ, HalfIntegralThreeHalves m ξ g ∧
    ∀ z : ℍ, HasSum (fun n : ℕ => ι (a n) * Function.Periodic.qParam 1 (z : ℂ) ^ n) (g z)

/-- ELLIOT, tex 8623–8637 and 8948–9022: transformation and cusp
holomorphy of the *same* extracted weighted ternary series. The coefficient
`E.aθ n = E.H (S.m * n)` uses the weight `E.geom.f`. On the actual
stage this is the field `f` of `PMLocal`, via its existing lift.
The character parameter is the one in (O.5); the level includes the
coefficient sieves used to define this source. -/
def StageTernaryTransformation {O : Type} [CommRing O] {M : ℕ}
    {S : AppF.ThetaStage (Odd.StageRing O M)} (E : Lift S) (ι : O →+* ℂ)
    (m : ℕ) (ξ : (ZMod m)ˣ →* ℂˣ) : Prop :=
  HasThreeHalvesExpansion ι m ξ E.aθ

#print axioms thetaFun_holo
#print axioms thetaFun_ne_zero
#print axioms theta_product_slash
#print axioms theta_product_cusp
#print axioms theta_product_modular

end ZInQ.Manuscript.RC.BlocksPerU
