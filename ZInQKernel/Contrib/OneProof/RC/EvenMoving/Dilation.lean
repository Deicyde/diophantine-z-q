import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Theta
import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.Operators

/-! The actual operator `V_p` raises the level by `p` (tex 9497–9512). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenMoving

open BlocksPerU EvenExpansion CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups Manifold

theorem Vp_eq_scale (p : ℕ) (hp : 0 < p) (g : ℍ → ℂ) :
    Vp p hp g = fun z => g (scalePoint p hp z) := by
  funext z
  unfold Vp
  apply congrArg g
  apply UpperHalfPlane.ext
  change ((p : ℝ) : ℂ) * (z : ℂ) = _
  rw [Complex.ofReal_natCast, scalePoint_coe]

theorem unitCharacter_d {m : ℕ} (χ : DirichletCharacter ℂ m) (γ : ↥(Gamma0 m)) :
    (χ.toUnitHom ((Gamma0Map m).toHomUnits γ) : ℂ) =
      χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod m) := by
  rw [MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, Gamma0Map_apply]

/-- The whole law (holomorphy, transformation, and cusp bounds) for the
actual dilate with its prescribed character. -/
theorem Vp_threeHalves {M p : ℕ} [Fact p.Prime] (hodd : Odd p) (h4 : 4 ∣ M)
    {χ : DirichletCharacter ℂ M} {g : ℍ → ℂ}
    (hg : HalfIntegralThreeHalves M χ.toUnitHom g) :
    HalfIntegralThreeHalves (M * p)
      (χ.changeLevel (dvd_mul_right M p) *
        primeCharacter (h4.trans (dvd_mul_right M p)) (dvd_mul_left p M)).toUnitHom
      (Vp p (Fact.out : p.Prime).pos g) := by
  let hp := (Fact.out : p.Prime)
  let k := primeCharacter (h4.trans (dvd_mul_right M p)) (dvd_mul_left p M)
  rw [Vp_eq_scale]
  refine ⟨hg.holo.comp (affinePoint_holo _ _ _), ?_, fun γ =>
    affinePoint_cusps _ hg.cusps _ _ _ γ⟩
  intro γ z
  let A := (γ : SL(2, ℤ))
  have hc := (mem_level_iff A).mp γ.property
  have hpc : (p : ℤ) ∣ A 1 0 := (Int.natCast_dvd_natCast.mpr (dvd_mul_left p M)).trans hc
  let D := scaleLower p A hpc
  obtain ⟨ha, hb, hD, hd⟩ := scaleLower_entries p A hpc
  have hDM : D ∈ Gamma0 M := by
    obtain ⟨t, ht⟩ := hc
    apply (mem_level_iff D).mpr
    refine ⟨t, mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0) ?_⟩
    rw [hD, ht]
    push_cast
    ring
  have hD4 : (4 : ℤ) ∣ D 1 0 := (Int.natCast_dvd_natCast.mpr h4).trans ((mem_level_iff D).mp hDM)
  have hθ := thetaMultiplier_scale (h4.trans (dvd_mul_right M p)) (dvd_mul_left p M)
    hodd A D γ.property hD4 ha hb hD hd z
  have hunit := AppE.isCoprime_d_of_mem_Gamma0 γ.property
  have hk := primeCharacter_sq (h4.trans (dvd_mul_right M p)) (dvd_mul_left p M) hunit
  have hk3 : (k (A 1 1 : ℤ)) ^ 3 = k (A 1 1 : ℤ) := by
    change (k (A 1 1 : ℤ)) ^ 2 * k (A 1 1 : ℤ) = _
    rw [hk, one_mul]
  rw [← scale_smul p hp.pos A D ha hb hD hd, hg.law ⟨D, hDM⟩, unitCharacter_d, unitCharacter_d]
  change χ (D 1 1 : ℤ) * _ * _ = _
  rw [hd, hθ, mul_pow, hk3, MulChar.mul_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hunit]
  ring

end ZInQ.Manuscript.RC.EvenMoving
