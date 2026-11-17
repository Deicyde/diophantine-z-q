import ZInQKernel.Contrib.OneProof.ThetaDirect.Modular

/-! # theta-direct (helper): the two relations among Igusa's theta expressions on the QM curve

With no leaf: from the modularity of the theta expressions `ψ₆`, `χ₁₂` at `M4`, `M6` (`Modular.lean`, from
gt-theta's transformation laws), the kernel's proved valence formula, elliptic-order divisibility and generation of
`Γ*`, and the algebraic theta ratios at the nodes `√2 + i` and `τ₂₄`:

* (R1) there is an algebraic `c₁` with `ψ₆(Ω(z))·Σθ⁸(Ω(z)) = c₁·∏θ²(Ω(z))` for all `z ∈ ℍ`
  (weight 20 for `Γ*`, one node `τ₂₄`);
* (R2) there are algebraic `c₂`, `c₃` with `(Σθ⁸)²χ₁₂ = c₂(Σθ⁸)⁵ + c₃(∏θ²)²` along `Ω(z)` (weight 40, nodes
  `√2 + i`, `τ₂₄`).

(Only algebraicity of the `c_i` is proved and used. If theta-glue's `LinYangThetaCurve` (Lin–Yang's Example 29 in
theta expressions) holds, then `c₁ = −3⁵`, `c₂ = 2⁻¹⁸3⁻⁶`, `c₃ = 3⁴2⁻¹²`; this is a computation from that unproved
statement, not checked here.) -/

set_option linter.all false

noncomputable section

namespace HDec.ThetaDirect

open Complex
open HDec.LeafQCheck.HM.QMSplit (Auto)
open HDec.HSyn.G0Split.FibreQM.PeriodMap (G8 U omegaSiegel_proof)
open HDec.HSyn.G0Split.FibreQM.PeriodGlue (M4 M6 M4_symp M6_symp zz_ne)
open HDec.HSyn.G0Split.ThetaPt.ThetaGlue (psi4Th psi6Th chi10Th chi12Th psi4T psi6T chi10T chi12T psi6Th_eq
  chi12Th_eq)

/-- `G20 = ∏θ²∘Ω/((z−3)(z+1))¹⁰` (the kernel's). -/
abbrev G20 : ℂ → ℂ := HDec.HSyn.G0Split.FibreQM.PeriodGlue.LQ20.G20

/-! ## The four automorphic forms for `Γ*` -/

theorem auto6 : Auto 6 (GS 6 psi6Th) :=
  autoGS ⟨3, rfl⟩ (fun z hz => psi6Th_M4 (omegaSiegel_proof z hz))
    (fun z hz => psi6Th_M6 (omegaSiegel_proof z hz))

theorem auto12 : Auto 12 (GS 12 chi12Th) :=
  autoGS ⟨6, rfl⟩ (fun z hz => chi12Th_M4 (omegaSiegel_proof z hz))
    (fun z hz => chi12Th_M6 (omegaSiegel_proof z hz))

theorem auto8' : Auto 4 G8 := HDec.LeafQCheck.HM.QMSplit.auto8 GapTheta.thetaModularity_proof

theorem auto20' : Auto 10 G20 := HDec.LeafQCheck.HM.QMSplit.auto20 GapTheta.thetaModularity_proof

theorem analytic_GS {w : ℕ} {S : Matrix (Fin 2) (Fin 2) ℂ → ℂ}
    (hS : ∀ z ∈ U, AnalyticAt ℂ (fun z => S (PkgI1.Omega z)) z) : AnalyticOnNhd ℂ (GS w S) U := fun z hz =>
  (hS z hz).div (by fun_prop) (pow_ne_zero _ (zz_ne hz))

theorem analytic_psi6 : AnalyticOnNhd ℂ (GS 6 psi6Th) U := by
  refine analytic_GS fun z hz => ?_
  have h := fun m => thetaConst_omega_analyticAt hz m
  unfold psi6Th
  fun_prop

theorem analytic_chi12 : AnalyticOnNhd ℂ (GS 12 chi12Th) U := by
  refine analytic_GS fun z hz => ?_
  have h := fun m => thetaConst_omega_analyticAt hz m
  unfold chi12Th
  fun_prop

theorem analytic_G8 : AnalyticOnNhd ℂ G8 U := fun z hz => HDec.LeafQCheck.HM.G8_analytic hz
theorem analytic_G20 : AnalyticOnNhd ℂ G20 U := fun z hz => HDec.LeafQCheck.HM.G20_analytic hz


/-! ## The nodes -/

/-- `√2 + i`, the CM point of discriminant `−4` (period-map's `tau4`). -/
abbrev tau4 : UpperHalfPlane := HDec.HSyn.G0Split.FibreQM.PeriodMap.tau4
/-- `τ₂₄ = i√(9 + 6√2)`, the CM point of discriminant `−24` (qm-glue's `tau24`). -/
abbrev tau24 : UpperHalfPlane := HDec.LeafQCheck.HM.QMSplit.Value24.tau24

theorem tau24_omega : PkgI1.Omega (tau24 : ℂ) = HDec.LeafQCheck.HM.QMSplit.Value24.Om24 := by
  have e : ((HDec.LeafQCheck.HM.QMSplit.Value24.tau24 : UpperHalfPlane) : ℂ) =
      Complex.I * (HDec.LeafQCheck.HM.QMSplit.Value24.s24 : ℂ) := rfl
  rw [e, HDec.LeafQCheck.HM.QMSplit.Value24.omega_tau24]

theorem tau4_omega : PkgI1.Omega (tau4 : ℂ) = PkgI1.Omega ((√2 : ℂ) + I) := rfl

theorem Zf4_ne : ((tau4 : ℂ) - 3) * ((tau4 : ℂ) + 1) ≠ 0 := zz_ne tau4.im_pos
theorem Zf24_ne : ((tau24 : ℂ) - 3) * ((tau24 : ℂ) + 1) ≠ 0 := zz_ne tau24.im_pos

theorem sum8_tau4 : PkgI1.thetaSum8 (PkgI1.Omega (tau4 : ℂ)) ≠ 0 := HDec.LeafQCheck.HM.Sf_tau4
theorem prod2_tau4 : PkgI1.thetaProd2 (PkgI1.Omega (tau4 : ℂ)) = 0 := HDec.LeafQCheck.HM.Pf_tau4

theorem sum8_tau24 : PkgI1.thetaSum8 (PkgI1.Omega (tau24 : ℂ)) ≠ 0 := by
  rw [tau24_omega]
  obtain ⟨hD, -⟩ := CM24.thetaValueAtOmega24
  exact fun h => hD (by rw [PkgI1.jDen, h]; ring)

theorem prod2_tau24 : PkgI1.thetaProd2 (PkgI1.Omega (tau24 : ℂ)) ≠ 0 := by
  rw [tau24_omega]
  obtain ⟨-, hv⟩ := CM24.thetaValueAtOmega24
  intro h0
  rw [PkgI1.jNum, h0] at hv
  norm_num at hv

theorem G8_eq' (z : ℂ) : G8 z = PkgI1.thetaSum8 (PkgI1.Omega z) / ((z - 3) * (z + 1)) ^ 4 := rfl
theorem G20_eq' (z : ℂ) : G20 z = PkgI1.thetaProd2 (PkgI1.Omega z) / ((z - 3) * (z + 1)) ^ 10 := rfl

theorem G8_tau4 : G8 (tau4 : ℂ) ≠ 0 := by
  rw [G8_eq']; exact div_ne_zero sum8_tau4 (pow_ne_zero _ Zf4_ne)
theorem G20_tau4 : G20 (tau4 : ℂ) = 0 := by rw [G20_eq', prod2_tau4, zero_div]
theorem G8_tau24 : G8 (tau24 : ℂ) ≠ 0 := by
  rw [G8_eq']; exact div_ne_zero sum8_tau24 (pow_ne_zero _ Zf24_ne)
theorem G20_tau24 : G20 (tau24 : ℂ) ≠ 0 := by
  rw [G20_eq']; exact div_ne_zero prod2_tau24 (pow_ne_zero _ Zf24_ne)

theorem tau4_ne_tau24 : tau4 ≠ tau24 := by
  intro h
  have : G20 (tau4 : ℂ) = G20 (tau24 : ℂ) := congrArg (fun w : UpperHalfPlane => G20 (w : ℂ)) h
  rw [G20_tau4] at this
  exact G20_tau24 this.symm

open scoped Classical

/-- `√2 + i` and `τ₂₄` are `Γ*`-inequivalent (`G20` vanishes at one and not at the other). -/
theorem pairwise_nodes : (({tau4, tau24} : Finset UpperHalfPlane) : Set UpperHalfPlane).Pairwise
    (fun z w => ∀ γ ∈ PkgI1.GammaStar, γ • z ≠ w) := by
  intro z hz w hw hzw γ hγ hγz
  have e := HDec.LeafQCheck.HM.QMSplit.zero_iff auto20' hγ z
  rw [hγz] at e
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hz hw
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · exact hzw rfl
  · exact G20_tau24 (e.mpr G20_tau4)
  · exact G20_tau24 (e.mp G20_tau4)
  · exact hzw rfl

/-! ## (R1) `ψ₆·Σθ⁸ = c₁·∏θ²` along `Ω` -/

/-- The constant of (R1), read off at `τ₂₄`. -/
def c1 : ℂ := GS 6 psi6Th (tau24 : ℂ) * G8 (tau24 : ℂ) / G20 (tau24 : ℂ)

theorem rel1_G : ∀ z ∈ U, GS 6 psi6Th z * G8 z = c1 * G20 z := by
  have key := eq_zero_of_nodes (m := 10) (F := fun z => GS 6 psi6Th z * G8 z - c1 * G20 z) (F₂ := G20)
    (fun z hz => ((analytic_psi6 z hz).mul (analytic_G8 z hz)).sub (analyticAt_const.mul (analytic_G20 z hz)))
    analytic_G20 (auto_sub (auto_mul auto6 auto8') (auto_const_mul c1 auto20')) auto20' {tau24}
    (by simp) (by
      intro z hz
      rw [Finset.mem_singleton] at hz
      subst hz
      simp only [c1]
      rw [div_mul_cancel₀ _ G20_tau24, sub_self])
    (by intro z hz; rw [Finset.mem_singleton] at hz; subst hz; exact G20_tau24) (by simp)
  intro z hz
  exact sub_eq_zero.mp (key z hz)

/-- **(R1) in theta form.** -/
theorem rel1 {z : ℂ} (hz : 0 < z.im) :
    psi6Th (PkgI1.Omega z) * PkgI1.thetaSum8 (PkgI1.Omega z) = c1 * PkgI1.thetaProd2 (PkgI1.Omega z) := by
  have h := rel1_G z hz
  rw [G8_eq', G20_eq'] at h
  unfold GS at h
  have hZ := zz_ne hz
  generalize (z - 3) * (z + 1) = Z at h hZ
  field_simp at h
  linear_combination h

/-! ## (R2) `(Σθ⁸)²χ₁₂ = c₂(Σθ⁸)⁵ + c₃(∏θ²)²` along `Ω` -/

/-- The constants of (R2), read off at `√2 + i` and `τ₂₄`. -/
def c2 : ℂ := GS 12 chi12Th (tau4 : ℂ) / G8 (tau4 : ℂ) ^ 3
def c3 : ℂ := (G8 (tau24 : ℂ) ^ 2 * GS 12 chi12Th (tau24 : ℂ) - c2 * G8 (tau24 : ℂ) ^ 5) / G20 (tau24 : ℂ) ^ 2

theorem rel2_G :
    ∀ z ∈ U, G8 z ^ 2 * GS 12 chi12Th z - c2 * G8 z ^ 5 - c3 * G20 z ^ 2 = 0 := by
  have hA : Auto 20 (fun z => G8 z ^ 2 * GS 12 chi12Th z - c2 * G8 z ^ 5 - c3 * G20 z ^ 2) :=
    auto_sub (auto_sub (auto_mul (auto_pow auto8' 2) auto12) (auto_const_mul c2 (auto_pow auto8' 5)))
      (auto_const_mul c3 (auto_pow auto20' 2))
  exact eq_zero_of_nodes (m := 20) (F₂ := fun z => G8 z ^ 5)
    (fun z hz => ((((analytic_G8 z hz).pow 2).mul (analytic_chi12 z hz)).sub
      (analyticAt_const.mul ((analytic_G8 z hz).pow 5))).sub (analyticAt_const.mul ((analytic_G20 z hz).pow 2)))
    (fun z hz => (analytic_G8 z hz).pow 5) hA (auto_pow auto8' 5) {tau4, tau24} pairwise_nodes
    (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · rw [G20_tau4, c2]
        have := G8_tau4
        field_simp
        ring
      · rw [c3]
        have := G20_tau24
        field_simp
        ring)
    (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact pow_ne_zero _ G8_tau4
      · exact pow_ne_zero _ G8_tau24)
    (by rw [Finset.card_pair tau4_ne_tau24]; norm_num)

/-- **(R2) in theta form.** -/
theorem rel2 {z : ℂ} (hz : 0 < z.im) :
    PkgI1.thetaSum8 (PkgI1.Omega z) ^ 2 * chi12Th (PkgI1.Omega z) =
      c2 * PkgI1.thetaSum8 (PkgI1.Omega z) ^ 5 + c3 * PkgI1.thetaProd2 (PkgI1.Omega z) ^ 2 := by
  have h := rel2_G z hz
  rw [G8_eq', G20_eq'] at h
  unfold GS at h
  have hZ := zz_ne hz
  generalize (z - 3) * (z + 1) = Z at h hZ
  field_simp at h
  linear_combination h

end HDec.ThetaDirect
