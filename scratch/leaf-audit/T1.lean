import ZInQKernel.Contrib.OneProof.LinYangPrinted

noncomputable section

namespace LeafAudit1115

open HDec HDec.HSyn.G0Split.ThetaPt.LinYangPrinted

/-- Complex conjugation on the Riemann sphere `ℂ ∪ {∞}`. -/
def conjOP : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  Homeomorph.onePointCongr Complex.conjLIE.toHomeomorph

@[simp] theorem conjOP_coe (z : ℂ) :
    conjOP (z : OnePoint ℂ) = ((starRingEnd ℂ z : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem conjOP_infty : conjOP OnePoint.infty = OnePoint.infty := rfl

/-- **`LinYangEx29All` forces `(z − z̄)·s₂³ = 0`.** Its premises on `j₆` are invariant under
`j₆ ↦ conj ∘ j₆` (conjugation fixes `0`, `∞`, `−16/27`), its conclusion `s₃² = z s₂³` is not. -/
theorem linYangEx29All_conj (hA : LinYangEx29All) (j6 : UpperHalfPlane → OnePoint ℂ)
    (hc : Continuous j6)
    (hfib : ∀ τ τ' : UpperHalfPlane, j6 τ = j6 τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ')
    (hs : Function.Surjective j6)
    (h4 : ∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = ((0 : ℂ) : OnePoint ℂ))
    (h3 : ∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = (OnePoint.infty : OnePoint ℂ))
    (h24 : ∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = ((-16/27 : ℂ) : OnePoint ℂ))
    (τ : UpperHalfPlane) (z : ℂ) (hz : j6 τ = (z : OnePoint ℂ)) :
    (z - starRingEnd ℂ z) * lyS2 (PkgI1.Omega τ) ^ 3 = 0 := by
  have e1 := (hA j6 hc hfib hs h4 h3 h24 τ z hz).1
  have e2 := (hA (conjOP ∘ j6) (conjOP.continuous.comp hc)
    (fun τ τ' => by
      simp only [Function.comp_apply]
      rw [conjOP.injective.eq_iff]
      exact hfib τ τ')
    (conjOP.surjective.comp hs)
    (fun x hx hxx γ hγ τ hτ => by simp [h4 x hx hxx γ hγ τ hτ])
    (fun x hx hxx γ hγ τ hτ => by simp [h3 x hx hxx γ hγ τ hτ])
    (fun x hx hxx γ hγ τ hτ => by
      simp only [Function.comp_apply, h24 x hx hxx γ hγ τ hτ, conjOP_coe]
      congr 1
      rw [map_div₀, map_neg, map_ofNat, map_ofNat])
    τ (starRingEnd ℂ z) (by simp [hz])).1
  linear_combination e2 - e1

/-- **With Igusa's theta expressions and `QMHauptmodul`, `LinYangEx29All` makes `j_θ` real** wherever its
denominator `jDen = (Σθ⁸)⁵` does not vanish. Numerically `j_θ(0.3 + 1.1i) = 4.2731… − 0.6831…i` with
`|jDen| ≈ 3·10⁵` (scratch/leaf-audit/py/jtheta_nonreal.py), so the three statements are inconsistent. -/
theorem jtheta_real_of_leaves (hI : IgusaThetaExpressions) (hA : LinYangEx29All)
    (hH : PkgI1.QMHauptmodul) (τ : UpperHalfPlane) (hden : PkgI1.jDen (PkgI1.Omega τ) ≠ 0) :
    (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)).im = 0 := by
  obtain ⟨f, hc, hval, hfib, hs, h4, h3, h24⟩ := hH
  set w := PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) with hw
  have hrel := linYangEx29All_conj hA f hc hfib hs h4 h3 h24 τ w (hval τ hden)
  have hs2 : lyS2 (PkgI1.Omega τ) ≠ 0 := by
    have hSieg := HDec.HSyn.G0Split.FibreQM.PeriodMap.omegaSiegel_proof (τ : ℂ) τ.im_pos
    rw [lyS2, (hI _ hSieg).1, HDec.HSyn.G0Split.ThetaPt.ThetaGlue.psi4Th]
    intro h
    apply hden
    rw [PkgI1.jDen]
    have : PkgI1.thetaSum8 (PkgI1.Omega τ) = 0 := by linear_combination 4 * h
    rw [this]; ring
  have hw0 : w - starRingEnd ℂ w = 0 := by
    rcases mul_eq_zero.1 hrel with h | h
    · exact h
    · exact (hs2 ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).1 h)).elim
  have := congrArg Complex.im hw0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
  linarith

/-- **`LinYangEx29All` is refuted** by Igusa's theta expressions, `QMHauptmodul` and one point where
`j_θ = jNum/jDen ∘ Ω` is finite and not real (numerics: `τ = 0.3 + 1.1i`). -/
theorem not_linYangEx29All (hI : IgusaThetaExpressions) (hH : PkgI1.QMHauptmodul)
    (hnum : ∃ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) ≠ 0 ∧
      (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)).im ≠ 0) :
    ¬ LinYangEx29All := by
  intro hA
  obtain ⟨τ, hden, him⟩ := hnum
  exact him (jtheta_real_of_leaves hI hA hH τ hden)

/-- The corrected (existential) form `LinYangEx29` already feeds the consumer, with no `QMHauptmodul`. -/
example (hI : IgusaThetaExpressions) (hL : LinYangEx29) :
    HDec.HSyn.G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM :=
  HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.thetaRatiosAtQM_of_printed hI hL

end LeafAudit1115

#print axioms LeafAudit1115.not_linYangEx29All
