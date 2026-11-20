import ZInQKernel.Contrib.OneProof.RC.CMScope.Evaluation
import ZInQKernel.Contrib.OneProof.RC.CMScope.Orientation
import ZInQKernel.Contrib.OneProof.RC.HeegnerAnchor.Conductors
import ZInQKernel.Contrib.OneProof.RC.StageSelector.Selector
import ZInQKernel.Contrib.CloudB3RC53.Splitting.Criterion

/-! The conductor-one point of tex 2411–2412 and 8209–8217 (c). -/

open NumberField WeierstrassCurve ZInQ.Progressions TauCeti.GlobalNumberFields
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
  ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.CMScope

/-- Discriminant coprimality in the form supplied by the local unit classes. -/
theorem coprime_level {N : ℕ} {d : ℤ}
    (hloc : ∀ p : ℕ, p.Prime → p ∣ 2 * N → SquareAt p d) : IsCoprime d (N : ℤ) := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  change d.natAbs.Coprime N
  exact Nat.coprime_of_dvd fun p hp hpd hpN =>
    (hloc p hp (dvd_mul_of_dvd_right hpN 2)).1 (Int.natCast_dvd.mpr hpd)

/-- The unit square class at two excludes the two exceptional discriminants. -/
theorem discr_ne_of_mod_eight {d : ℤ} (h8 : d % 8 = 1) : d ≠ -4 ∧ d ≠ -3 := by
  constructor
  · intro h
    rw [h] at h8
    norm_num at h8
  · intro h
    rw [h] at h8
    norm_num at h8

/-- The same prepared values as `PreparedParam.preparedParamValues`,
specializing scoped descent to the selector's form. -/
theorem preparedParamValues {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [NeZero (newformLevel E)] {X : X0Model (newformLevel E)}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} (hCM : CMFieldOfDefinitionScoped X)
    (hπ : AlgebraicParametrizationAtScale E X f Lat κ)
    (hN : 0 < newformLevel E) {hstar : ℤ} (hgp : GenusPartner E hstar) :
    ∀ D (hp : Prepared E hstar D), StageSelector.PreparedParamValue E f Lat κ hN hgp hp := by
  intro D hp
  obtain ⟨hd, hsq, hloc⟩ := StageSelector.prepared_discriminant hp hgp
  have h2 := hloc 2 Nat.prime_two (dvd_mul_right 2 _)
  let _ : Fact (¬ IsSquare ((D * hstar : ℤ) : ℚ)) :=
    ⟨Qsqrt.not_isSquare_of_squarefree hsq (ne_of_lt (hd.trans zero_lt_one))⟩
  let K := Qsqrt (D * hstar)
  have hD : discr K = D * hstar := StageSelector.qsqrt_discr hd hsq h2.mod_four
  have hs : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel E → SplitsIn K p := by
    intro p hp hpn
    exact Splitting.splittingCriterion_proof K Qsqrt.finrank p hp (hD.symm ▸ hloc p hp hpn)
  have h8 : discr K % 8 = 1 := by
    rw [hD]
    exact h2.2.1 rfl
  obtain ⟨h4, h3⟩ := discr_ne_of_mod_eight h8
  have hO := HeegnerAnchor.conductorOrder_discr (K := K) Qsqrt.finrank 1
  have he : discr K * (↑(1 : ℕ) : ℤ) ^ 2 = D * hstar := by simpa using hD
  let bc := (StageSelector.formAtLevel hN hgp hp).val
  obtain ⟨ι, x, hx⟩ := hCM.atForm (K := K) Qsqrt.finrank (Qsqrt.isTotallyComplex hd) hs
    h4 h3 (c := 1) (by simp) (A := (newformLevel E : ℤ)) (B := bc.1) (C := bc.2) hO
    (by rw [he]; exact hd) (by rw [he]; exact coprime_level hloc)
    (by rw [he]; exact (StageSelector.formAtLevel hN hgp hp).property)
  obtain ⟨y, hy⟩ := value_of_cmPoint hπ ι x hx
  unfold StageSelector.PreparedParamValue
  refine ⟨ι, y, hy.trans ?_⟩
  exact congrArg (fun d => phiAn E f Lat κ (cmPoint (newformLevel E) bc.1 d)) he

end ZInQ.Manuscript.RC.CMScope
