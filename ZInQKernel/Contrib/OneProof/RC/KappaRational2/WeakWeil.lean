import ZInQKernel.Contrib.OneProof.RC.KappaRational2.Periods
import ZInQKernel.Contrib.RC53Assist.IsogenyLatticeAnalytic.AnalyticTransport

/-! The existing modularity-to-weak-Weil glue of tex 1779–1787 suffices
for the reference scale on the given form and lattice. -/

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.ModularWeil
open ZInQ.Contrib.RC53Assist.NewformPeriods ZInQ.Contrib.RC53Assist.IsogenyLatticeAnalytic

namespace ZInQ.Manuscript.RC.KappaRational2

/-- The weak Weil input can first choose the form and lattice itself.
Coefficient uniqueness identifies the form, and the identity isogeny
transports its periods to the prescribed normalized lattice. -/
theorem newformPeriodsRational_of_modularToWeakWeil (h : ModularToWeakWeil) :
    NewformPeriodsRational := by
  intro E hE f hf Lat hLat
  by_cases hN : newformLevel E = 0
  · exact ⟨1, isParamScale_of_level_zero hN f Lat⟩
  have hNpos := Nat.pos_of_ne_zero hN
  obtain ⟨g, L, r, hg, hL, hr⟩ := h E hE ⟨newformLevel E, hNpos, f, hf⟩
  have hfg : (f : ℍ → ℂ) = (g : ℍ → ℂ) :=
    coe_eq_of_qExpansion_coeff_eq f g (fun n hn => (hf n hn).trans (hg n hn).symm)
  have hsend (l : ℂ) (hl : l ∈ L.lattice) : l ∈ Lat.lattice := by
    simpa using isogenyLatticeAnalyticGlue_holds ℚ (Rat.castHom ℂ) E E hE hE
      (TauCeti.Isogeny.id E.toAffine) 1 (isPullbackScalar_id E.toAffine) L Lat
      (isLatticeOfEmb_ratCast hL) (isLatticeOfEmb_ratCast hLat) l hl
  refine ⟨r, hr.1, fun γ hγ τ => ?_⟩
  rw [hfg]
  exact hsend _ (hr.2 γ hγ τ)

/-- A provider for `ModularToWeakWeil` suffices for rationality of the original admissible
scale. `ModularToWeakWeil` is proved from printed theorems in
`RC53Assist.NewformGlues.modularToWeakWeil_of_printed` (Shimura 1973 Thm 1, Faltings 1983
Kor 2 and the newform leaves listed there). -/
theorem rational_of_modularToWeakWeil (h : ModularToWeakWeil)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [NeZero (newformLevel E)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel E) f Lat κ) :
    ∃ c : ℚ, (c : ℂ) = κ :=
  rational_of_matching_coeffs E f hf hNC hκ
    (newformPeriodsRational_of_modularToWeakWeil h E inferInstance f hf Lat hLat)

end ZInQ.Manuscript.RC.KappaRational2
