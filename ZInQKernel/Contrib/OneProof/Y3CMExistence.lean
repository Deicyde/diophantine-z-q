import ZInQKernel.Contrib.OneProof.Y3CMPeriodValues

/-! The three algebraic CM types exist using their explicit fixed periods and
the existing CM descent theorem. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeafQM LeafQM.AV HDec
open HDec.HSyn.G0Split.FibreQM HDec.HSyn.G0Split.FibreQM.PeriodMapH
open RayClassCFT Y3Fix

namespace Y3P1j

/-- The three fixed periods of the manuscript supply the three algebraic CM
objects through the printed fine model and arithmetic CM descent. -/
theorem exists_CM_objects_of_fixed_periods
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (hΦ : R1fpPropsAbP Y Φ)
    (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint) (hF : CMFixedHasCM)
    (hC : CMDescends) :
    (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q) := by
  obtain ⟨Ψ, -, hU⟩ := Y3Hodge.deligneH_of_print hD Y Φ hΦ
  have hPeriod (τ : UpperHalfPlane) : ∃ P : QML3 ℂ, HasQMPeriod P τ := by
    have h1 : (1 : ShimuraCFT.BAQˣ) ∈ OhatU :=
      ⟨OhatQ_one, by simpa using OhatQ_one⟩
    obtain ⟨P, -, hP⟩ := units_of_H hU 1 h1 τ
    exact ⟨P, hP⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, he, g, hg, τ, hτ⟩ := PeriodMap.cm4_exists
    obtain ⟨Q, hQ⟩ := hPeriod τ
    obtain ⟨_, P, _, _, hP, _⟩ := (hC Q).1 ((hF Q τ hQ x g hx hg hτ).1 he)
    exact ⟨P, hP⟩
  · obtain ⟨x, hx, he, g, hg, τ, hτ⟩ := PeriodMap.cm3_exists
    obtain ⟨Q, hQ⟩ := hPeriod τ
    obtain ⟨_, P, _, _, hP, _⟩ := (hC Q).2.1 ((hF Q τ hQ x g hx hg hτ).2.1 he)
    exact ⟨P, hP⟩
  · obtain ⟨x, hx, he, g, hg, τ, hτ⟩ := PeriodMap.cm24_exists
    obtain ⟨Q, hQ⟩ := hPeriod τ
    obtain ⟨_, P, _, _, hP, _⟩ := (hC Q).2.2 ((hF Q τ hQ x g hx hg hτ).2.2 he)
    exact ⟨P, hP⟩

end Y3P1j

#print axioms Y3P1j.exists_CM_objects_of_fixed_periods
