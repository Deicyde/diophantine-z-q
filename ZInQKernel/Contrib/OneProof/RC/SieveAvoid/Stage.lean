import ZInQKernel.Contrib.OneProof.RC.SieveAvoid.Theta
import ZInQKernel.Contrib.OneProof.RC.O12Theta.AtPrecision
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Model
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Expansions
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Symbol

/-! Connect the stage divisions to the common-model interface. The realization
assumption is on the whole tested domain; the zero extension of a finite pool
cannot be substituted for it. -/

noncomputable section

namespace ZInQ.Manuscript.RC.SieveAvoid

open O12Realize O12Theta AddressGenuine PrintsArith TraceLimits ZInQ.Manuscript.RC.Odd ThetaCoeff O12
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped Classical MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {Scoeff : Finset ℕ}
variable {χ : GalQ →* Multiplicative L} {R₀ : Finset ℕ → ZMod 2} {B : ℕ}

section Theta

variable {M W R : ℕ} {δ : ℤ} {adm : ℕ → Prop}
variable {ap : ℕ → ℤ} {X : GaloisConstituentModel T R₀ ap B χ}
variable [CharZero X.O] [IsDomain X.O] [CharZero X.K]
variable {S : AppF.ThetaStage (StageRing X.O M)}
variable (A : FourierData X) (E : Lift S) (D : Divisions E δ W R adm)

/-- The inputs of the genuine intrinsic valuation reading. `onFilter`
is the phase comparison with its integer representative at stage precision;
`offFilter` is the support comparison at that same precision. -/
structure StageValuation' (Scoeff : Finset ℕ) where
  filter : Finset ℕ → Prop
  integer : Finset ℕ → ℤ
  read : ∀ V : Finset ℕ, GoodSet T Scoeff V → V.card ≤ B →
    R₀ V = if filter V ∧ Odd.vZ (integer V) = ((δ + (V.card : ℤ) : ℤ) : WithTop ℤ) then 1 else 0
  onFilter : ∀ V : Finset ℕ, GoodSet T Scoeff V → V.card ≤ B → filter V →
    ((δ + (V.card : ℤ) : ℤ) : WithTop ℤ) ≤ Odd.vZ (integer V) ∧
    ∃ ζ : X.O, (∃ k : ℕ, ζ ^ (2 ^ k : ℕ) = 1) ∧
      S.aθ (∏ p ∈ V, p) = stageReduction X.O M (ζ * (integer V : X.O))
  offFilter : ∀ V : Finset ℕ, GoodSet T Scoeff V → V.card ≤ B → ¬ filter V →
    S.aθ (∏ p ∈ V, p) = 0

include A D in
/-- Evaluate the stage symbol after the integral division, including the
zero case off the filter. -/
theorem stage_source_symbol' (hbudget : B ≤ W + 1) (hm : X.m.IsMaximal)
    (V : StageValuation' (X := X) (S := S) (δ := δ) Scoeff)
    (U : Finset ℕ) (q : ℕ) (hU : GoodSet T Scoeff U) (hq : T.Good q) (hf : q ∉ Scoeff ∪ U)
    (hB : (insert q U).card ≤ B) (b : X.O)
    (hb : algebraMap X.O X.K b = scale X.K δ U *
      algebraMap X.O X.K (E.aθ ((∏ p ∈ U, p) * q))) :
    Ideal.Quotient.mk X.m b = if R₀ (insert q U) = 0 then 0 else 1 := by
  let J := insert q U
  have hqU : q ∉ U := fun h => hf (Finset.mem_union_right _ h)
  have hJ : GoodSet T Scoeff J := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨hq, fun h => hf (Finset.mem_union_left _ h)⟩
    · exact hU p hp
  have hcard : J.card = U.card + 1 := Finset.card_insert_of_notMem hqU
  have hW : U.card ≤ W := by change J.card ≤ B at hB; omega
  have he := D.stage.precision D.precision hW
  have hp : δ + (U.card : ℤ) + 1 < (M : ℤ) := by omega
  rw [V.read J hJ hB]
  have hc : δ + (J.card : ℤ) = δ + (U.card : ℤ) + 1 := by simp [hcard, add_assoc]
  have hprod : (∏ p ∈ J, p) = (∏ p ∈ U, p) * q := by
    exact (Finset.prod_insert hqU).trans (mul_comm _ _)
  have hb' : algebraMap X.O X.K b = (2 : X.K) ^ (-(δ + (U.card : ℤ) + 1)) *
      algebraMap X.O X.K (E.aθ (∏ p ∈ J, p)) := by simpa only [scale, hprod] using hb
  by_cases hf : V.filter J
  · obtain ⟨hval, ζ, hζ, hrep⟩ := V.onFilter J hJ hB hf
    have h := source_symbol_on_filter A.integral_inclusion hm X.two_mem hp hζ
      ((E.aθ_reduce _).trans hrep) (by rwa [hc] at hval) hb'
    rw [h, hc]
    by_cases hval' : Odd.vZ (V.integer J) = ((δ + (U.card : ℤ) + 1 : ℤ) : WithTop ℤ)
    · have hh : V.filter J ∧ Odd.vZ (V.integer J) =
          ((δ + (U.card : ℤ) + 1 : ℤ) : WithTop ℤ) := ⟨hf, hval'⟩
      rw [ite_eq_left hval', ite_eq_left hh, ite_eq_right one_ne_zero]
    · have hh : ¬ (V.filter J ∧ Odd.vZ (V.integer J) =
          ((δ + (U.card : ℤ) + 1 : ℤ) : WithTop ℤ)) := fun h => hval' h.2
      rw [ite_eq_right hval', ite_eq_right hh, ite_eq_left rfl]
  · have h := source_symbol_off_support A.integral_inclusion X.two_mem hp
      ((E.aθ_reduce _).trans (V.offFilter J hJ hB hf)) hb'
    simpa [hf] using h

/-- The coefficient-one input at an actual realization of a single form.
Only the Hecke comparison at the tested pair is used, and the exact Brandt
recurrence on the integral lifts is unnecessary. -/
theorem fresh_input_of_stage' (hbudget : B ≤ W + 1) (hm : X.m.IsMaximal)
    (valuation : StageValuation' (X := X) (S := S) (δ := δ) Scoeff)
    {U : Finset ℕ} {q : ℕ} (hu : Admissible S W U)
    (hU : GoodSet T Scoeff U) (hq : T.Good q) (hf : q ∉ Scoeff ∪ U)
    (hB : (insert q U).card ≤ B)
    (hexp : A.coeff q (X.F U) = E.FourierF D hu q)
    (htrace : A.coeff 1 (X.tΛ (X.frob q) (X.F U)) = A.coeff q (X.F U)) :
    R₀ (insert q U) = X.read U (X.redE (X.tΛ (X.frob q) (X.F U))) := by
  have hqU : q ∉ U := fun h => hf (Finset.mem_union_right _ h)
  have he : algebraMap X.O X.K (E.HU D hu q) =
      scale X.K δ U * algebraMap X.O X.K (E.aθ ((∏ s ∈ U, s) * q)) :=
    hu_fresh E D hu hq.1 hqU
  rw [A.read_orbit, A.orbitCoeff_eq, htrace, hexp,
    residue_congr X.two_mem (fourierF_sub_hu E D hu q),
    stage_source_symbol' A E D hbudget hm valuation U q hU hq hf hB _ he]
  generalize R₀ (insert q U) = r
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) r with rfl | rfl <;>
    simp [A.decode_one]

/-- Construct the App F theta data on a model carrying the exact expansions
on the tested domain. The exact signed recurrence is an input of this
interface; the odd-stage calculation alone proves it modulo `2^M`. -/
def thetaData'
    (hgood : ∀ p, GoodPrime T Scoeff p → S.Good p) (hbudget : B ≤ W + 1)
    (hap : S.ap = ap) (hm : X.m.IsMaximal)
    (hcore : SourceCore E.η (GoodPrime T Scoeff) adm S.ap E.aθ)
    (hsigned : ∀ p (hp : GoodPrime T Scoeff p),
      @RecAt X.O _ p ⟨hp.1.1⟩ (E.η p) (ratio p hp.1.1) (ap p) E.aθ)
    (hphase : ∀ p, GoodPrime T Scoeff p → ∃ k : ℕ, E.η p ^ (2 ^ k) = 1)
    (hexp : ∀ U (hu : Admissible S W U), GoodSet T Scoeff U → U.card + 1 ≤ B →
      ∀ n, n ≠ 0 → A.coeff n (X.F U) = E.FourierF D hu n)
    {avoid : Finset ℕ} (_havoid : Scoeff ⊆ avoid) (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (DF : ∀ U, DeterminantFourierData ops X.m (X.F U))
    (hDF : ∀ U, (DF U).coeff = A.coeff)
    (hexcl : Hexcl' A Scoeff avoid)
    (valuation : StageValuation' (X := X) (S := S) (δ := δ) Scoeff) :
    ThetaData' Scoeff A := by
  have hu (U : Finset ℕ) (hU : GoodSet T Scoeff U) (hB : U.card + 1 ≤ B) :
      Admissible S W U := ⟨by omega, fun p hp => hgood p (hU p hp)⟩
  let κ := fun p => if hp : p.Prime then ratio p hp else 0
  refine {
    δ := δ
    truncation := budgetLevel δ W R
    admissible := adm
    a := E.aθ
    η := E.η
    ratio := κ
    H := stageH E D
    residue_maximal := hm
    source := ?_
    ratio_sign := ?_
    signed_recur := ?_
    eta_phase := hphase
    good_hecke' := formwiseHecke_of_ambient A ops DF hDF hexcl
    theta_mod_two := ?_
    H_off_unary := ?_
    source_symbol := stage_source_symbol' A E D hbudget hm valuation }
  · exact (congrArg (fun f => SourceHyp (budgetLevel δ W R) δ E.η (GoodPrime T Scoeff) adm f E.aθ)
      hap).mp (lift_source E D hcore)
  · intro p hp
    simpa only [κ, dite_eq_left hp.1.1] using ratio_sign hp.1.1
  · intro p hp
    simpa only [κ, dite_eq_left hp.1.1] using hsigned p hp
  · intro U hU hB n hn
    rw [stageH, dite_eq_left (hu U hU hB), hexp U (hu U hU hB) hU hB n hn]
    exact fourierF_sub_hu E D (hu U hU hB) n
  · intro U hU hB J hJ hJU n hn
    refine ⟨E.HU D (hu U hU hB) n, ?_, ?_⟩
    · exact hu_off_unary E D (hu U hU hB) J hJ hJU hn
    · rw [stageH, dite_eq_left (hu U hU hB), sub_self]
      exact dvd_zero _

/-- The constituent input identities on the actual tests using an odd stage of sufficient
precision. This route does not require an exact integral `SourceCore` or
`RecAt`. Realization on the whole tested domain remains an input. -/
theorem inputs_at_precision'
    (hgood : ∀ p, GoodPrime T Scoeff p → S.Good p) (hbudget : B ≤ W + 1)
    (hap : S.ap = ap) (hm : X.m.IsMaximal) (htyp : IsTypeChar T χ)
    (hphase : ∀ p, GoodPrime T Scoeff p → ∃ k : ℕ, E.η p ^ (2 ^ k) = 1)
    (hexp : ∀ U (hu : Admissible S W U), GoodSet T Scoeff U → U.card + 1 ≤ B →
      ∀ n, A.coeff n (X.F U) = E.FourierF D hu n)
    {avoid : Finset ℕ} (_havoid : Scoeff ⊆ avoid) (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (DF : ∀ U, DeterminantFourierData ops X.m (X.F U)) (hDF : ∀ U, (DF U).coeff = A.coeff)
    (hhecke : FormwiseHecke' A Scoeff)
    (valuation : StageValuation' (X := X) (S := S) (δ := δ) Scoeff)
    (localData : LocalInput' A Scoeff) : Inputs' X Scoeff := by
  have admissible (U : Finset ℕ) (hU : GoodSet T Scoeff U) (hB : U.card + 1 ≤ B) :
      Admissible S W U := ⟨by omega, fun p hp => hgood p (hU p hp)⟩
  refine ⟨?_, ?_⟩
  · intro U q hU hq hf hB
    have hqU : q ∉ U := fun h => hf (Finset.mem_union_right _ h)
    have hb : U.card + 1 ≤ B := by rwa [Finset.card_insert_of_notMem hqU] at hB
    have hu := admissible U hU hb
    refine fresh_input_of_stage' A E D hbudget hm valuation hu hU hq hf hB
      (hexp U hu hU hb q) ?_
    simpa only [mul_one] using SieveAvoid.trace_coeff_of_not_dvd hhecke hU hq hf hb (n := 1)
      (fun h => hq.1.ne_one (Nat.dvd_one.mp h))
  · intro U p hpU hU hB g
    have hu := admissible U hU hB
    have hV : GoodSet T Scoeff (U.erase p) := fun q hq => hU q (Finset.mem_of_mem_erase hq)
    have hBV := (Nat.add_le_add_right (Finset.card_le_card (Finset.erase_subset p U)) 1).trans hB
    have hv := admissible (U.erase p) hV hBV
    exact o12_at_one_of_stage A E D ops DF hDF hap hm htyp U p hpU
      (fun p hp => (hU p hp).1) hB g hu hv
      (hexp U hu hU hB) (hexp (U.erase p) hv hV hBV) (hphase p (hU p hpU))
      (localData U p hpU hU hB)

/-- Read at a prescribed allowed prime in a single actual window. The
excluded branch uses only coefficient one. -/
theorem root_readings_of_stage' {U avoid : Finset ℕ}
    (hU : GoodSet T Scoeff U) (hB : U.card + 1 ≤ B) (hbudget : B ≤ W + 1)
    (hexp : ExpansionsOn A E D U) (hm : X.m.IsMaximal)
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (DF : DeterminantFourierData ops X.m (X.F U)) (hDF : DF.coeff = A.coeff)
    (valuation : StageValuation' (X := X) (S := S) (δ := δ) Scoeff)
    (hexcl : ∀ q, T.Good q → q ∉ Scoeff ∪ U → q ∈ avoid →
      A.coeff 1 (X.tΛ (X.frob q) (X.F U)) = A.coeff q (X.F U)) :
    ∀ q, T.Good q → q ∉ Scoeff ∪ U → FreshAt X U q := by
  intro q hq hf
  obtain ⟨hu, hfu⟩ := hexp U (Finset.Subset.refl U)
  have hqU : q ∉ U := fun h => hf (Finset.mem_union_right _ h)
  exact fresh_input_of_stage' A E D hbudget hm valuation hu hU hq hf
    (by rwa [Finset.card_insert_of_notMem hqU]) (hfu q)
    (ambient_trace_at_one ops DF hDF hexcl hq hf)

/-- Actual finite-window data suffice for the omission port. The same
pointwise omission proof uses only ambient representatives. -/
theorem readings_on_of_stage' {U avoid : Finset ℕ}
    (hU : GoodSet T Scoeff U) (hB : U.card + 1 ≤ B) (hbudget : B ≤ W + 1)
    (hexp : ExpansionsOn A E D U) (hm : X.m.IsMaximal) (hap : S.ap = ap)
    (htyp : IsTypeChar T χ) (havoid : Scoeff ⊆ avoid)
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (DF : ∀ V, DeterminantFourierData ops X.m (X.F V)) (hDF : ∀ V, (DF V).coeff = A.coeff)
    (valuation : StageValuation' (X := X) (S := S) (δ := δ) Scoeff)
    (hphase : ∀ p ∈ U, ∃ k : ℕ, E.η p ^ (2 ^ k) = 1)
    (localData : LocalOn A U (fun p hp => (hU p hp).1)) :
    ReadingsOn X U (Scoeff ∪ avoid) := by
  refine ⟨?_, ?_⟩
  · intro V hV q hq hqV hqa
    have hqA : q ∉ avoid := fun h => hqa (Finset.mem_union_right _ h)
    have hf : q ∉ Scoeff ∪ V := by
      intro e
      exact (Finset.mem_union.mp e).elim (fun h => hqA (havoid h)) hqV
    obtain ⟨hv, hfv⟩ := hexp V hV
    obtain ⟨_, hh⟩ := A.goodHecke_of_data ops V (DF V) (hDF V) hq hqA
    have hn : ¬ q ∣ 1 := fun h => hq.1.ne_one (Nat.dvd_one.mp h)
    exact fresh_input_of_stage' A E D hbudget hm valuation hv (fun p hp => hU p (hV hp)) hq hf
      (by
        rw [Finset.card_insert_of_notMem hqV]
        exact (Nat.add_le_add_right (Finset.card_le_card hV) 1).trans hB)
      (hfv q) (by rw [hh, mul_one, ite_eq_right hn, add_zero])
  · intro p hpU g
    obtain ⟨hu, hfu⟩ := hexp U (Finset.Subset.refl U)
    obtain ⟨hv, hfv⟩ := hexp (U.erase p) (Finset.erase_subset p U)
    exact o12_at_one_of_stage A E D ops DF hDF hap hm htyp
      U p hpU (fun q hq => (hU q hq).1) hB g hu hv hfu hfv (hphase p hpU) (localData p hpU)

#print axioms stage_source_symbol'
#print axioms fresh_input_of_stage'
#print axioms thetaData'
#print axioms inputs_at_precision'
#print axioms root_readings_of_stage'
#print axioms readings_on_of_stage'

end Theta

end ZInQ.Manuscript.RC.SieveAvoid
