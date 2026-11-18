import ZInQKernel.Contrib.OneProof.RC.O12.Inputs
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Model
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Expansions
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Symbol

/-! Connect the stage divisions to the common-model interface. The realization
assumption is on the whole tested domain; the zero extension of a finite pool
cannot be substituted for it. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Theta

open AddressGenuine PrintsArith TraceLimits ZInQ.Manuscript.RC.Odd ThetaCoeff O12
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped Classical MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
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
structure StageValuation where
  filter : Finset ℕ → Prop
  integer : Finset ℕ → ℤ
  read : ∀ V : Finset ℕ, (∀ p ∈ V, T.Good p) → V.card ≤ B →
    R₀ V = if filter V ∧ Odd.vZ (integer V) = ((δ + (V.card : ℤ) : ℤ) : WithTop ℤ) then 1 else 0
  onFilter : ∀ V : Finset ℕ, (∀ p ∈ V, T.Good p) → V.card ≤ B → filter V →
    ((δ + (V.card : ℤ) : ℤ) : WithTop ℤ) ≤ Odd.vZ (integer V) ∧
    ∃ ζ : X.O, (∃ k : ℕ, ζ ^ (2 ^ k : ℕ) = 1) ∧
      S.aθ (∏ p ∈ V, p) = stageReduction X.O M (ζ * (integer V : X.O))
  offFilter : ∀ V : Finset ℕ, (∀ p ∈ V, T.Good p) → V.card ≤ B → ¬ filter V →
    S.aθ (∏ p ∈ V, p) = 0

include A D in
/-- Evaluate the stage symbol after the integral division, including the
zero case off the filter. -/
theorem stage_source_symbol (hbudget : B ≤ W + 1) (hm : X.m.IsMaximal)
    (V : StageValuation (X := X) (S := S) (δ := δ))
    (U : Finset ℕ) (q : ℕ) (hU : ∀ p ∈ U, T.Good p) (hq : T.Good q) (hqU : q ∉ U)
    (hB : (insert q U).card ≤ B) (b : X.O)
    (hb : algebraMap X.O X.K b = scale X.K δ U *
      algebraMap X.O X.K (E.aθ ((∏ p ∈ U, p) * q))) :
    Ideal.Quotient.mk X.m b = if R₀ (insert q U) = 0 then 0 else 1 := by
  let J := insert q U
  have hJ : ∀ p ∈ J, T.Good p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hq
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
theorem fresh_input_of_stage (hbudget : B ≤ W + 1) (hm : X.m.IsMaximal)
    (valuation : StageValuation (X := X) (S := S) (δ := δ))
    {U : Finset ℕ} {q : ℕ} (hu : Admissible S W U)
    (hU : ∀ p ∈ U, T.Good p) (hq : T.Good q) (hqU : q ∉ U)
    (hB : (insert q U).card ≤ B)
    (hexp : A.coeff q (X.F U) = E.FourierF D hu q)
    (htrace : A.coeff 1 (X.tΛ (X.frob q) (X.F U)) = A.coeff q (X.F U)) :
    R₀ (insert q U) = X.read U (X.redE (X.tΛ (X.frob q) (X.F U))) := by
  have hf : algebraMap X.O X.K (E.HU D hu q) =
      scale X.K δ U * algebraMap X.O X.K (E.aθ ((∏ s ∈ U, s) * q)) :=
    hu_fresh E D hu hq.1 hqU
  rw [A.read_orbit, A.orbitCoeff_eq, htrace, hexp,
    residue_congr X.two_mem (fourierF_sub_hu E D hu q),
    stage_source_symbol A E D hbudget hm valuation U q hU hq hqU hB _ hf]
  generalize R₀ (insert q U) = r
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) r with rfl | rfl <;>
    simp [A.decode_one]

def stageH (U : Finset ℕ) (n : ℕ) : X.O :=
  if hu : Admissible S W U then E.HU D hu n else 0

/-- Construct the App F theta data on a model carrying the exact expansions
on the tested domain. The exact signed recurrence is an input of this
interface; the odd-stage calculation alone proves it modulo `2^M`. -/
def thetaData
    (hgood : ∀ p, T.Good p → S.Good p) (hbudget : B ≤ W + 1)
    (hap : S.ap = ap) (hm : X.m.IsMaximal)
    (hcore : SourceCore E.η T.Good adm S.ap E.aθ)
    (hsigned : ∀ p (hp : T.Good p),
      @RecAt X.O _ p ⟨hp.1⟩ (E.η p) (ratio p hp.1) (ap p) E.aθ)
    (hphase : ∀ p, T.Good p → ∃ k : ℕ, E.η p ^ (2 ^ k) = 1)
    (hexp : ∀ U (hu : Admissible S W U), (∀ p ∈ U, T.Good p) → U.card + 1 ≤ B →
      ∀ n, n ≠ 0 → A.coeff n (X.F U) = E.FourierF D hu n)
    {avoid : Finset ℕ} (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (DF : ∀ U, DeterminantFourierData ops X.m (X.F U))
    (hDF : ∀ U, (DF U).coeff = A.coeff)
    (hexcl : ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
      U.card + 1 ≤ B → q ∈ avoid → ∃ diamondF : X.Λ, ∀ n,
        A.coeff n (X.tΛ (X.frob q) (X.F U)) =
          A.coeff (q * n) (X.F U) + if q ∣ n then (q : X.O) * A.coeff (n / q) diamondF else 0)
    (valuation : StageValuation (X := X) (S := S) (δ := δ)) :
    ThetaData A := by
  have hu (U : Finset ℕ) (hU : ∀ p ∈ U, T.Good p) (hB : U.card + 1 ≤ B) :
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
    good_hecke := formwiseHecke_of_ambient A ops DF hDF hexcl
    theta_mod_two := ?_
    H_off_unary := ?_
    source_symbol := stage_source_symbol A E D hbudget hm valuation }
  · exact (congrArg (fun f => SourceHyp (budgetLevel δ W R) δ E.η T.Good adm f E.aθ)
      hap).mp (lift_source E D hcore)
  · intro p hp
    simpa only [κ, dite_eq_left hp.1] using ratio_sign hp.1
  · intro p hp
    simpa only [κ, dite_eq_left hp.1] using hsigned p hp
  · intro U hU hB n hn
    rw [stageH, dite_eq_left (hu U hU hB), hexp U (hu U hU hB) hU hB n hn]
    exact fourierF_sub_hu E D (hu U hU hB) n
  · intro U hU hB J hJ hJU n hn
    refine ⟨E.HU D (hu U hU hB) n, ?_, ?_⟩
    · exact hu_off_unary E D (hu U hU hB) J hJ hJU hn
    · rw [stageH, dite_eq_left (hu U hU hB), sub_self]
      exact dvd_zero _

/-- Apply the unchanged (O.12) consumer, using the actual theta data
constructed above and the named local input on the same lattice. -/
theorem inputs_of_stage
    (hgood : ∀ p, T.Good p → S.Good p) (hbudget : B ≤ W + 1)
    (hap : S.ap = ap) (hm : X.m.IsMaximal)
    (hcore : SourceCore E.η T.Good adm S.ap E.aθ)
    (hsigned : ∀ p (hp : T.Good p),
      @RecAt X.O _ p ⟨hp.1⟩ (E.η p) (ratio p hp.1) (ap p) E.aθ)
    (hphase : ∀ p, T.Good p → ∃ k : ℕ, E.η p ^ (2 ^ k) = 1)
    (hexp : ∀ U (hu : Admissible S W U), (∀ p ∈ U, T.Good p) → U.card + 1 ≤ B →
      ∀ n, n ≠ 0 → A.coeff n (X.F U) = E.FourierF D hu n)
    {avoid : Finset ℕ} (ops : GoodOperators T avoid X.frob X.ρ X.Λ)
    (DF : ∀ U, DeterminantFourierData ops X.m (X.F U))
    (hDF : ∀ U, (DF U).coeff = A.coeff)
    (hexcl : ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
      U.card + 1 ≤ B → q ∈ avoid → ∃ diamondF : X.Λ, ∀ n,
        A.coeff n (X.tΛ (X.frob q) (X.F U)) =
          A.coeff (q * n) (X.F U) + if q ∣ n then (q : X.O) * A.coeff (n / q) diamondF else 0)
    (valuation : StageValuation (X := X) (S := S) (δ := δ))
    (localData : LocalInput A) (htyp : IsTypeChar T χ) : X.Inputs :=
  O12.inputs_of_theta
    (thetaData A E D hgood hbudget hap hm hcore hsigned hphase hexp ops DF hDF hexcl valuation)
    localData htyp

#print axioms stage_source_symbol
#print axioms fresh_input_of_stage
#print axioms stageH
#print axioms thetaData
#print axioms inputs_of_stage

end Theta

end ZInQ.Manuscript.RC.O12Theta
