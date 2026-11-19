import ZInQKernel.Contrib.OneProof.RC.O12Theta.AtPrecision
import ZInQKernel.Contrib.OneProof.RC.Symbols.SymbolDef
import ZInQKernel.Contrib.OneProof.RC.Visibility.Models

/-! App G chooses the stage for the integer representatives of (O.7).
The symbol and the theta divisions use that same choice. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12StageVal
set_option maxHeartbeats 800000

open ZInQ.Manuscript.RC.Odd ThetaCoeff O12Theta Filter
open ZInQ.Contrib.CloudB3RC53.AppGEndpoints
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped Classical

variable {O : Type} [CommRing O] {M W R B : ℕ} {δ : ℤ}
variable {S : AppF.ThetaStage (StageRing O M)} {adm : ℕ → Prop}

/-- App G's precision and depth, on the integers before their images are taken
in the character ring. Here `a` is the phase-removed representative. -/
structure IntegerDepth (M W R : ℕ) (δ : ℤ) (adm : ℕ → Prop) (a : ℤ → ℤ) : Prop where
  precision : budgetLevel δ W R ≤ M
  depth : ∀ n : ℕ, Squarefree n → adm n →
    ((min (budgetLevel δ W R : ℤ) (δ + ArithmeticFunction.cardDistinctFactors n) : ℤ) :
      WithTop ℤ) ≤ Odd.vZ (a n)

/-- App G's eventual valid stages for the given attained minimum. The
bound is on the integers used in the symbol, before transfer to the stage ring. -/
theorem integerDepth_of_min (U : Ultrafilter ℕ) (prec : ℕ → ℕ)
    (hM : Tendsto prec (U : Filter ℕ) atTop)
    (a : ℕ → ℤ → ℤ) (domain : ℕ → ℤ → Prop) (C : ℚ)
    (hF5 : ∀ i n, domain i n → QLe (min (prec i : ℚ) (omega n - C)) (Odd.vZ (a i n)))
    (hδ : IsLeast (DepthSet U prec (fun i n => Odd.vZ (a i n)) domain) δ)
    (hR : 2 ≤ R) :
    ∀ᶠ i in (U : Filter ℕ), IntegerDepth (prec i) W R δ (fun n => domain i n) (a i) := by
  obtain ⟨T, -, -, hT⟩ :=
    stageChoice_proof U prec (fun i n => Odd.vZ (a i n)) domain C δ W R hR hM hF5
      (f6_of_isLeast hF5 hδ)
  filter_upwards [hT] with i hi
  obtain ⟨-, hprec, -, -, hdepth⟩ := hi
  have hbudget := budgetLevel_cast δ W R
  refine ⟨by exact_mod_cast hbudget.trans_le hprec, fun n _ hn => ?_⟩
  obtain ⟨hlarge, hsmall⟩ := hdepth (n : ℤ) hn
  rw [appG_omega_natCast] at hlarge hsmall
  by_cases hb : T < ArithmeticFunction.cardDistinctFactors n
  · rw [← hbudget] at hlarge
    exact le_trans (WithTop.coe_le_coe.mpr (min_le_left _ _)) (hlarge hb)
  · refine le_trans (WithTop.coe_le_coe.mpr (min_le_right _ _)) ?_
    simpa only [add_comm δ] using hsmall (not_lt.mp hb)

/-- The fixed-witness App G selection, stated for the same integers that will be
used in the reading. The chosen valid stages are eventual for each budget. -/
theorem integerDepth_of_witness (U : Ultrafilter ℕ) (prec : ℕ → ℕ)
    (hM : Tendsto prec (U : Filter ℕ) atTop)
    (a : ℕ → ℤ → ℤ) (domain : ℕ → ℤ → Prop) (C : ℚ)
    (hF5 : ∀ i n, domain i n → QLe (min (prec i : ℚ) (omega n - C)) (Odd.vZ (a i n)))
    (hw : ∃ n c : ℤ, ∀ᶠ i in (U : Filter ℕ),
      domain i n ∧ Odd.vZ (a i n) = (c : WithTop ℤ) ∧ (c : WithTop ℤ) < prec i) :
    ∃ δ : ℤ, IsLeast (DepthSet U prec (fun i n => Odd.vZ (a i n)) domain) δ ∧
      ∀ W R : ℕ, 2 ≤ R → ∀ᶠ i in (U : Filter ℕ),
        IntegerDepth (prec i) W R δ (fun n => domain i n) (a i) := by
  obtain ⟨δ, hδ, -⟩ :=
    oddMinimumF6_proof U prec (fun i n => Odd.vZ (a i n)) domain C hF5 hw
  exact ⟨δ, hδ, fun _ _ hR => integerDepth_of_min U prec hM a domain C hF5 hδ hR⟩

/-- Named upstream input, (O.7) on the full squarefree filter at this stage.
The integer is a representative after phase removal; the equality is in the stage ring. -/
structure O7Comparison (S : AppF.ThetaStage (StageRing O M))
    (adm : ℕ → Prop) (a : ℤ → ℤ) : Prop where
  compare : ∀ n : ℕ, Squarefree n → adm n →
    ∃ ζ : O, (∃ k : ℕ, ζ ^ (2 ^ k : ℕ) = 1) ∧
      S.aθ n = stageReduction O M (ζ * (a n : O))

/-- Use the already formalized comparison argument with the given (O.7) data
on the particular lift. The representatives are the fixed integer multiplier
times the lifted Kummer evaluations (tex 9112–9113, 9373–9402). -/
theorem o7Comparison_of_core (E : Lift S) (lam : ℤ → ℤ) (ω : ℕ) (ζ : ℕ → O)
    (core : ∀ n : ℕ, Squarefree n → adm n →
      Visibility.ComparisonCore E.geom M (S.m : ℤ) (n : ℤ) ω (lam n) (ζ n))
    (hζ : ∀ n : ℕ, Squarefree n → adm n → ∃ k : ℕ, ζ n ^ (2 ^ k : ℕ) = 1) :
    O7Comparison S adm (fun n => (c0 : ℤ) * 2 ^ ω * lam n) := by
  refine ⟨fun n hn ha => ⟨ζ n, hζ n hn ha, ?_⟩⟩
  obtain ⟨r, hr⟩ := (core n hn ha).O7
  rw [← E.aθ_reduce]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  refine ⟨r, ?_⟩
  convert hr using 1
  simp only [Lift.aθ, Lift.H, Nat.cast_mul, Int.cast_mul, Int.cast_natCast,
    Int.cast_pow, Int.cast_ofNat]
  ring

/-- Assemble the odd-stage divisions from the same App F coefficients. Exact
Fourier support supplies the prime exclusions; separate local support gives
stage zero on squarefree indices off the full filter (tex 2530–2532, 9471–9478). -/
theorem divisions (E : Lift S) {a : ℤ → ℤ} (C : O7Comparison S adm a)
    (depth : IntegerDepth M W R δ adm a) (hR : 2 ≤ R)
    (hap : ∀ p, S.Good p → S.ap p ≡ p + 1 [ZMOD 4])
    (zero : E.aθ 0 = 0)
    (sieve : ∀ p, p.Prime → ¬ S.Good p → ∀ n, p ∣ n → E.aθ n = 0)
    (off : ∀ n, Squarefree n → ¬ adm n → S.aθ n = 0) :
    Divisions E δ W R adm := by
  refine ⟨S.oddStageSource hap ?_ off depth.precision ?_, hR, zero, sieve⟩
  · rintro n ⟨p, hp, hbad⟩
    rw [← E.aθ_reduce, sieve p (Nat.prime_of_mem_primeFactors hp) hbad n
      (Nat.dvd_of_mem_primeFactors hp), map_zero]
  · intro n hn ha
    obtain ⟨ζ, -, he⟩ := C.compare n hn ha
    rw [he]
    let t : ℤ := min (budgetLevel δ W R : ℤ) (δ + ArithmeticFunction.cardDistinctFactors n)
    change (2 : StageRing O M) ^ t.toNat ∣ _
    by_cases ht : t < 0
    · rw [Int.toNat_of_nonpos ht.le, pow_zero]
      exact one_dvd _
    · apply two_pow_dvd_stage_of_le_vZ
      rw [Int.toNat_of_nonneg (le_of_not_gt ht)]
      exact depth.depth n hn ha

/-- Every tested set has the squarefree index of the intrinsic symbol, with
the required count of distinct factors. The set may be empty. -/
theorem prime_index {V : Finset ℕ} (hV : ∀ p ∈ V, p.Prime) :
    Squarefree (∏ p ∈ V, p) ∧ ArithmeticFunction.cardDistinctFactors (∏ p ∈ V, p) = V.card := by
  have hs : Squarefree (∏ p ∈ V, p) :=
    Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq =>
      Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hV p hp) (hV q hq)).mpr hpq))
      (fun p hp => (hV p hp).squarefree)
  refine ⟨hs, ?_⟩
  rw [← card_oddPart_of_squarefree hs, oddPart_of_squarefree hs]
  exact Symbols.card_primeFactors_prod hV

/-- The tree's intrinsic coefficient symbol evaluated on the product of the
vertices. Here the coefficient function is the integer representative in `ℚ₂`. -/
def intrinsic (a : ℤ → ℤ) (δ : ℤ) (adm : ℕ → Prop) (V : Finset ℕ) : ZMod 2 :=
  Symbols.coeffSymbol (fun n => ((a n : ℚ) : ℚ_[2])) δ adm (∏ p ∈ V, p)

/-- The intrinsic reading is the threshold on the phase-removed integer
(tex 2074–2086, 9675–9680). On-the-spot (c): matching the two valuation interfaces. -/
theorem intrinsic_read (a : ℤ → ℤ) (δ : ℤ) (adm : ℕ → Prop)
    {V : Finset ℕ} (hV : ∀ p ∈ V, p.Prime) :
    intrinsic a δ adm V =
      if adm (∏ p ∈ V, p) ∧ Odd.vZ (a (∏ p ∈ V, p : ℕ)) = ((δ + (V.card : ℤ) : ℤ) : WithTop ℤ)
      then 1 else 0 := by
  unfold intrinsic Symbols.coeffSymbol
  rw [Symbols.card_primeFactors_prod hV]
  have hr (z e : ℤ) :
      (((z : ℚ) : ℚ_[2]) ≠ 0 ∧ Padic.valuation ((z : ℚ) : ℚ_[2]) = e) ↔
      Odd.vZ z = (e : WithTop ℤ) := by
    by_cases hz : z = 0
    · subst z
      simp [Odd.vZ]
    · have hq : ((z : ℚ) : ℚ_[2]) ≠ 0 := by exact_mod_cast hz
      rw [Odd.vZ, Padic.addValuation.apply hq, WithTop.coe_inj]
      exact and_iff_right hq
  simp only [hr]

/-- The integer threshold is unchanged by changing the representative by
`2^M` when the threshold is below `M` (tex 2081–2086, 9699–9704).
On-the-spot (c): both divisibility tests are below or at the precision. -/
theorem threshold_congr {z z' e : ℤ} (he : e < (M : ℤ))
    (h : (2 : ℤ) ^ M ∣ z - z') :
    Odd.vZ z = (e : WithTop ℤ) ↔ Odd.vZ z' = (e : WithTop ℤ) := by
  have hnonneg (x : ℤ) : ((0 : ℤ) : WithTop ℤ) ≤ Odd.vZ x := by
    simpa using (two_pow_dvd_iff_le_vZ x 0).mp (by simp)
  by_cases he0 : e < 0
  · have hno (x : ℤ) : Odd.vZ x ≠ (e : WithTop ℤ) := by
      intro hx
      have hle := hnonneg x
      rw [hx, WithTop.coe_le_coe] at hle
      omega
    simp [hno]
  · let k := e.toNat
    have hk : (k : ℤ) = e := Int.toNat_of_nonneg (le_of_not_gt he0)
    have hdiv (j : ℕ) (hj : j ≤ M) : (2 : ℤ) ^ j ∣ z ↔ (2 : ℤ) ^ j ∣ z' := by
      have hsub := two_pow_dvd_of_le hj h
      exact ⟨fun hz => by simpa using dvd_sub hz hsub,
        fun hz => by simpa [add_comm] using dvd_add hsub hz⟩
    have hval (x : ℤ) : Odd.vZ x = (e : WithTop ℤ) ↔
        (2 : ℤ) ^ k ∣ x ∧ ¬ (2 : ℤ) ^ (k + 1) ∣ x := by
      rw [two_pow_dvd_iff_le_vZ, two_pow_dvd_iff_le_vZ, hk, Nat.cast_add, Nat.cast_one, hk, not_le]
      induction Odd.vZ x using WithTop.recTopCoe with
      | top => simp
      | coe w =>
        simp only [WithTop.coe_inj, WithTop.coe_le_coe, WithTop.coe_lt_coe]
        omega
    rw [hval, hval, hdiv k (by omega), hdiv (k + 1) (by omega)]

/-- Every tested output is below the precision, and on the filter the
truncated App G bound is the full threshold there. -/
theorem tested_depth (a : ℤ → ℤ) (depth : IntegerDepth M W R δ adm a)
    (hR : 2 ≤ R) (hbudget : B ≤ W + 1) {V : Finset ℕ}
    (hV : ∀ p ∈ V, p.Prime) (hB : V.card ≤ B) :
    δ + (V.card : ℤ) < (M : ℤ) ∧
    (adm (∏ p ∈ V, p) →
      ((δ + (V.card : ℤ) : ℤ) : WithTop ℤ) ≤ Odd.vZ (a (∏ p ∈ V, p : ℕ))) := by
  have hb := budgetLevel_cast δ W R
  have hm : (budgetLevel δ W R : ℤ) ≤ (M : ℤ) := by exact_mod_cast depth.precision
  obtain ⟨hs, hc⟩ := prime_index hV
  refine ⟨by omega, fun ha => ?_⟩
  simpa only [hc, min_eq_right (show δ + (V.card : ℤ) ≤ (budgetLevel δ W R : ℤ) by omega)]
    using depth.depth _ hs ha

open AddressGenuine PrintsArith TraceLimits

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {χ : GalQ →* Multiplicative L} {R₀ : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
variable {X : GaloisConstituentModel T R₀ ap B χ}

/-- The good-domain transfer by divisibility of the excluded primes. The
type domain may omit additional primes without imposing another Fourier sieve. -/
theorem good_of_support {support : Finset ℕ}
    (hcover : ∀ p ∈ support, p.Prime → p ∣ T.m) {p : ℕ} (hp : T.Good p) :
    p.Prime ∧ p ∉ support :=
  ⟨hp.1, fun hm => ((Nat.Prime.coprime_iff_not_dvd hp.1).mp hp.2) (hcover p hm hp.1)⟩

/-- In the tested budget, the same good primes give the admissible operator sets. -/
theorem admissible_of_good {S : AppF.ThetaStage (StageRing O M)}
    (hgood : ∀ p, T.Good p → S.Good p) (hbudget : B ≤ W + 1)
    {U : Finset ℕ} (hU : ∀ p ∈ U, T.Good p) (hB : U.card + 1 ≤ B) :
    Admissible S W U :=
  ⟨by omega, fun p hp => hgood p (hU p hp)⟩

/-- Build the valuation input on the *same* stage used for the divisions.
The symbol is identified only on tested sets, with squarefree support taken
from that stage's `OddStageSource`. -/
def stageValuation {S : AppF.ThetaStage (StageRing X.O M)}
    (E : Lift S) (D : Divisions E δ W R adm) {a : ℤ → ℤ}
    (C : O7Comparison S adm a) (depth : IntegerDepth M W R δ adm a)
    (hbudget : B ≤ W + 1)
    (hread : ∀ V : Finset ℕ, (∀ p ∈ V, T.Good p) → V.card ≤ B → R₀ V = intrinsic a δ adm V) :
    StageValuation (X := X) (S := S) (δ := δ) where
  filter V := adm (∏ p ∈ V, p)
  integer V := a (∏ p ∈ V, p : ℕ)
  read V hV hB := (hread V hV hB).trans (intrinsic_read a δ adm (fun p hp => (hV p hp).1))
  onFilter V hV hB hf := by
    have hp : ∀ p ∈ V, p.Prime := fun p hp => (hV p hp).1
    exact ⟨(tested_depth a depth D.precision hbudget hp hB).2 hf, C.compare _ (prime_index hp).1 hf⟩
  offFilter V hV _ hf :=
    D.stage.2.support_adm _ (prime_index (fun p hp => (hV p hp).1)).1 hf

#print axioms integerDepth_of_min
#print axioms integerDepth_of_witness
#print axioms o7Comparison_of_core
#print axioms divisions
#print axioms prime_index
#print axioms intrinsic
#print axioms intrinsic_read
#print axioms threshold_congr
#print axioms tested_depth
#print axioms good_of_support
#print axioms admissible_of_good
#print axioms stageValuation

end ZInQ.Manuscript.RC.O12StageVal
