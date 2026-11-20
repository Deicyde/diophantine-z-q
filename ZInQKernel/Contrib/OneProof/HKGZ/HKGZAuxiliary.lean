import ZInQKernel.Contrib.OneProof.HKGZ.HKGZPrints
import ZInQKernel.Contrib.CloudB3RC53.Hasse.Final
import ZInQKernel.Contrib.CloudB3RC53.Companion.Disc
import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.WeakWeil
import ZInQKernel.Contrib.OneProof.RC.Height.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.FromPrintsAnalytic
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Parity
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Uses

/-! # The auxiliary imaginary quadratic field from the second BFH clause -/

namespace ZInQ.Manuscript.HKGZ

open NumberField WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open RC.PrintsAnalytic HeckeRing.GL2 UpperHalfPlane

theorem squareAt_of_kronecker {D : ℤ} (hD : IsFundamentalDiscriminant D)
    {p : ℕ} (hp : p.Prime) (hχ : kronecker D p = 1) : GenusOdd.SquareAt p D := by
  have h := RC.Nonvanishing.FromRC8.splitsIn_of_kronecker hD hp hχ
  by_cases hp2 : p = 2
  · subst p
    have h8 := h.1 rfl
    exact ⟨by omega, fun _ => h8, fun hn => (hn rfl).elim⟩
  · exact ⟨(h.2 hp2).1, fun he => (hp2 he).elim, fun _ => (h.2 hp2).2⟩

/-- A coefficient-matching newform has exactly the least coefficient-matching cusp-form
level used in the stage-one dictionary. -/
theorem newformLevel_eq_of_isNewformOf {E : WeierstrassCurve ℚ}
    {M : ℕ} [NeZero M] {f : Newform M 2} (hf : IsNewformOf E f) :
    newformLevel E = M := by
  obtain ⟨hN, hmin⟩ := ModularWeil.exists_form_at_newformLevel E (isModular_of_isNewformOf hf)
  refine Nat.le_antisymm ?_ (Nat.le_of_dvd hN (GenusOdd.dvd_of_hasCuspFormAtLevel hf hN hmin))
  apply Nat.sInf_le
  have hmem : f.toCuspForm ∈ cuspFormCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ) := by
    have h := f.mem_charSpace
    rwa [hf.1] at h
  refine ⟨NeZero.pos M, TauCeti.cuspFormCharSpaceOneEquiv M 2 ⟨f.toCuspForm, hmem⟩,
    fun n hn => ?_⟩
  rw [TauCeti.coe_cuspFormCharSpaceOneEquiv_apply]
  exact hf.2 n hn

/-- The simple zero gives sign `-1`. Applying BFH with an enlarged finite splitting set
gives a negative fundamental discriminant, a genuine split imaginary quadratic field, and
the nonzero twist value (stated as analytic rank zero). Including 2 lets us use the odd
discriminant form of the tree's Artin factorization and avoids the extra-unit fields. -/
theorem exists_auxiliary_of_bfh (hB : BFHTwistNonvanishingDraft) (hM : ModularNewform)
    (E : WeierstrassCurve ℚ) [hE : E.IsElliptic] (hA : AnalyticRankOne E) :
    RootNumber E (-1) ∧
      ∃ (K : Type) (hF : Field K), letI : Field K := hF
        ∃ hNF : NumberField K, letI : NumberField K := hNF
          SplitHeegnerField E K ∧ Odd (discr K) ∧
          Nat.Coprime (discr K).natAbs (newformLevel E) ∧
          AnalyticRank (qtwist E (discr K)) 0 := by
  classical
  have hH := Hasse.hasseConvergence_proved
  obtain ⟨M, _, f, hf⟩ := hM E hE
  obtain ⟨w, -, hw⟩ := rootNumberAt_of_isNewformOf hH hf
  have hroot := rootNumber_iff_exists_rootNumberAt.mpr ⟨M, hw⟩
  have hs : w = -1 := by
    have h := rootNumber_parity_of_analyticRank hroot ((analyticRank_one_iff E).mpr hA)
    simpa using h.symm
  subst w
  refine ⟨hroot, ?_⟩
  have hlevel := newformLevel_eq_of_isNewformOf hf
  have hN : 0 < newformLevel E := by simpa only [hlevel] using (NeZero.pos M)
  let S := insert 2 M.primeFactors
  have hS : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Nat.prime_two
    · exact (Nat.mem_primeFactors.mp hp).1
  have hMS : ∀ p : ℕ, p.Prime → p ∣ M → p ∈ S := fun p hp hd =>
    Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne M⟩)
  have hNS : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → p ∈ S := by
    simpa only [hlevel] using hMS
  have hCurve := RC.TwistDictionary.bfhCurve_of_print hB hM hH
  obtain ⟨D, hD, hsign, hχ, hzero⟩ := (hCurve E hE M (-1) hw S hS hMS).2
  have hneg : D < 0 := by linarith
  have h8 := (squareAt_of_kronecker hD Nat.prime_two (hχ 2 (Finset.mem_insert_self _ _))).2.1 rfl
  have hDodd : Odd D := Int.odd_iff.mpr (by omega)
  have h4sq : D % 4 = 1 ∧ Squarefree D := by
    rcases hD.2 with h | ⟨m, hm, _, _⟩
    · exact h
    · omega
  let : Fact (¬ IsSquare (D : ℚ)) := ⟨by
    rintro ⟨x, hx⟩
    have hd : (D : ℚ) < 0 := by exact_mod_cast hneg
    nlinarith [sq_nonneg x]⟩
  let K := RC.Height.SqrtField (D : ℚ)
  let : Field K := inferInstanceAs (Field (RC.Height.SqrtField (D : ℚ)))
  let : NumberField K := inferInstanceAs (NumberField (RC.Height.SqrtField (D : ℚ)))
  have hK2 : Module.finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  have hr := RC.Height.SqrtField.root_sq (D : ℚ)
  have hr' : RC.Height.SqrtField.root (D : ℚ) ^ 2 = (D : K) := by
    simpa using hr
  have hdisc := Companion.discr_eq_of_sq hK2 h4sq.2 h4sq.1 (by omega) hr'
  have htc : IsTotallyComplex K := isTotallyComplex_of_sq_ratCast_of_neg hr (by exact_mod_cast hneg)
  refine ⟨K, inferInstance, inferInstance, ⟨hK2, htc, ?_, ?_, hN, ?_⟩, ?_, ?_, ?_⟩
  · rw [hdisc]
    omega
  · rw [hdisc]
    omega
  · intro p hp hd
    apply Splitting.splittingCriterion_proof K hK2 p hp
    rw [hdisc]
    exact squareAt_of_kronecker hD hp (hχ p (hNS p hp hd))
  · simpa [hdisc] using hDodd
  · rw [hdisc]
    exact Int.isCoprime_iff_gcd_eq_one.mp
      (isCoprime_of_forall_kronecker_eq_one fun p hp hd => hχ p (hNS p hp hd))
  · simpa [hdisc] using hzero

end ZInQ.Manuscript.HKGZ
