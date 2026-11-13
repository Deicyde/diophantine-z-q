import Mathlib
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Exponent
import ZInQKernel.Contrib.TauCeti.RingTheory.Ideal.RamificationGroup

/-!
# Bridge from Tau Ceti's global different theory to the leaves of `Breaks.lean`; T20 proved

* `ZInQ.Contrib.Different.hilbertDifferentFormula : GlueConductor.HilbertDifferentFormula`
  (T20), from Tau Ceti's
  `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one`
  (`LocalGlobal/Different/Exponent.lean`) and `Ideal.exists_forall_ramificationGroup_eq_bot`.
  Tau Ceti's `Ideal.ramificationGroup G Q i` is by definition `(Q ^ (i + 1)).inertia G`, i.e.
  `GlueConductor.ramGroup` (`ramificationGroup_eq_ramGroup`).
* The bridge lemmas used for T21 (`Global.lean`, `SerreLocal.lean`): Tau Ceti works over `𝓞 ℚ`,
  the leaves over `ℤ` (`differentIdeal_int_eq_differentIdeal_ringOfIntegers_rat`,
  `ramificationIdx_int_eq`), and `v_P(e) = e · v_p(e)` (`multiplicity_span_ramificationIdx_le`).

No `sorry`, no `axiom`.
-/

open NumberField IsDedekindDomain

namespace ZInQ.Contrib.Different

/-- The image of `𝓞 ℚ` in `ℚ` is the image of `ℤ`. -/
theorem range_algebraMap_ringOfIntegers_rat :
    (algebraMap (𝓞 ℚ) ℚ).range = (algebraMap ℤ ℚ).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp y.isIntegral_coe
    exact ⟨n, hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp⟩

/-- `ℤ → 𝓞 ℚ` is surjective. -/
theorem algebraMap_int_ringOfIntegers_rat_surjective :
    Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := by
  intro y
  have : (algebraMap (𝓞 ℚ) ℚ y) ∈ (algebraMap ℤ ℚ).range := by
    rw [← range_algebraMap_ringOfIntegers_rat]; exact ⟨y, rfl⟩
  obtain ⟨n, hn⟩ := this
  refine ⟨n, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 ℚ) ℚ
  rw [← hn, ← IsScalarTower.algebraMap_apply]

variable (L : Type*) [Field L] [NumberField L]

/-- The different of `𝓞 L` over `ℤ` is the different over `𝓞 ℚ`. -/
theorem differentIdeal_int_eq_differentIdeal_ringOfIntegers_rat :
    differentIdeal ℤ (𝓞 L) = differentIdeal (𝓞 ℚ) (𝓞 L) := by
  apply IsFractionRing.coeSubmodule_injective (𝓞 L) L
  rw [coeSubmodule_differentIdeal ℤ ℚ, coeSubmodule_differentIdeal (𝓞 ℚ) ℚ]
  congr 1
  ext x
  simp only [Submodule.mem_traceDual, range_algebraMap_ringOfIntegers_rat]

variable {L}

/-- The ramification index of a prime `P` of `𝓞 L` over `ℤ` equals the one over `𝓞 ℚ`. -/
theorem ramificationIdx_int_eq (P : Ideal (𝓞 L)) [P.IsPrime] :
    P.ramificationIdx ℤ = P.ramificationIdx (𝓞 ℚ) := by
  have key : Ideal.map (algebraMap ℤ (Localization.AtPrime P)) (Ideal.under ℤ P) =
      Ideal.map (algebraMap (𝓞 ℚ) (Localization.AtPrime P)) (Ideal.under (𝓞 ℚ) P) := by
    rw [IsScalarTower.algebraMap_eq ℤ (𝓞 ℚ) (Localization.AtPrime P), ← Ideal.map_map]
    congr 1
    rw [← Ideal.under_under (B := 𝓞 ℚ) P]
    exact Ideal.map_comap_of_surjective _ algebraMap_int_ringOfIntegers_rat_surjective _
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def]
  congr 3

/-- A nonzero prime of `𝓞 L`, as a point of the height one spectrum. -/
def toHeightOneSpectrum (P : Ideal (𝓞 L)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) :
    HeightOneSpectrum (𝓞 L) :=
  ⟨P, hP, hP0⟩

/-- Tau Ceti's ramification groups are `GlueConductor.ramGroup`. -/
theorem ramificationGroup_eq_ramGroup [IsGalois ℚ L] (P : Ideal (𝓞 L)) (i : ℕ) :
    P.ramificationGroup (L ≃ₐ[ℚ] L) i = GlueConductor.ramGroup L P i :=
  Ideal.ramificationGroup_def P i

/-- **T20, global (`GlueConductor.HilbertDifferentFormula`).** -/
theorem hilbertDifferentFormula : GlueConductor.HilbertDifferentFormula := by
  intro L _ _ _ P _ hP0
  set w := toHeightOneSpectrum P hP0 with hw
  have hH := HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one
    (K := ℚ) w
  have hwP : w.asIdeal = P := rfl
  rw [hwP] at hH
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have : FaithfulSMul (L ≃ₐ[ℚ] L) (𝓞 L) := IsGaloisGroup.faithful (𝓞 ℚ)
  obtain ⟨N, hN⟩ := Ideal.exists_forall_ramificationGroup_eq_bot (G := L ≃ₐ[ℚ] L) hPtop
  have hfin : ∑ᶠ i : ℕ, (Nat.card (P.ramificationGroup (L ≃ₐ[ℚ] L) i) - 1) =
      ∑ i ∈ Finset.range N, (GlueConductor.ramCard L P i - 1) := by
    rw [finsum_eq_sum_of_support_subset (s := Finset.range N)]
    · rfl
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hle
      apply hi
      rw [hN i (not_lt.mp hle)]
      simp
  rw [hfin, ← differentIdeal_int_eq_differentIdeal_ringOfIntegers_rat] at hH
  have hD0 : differentIdeal ℤ (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  have hF : FiniteMultiplicity P (differentIdeal ℤ (𝓞 L)) := Ideal.finiteMultiplicity hPtop hD0
  refine ⟨N, ?_, ?_, ?_⟩
  · rw [← ramificationGroup_eq_ramGroup]
    exact hN N le_rfl
  · rw [← hH]
    exact pow_multiplicity_dvd _ _
  · apply hF.not_pow_dvd_of_multiplicity_lt
    rw [hH]
    exact Nat.lt_succ_self _

/-- `v_P(e) ≤ e · v_p(e)` for the natural number `e = e(P/p)`. -/
theorem multiplicity_span_ramificationIdx_le (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime]
    [hPl : P.LiesOver (Ideal.span {(p : ℤ)})] (hP0 : P ≠ ⊥) :
    multiplicity P (Ideal.span {((P.ramificationIdx ℤ : ℕ) : 𝓞 L)}) ≤
      P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set e := P.ramificationIdx ℤ with he_def
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos ℤ P).ne'
  set k := padicValNat p e with hk
  obtain ⟨m, hm⟩ : p ^ k ∣ e := pow_padicValNat_dvd (p := p)
  have hpm : ¬ p ∣ m := by
    rintro ⟨c, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := p) he0
    rw [← hk, hm, pow_succ, ← mul_assoc]
    exact dvd_mul_right _ _
  have hprime : Prime P := Ideal.prime_of_isPrime hP0 ‹_›
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have hspan : Ideal.span {((e : ℕ) : 𝓞 L)} =
      Ideal.span {((p : ℕ) : 𝓞 L)} ^ k * Ideal.span {((m : ℕ) : 𝓞 L)} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, hm]
    push_cast
    rfl
  have hunder : Ideal.span {(p : ℤ)} = P.under ℤ := hPl.over
  have hpe : e = multiplicity P (Ideal.span {((p : ℕ) : 𝓞 L)}) := by
    have h0 : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (𝓞 L)) ≠ ⊥ := by
      rw [Ideal.map_span, Set.image_singleton, ne_eq, Ideal.span_singleton_eq_bot]
      simp [hp.ne_zero]
    rw [he_def, Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(p : ℤ)}) P h0,
      Ideal.map_span, Set.image_singleton]
    simp
  have hmP : emultiplicity P (Ideal.span {((m : ℕ) : 𝓞 L)}) = 0 := by
    rw [emultiplicity_eq_zero, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    intro hmem
    have : ((m : ℕ) : ℤ) ∈ P.under ℤ := by
      rw [Ideal.mem_comap]; simpa using hmem
    rw [← hunder, Ideal.mem_span_singleton] at this
    exact hpm (Int.natCast_dvd_natCast.mp this)
  have hfinp : FiniteMultiplicity P (Ideal.span {((p : ℕ) : 𝓞 L)}) :=
    Ideal.finiteMultiplicity hPtop (by simp [hp.ne_zero])
  have hfine : FiniteMultiplicity P (Ideal.span {((e : ℕ) : 𝓞 L)}) :=
    Ideal.finiteMultiplicity hPtop (by simp [he0])
  have key : (multiplicity P (Ideal.span {((e : ℕ) : 𝓞 L)}) : ℕ∞) = (k * e : ℕ) := by
    rw [← hfine.emultiplicity_eq_multiplicity, hspan, emultiplicity_mul hprime,
      emultiplicity_pow hprime, hmP, hfinp.emultiplicity_eq_multiplicity, ← hpe]
    push_cast
    ring
  have := Nat.cast_inj.mp key
  rw [this, mul_comm]

end ZInQ.Contrib.Different
