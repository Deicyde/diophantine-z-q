import Mathlib
import ZInQKernel.Contrib.Different.Bridge
import ZInQKernel.Contrib.Different.Local

/-!
# The global Serre bound T21 from task t-different's local bound

* `ZInQ.Contrib.Different.serreDifferentBound_of_local : GlueConductor.SerreDifferentBound`
  (T21), from `PkgI6.differentBound` (`Local.lean`: Serre's bound
  `𝔇_{B/A} ∣ 𝔪_B^{e-1} · (e)` for complete DVRs, proved by task t-different) applied to the
  completed integer rings `A = ℤ_p = v.adicCompletionIntegers ℚ`, `B = w.adicCompletionIntegers L`,
  and transported to `𝓞 L` with Tau Ceti's completion lemmas
  `multiplicity_differentIdeal_adicCompletionIntegers_eq_multiplicity_asIdeal` (the exponent of the
  different is preserved by completion) and `multiplicity_map_adicCompletionIntegers`.

This proof does not use Tau Ceti's `LocalGlobal/Different/Wild.lean` (nor the 11 modules vendored
for it); `Global.lean` has the proof through `Wild.lean`. `D1_genuine_closed_of_local` is
`GlueConductor.D1_genuine` with T20 (`Bridge.lean`) and this T21 applied.

Identifications proved here: `v·𝒪_v = 𝔪_v` (`map_asIdeal_eq_maximalIdeal`), and the ramification
index of `𝔪_B` over `A` (Mathlib's `Ideal.ramificationIdx`, the one in `PkgI6.DifferentBound`) is
the global `e(w/v)` (`ramificationIdx_maximalIdeal_adicCompletionIntegers`).
No `sorry`, no `axiom`.
-/

open NumberField IsDedekindDomain IsLocalRing
open scoped AdicCompletionExtension

namespace ZInQ.Contrib.Different

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {L : Type} [Field L] [NumberField L]

/-- `v · 𝒪_v` is the maximal ideal of the completed integer ring `𝒪_v`. -/
theorem map_asIdeal_eq_maximalIdeal (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal.map (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ)) =
      maximalIdeal (v.adicCompletionIntegers ℚ) := by
  set I := v.asIdeal.map (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ)) with hI
  have hmult : multiplicity (maximalIdeal (v.adicCompletionIntegers ℚ)) I = 1 := by
    rw [hI, HeightOneSpectrum.multiplicity_map_adicCompletionIntegers v v.asIdeal v.ne_bot]
    exact (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible.multiplicity_self
  have hI0 : I ≠ ⊥ := by
    intro h
    rw [h, ← Ideal.zero_eq_bot, multiplicity_zero_right] at hmult
    exact zero_ne_one hmult
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers ℚ)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI0 hπ
  have hm : maximalIdeal (v.adicCompletionIntegers ℚ) = Ideal.span {π} := hπ.maximalIdeal_eq
  have hIn : I = maximalIdeal (v.adicCompletionIntegers ℚ) ^ n := by
    rw [hn, hm, Ideal.span_singleton_pow]
  have hprime : Prime (maximalIdeal (v.adicCompletionIntegers ℚ)) :=
    Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance
  rw [hIn, multiplicity_pow_self_of_prime hprime] at hmult
  rw [hIn, hmult, pow_one]

/-- The ramification index of `𝔪_w` over `𝒪_v` is the global one. -/
theorem ramificationIdx_maximalIdeal_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 ℚ))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    Ideal.ramificationIdx (maximalIdeal (w.adicCompletionIntegers L)) (v.adicCompletionIntegers ℚ) =
      w.asIdeal.ramificationIdx (𝓞 ℚ) := by
  have hsq : (algebraMap (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)).comp
      (algebraMap (𝓞 ℚ) (v.adicCompletionIntegers ℚ)) =
      (algebraMap (𝓞 L) (w.adicCompletionIntegers L)).comp (algebraMap (𝓞 ℚ) (𝓞 L)) := by
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply,
      HeightOneSpectrum.algebraMap_adicCompletionIntegersExtensionAlgebra,
      HeightOneSpectrum.adicCompletionIntegersExtension_algebraMap]
  have hinj : Function.Injective (algebraMap (𝓞 ℚ) (𝓞 L)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hne : v.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 L)) ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_of_injective hinj]; exact v.ne_bot
  have hmap : (maximalIdeal (v.adicCompletionIntegers ℚ)).map
      (algebraMap (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)) =
      (v.asIdeal.map (algebraMap (𝓞 ℚ) (𝓞 L))).map (algebraMap (𝓞 L) (w.adicCompletionIntegers L)) := by
    rw [← map_asIdeal_eq_maximalIdeal, Ideal.map_map, hsq, ← Ideal.map_map]
  have h0 : (maximalIdeal (v.adicCompletionIntegers ℚ)).map
      (algebraMap (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)) ≠ ⊥ := by
    rw [hmap]
    intro h
    have := HeightOneSpectrum.multiplicity_map_adicCompletionIntegers (K := L) w _ hne
    rw [h, ← Ideal.zero_eq_bot, multiplicity_zero_right,
      ← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal w.asIdeal hne] at this
    exact (Ideal.ramificationIdx_pos (𝓞 ℚ) w.asIdeal).ne this
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ h0, hmap,
    HeightOneSpectrum.multiplicity_map_adicCompletionIntegers (K := L) w _ hne,
    ← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal w.asIdeal hne]

/-- **T21, global (`GlueConductor.SerreDifferentBound`), from t-different's local bound.** -/
theorem serreDifferentBound_of_local : GlueConductor.SerreDifferentBound := by
  intro L _ _ p hp P _ hPl
  have hP0 : P ≠ ⊥ := by
    intro h
    have := hPl.over
    rw [h, Ideal.under_bot] at this
    have h2 := Ideal.span_singleton_eq_bot.mp this
    simp [hp.ne_zero] at h2
  set w := toHeightOneSpectrum P hP0 with hw
  set v : HeightOneSpectrum (𝓞 ℚ) := w.under (𝓞 ℚ) with hv
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hwP : w.asIdeal = P := rfl
  have hD := PkgI6.differentBound (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)
  rw [ramificationIdx_maximalIdeal_adicCompletionIntegers v w, hwP, ← ramificationIdx_int_eq] at hD
  set e := P.ramificationIdx ℤ with he
  set mB := maximalIdeal (w.adicCompletionIntegers L) with hmB
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos ℤ P).ne'
  have hmBtop : mB ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have hprime : Prime mB :=
    Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field _) inferInstance
  -- the ideal `(e)` of `𝒪_w` is the extension of the ideal `(e)` of `𝓞 L`
  have hspan : Ideal.span {((e : ℕ) : w.adicCompletionIntegers L)} =
      (Ideal.span {((e : ℕ) : 𝓞 L)}).map (algebraMap (𝓞 L) (w.adicCompletionIntegers L)) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hspan0 : Ideal.span {((e : ℕ) : 𝓞 L)} ≠ ⊥ := by simp [he0]
  have h3 : multiplicity mB (Ideal.span {((e : ℕ) : w.adicCompletionIntegers L)}) =
      multiplicity P (Ideal.span {((e : ℕ) : 𝓞 L)}) := by
    rw [hspan, hmB, HeightOneSpectrum.multiplicity_map_adicCompletionIntegers (K := L) w _ hspan0]
    rfl
  have hspanB0 : Ideal.span {((e : ℕ) : w.adicCompletionIntegers L)} ≠ ⊥ := by
    simp [he0]
  have hmB0 : mB ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hFD : FiniteMultiplicity mB
      (differentIdeal (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)) :=
    Ideal.finiteMultiplicity hmBtop differentIdeal_ne_bot
  have hFs : FiniteMultiplicity mB (Ideal.span {((e : ℕ) : w.adicCompletionIntegers L)}) :=
    Ideal.finiteMultiplicity hmBtop hspanB0
  have hFR : FiniteMultiplicity mB
      (mB ^ (e - 1) * Ideal.span {((e : ℕ) : w.adicCompletionIntegers L)}) :=
    Ideal.finiteMultiplicity hmBtop (mul_ne_zero (pow_ne_zero _ hmB0) hspanB0)
  have h1 : multiplicity mB
      (differentIdeal (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)) ≤
      multiplicity mB (mB ^ (e - 1) * Ideal.span {((e : ℕ) : w.adicCompletionIntegers L)}) := by
    have := emultiplicity_le_emultiplicity_of_dvd_right (a := mB) hD
    rw [hFD.emultiplicity_eq_multiplicity, hFR.emultiplicity_eq_multiplicity] at this
    exact_mod_cast this
  have h2 : multiplicity mB (mB ^ (e - 1) * Ideal.span {((e : ℕ) : w.adicCompletionIntegers L)}) =
      (e - 1) + multiplicity mB (Ideal.span {((e : ℕ) : w.adicCompletionIntegers L)}) := by
    have := emultiplicity_mul hprime (a := mB ^ (e - 1))
      (b := Ideal.span {((e : ℕ) : w.adicCompletionIntegers L)})
    rw [emultiplicity_pow_self_of_prime hprime, hFR.emultiplicity_eq_multiplicity,
      hFs.emultiplicity_eq_multiplicity] at this
    exact_mod_cast this
  have h4 : multiplicity mB
      (differentIdeal (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)) =
      multiplicity P (differentIdeal ℤ (𝓞 L)) := by
    rw [hmB, HeightOneSpectrum.multiplicity_differentIdeal_adicCompletionIntegers_eq_multiplicity_asIdeal
      v w, hwP, differentIdeal_int_eq_differentIdeal_ringOfIntegers_rat]
  have hS := multiplicity_span_ramificationIdx_le p hp P hP0
  have hF : FiniteMultiplicity P (differentIdeal ℤ (𝓞 L)) :=
    Ideal.finiteMultiplicity (Ideal.IsPrime.ne_top ‹_›) differentIdeal_ne_bot
  apply hF.not_pow_dvd_of_multiplicity_lt
  rw [← he] at hS
  omega

/-- **`GlueConductor.D1_genuine` with both leaves discharged, without Tau Ceti's `Wild.lean`.** -/
theorem D1_genuine_closed_of_local (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ)
    [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (a : ℕ) (ha : 1 ≤ a) (hea : P.ramificationIdx ℤ ≤ a.factorial)
    (b : ℕ) (hb : GlueConductor.ramGroup L P b ≠ ⊥) :
    GlueConductor.phi (GlueConductor.ramCard L P) b ≤ 4 * a ^ 2 :=
  GlueConductor.D1_genuine hilbertDifferentFormula serreDifferentBound_of_local L p P a ha hea b hb

end ZInQ.Contrib.Different
