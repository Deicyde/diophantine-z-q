import ZInQKernel.Contrib.CloudB3E1RingClass.KummerUnits
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Restriction

/-!
# The Kummer relations are divisible at the active primes (`KR_val`)

Manuscript `diophantine_zq.tex`, tex 3551–3557: "if `∏_a α_a^{b_a}` is a `2^n`-th power in `F_∞`,
its root lies in a finite cyclotomic layer. At every nonzero-weight prime that layer is unramified
over `K`, since the prime is odd. Consequently `2^n` divides `∑_a b_a m_j^{(a)}` at each such prime."

For `K = ℚ(s) ⊂ ℚ̄` and `k ≥ 0`:
* `Lk s k = K(μ_{2^k}) ⊂ ℚ̄` is a cyclotomic extension of `K` and a number field;
* `F_∞ = ⋃_k Lk s k` (`exists_mem_Lk`);
* at an odd prime `𝔭` of `K` (`2 ∉ 𝔭`) there is a prime `w` of `Lk s k` over `𝔭` with ramification
  index one (`exists_unramified_prime`, from Tau Ceti's `isUnramifiedAt_of_natCast_notMem`), so
  `w`'s valuation restricts to `𝔭`'s on `K` (`valuation_liesOver`).

**`krVal_genuine`** (PROVED): if the active primes `𝔭_j` of `K` are odd and
`v_{𝔭_j}(α_a) = m_j^{(a)}`, then `2^n ∣ ∑_a b_a m_j^{(a)}` for every Kummer relation `b`. This is the
interface field `KR_val` (ELLIOT/GLUE in RC4) for the Kummer data over `K`.

**`hαunit_of_support`** (PROVED): `frob_kummer`'s `hαunit` from the radicands having valuation one
at every prime of `K` over a prime outside `Sexc` (the Frobenius place restricts to such a prime,
with compatible valuation rings).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)

variable (s : Qbar)

/-- `K = ℚ(s)` is a number field. Kind: PROVED. -/
instance quadField_numberField : NumberField (quadField s) := by
  have : FiniteDimensional ℚ (quadField s) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ) s)
  exact ⟨⟩

/-- **The cyclotomic layer** `K(μ_{2^k}) ⊂ ℚ̄`. Kind: definition. -/
def Lk (k : ℕ) : IntermediateField (quadField s) Qbar :=
  IntermediateField.adjoin (quadField s) {b : Qbar | ∃ n ∈ ({2 ^ k} : Set ℕ), n ≠ 0 ∧ b ^ n = 1}

/-- `ℚ̄` has primitive roots of unity of every order. Kind: PROVED. -/
theorem exists_primitive (n : ℕ) (hn : n ≠ 0) : ∃ r : Qbar, IsPrimitiveRoot r n := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Qbar)
    (by rw [Polynomial.degree_cyclotomic]
        exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne')
  exact ⟨r, (Polynomial.isRoot_cyclotomic_iff).mp hr⟩

instance (k : ℕ) : IsCyclotomicExtension {2 ^ k} (quadField s) (Lk s k) :=
  IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot _ _ _ (fun n _ hn =>
    exists_primitive n hn)

instance (k : ℕ) : NumberField (Lk s k) :=
  IsCyclotomicExtension.numberField {2 ^ k} (quadField s) _

instance (k : ℕ) : FiniteDimensional (quadField s) (Lk s k) :=
  IsCyclotomicExtension.finiteDimensional {2 ^ k} _ _

/-! ### `F_∞` is the union of the layers -/

theorem Lk_mono {k k' : ℕ} (h : k ≤ k') : Lk s k ≤ Lk s k' := by
  refine IntermediateField.adjoin.mono _ _ _ ?_
  rintro b ⟨n, hn, hn0, hb⟩
  rw [Set.mem_singleton_iff] at hn
  subst hn
  refine ⟨2 ^ k', rfl, pow_ne_zero _ two_ne_zero, ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, pow_mul, hb, one_pow]

/-- **Every element of `F_∞` lies in a layer `K(μ_{2^k})`.** Kind: PROVED. -/
theorem exists_mem_Lk {y : Qbar} (hy : y ∈ Finf s) : ∃ k, y ∈ Lk s k := by
  let M : ℕ → IntermediateField ℚ Qbar := fun k => (Lk s k).restrictScalars ℚ
  have hdir : Directed (· ≤ ·) M := fun a b =>
    ⟨max a b, Lk_mono s (le_max_left a b), Lk_mono s (le_max_right a b)⟩
  have hle : Finf s ≤ ⨆ k, M k := by
    rw [Finf, IntermediateField.adjoin_le_iff]
    rintro x (hx | ⟨k, hk⟩)
    · rw [Set.mem_singleton_iff.mp hx]
      refine (le_iSup M 0) ?_
      change s ∈ Lk s 0
      exact (Lk s 0).algebraMap_mem ⟨s, IntermediateField.mem_adjoin_simple_self ℚ s⟩
    · refine (le_iSup M k) ?_
      change x ∈ Lk s k
      exact IntermediateField.subset_adjoin _ _ ⟨2 ^ k, rfl, pow_ne_zero _ two_ne_zero, hk⟩
  have hy' : y ∈ ((⨆ k, M k : IntermediateField ℚ Qbar) : Set Qbar) := hle hy
  rw [IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion] at hy'
  exact hy'

/-! ### An unramified prime of the layer over an odd prime of `K` -/

/-- **An unramified prime over an odd prime** (tex 3555–3556): for a prime `𝔭` of `K` not over
`2`, some prime of `K(μ_{2^k})` lies over `𝔭` with ramification index one. Kind: PROVED. -/
theorem exists_unramified_prime (k : ℕ) (𝔭 : HeightOneSpectrum (𝓞 (quadField s)))
    (h2 : (2 : 𝓞 (quadField s)) ∉ 𝔭.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 (Lk s k)), w.asIdeal.LiesOver 𝔭.asIdeal ∧
      w.asIdeal.ramificationIdx (𝓞 (quadField s)) = 1 := by
  obtain ⟨Q, hQ, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := 𝓞 (Lk s k)) 𝔭.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  refine ⟨⟨Q, hQ.isPrime, hQ0⟩, hQl, ?_⟩
  have hm : ((2 ^ k : ℕ) : 𝓞 (quadField s)) ∉ 𝔭.asIdeal := by
    push_cast
    exact fun h => h2 (𝔭.isPrime.mem_of_pow_mem k h)
  have : Algebra.IsUnramifiedAt (𝓞 (quadField s)) Q :=
    IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem (Lk s k) (2 ^ k) hm Q
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

/-! ### `KR_val` -/

theorem exp_sum' {ι : Type*} (S : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ S, WithZero.exp (f i) = WithZero.exp (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, WithZero.exp_add]

/-- **`KR_val` for the Kummer data over `K = ℚ(s)`** (tex 3551–3557): if the active primes `𝔭_j`
of `K` are odd and `v_{𝔭_j}(α_a) = m_j^{(a)}` (in Mathlib's normalization
`v(α) = exp(−m)`), then `2^n ∣ ∑_a b_a m_j^{(a)}` for every Kummer relation `b`. Kind: PROVED. -/
theorem krVal_genuine {n t S : ℕ} (kd : KummerData s n t) (act : Fin S → Prop)
    (m : Fin t → Fin S → ℤ) (𝔭 : Fin S → HeightOneSpectrum (𝓞 (quadField s)))
    (h2 : ∀ j, act j → (2 : 𝓞 (quadField s)) ∉ (𝔭 j).asIdeal)
    (hval : ∀ j, act j → ∀ a,
      (𝔭 j).valuation (quadField s) ⟨kd.α a, kd.α_mem a⟩ = WithZero.exp (-(m a j))) :
    ∀ b ∈ kd.KR, ∀ j, act j → (2 : ℤ) ^ n ∣ ∑ a, b a * m a j := by
  intro b hb j hj
  obtain ⟨y, hy, hyb⟩ := hb
  obtain ⟨k, hyk⟩ := exists_mem_Lk s hy
  obtain ⟨w, hl, he⟩ := exists_unramified_prime s k (𝔭 j) (h2 j hj)
  have : w.asIdeal.LiesOver (𝔭 j).asIdeal := hl
  let αK : Fin t → quadField s := fun a => ⟨kd.α a, kd.α_mem a⟩
  have hαK0 : ∀ a, αK a ≠ 0 := fun a h => kd.α_ne a (congrArg Subtype.val h)
  let P : quadField s := ∏ a, αK a ^ b a
  let yL : Lk s k := ⟨y, hyk⟩
  have hPy : algebraMap (quadField s) (Lk s k) P = yL ^ 2 ^ n := by
    apply Subtype.ext
    change ((P : quadField s) : Qbar) = ((yL ^ 2 ^ n : Lk s k) : Qbar)
    rw [SubmonoidClass.coe_pow]
    change _ = y ^ 2 ^ n
    rw [hyb]
    simp only [P, αK]
    push_cast
    rfl
  have hprod0 : (∏ a, kd.α a ^ b a) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => zpow_ne_zero _ (kd.α_ne a)
  have hy0 : yL ≠ 0 := by
    intro h
    have : y = 0 := congrArg Subtype.val h
    rw [this, zero_pow (pow_ne_zero _ two_ne_zero)] at hyb
    exact hprod0 hyb.symm
  have hlies := HeightOneSpectrum.valuation_liesOver (Lk s k) (𝔭 j) w P
  rw [he, pow_one, hPy, map_pow] at hlies
  have hvP : (𝔭 j).valuation (quadField s) P = WithZero.exp (-∑ a, b a * m a j) := by
    simp only [P, map_prod, map_zpow₀]
    rw [show (fun a => (𝔭 j).valuation (quadField s) (αK a) ^ b a) =
        fun a => WithZero.exp (b a • -(m a j)) from
      funext fun a => by rw [WithZero.exp_zsmul]; exact congrArg (· ^ b a) (hval j hj a),
      exp_sum']
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul]; ring
  have hw0 : w.valuation (Lk s k) yL ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact hy0
  rw [hvP, ← WithZero.exp_log hw0, ← WithZero.exp_nsmul, WithZero.exp_inj] at hlies
  refine ⟨-WithZero.log (w.valuation (Lk s k) yL), ?_⟩
  rw [nsmul_eq_mul] at hlies
  push_cast at hlies
  linarith

/-! ### `hαunit` from the prime supports of the radicands -/

open ZInQ.Manuscript.RC.WitnessSpec in
/-- **`hαunit` from the prime supports** (tex 3536–3540): if every radicand `α_a ∈ K` has
valuation one at every prime of `K` over a prime outside `Sexc` (`α_a = β_a/β̄_a` is supported on the
chosen primes, which lie over `Sexc`), then the radicands are units at every Frobenius place over a
good prime. The Frobenius place restricts to a prime of `K` over `r` with compatible valuation rings
(`valuation_le_one_restrict`). Kind: PROVED. -/
theorem hαunit_of_support {E : WeierstrassCurve ℚ} {n t : ℕ} (kd : KummerData s n t)
    (Sexc : Finset ℕ)
    (hsupp : ∀ a (𝔯 : HeightOneSpectrum (𝓞 (quadField s))) (q : ℕ), q.Prime → q ∉ Sexc →
      ((q : ℤ) : 𝓞 (quadField s)) ∈ 𝔯.asIdeal →
        𝔯.valuation (quadField s) ⟨kd.α a, kd.α_mem a⟩ = 1) :
    ∀ (r : ℕ) [Fact r.Prime] (v : kummerPlaces r), GoodPrime E s Sexc r →
      ∀ a, v.2.valuationRing.valuation (kd.α a) = 1 := by
  intro r _ v hgood a
  let e : quadField s →ₐ[ℚ] Qbar := (quadField s).val
  let 𝔯 := v.2.restrictHeightOne e
  have hr𝔯 : ((r : ℤ) : 𝓞 (quadField s)) ∈ 𝔯.asIdeal := by
    have h := v.2.restrictPrime_under e
    have hm : (r : ℤ) ∈ (v.2.restrictPrime e).under ℤ := by
      rw [h]; exact Ideal.mem_span_singleton_self _
    change algebraMap ℤ (𝓞 (quadField s)) (r : ℤ) ∈ v.2.restrictPrime e at hm
    have h𝔯 : 𝔯.asIdeal = v.2.restrictPrime e := rfl
    rw [h𝔯]
    simpa using hm
  have h1 := hsupp a 𝔯 r hgood.1 hgood.2.2.2.1 hr𝔯
  set x : quadField s := ⟨kd.α a, kd.α_mem a⟩
  have hx0 : x ≠ 0 := fun h => kd.α_ne a (congrArg Subtype.val h)
  have le1 : v.2.valuationRing.valuation (e x) ≤ 1 :=
    (v.2.valuation_le_one_restrict e x).mpr h1.le
  have le2 : v.2.valuationRing.valuation (e x⁻¹) ≤ 1 :=
    (v.2.valuation_le_one_restrict e x⁻¹).mpr (by rw [map_inv₀, h1, inv_one])
  change v.2.valuationRing.valuation (e x) = 1
  rw [map_inv₀, map_inv₀] at le2
  have hV0 : v.2.valuationRing.valuation (e x) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact (map_ne_zero e).mpr hx0
  rw [inv_le_one₀ (zero_lt_iff.mpr hV0)] at le2
  exact le_antisymm le1 le2

end ZInQ.Contrib.CloudB3E1RingClass
