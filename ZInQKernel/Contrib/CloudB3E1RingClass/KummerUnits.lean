import ZInQKernel.Contrib.CloudB3E1RingClass.FrobKummer

/-!
# The radicands are units at good primes (`hαunit`), and the Kummer-relation valuations (`KR_val`)

Manuscript `diophantine_zq.tex`, tex 3536–3557.

**Units at good primes.** `frob_kummer_genuine` asks that the radicands `α_a = β_a/β̄_a` be units
at the places over good primes (`hαunit`). These radicands are supported on the chosen primes, which
lie over the excluded rational primes `Sexc`. `hαunit_of_sUnit` proves `hαunit` from the
corresponding `S`-unit statement: some `N`, all of whose prime factors are in `Sexc`, makes `N α_a`
and `N α_a⁻¹` algebraic integers. Its ingredients are `val_le_one_of_isIntegral` (algebraic integers
have valuation `≤ 1` at every Frobenius place) and `val_natCast_inv_le_one` (`1/N` is integral at a
place over `r ∤ N`).

**Kummer relations.** `KR_val` (ELLIOT/GLUE, tex 3551–3557) says `2^n ∣ ∑_a b_a m_j^{(a)}` for
every Kummer relation `b` and active `j`. The manuscript argues: the `2^n`-th root of
`∏ α_a^{b_a}` lies in a cyclotomic layer of `F_∞`, which is unramified at the odd prime `𝔭_j`, so its
`𝔭_j`-valuation is an integer `k`, and `∑_a b_a m_j^{(a)} = 2^n k`. `krVal_of_valuations` proves
`KR_val` from exactly that content, stated as an integer-valued valuation `ν_j` on `F_∞^×` at each
active `𝔭_j` (a homomorphism `F_∞^× → ℤ`, which exists because `F_∞/K` is unramified at `𝔭_j`) with
`ν_j(α_a) = m_j^{(a)}`.

Kinds: PROVED. The hypotheses (`S`-unit, `ν_j`) are named inputs.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open IsLocalRing
open ZInQ.Contrib.ChebFD.C10 (Zbar Qbar GQ IsFrobAt)
open ZInQ.Manuscript.RC.WitnessSpec
open ZInQ.Manuscript.RC.TateWiring

/-! ### Valuations at Frobenius places -/

variable {r : ℕ} [hr : Fact r.Prime] (v : kummerPlaces r)

/-- Algebraic integers have valuation `≤ 1` at every Frobenius place. Kind: PROVED. -/
theorem val_le_one_of_isIntegral {x : Qbar} (hx : IsIntegral ℤ x) :
    v.2.valuationRing.valuation x ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff]
  change x ∈ v.2.localRing.toSubring
  have : v.2.prime.IsPrime := v.2.isPrime
  exact LocalSubring.le_ofPrime _ _ (show x ∈ (integralClosure ℤ Qbar).toSubring from hx)

/-- `1/N` is integral at a place over `r ∤ N`. Kind: PROVED. -/
theorem val_natCast_inv_le_one {N : ℕ} (hN : ¬ r ∣ N) :
    v.2.valuationRing.valuation ((N : Qbar)⁻¹) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff]
  change (N : Qbar)⁻¹ ∈ v.2.localRing.toSubring
  have : v.2.prime.IsPrime := v.2.isPrime
  have hNp : (N : Zbar) ∉ v.2.prime := by
    intro h
    have hm : (N : ℤ) ∈ v.2.prime.under ℤ := by
      change algebraMap ℤ Zbar (N : ℤ) ∈ v.2.prime
      simpa using h
    rw [v.2.under, Ideal.mem_span_singleton] at hm
    exact hN (by exact_mod_cast hm)
  let A : Subring Qbar := (integralClosure ℤ Qbar).toSubring
  let s : v.2.prime.primeCompl := ⟨(N : Zbar), hNp⟩
  refine ⟨IsLocalization.mk' (Localization.AtPrime v.2.prime) (1 : Zbar) s, ?_⟩
  change IsLocalization.lift _ (IsLocalization.mk' (Localization.AtPrime v.2.prime) (1 : Zbar) s) = _
  rw [IsLocalization.lift_mk'_spec]
  change (1 : Qbar) = ((N : Zbar) : Qbar) * (N : Qbar)⁻¹
  have hN0 : (N : Qbar) ≠ 0 := by
    intro h0
    apply hNp
    have : (N : Zbar) = 0 := Subtype.ext (by simpa using h0)
    rw [this]; exact v.2.prime.zero_mem
  rw [show ((N : Zbar) : Qbar) = (N : Qbar) from by simp, mul_inv_cancel₀ hN0]

/-- **An `S`-unit is a unit at a place over `r ∉ S`**: if `N α` and `N α⁻¹` are algebraic
integers for some `N` prime to `r`, then `α` has valuation one. Kind: PROVED. -/
theorem val_eq_one_of_sUnit {α : Qbar} (hα0 : α ≠ 0) {N : ℕ} (hN : ¬ r ∣ N)
    (h1 : IsIntegral ℤ ((N : Qbar) * α)) (h2 : IsIntegral ℤ ((N : Qbar) * α⁻¹)) :
    v.2.valuationRing.valuation α = 1 := by
  set V := v.2.valuationRing.valuation
  have hNi := val_natCast_inv_le_one v hN
  have hN0 : (N : Qbar) ≠ 0 := by
    intro h0
    have := (Nat.cast_eq_zero (R := Qbar)).mp h0
    exact hN (this ▸ dvd_zero r)
  have e1 : V α ≤ 1 := by
    have : α = (N : Qbar)⁻¹ * ((N : Qbar) * α) := by field_simp
    rw [this, map_mul]
    exact mul_le_one' hNi (val_le_one_of_isIntegral v h1)
  have e2 : V α⁻¹ ≤ 1 := by
    have : α⁻¹ = (N : Qbar)⁻¹ * ((N : Qbar) * α⁻¹) := by field_simp
    rw [this, map_mul]
    exact mul_le_one' hNi (val_le_one_of_isIntegral v h2)
  rw [map_inv₀] at e2
  have hV0 : V α ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact hα0
  exact le_antisymm e1 (by
    have := (one_le_inv₀ (zero_lt_iff.mpr hV0)).mpr e1
    rw [inv_le_one₀ (zero_lt_iff.mpr hV0)] at e2
    exact e2)

omit hr in
/-- **`hαunit` from the `S`-unit property** (tex 3536–3540): if, for each radicand, some `N` all of
whose prime factors lie in `Sexc` makes `N α_a` and `N α_a⁻¹` algebraic integers, then the
radicands are units at every place over a good prime. Kind: PROVED. -/
theorem hαunit_of_sUnit {E : WeierstrassCurve ℚ} {s : Qbar} {n t : ℕ} (kd : KummerData s n t)
    (Sexc : Finset ℕ)
    (hS : ∀ a, ∃ N : ℕ, (∀ q, q.Prime → q ∣ N → q ∈ Sexc) ∧
      IsIntegral ℤ ((N : Qbar) * kd.α a) ∧ IsIntegral ℤ ((N : Qbar) * (kd.α a)⁻¹)) :
    ∀ (r : ℕ) [Fact r.Prime] (v : kummerPlaces r), GoodPrime E s Sexc r →
      ∀ a, v.2.valuationRing.valuation (kd.α a) = 1 := by
  intro r _ v hgood a
  obtain ⟨N, hNS, h1, h2⟩ := hS a
  have hN : ¬ r ∣ N := fun h => hgood.2.2.2.1 (hNS r hgood.1 h)
  exact val_eq_one_of_sUnit v (kd.α_ne a) hN h1 h2

/-! ### The Kummer relations -/

/-- `K = ℚ(s) ⊆ F_∞`. Kind: PROVED. -/
theorem quadField_le_Finf (s : Qbar) : quadField s ≤ Finf s := by
  rw [quadField, Finf]
  exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))

/-- **`KR_val` from integer-valued valuations at the active primes** (tex 3551–3557): if each
active `𝔭_j` carries a homomorphism `ν_j : F_∞^× → ℤ` (its normalized valuation, integer-valued
since `F_∞/K` is unramified at the odd prime `𝔭_j`) with `ν_j(α_a) = m_j^{(a)}`, then
`2^n ∣ ∑_a b_a m_j^{(a)}` for every Kummer relation `b`. Kind: PROVED. -/
theorem krVal_of_valuations {s : Qbar} {n t : ℕ} (kd : KummerData s n t) {S : ℕ}
    (act : Fin S → Prop) (m : Fin t → Fin S → ℤ)
    (ν : ∀ j, act j → (Finf s)ˣ →* Multiplicative ℤ)
    (hν : ∀ j (hj : act j) a, ν j hj (Units.mk0 ⟨kd.α a, quadField_le_Finf s (kd.α_mem a)⟩
      (fun h => kd.α_ne a (congrArg Subtype.val h))) = Multiplicative.ofAdd (m a j)) :
    ∀ b ∈ kd.KR, ∀ j, act j → (2 : ℤ) ^ n ∣ ∑ a, b a * m a j := by
  intro b hb j hj
  obtain ⟨y, hy, hyb⟩ := hb
  have hprod0 : (∏ a, kd.α a ^ b a) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => zpow_ne_zero _ (kd.α_ne a)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ two_ne_zero)] at hyb
    exact hprod0 hyb.symm
  let αu : Fin t → (Finf s)ˣ := fun a => Units.mk0 ⟨kd.α a, quadField_le_Finf s (kd.α_mem a)⟩
    (fun h => kd.α_ne a (congrArg Subtype.val h))
  let yu : (Finf s)ˣ := Units.mk0 ⟨y, hy⟩ (fun h => hy0 (congrArg Subtype.val h))
  have hu : yu ^ 2 ^ n = ∏ a, αu a ^ b a := by
    apply Units.ext
    apply Subtype.ext
    simp only [yu, αu, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_prod,
      Units.val_zpow_eq_zpow_val]
    rw [SubmonoidClass.coe_pow, hyb]
    push_cast
    rfl
  have h1 := congrArg (fun z => Multiplicative.toAdd (ν j hj z)) hu
  simp only [map_pow, map_prod, map_zpow, toAdd_pow, toAdd_prod, toAdd_zpow] at h1
  refine ⟨Multiplicative.toAdd (ν j hj yu), ?_⟩
  have h2 : ∑ a, b a * m a j = ∑ x, b x • Multiplicative.toAdd ((ν j hj) (αu x)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show ν j hj (αu a) = Multiplicative.ofAdd (m a j) from hν j hj a, toAdd_ofAdd, smul_eq_mul]
  rw [h2, ← h1, nsmul_eq_mul]
  push_cast; ring

end ZInQ.Contrib.CloudB3E1RingClass
