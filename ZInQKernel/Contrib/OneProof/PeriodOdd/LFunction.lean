import ZInQKernel.Contrib.HeckeAll.LocalCd
import ZInQKernel.Contrib.PSide.APZero

/-!
# period-odd: the 2-isogenous curve `E'_d : y² = x³ + 4d² x` has the L-function of `C_d`

Task period-odd (2026-11-16). Report `docs/research/period-odd.md`.

For odd squarefree `d`, the curve `E'_d : y² = x³ + 4d² x` (the image of `C_d : y² = x³ − d² x`
under the 2-isogeny with kernel `{O, (0, 0)}`) has the same Mathlib L-function as `C_d`:

* at `p ∤ 2d` both have good reduction and the same number of points over `𝔽_p`
  (`card_solutions_isog`: `Σ_x χ(x³ + a x) = Σ_X χ(X³ − 4a X)` for `a ≠ 0`, by `X = x + a/x`);
* at `p ∣ 2d` both models are minimal with additive reduction (at `2`, `v₂(Δ(E'_d)) = 12`, and
  minimality follows from `c₄` as in `HeckeAll/LocalCd.lean`).

Main result: `LFunction_ePrime_eq` (`(ePrime d).LFunction = (shortCurve (-(d : ℚ) ^ 2)).LFunction`).
-/

namespace ZInQ.PeriodOdd

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ZInQ.Literature

/-! ## §1. The character sum identity of the 2-isogeny -/

section CharSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The roots of `x² − X x + a` correspond to the square roots of `X² − 4a` (`u = 2x − X`). -/
theorem card_roots_quad (hF : ringChar F ≠ 2) (a X : F) :
    ((Finset.univ.filter fun x : F => x ^ 2 - X * x + a = 0).card : ℤ) =
      quadraticChar F (X ^ 2 - 4 * a) + 1 := by
  rw [← quadraticChar_card_sqrts hF (X ^ 2 - 4 * a)]
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  congr 1
  refine Finset.card_bij' (fun x _ => 2 * x - X) (fun u _ => (u + X) / 2) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq]
    linear_combination 4 * hx
  · intro u hu
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    field_simp
    linear_combination hu
  · intro x _; field_simp; ring
  · intro u _; field_simp; ring

/-- **The 2-isogeny character sum.** For `a ≠ 0` in a finite field of odd characteristic,
`Σ_x χ(x³ + a x) = Σ_X χ(X³ − 4a X)`: with `X = x + a/x`, `χ(x³ + ax) = χ(X)` for `x ≠ 0`, and
each `X` has `1 + χ(X² − 4a)` preimages. -/
theorem charSum_isog (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    ∑ x, quadraticChar F (x ^ 3 + a * x) = ∑ X, quadraticChar F (X ^ 3 - 4 * a * X) := by
  have s1 : ∀ x : F, quadraticChar F (x ^ 3 + a * x) = quadraticChar F (x + a / x) := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have : x ^ 3 + a * x = x ^ 2 * (x + a / x) := by field_simp
      rw [this, map_mul, quadraticChar_sq_one' hx, one_mul]
  simp_rw [s1]
  rw [← Finset.sum_fiberwise Finset.univ (fun x : F => x + a / x)
    (fun x => quadraticChar F (x + a / x))]
  have s2 : ∀ X : F, ∑ x ∈ Finset.univ.filter (fun x : F => x + a / x = X),
      quadraticChar F (x + a / x) = quadraticChar F X * (quadraticChar F (X ^ 2 - 4 * a) + 1) := by
    intro X
    rw [Finset.sum_congr rfl (g := fun _ => quadraticChar F X) (fun x hx => by
      simp only [Finset.mem_filter] at hx; rw [hx.2]), Finset.sum_const, nsmul_eq_mul, mul_comm]
    by_cases hX : X = 0
    · simp [hX]
    congr 1
    rw [← card_roots_quad hF a X]
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hx : x = 0
    · subst hx
      simp only [div_zero, add_zero]
      constructor
      · intro h; exact absurd h.symm hX
      · intro h; simp at h; exact absurd h ha
    · constructor
      · intro h; rw [← h]; field_simp; ring
      · intro h
        field_simp
        linear_combination h
  simp_rw [s2, mul_add, mul_one, Finset.sum_add_distrib, quadraticChar_sum_zero hF, add_zero]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [← map_mul]; congr 1; ring

/-- **Point counts of 2-isogenous short curves.** For `a ≠ 0` (odd characteristic),
`#{y² = x³ + a x} = #{y² = x³ − 4a x}`. -/
theorem card_solutions_isog (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1} =
      Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 - 4 * a * xy.1} := by
  have h1 := ZInQ.Contrib.PSide.card_solutions_eq hF (fun x => x ^ 3 + a * x)
  have h2 := ZInQ.Contrib.PSide.card_solutions_eq hF (fun x => x ^ 3 - 4 * a * x)
  have := charSum_isog hF ha
  have h : (Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1} : ℤ) =
      Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 - 4 * a * xy.1} := by
    rw [h1, h2, this]
  exact_mod_cast h

end CharSum

/-! ## §2. The model `y² = x³ + (2d)² x` -/

section Model

/-- The integral model `y² = x³ + (2d)² x` over any commutative ring. -/
def eModel (S : Type*) [CommRing S] (d : ℕ) : WeierstrassCurve S where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := ((2 * d : ℕ) : S) ^ 2
  a₆ := 0

variable {S : Type*} [CommRing S] (d : ℕ)

theorem eModel_Δ : (eModel S d).Δ = -((4 * d : ℕ) : S) ^ 6 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, eModel]
  push_cast; ring

theorem eModel_c₄ : (eModel S d).c₄ = -((192 * d ^ 2 : ℕ) : S) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, eModel]
  push_cast; ring

theorem eModel_map {T : Type*} [CommRing T] (f : S →+* T) : (eModel S d).map f = eModel T d := by
  ext <;> simp [eModel, map_ofNat]

/-- **The curve `E'_d : y² = x³ + 4d² x`**, 2-isogenous to `C_d : y² = x³ − d² x`. -/
def ePrime (d : ℕ) : WeierstrassCurve ℚ := shortCurve (4 * (d : ℚ) ^ 2)

theorem eModel_eq_shortCurve (F : Type*) [Field F] :
    eModel F d = shortCurve (4 * (d : F) ^ 2) := by
  ext <;> simp [eModel, shortCurve]; ring

theorem eModel_eq_ePrime : eModel ℚ d = ePrime d := eModel_eq_shortCurve d ℚ

end Model

/-! ## §3. Local factors -/

section Completion

open Rat.HeightOneSpectrum ZInQ.Contrib.HeckeAll

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

local notation "Rv" => v.adicCompletionIntegers ℚ

/-- `E'_d` over the completion `ℚ_v`. -/
noncomputable abbrev eLocal (d : ℕ) : WeierstrassCurve (v.adicCompletion ℚ) :=
  (ePrime d).baseChange (v.adicCompletion ℚ)

theorem eLocal_eq (d : ℕ) : eLocal v d = eModel (v.adicCompletion ℚ) d := by
  rw [eLocal, ← eModel_eq_ePrime]; exact eModel_map d _

theorem eModel_baseChange (d : ℕ) :
    (eModel Rv d)⁄(v.adicCompletion ℚ) = eLocal v d := by
  rw [eLocal_eq]; exact eModel_map d _

theorem eLocal_Δ_eq (d : ℕ) :
    (eLocal v d).Δ = algebraMap Rv (v.adicCompletion ℚ) (-((4 * d : ℕ) : Rv) ^ 6) := by
  rw [← eModel_baseChange, baseChange, map_Δ, eModel_Δ]

theorem eLocal_c₄_eq (d : ℕ) :
    (eLocal v d).c₄ = algebraMap Rv (v.adicCompletion ℚ) (-((192 * d ^ 2 : ℕ) : Rv)) := by
  rw [← eModel_baseChange, baseChange, map_c₄, eModel_c₄]

theorem eLocal_Δ_ne_zero {d : ℕ} (hd : d ≠ 0) : (eLocal v d).Δ ≠ 0 := by
  rw [eLocal_eq, eModel_Δ, ← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
  refine neg_ne_zero.mpr (pow_ne_zero _ ((map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (by omega))))

/-- **Minimality of `y² = x³ + 4d² x` at `2`** (odd `d`): `v₂(c₄) = 6`. -/
theorem isMinimal_eLocal_two {d : ℕ} (hv : natGenerator v = 2) (hd : Odd d) :
    IsMinimal Rv (eLocal v d) := by
  rw [← eModel_baseChange]
  apply isMinimal_baseChange_of_c₄
  intro r hr W' heq
  have hm := mem_maximalIdeal_iff_dvd v
  rw [hv] at hm
  have h3 : ((3 * d ^ 2 : ℕ) : Rv) ∉ IsLocalRing.maximalIdeal Rv := by
    rw [natCast_mem_maximalIdeal_iff, hv]
    intro h
    have : Odd (3 * d ^ 2) := (by decide : Odd 3).mul (hd.pow)
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h)
  have h16 : (16 : Rv) ≠ 0 := by
    have : (16 : Rv) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ (two_ne_zero_Rv v)
  have h4 : (4 : Rv) ≠ 0 := by
    have : (4 : Rv) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero _ (two_ne_zero_Rv v)
  obtain ⟨s, rfl⟩ := (hm r).mp hr
  rw [eModel_c₄] at heq
  push_cast at heq
  -- `12 d² = s⁴ (−c₄')`
  have h12 : (12 : Rv) * (d : Rv) ^ 2 = s ^ 4 * (-W'.c₄) := by
    apply mul_left_cancel₀ h16
    linear_combination -heq
  apply h3
  rcases c₄_two_adic v hv W' with ⟨X, hX⟩ | hc
  · rw [hX] at h12
    have : ((3 * d ^ 2 : ℕ) : Rv) = 2 * (2 * s ^ 4 * (-X)) := by
      apply mul_left_cancel₀ h4
      push_cast
      linear_combination h12
    exact (hm _).mpr ⟨_, this⟩
  · have hs : s ∈ IsLocalRing.maximalIdeal Rv := by
      have hmem : s ^ 4 * (-W'.c₄) ∈ IsLocalRing.maximalIdeal Rv := by
        rw [← h12]
        exact (hm _).mpr ⟨6 * (d : Rv) ^ 2, by push_cast; ring⟩
      rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h | h
      · exact Ideal.IsPrime.mem_of_pow_mem inferInstance 4 h
      · exact absurd (by simpa using (IsLocalRing.maximalIdeal Rv).neg_mem_iff.mp h) hc
    obtain ⟨s', rfl⟩ := (hm s).mp hs
    have : ((3 * d ^ 2 : ℕ) : Rv) = 2 * (2 * s' ^ 4 * (-W'.c₄)) := by
      apply mul_left_cancel₀ h4
      push_cast
      linear_combination h12
    exact (hm _).mpr ⟨_, this⟩

/-- **The model `y² = x³ + 4d² x` is minimal at every place**, for odd squarefree `d`. -/
theorem isMinimal_eLocal {d : ℕ} (hd : Odd d) (hsq : Squarefree d) : IsMinimal Rv (eLocal v d) := by
  by_cases hv : natGenerator v = 2
  · exact isMinimal_eLocal_two v hv hd
  · rw [← eModel_baseChange]
    apply isMinimal_baseChange_of_notMem
    rw [eModel_Δ, neg_mem_iff, ← Nat.cast_pow, ← Int.cast_natCast,
      intCast_mem_maximalIdeal_pow_iff]
    intro h
    have hp := prime_natGenerator v
    have h' : (natGenerator v ^ 2) ^ 6 ∣ (4 * d) ^ 6 := by
      rw [← pow_mul]; exact_mod_cast h
    rw [Nat.pow_dvd_pow_iff (by norm_num)] at h'
    have hcop : Nat.Coprime (natGenerator v ^ 2) 4 := by
      have : Nat.Coprime (natGenerator v) 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hv
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4]; exact Nat.Coprime.pow 2 2 this
    have := hsq (natGenerator v) (by rw [← pow_two]; exact hcop.dvd_of_dvd_mul_left h')
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)

/-- Good reduction at `v ∤ 2d`. -/
theorem hasGoodReduction_eLocal {d : ℕ} (hp : ¬ natGenerator v ∣ 2 * d) :
    HasGoodReduction Rv (eLocal v d) := by
  have hm4 : ((4 * d : ℕ) : Rv) ∉ IsLocalRing.maximalIdeal Rv := by
    rw [natCast_mem_maximalIdeal_iff]
    intro h
    exact hp ((Nat.Coprime.dvd_of_dvd_mul_left
      (by
        rcases (Nat.coprime_or_dvd_of_prime (prime_natGenerator v) 2) with h2 | h2
        · exact h2
        · exact absurd (h2.trans (dvd_mul_right 2 d)) hp) (show natGenerator v ∣ 2 * (2 * d) by
          rw [← mul_assoc]; exact h)))
  have hm : -((4 * d : ℕ) : Rv) ^ 6 ∉ IsLocalRing.maximalIdeal Rv := fun h =>
    hm4 (Ideal.IsPrime.mem_of_pow_mem inferInstance 6
      ((IsLocalRing.maximalIdeal Rv).neg_mem_iff.mp h))
  have hmin : IsMinimal Rv (eLocal v d) := by
    rw [← eModel_baseChange]
    apply isMinimal_baseChange_of_notMem
    rw [eModel_Δ]
    exact fun h => hm (Ideal.pow_le_self (by norm_num) h)
  refine (hasGoodReduction_iff _ _).mpr ⟨hmin, ?_⟩
  rw [eLocal_Δ_eq, valuation_of_algebraMap, intValuation_eq_one_iff]
  exact hm

/-- Additive reduction at `v ∣ 2d`. -/
theorem hasAdditiveReduction_eLocal {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (hp : natGenerator v ∣ 2 * d) : HasAdditiveReduction Rv (eLocal v d) := by
  have hm : ((4 * d : ℕ) : Rv) ∈ IsLocalRing.maximalIdeal Rv :=
    (natCast_mem_maximalIdeal_iff v _).mpr (hp.trans ⟨2, by ring⟩)
  refine (hasAdditiveReduction_iff _ _).mpr ⟨isMinimal_eLocal v hd hsq, ?_, ?_⟩
  · rw [eLocal_Δ_eq, valuation_of_algebraMap, intValuation_lt_one_iff_mem]
    exact (IsLocalRing.maximalIdeal Rv).neg_mem_iff.mpr
      (Ideal.pow_mem_of_mem _ hm 6 (by norm_num))
  · rw [eLocal_c₄_eq, valuation_of_algebraMap, intValuation_lt_one_iff_mem]
    exact (IsLocalRing.maximalIdeal Rv).neg_mem_iff.mpr
      ((natCast_mem_maximalIdeal_iff v _).mpr (hp.trans ⟨96 * d, by ring⟩))

theorem reduction_eLocal (d : ℕ) [IsMinimal Rv (eLocal v d)] :
    (eLocal v d).reduction Rv = eModel (IsLocalRing.ResidueField Rv) d := by
  have hI : integralModel Rv (eLocal v d) = eModel Rv d := by
    apply WeierstrassCurve.map_injective (IsFractionRing.injective _ (v.adicCompletion ℚ))
    change (integralModel _ (eLocal v d))⁄(v.adicCompletion ℚ) = (eModel _ d)⁄_
    rw [baseChange_integralModel_eq, eModel_baseChange]
  rw [reduction, hI, eModel_map]

/-- `#E'_d(𝔽_p) = #C_d(𝔽_p)` for `p ∤ 2d`. -/
theorem natCard_point_ePrime_zmod {d : ℕ} (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 2 * d) :
    Nat.card (shortCurve (4 * (d : ZMod p) ^ 2)).toAffine.Point =
      Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp (this.trans (dvd_mul_right 2 d))
  have hd0 : (d : ZMod p) ≠ 0 := by
    intro h
    exact hp (((ZMod.natCast_eq_zero_iff d p).mp h).trans (dvd_mul_left d 2))
  have : NeZero (2 : ZMod p) := ⟨h2⟩
  have h4 : (4 * (d : ZMod p) ^ 2) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) (pow_ne_zero 2 hd0)
  have hE2 := shortCurve_isElliptic (F := ZMod p) h4
  have hp2 : p ≠ 2 := fun h => hp (h ▸ dvd_mul_right 2 d)
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have key := card_solutions_isog hF (a := -(d : ZMod p) ^ 2) (neg_ne_zero.mpr (pow_ne_zero 2 hd0))
  rw [natCard_point_shortCurve_zmod p hp, Nat.card_congr (pointEquivOption _), Finite.card_option]
  congr 1
  calc Nat.card {xy : ZMod p × ZMod p //
        (shortCurve (4 * (d : ZMod p) ^ 2)).toAffine.Equation xy.1 xy.2}
      = Nat.card {xy : ZMod p × ZMod p //
          xy.2 ^ 2 = xy.1 ^ 3 - 4 * (-(d : ZMod p) ^ 2) * xy.1} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun xy => by
          rw [shortCurve_equation_iff]; ring_nf)
    _ = Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + (-(d : ZMod p) ^ 2) * xy.1} :=
        key.symm
    _ = Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun xy => by ring_nf)

theorem isElliptic_eModel_residue {d : ℕ} (hp : ¬ natGenerator v ∣ 2 * d) :
    (eModel (IsLocalRing.ResidueField Rv) d).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [eModel_Δ, neg_ne_zero, ← map_natCast (IsLocalRing.residue Rv), ← map_pow, Ne,
    IsLocalRing.residue_eq_zero_iff]
  intro h
  have h4 := Ideal.IsPrime.mem_of_pow_mem inferInstance 6 h
  rw [natCast_mem_maximalIdeal_iff] at h4
  rcases (Nat.coprime_or_dvd_of_prime (prime_natGenerator v) 2) with h2 | h2
  · exact hp (h2.dvd_of_dvd_mul_left (show natGenerator v ∣ 2 * (2 * d) by
      rw [← mul_assoc]; exact h4))
  · exact hp (h2.trans (dvd_mul_right 2 d))

/-- `#E'_d(𝔽_p) = #C_d(𝔽_p)` at a good place. -/
theorem natCard_point_reduction_eLocal {d : ℕ} (hp : ¬ natGenerator v ∣ 2 * d)
    [IsMinimal Rv (eLocal v d)] :
    Nat.card ((eLocal v d).reduction Rv).toAffine.Point =
      Nat.card (shortCurve (-(d : ZMod (natGenerator v)) ^ 2)).toAffine.Point := by
  rw [reduction_eLocal]
  have := isElliptic_eModel_residue v hp
  rw [← natCard_point_map_ringEquiv _ (residueEquiv v), eModel_map, eModel_eq_shortCurve]
  exact natCard_point_ePrime_zmod _ hp

/-- **The local polynomials of `E'_d` and `C_d` agree at every place** (odd squarefree `d`). -/
theorem localPolynomial_eLocal_eq {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
    (eLocal v d).localPolynomial Rv = (cdLocal v d).localPolynomial Rv := by
  by_cases hp : natGenerator v ∣ 2 * d
  · rw [localPolynomial_cdLocal_of_dvd v hd hsq hp]
    have := hasAdditiveReduction_eLocal v hd hsq hp
    exact localPolynomial_of_hasAdditiveReduction _ (eLocal_Δ_ne_zero v (by
      rintro rfl; simp at hd))
  · rw [localPolynomial_cdLocal_of_not_dvd v hp]
    have := hasGoodReduction_eLocal v hp
    rw [localPolynomial_of_hasGoodReduction, natCard_residueField,
      natCard_point_reduction_eLocal v hp]

end Completion

/-! ## §4. The L-functions -/

/-- **`L(E'_d, s) = L(C_d, s)`** (Mathlib's L-function, every coefficient), for odd squarefree `d`. -/
theorem LFunction_ePrime_eq {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
    (ePrime d).LFunction = (shortCurve (-(d : ℚ) ^ 2)).LFunction := by
  unfold LFunction
  congr 1
  funext v
  unfold localEulerFactor localPowerSeries
  change ArithmeticFunction.ofPowerSeries _ (PowerSeries.invOfUnit
      ((eLocal v d).localPolynomial _ : PowerSeries ℤ) 1) = ArithmeticFunction.ofPowerSeries _
    (PowerSeries.invOfUnit ((cdLocal v d).localPolynomial _ : PowerSeries ℤ) 1)
  rw [localPolynomial_eLocal_eq v hd hsq]

end ZInQ.PeriodOdd
