import ZInQKernel.RouteK.Rank.LFunctionCd
import ZInQKernel.Contrib.PoleRC.KummerF
import ZInQKernel.Hypotheses.PoleManuscript

/-!
# Lane RC3: Mathlib's `a_p` of `E_m : y² = x(x − m)(x + 3m)` at a good prime

The manuscript writes `a_p = a_p(E^{(k)})` (tex 10334, 10456) for the trace of Frobenius at a good
prime `p` of `E^{(k)} : y² = x(x − kℓ)(x + 3kℓ)`, i.e. `a_p = p + 1 − #Ẽ^{(k)}(𝔽_p)`. This file
identifies that number with the Dirichlet coefficient at `p` of Mathlib's L-function
`WeierstrassCurve.LFunction` of `ZInQ.Manuscript.curve (k * ℓ)`: take `m = kℓ` in
`LFunction_curve_apply_prime`.

Mathlib defines `LFunction` as the Euler product, over the places `v` of `ℚ`, of local factors
computed from a minimal model over the completion `ℚ_v` chosen by `Classical.choice`. The
computation follows the one for the congruent number curves
(`ZInQ.Literature.LFunction_cd_apply_prime`) and reuses its generic lemmas
(`ZInQ.Literature.isMinimal_baseChange_of_notMem`,
`ZInQ.Literature.localPolynomial_of_hasGoodReduction`, `ZInQ.Literature.residueEquiv`, ...).

## Main results

* `curveModel S m`: the integral model `y² = x³ + 2mx² − 3m²x` over a commutative ring `S`;
  `curve_intCast_eq` (over `ℚ` it is `curve m`), `curveModel_zmod_eq` (over `𝔽_p` it is
  `PoleRC.curveF (m mod p)`), `curveModel_Δ` (`Δ = 2304 m⁶ = 2⁸ · 3² · m⁶`).
* `LFunction_apply_prime_pow_eq`: for every `W` over `ℚ`, the coefficient of Mathlib's `L(W, s)` at
  `p ^ k` is the coefficient of `T ^ k` in the inverse of the local polynomial of `W` at the place
  above `p`; no other place contributes.
* At the place `v` above a prime `p ∤ 6m`: `hasGoodReduction_curveLocal` (the model is minimal with
  good reduction, since `Δ` is a `v`-adic unit), `natCard_point_reduction_curveLocal` (the
  reduction has `#Ẽ_m(𝔽_p)` points) and `localPolynomial_curveLocal` (`1 − a_p T + p T²`).
* `LFunction_curve_apply_prime`: **the coefficient of `L(E_m, s)` at a prime `p ∤ 6m` is
  `a_p = p + 1 − #Ẽ_m(𝔽_p)`**, with `Ẽ_m = PoleRC.curveF (m mod p)` (point at infinity included);
  `LFunction_curve_apply_prime_pow`: at `p ^ k` it is the coefficient of `T ^ k` in
  `1 / (1 − a_p T + p T²)`.

All results here are `PROVED`.
-/

namespace ZInQ.Manuscript.RC.KSplit

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ArithmeticFunction
  Rat.HeightOneSpectrum ZInQ.Literature

/-- The integral model `y² = x³ + 2mx² − 3m²x = x(x − m)(x + 3m)` over a commutative ring. -/
def curveModel (S : Type*) [CommRing S] (m : ℤ) : WeierstrassCurve S :=
  ⟨0, 2 * (m : S), 0, -3 * (m : S) ^ 2, 0⟩

/-- **Over `ℚ` the model is the manuscript's curve** (`PROVED`): `curve m = curveModel ℚ m`. -/
theorem curve_intCast_eq (m : ℤ) : ZInQ.Manuscript.curve (m : ℚ) = curveModel ℚ m := rfl

/-- **Over `𝔽_p` the model is `PoleRC.curveF (m mod p)`** (`PROVED`). The primality instance is
needed for `ZMod p` to be a field, which `curveF` requires. -/
theorem curveModel_zmod_eq (p : ℕ) [Fact p.Prime] (m : ℤ) :
    curveModel (ZMod p) m = ZInQ.Manuscript.PoleRC.curveF ((m : ℤ) : ZMod p) := rfl

/-- **The discriminant of the model** (`PROVED`): `Δ = 2304 m⁶ = 2⁸ · 3² · m⁶`. -/
theorem curveModel_Δ (S : Type*) [CommRing S] (m : ℤ) :
    (curveModel S m).Δ = 2304 * (m : S) ^ 6 := by
  simp only [curveModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The discriminant of the model as the image of the integer `2304 m⁶` (`PROVED`). -/
theorem curveModel_Δ_eq_intCast (S : Type*) [CommRing S] (m : ℤ) :
    (curveModel S m).Δ = ((2304 * m ^ 6 : ℤ) : S) := by
  rw [curveModel_Δ]; push_cast; ring

/-- The model is stable under ring homomorphisms (`PROVED`). -/
theorem curveModel_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (m : ℤ) :
    (curveModel S m).map f = curveModel T m := by
  ext <;> simp [curveModel, map_ofNat]

section Local

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

/-- An integer lies in the maximal ideal of `𝓞_v` iff `p = natGenerator v` divides it
(`PROVED`). -/
theorem intCast_mem_maximalIdeal_iff_dvd (n : ℤ) :
    (n : v.adicCompletionIntegers ℚ) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) ↔
      (natGenerator v : ℤ) ∣ n := by
  simpa only [pow_one] using intCast_mem_maximalIdeal_pow_iff v n 1

/-- `E_m` over the completion `ℚ_v`. -/
noncomputable abbrev curveLocal (m : ℤ) : WeierstrassCurve (v.adicCompletion ℚ) :=
  (ZInQ.Manuscript.curve (m : ℚ)).baseChange (v.adicCompletion ℚ)

/-- `E_m` over `ℚ_v` is the model over `ℚ_v` (`PROVED`). -/
theorem curveLocal_eq (m : ℤ) : curveLocal v m = curveModel (v.adicCompletion ℚ) m := by
  rw [curveLocal, curve_intCast_eq]; exact curveModel_map _ m

/-- The model over `𝓞_v` is an integral model of `E_m` over `ℚ_v` (`PROVED`). -/
theorem curveModel_baseChange (m : ℤ) :
    (curveModel (v.adicCompletionIntegers ℚ) m).baseChange (v.adicCompletion ℚ) =
      curveLocal v m := by
  rw [curveLocal_eq]; exact curveModel_map _ m

/-- **The discriminant is a `v`-adic unit at `p ∤ 6m`** (`PROVED`): `(6m)⁸ = 2304 m⁶ · 729 m²`
and the maximal ideal is prime. -/
theorem curveModel_Δ_notMem {m : ℤ} (hp : ¬ (natGenerator v : ℤ) ∣ 6 * m) :
    (curveModel (v.adicCompletionIntegers ℚ) m).Δ ∉
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) := by
  rw [curveModel_Δ_eq_intCast]
  intro h
  apply hp
  rw [← intCast_mem_maximalIdeal_iff_dvd v]
  refine Ideal.IsPrime.mem_of_pow_mem inferInstance 8 ?_
  have e : ((6 * m : ℤ) : v.adicCompletionIntegers ℚ) ^ 8 =
      ((2304 * m ^ 6 : ℤ) : v.adicCompletionIntegers ℚ) *
        ((729 * m ^ 2 : ℤ) : v.adicCompletionIntegers ℚ) := by
    push_cast; ring
  rw [e]
  exact Ideal.mul_mem_right _ _ h

/-- **The model is minimal at `p ∤ 6m`** (`PROVED`): its discriminant is not in `𝔪 ^ 12`. -/
theorem isMinimal_curveLocal {m : ℤ} (hp : ¬ (natGenerator v : ℤ) ∣ 6 * m) :
    IsMinimal (v.adicCompletionIntegers ℚ) (curveLocal v m) := by
  rw [← curveModel_baseChange]
  exact isMinimal_baseChange_of_notMem _ fun h =>
    curveModel_Δ_notMem v hp (Ideal.pow_le_self (by norm_num) h)

/-- The discriminant of `E_m` over `ℚ_v` is that of the model over `𝓞_v` (`PROVED`). -/
theorem curveLocal_Δ_eq (m : ℤ) :
    (curveLocal v m).Δ = algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      (curveModel (v.adicCompletionIntegers ℚ) m).Δ := by
  rw [← curveModel_baseChange, baseChange, map_Δ]

/-- **Good reduction at `p ∤ 6m`** (`PROVED`). -/
theorem hasGoodReduction_curveLocal {m : ℤ} (hp : ¬ (natGenerator v : ℤ) ∣ 6 * m) :
    HasGoodReduction (v.adicCompletionIntegers ℚ) (curveLocal v m) := by
  refine (hasGoodReduction_iff _ _).mpr ⟨isMinimal_curveLocal v hp, ?_⟩
  rw [curveLocal_Δ_eq, valuation_of_algebraMap, intValuation_eq_one_iff]
  exact curveModel_Δ_notMem v hp

/-- When the model is minimal, Mathlib's integral model is the model (`PROVED`). -/
theorem integralModel_curveLocal (m : ℤ)
    [IsMinimal (v.adicCompletionIntegers ℚ) (curveLocal v m)] :
    integralModel (v.adicCompletionIntegers ℚ) (curveLocal v m) =
      curveModel (v.adicCompletionIntegers ℚ) m := by
  apply WeierstrassCurve.map_injective (IsFractionRing.injective _ (v.adicCompletion ℚ))
  change (integralModel _ (curveLocal v m)).baseChange (v.adicCompletion ℚ) =
    (curveModel _ m).baseChange (v.adicCompletion ℚ)
  rw [baseChange_integralModel_eq, curveModel_baseChange]

/-- **The reduction is the model over the residue field** (`PROVED`). -/
theorem reduction_curveLocal (m : ℤ) [IsMinimal (v.adicCompletionIntegers ℚ) (curveLocal v m)] :
    (curveLocal v m).reduction (v.adicCompletionIntegers ℚ) =
      curveModel (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) m := by
  rw [reduction, integralModel_curveLocal, curveModel_map]

/-- **The reduction at `p ∤ 6m` has `#Ẽ_m(𝔽_p)` points** (`PROVED`), where
`Ẽ_m = PoleRC.curveF (m mod p)`: the residue field of `𝓞_v` is `ZMod p`. -/
theorem natCard_point_reduction_curveLocal {m : ℤ} (hp : ¬ (natGenerator v : ℤ) ∣ 6 * m)
    [IsMinimal (v.adicCompletionIntegers ℚ) (curveLocal v m)] :
    Nat.card ((curveLocal v m).reduction (v.adicCompletionIntegers ℚ)).toAffine.Point =
      Nat.card (ZInQ.Manuscript.PoleRC.curveF
        ((m : ℤ) : ZMod (natGenerator v))).toAffine.Point := by
  rw [reduction_curveLocal]
  have hE : (curveModel (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) m).IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
    rw [curveModel_Δ_eq_intCast, ← map_intCast (IsLocalRing.residue (v.adicCompletionIntegers ℚ)),
      Ne, IsLocalRing.residue_eq_zero_iff, ← curveModel_Δ_eq_intCast]
    exact curveModel_Δ_notMem v hp
  rw [← natCard_point_map_ringEquiv _ (residueEquiv v), curveModel_map, curveModel_zmod_eq]

open Polynomial in
/-- **The local polynomial of `E_m` at the place above `p ∤ 6m`** (`PROVED`): `1 − a_p T + p T²`
with `a_p = p + 1 − #Ẽ_m(𝔽_p)`, `p = natGenerator v`. -/
theorem localPolynomial_curveLocal {m : ℤ} (hp : ¬ (natGenerator v : ℤ) ∣ 6 * m) :
    (curveLocal v m).localPolynomial (v.adicCompletionIntegers ℚ) =
      1 - C ((natGenerator v : ℤ) + 1 - Nat.card (ZInQ.Manuscript.PoleRC.curveF
        ((m : ℤ) : ZMod (natGenerator v))).toAffine.Point) * X +
      C (natGenerator v : ℤ) * X ^ 2 := by
  have := hasGoodReduction_curveLocal v hp
  rw [localPolynomial_of_hasGoodReduction, natCard_residueField,
    natCard_point_reduction_curveLocal v hp]

end Local

/-- **The coefficient of Mathlib's `L(W, s)` at a prime power** (`PROVED`), for any `W` over `ℚ`:
at `p ^ k` with `p = natGenerator v` it is the coefficient of `T ^ k` in the inverse of the local
polynomial of `W` at `v`. The Euler factors at the other places vanish at every divisor of
`p ^ k` other than `1`. -/
theorem LFunction_apply_prime_pow_eq (W : WeierstrassCurve ℚ) (p k : ℕ)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (hv : natGenerator v = p) :
    W.LFunction (p ^ k) = PowerSeries.coeff k (PowerSeries.invOfUnit
      ((W.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) :
        PowerSeries ℤ) 1) := by
  classical
  subst hv
  have hp := prime_natGenerator v
  set q := fun w : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
    Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)) with hq_def
  set F := fun w : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
    (W.baseChange (w.adicCompletion ℚ)).localPowerSeries (w.adicCompletionIntegers ℚ) with hF_def
  have hF : ∀ w, PowerSeries.constantCoeff (F w) = 1 := fun w => by
    simp [F, localPowerSeries, PowerSeries.constantCoeff_invOfUnit]
  have hf1 : ∀ w, ofPowerSeries (q w) (F w) 1 = 1 := fun w => by
    rw [ofPowerSeries_apply_one, hF]
  have hvan : ∀ w, w ≠ v → ∀ m, m ∣ natGenerator v ^ k → m ≠ 1 →
      ofPowerSeries (q w) (F w) m = 0 := by
    intro w hw m hm hm1
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm
    have hqw : q w = natGenerator w := natCard_residueField w
    rw [hqw, ofPowerSeries_apply (prime_natGenerator w).one_lt, Function.extend_apply']
    · rfl
    rintro ⟨l, hl⟩
    rcases j with _ | j
    · exact hm1 (pow_zero _)
    rcases l with _ | l
    · exact (Nat.one_lt_pow (Nat.succ_ne_zero j) hp.one_lt).ne (by simpa using hl)
    · have hdvd : natGenerator w ∣ natGenerator v ^ (j + 1) :=
        hl ▸ dvd_pow_self _ (Nat.succ_ne_zero l)
      exact hw (natGenerator_injective ((Nat.prime_dvd_prime_iff_eq (prime_natGenerator w) hp).mp
        ((prime_natGenerator w).dvd_of_dvd_pow hdvd)))
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.mp
    (tendsTo_eulerProduct_ofPowerSeries q F hF (natGenerator v ^ k))
  have key := hs0 (insert v s0) (Finset.subset_insert _ _)
  change eulerProduct (fun w => ofPowerSeries (q w) (F w)) (natGenerator v ^ k) = _
  have hrest := prod_vanish (fun w => ofPowerSeries (q w) (F w)) (natGenerator v ^ k)
    ((insert v s0).erase v) fun w hw => ⟨hf1 w, hvan w (Finset.ne_of_mem_erase hw)⟩
  rw [← key, ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v s0), mul_comm,
    mul_apply_of_vanish hrest.1 hrest.2]
  have hq : q v = natGenerator v := natCard_residueField v
  rw [hq, ofPowerSeries_apply_pow hp.one_lt]
  rfl

open Polynomial in
/-- **The coefficient of Mathlib's `L(E_m, s)` at `p ^ k` for a good prime `p ∤ 6m`**
(`PROVED`): the coefficient of `T ^ k` in `1 / (1 − a_p T + p T²)`, with
`a_p = p + 1 − #Ẽ_m(𝔽_p)` and `Ẽ_m = PoleRC.curveF (m mod p)`. -/
theorem LFunction_curve_apply_prime_pow (m : ℤ) (p : ℕ) [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ 6 * m) (k : ℕ) :
    (ZInQ.Manuscript.curve (m : ℚ)).LFunction (p ^ k) =
      PowerSeries.coeff k (PowerSeries.invOfUnit
        ((1 - C ((p : ℤ) + 1 - Nat.card (ZInQ.Manuscript.PoleRC.curveF
          ((m : ℤ) : ZMod p)).toAffine.Point) * X + C (p : ℤ) * X ^ 2 : ℤ[X]) :
            PowerSeries ℤ) 1) := by
  obtain ⟨v, rfl⟩ := exists_natGenerator_eq p
  rw [LFunction_apply_prime_pow_eq _ _ k v rfl, localPolynomial_curveLocal v hp]

/-- **Mathlib's `a_p` of `E_m : y² = x(x − m)(x + 3m)` at a good prime** (Lane RC3; `PROVED`): for a
prime `p ∤ 6m`, the Dirichlet coefficient at `p` of Mathlib's L-function of `curve m` is
`p + 1 − #Ẽ_m(𝔽_p)`, where `Ẽ_m = curveF (m mod p)` is the reduction (point at infinity
included). -/
theorem LFunction_curve_apply_prime (m : ℤ) (p : ℕ) [Fact p.Prime] (hp : ¬ (p : ℤ) ∣ 6 * m) :
    (ZInQ.Manuscript.curve (m : ℚ)).LFunction p =
      (p : ℤ) + 1 - Nat.card (ZInQ.Manuscript.PoleRC.curveF ((m : ℤ) : ZMod p)).toAffine.Point := by
  obtain ⟨v, rfl⟩ := exists_natGenerator_eq p
  have h := LFunction_apply_prime_pow_eq (ZInQ.Manuscript.curve (m : ℚ)) _ 1 v rfl
  rw [pow_one] at h
  rw [h, localPolynomial_curveLocal v hp, coeff_one_invOfUnit]
  · simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]
  · simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]

end ZInQ.Manuscript.RC.KSplit
