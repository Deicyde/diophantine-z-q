import ZInQKernel.Contrib.OneProof.RC.Determinant.OModel

/-!
# Laurent coefficients in `ℤ₂` of elements of `𝒪` (Lane RC7)

`𝒪 = (ℤ₂[[t]]_{(2)})^` (manuscript `diophantine_zq.tex`, tex 2747–2748, 3728) is modelled in
`OModel.lean` as the inverse limit `lim_n (ℤ/2ⁿ)((t))`.  An element `y ∈ 𝒪` therefore has, for every
`i ∈ ℤ`, a Laurent coefficient `[tⁱ]y ∈ ℤ₂ = lim_n ℤ/2ⁿ`, the `2`-adic integer whose reduction
modulo `2ⁿ` is the `i`-th coefficient of `y mod 2ⁿ`.  These are the coefficients `[tⁱ]f` used with
(5.9), tex 5626–5638 ("for `i < -L_T(M)` all sign values of `[tⁱ]f` are divisible by `2^M`"), and
in the coefficient transfer, tex 5665.

## Main definitions and results

* `coeffZ y i : ℤ_[2]` with `toZModPow_coeffZ`; it is additive and `ℤ`-linear in `y`, and
  `coeffZ_algebraMap` computes it on `Λ = ℤ₂[[t]]`;
* `coeff_proj_eq_zero_iff` : `(proj M y).coeff i = 0 ↔ 2^M ∣ coeffZ y i`;
* `coeffZ_decay` : for every `M`, `2^M ∣ coeffZ y i` for all sufficiently negative `i`;
* `two_pow_dvd_coeffZ_of_mem` : the pole bound `y ≡ t^{-L} a (mod 2^M)` gives `2^M ∣ [tⁱ]y`
  for `i < -L`;
* `hasSum_coeffZ_mul_algebraMap` : `[tⁿ](y g) = ∑_{k ≥ 0} [t^{n-k}]y · [tᵏ]g` for `g ∈ Λ`, as a
  convergent series in `ℤ₂` (and, `hasSum_coeffZ_mul_algebraMap_padic`, in `ℚ₂`).

Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Determinant

open OModel

namespace OModel

/-- The ring of compatible residue sequences `lim_n ℤ/2ⁿ` (all-pairs compatibility), which
`PadicInt.lift` identifies with `ℤ₂`. -/
def ZpSeq : Subring (∀ n : ℕ, ZMod (2 ^ n)) where
  carrier := {s | ∀ m n (h : m ≤ n), ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2 ^ m)) (s n) = s m}
  mul_mem' {a b} ha hb m n h := by
    simp only [Set.mem_ofPred_eq] at ha hb
    simp only [Pi.mul_apply, map_mul, ha m n h, hb m n h]
  one_mem' m n h := by simp only [Pi.one_apply, map_one]
  add_mem' {a b} ha hb m n h := by
    simp only [Set.mem_ofPred_eq] at ha hb
    simp only [Pi.add_apply, map_add, ha m n h, hb m n h]
  zero_mem' m n h := by simp only [Pi.zero_apply, map_zero]
  neg_mem' {a} ha m n h := by
    simp only [Set.mem_ofPred_eq] at ha
    simp only [Pi.neg_apply, map_neg, ha m n h]

/-- Evaluation of a compatible residue sequence at `k`. -/
def zpEval (k : ℕ) : ZpSeq →+* ZMod (2 ^ k) :=
  (Pi.evalRingHom (fun n => ZMod (2 ^ n)) k).comp ZpSeq.subtype

/-- **Tex 2747–2748, 3728 (PROVED).**  The evaluations of `ZpSeq` are compatible. -/
theorem zpEval_compat (k1 k2 : ℕ) (hk : k1 ≤ k2) :
    (ZMod.castHom (pow_dvd_pow 2 hk) _).comp (zpEval k2) = zpEval k1 := by
  ext s
  exact s.2 k1 k2 hk

/-- The `2`-adic integer of a compatible residue sequence. -/
noncomputable def zpLift : ZpSeq →+* ℤ_[2] := PadicInt.lift zpEval_compat

/-- **Tex 2747–2748, 3728 (PROVED).**  `zpLift s` reduces modulo `2ⁿ` to the `n`-th entry of `s`. -/
theorem toZModPow_zpLift (n : ℕ) (s : ZpSeq) :
    PadicInt.toZModPow n (zpLift s) = (s : ∀ n, ZMod (2 ^ n)) n :=
  RingHom.congr_fun (PadicInt.lift_spec zpEval_compat n) s

/-- The residue sequence `n ↦ (proj n y).coeff i`. -/
noncomputable def coeffSeq (y : OO) (i : ℤ) : ZpSeq :=
  ⟨fun n => (proj n y).coeff i, fun m n h => by
    rw [ZMod.castHom_apply]
    exact cast_coeff_of_le y h i⟩

end OModel

/-- The `i`-th Laurent coefficient `[tⁱ]y ∈ ℤ₂` of `y ∈ 𝒪` (tex 2747–2748, 3728; the
coefficients of (5.9), tex 5626–5638): the `2`-adic integer whose reduction modulo `2ⁿ` is
`(proj n y).coeff i` for every `n`. -/
noncomputable def coeffZ (y : OO) (i : ℤ) : ℤ_[2] := zpLift (coeffSeq y i)

/-- **Tex 2747–2748, 3728, 5626–5638 (PROVED).**  `coeffZ y i` reduces modulo `2ⁿ` to the
`i`-th coefficient of `y mod 2ⁿ`. -/
theorem toZModPow_coeffZ (y : OO) (i : ℤ) (n : ℕ) :
    PadicInt.toZModPow n (coeffZ y i) = (proj n y).coeff i :=
  toZModPow_zpLift n _

/-- **Tex 2747–2748, 3728, 5626–5638 (PROVED).**  `coeffZ y i` is the unique `2`-adic integer
with these reductions. -/
theorem eq_coeffZ_iff (y : OO) (i : ℤ) (z : ℤ_[2]) :
    z = coeffZ y i ↔ ∀ n, PadicInt.toZModPow n z = (proj n y).coeff i := by
  rw [← PadicInt.ext_of_toZModPow]
  simp only [toZModPow_coeffZ]

/-- **Tex 2747–2748, 3728, 5626–5638 (PROVED).**  `[tⁱ](y + z) = [tⁱ]y + [tⁱ]z`. -/
theorem coeffZ_add (y z : OO) (i : ℤ) : coeffZ (y + z) i = coeffZ y i + coeffZ z i := by
  symm
  rw [eq_coeffZ_iff]
  intro n
  rw [map_add, toZModPow_coeffZ, toZModPow_coeffZ, map_add, HahnSeries.coeff_add]

/-- **Tex 2747–2748, 3728, 5626–5638 (PROVED).**  `[tⁱ]0 = 0`. -/
theorem coeffZ_zero (i : ℤ) : coeffZ 0 i = 0 := by
  symm
  rw [eq_coeffZ_iff]
  intro n
  rw [map_zero, map_zero, HahnSeries.coeff_zero]

/-- **Tex 2747–2748, 3728, 5626–5638 (PROVED).**  `[tⁱ](-y) = -[tⁱ]y`. -/
theorem coeffZ_neg (y : OO) (i : ℤ) : coeffZ (-y) i = -coeffZ y i := by
  symm
  rw [eq_coeffZ_iff]
  intro n
  rw [map_neg, toZModPow_coeffZ, map_neg, HahnSeries.coeff_neg]

/-- **Tex 2747–2748, 3728, 5626–5638 (PROVED).**  `[tⁱ](y - z) = [tⁱ]y - [tⁱ]z`. -/
theorem coeffZ_sub (y z : OO) (i : ℤ) : coeffZ (y - z) i = coeffZ y i - coeffZ z i := by
  rw [sub_eq_add_neg, coeffZ_add, coeffZ_neg, ← sub_eq_add_neg]

/-- **Tex 2747–2748, 3728, 5626–5638 (PROVED).**  `[tⁱ](r y) = r [tⁱ]y` for `r ∈ ℤ`. -/
theorem coeffZ_intCast_mul (r : ℤ) (y : OO) (i : ℤ) :
    coeffZ ((r : OO) * y) i = r * coeffZ y i := by
  symm
  rw [eq_coeffZ_iff]
  intro n
  rw [map_mul, toZModPow_coeffZ, map_intCast, map_mul, map_intCast,
    ← map_intCast (HahnSeries.C : ZMod (2 ^ n) →+* LaurentSeries (ZMod (2 ^ n))),
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

/-- **Tex 2747–2748, 3728, 5626–5638 (PROVED).**  `[tⁱ](r • y) = r • [tⁱ]y` for `r ∈ ℤ`. -/
theorem coeffZ_zsmul (r : ℤ) (y : OO) (i : ℤ) : coeffZ (r • y) i = r • coeffZ y i := by
  rw [zsmul_eq_mul, zsmul_eq_mul, coeffZ_intCast_mul]

/-- **Tex 2747–2748, 3728, 5626–5638 (PROVED).**  On the image of `g ∈ Λ = ℤ₂[[t]]`, the Laurent
coefficients are the power-series coefficients of `g` (and vanish in negative degree). -/
theorem coeffZ_algebraMap (g : PowerSeries ℤ_[2]) (i : ℤ) :
    coeffZ (algebraMap (PowerSeries ℤ_[2]) OO g) i =
      if 0 ≤ i then PowerSeries.coeff i.toNat g else 0 := by
  symm
  rw [eq_coeffZ_iff]
  intro n
  rw [proj_algebraMap, PowerSeries.coeff_coe]
  split_ifs with h1 h2 h2
  · omega
  · rw [PowerSeries.coeff_map, show i.toNat = i.natAbs by omega]
  · rw [map_zero]
  · omega

/-- **Tex 5626–5638 (PROVED).**  Bridge between the two coefficient forms: the `i`-th coefficient
of `y mod 2^M` vanishes iff `2^M` divides `[tⁱ]y` in `ℤ₂`. -/
theorem coeff_proj_eq_zero_iff (M : ℕ) (y : OO) (i : ℤ) :
    (proj M y).coeff i = 0 ↔ (2 : ℤ_[2]) ^ M ∣ coeffZ y i := by
  rw [← toZModPow_coeffZ, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton,
    Nat.cast_ofNat]

namespace OModel

/-- **Tex 2747–2748, 3728 (PROVED).**  A Laurent series has no terms in sufficiently negative
degree. -/
theorem laurent_exists_coeff_eq_zero {R : Type*} [CommRing R] (x : LaurentSeries R) :
    ∃ L : ℕ, ∀ i : ℤ, i < -(L : ℤ) → x.coeff i = 0 := by
  refine ⟨(-x.order).toNat, fun i hi => HahnSeries.coeff_eq_zero_of_lt_order ?_⟩
  have := Int.self_le_toNat (-x.order)
  omega

end OModel

/-- **Tex 5626–5638 (PROVED).**  Decay of Laurent coefficients: for every `M`, `2^M ∣ [tⁱ]y` for
all sufficiently negative `i`. -/
theorem coeffZ_decay (y : OO) (M : ℕ) :
    ∃ L : ℕ, ∀ i : ℤ, i < -(L : ℤ) → (2 : ℤ_[2]) ^ M ∣ coeffZ y i := by
  obtain ⟨L, hL⟩ := laurent_exists_coeff_eq_zero (proj M y)
  exact ⟨L, fun i hi => (coeff_proj_eq_zero_iff M y i).mp (hL i hi)⟩

/-- **Tex 5626–5638 (PROVED).**  The pole bound in `ℤ₂`-coefficient form: if
`y ≡ t^{-L} a (mod 2^M)` in `𝒪` with `a ∈ Λ`, then `2^M ∣ [tⁱ]y` for every `i < -L`. -/
theorem two_pow_dvd_coeffZ_of_mem (M L : ℕ) (y : OO) (a : PowerSeries ℤ_[2])
    (hy : y - tInv ^ L * algebraMap _ OO a ∈ Ideal.span {(2 : OO) ^ M}) (i : ℤ)
    (hi : i < -(L : ℤ)) : (2 : ℤ_[2]) ^ M ∣ coeffZ y i :=
  (coeff_proj_eq_zero_iff M y i).mp (coeff_proj_eq_zero_of_mem M L y a hy i hi)


namespace OModel

/-- **Tex 2747–2748, 3728 (PROVED).**  A Laurent series without terms below degree `-L` is
`t^{-L}` times a power series. -/
theorem laurent_eq_single_mul_ofPowerSeries {R : Type*} [CommRing R] (x : LaurentSeries R)
    (L : ℕ) (hL : ∀ j : ℤ, j < -(L : ℤ) → x.coeff j = 0) :
    x = HahnSeries.single (-(L : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk fun m => x.coeff ((m : ℤ) - L)) := by
  ext j
  rw [HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  split_ifs with h
  · exact hL j (by omega)
  · rw [PowerSeries.coeff_mk]
    congr 1
    omega

/-- **Tex 2747–2748, 3728 (PROVED).**  Finite convolution formula: if `x` has no terms below
degree `-L` and `n + L < K`, then `[tⁿ](x h) = ∑_{k < K} [t^{n-k}]x · [tᵏ]h` for a power series
`h`. -/
theorem coeff_mul_ofPowerSeries_eq_sum {R : Type*} [CommRing R] (x : LaurentSeries R)
    (h : PowerSeries R) (L : ℕ) (hL : ∀ j : ℤ, j < -(L : ℤ) → x.coeff j = 0) (n : ℤ) (K : ℕ)
    (hK : n + L < K) :
    (x * HahnSeries.ofPowerSeries ℤ R h).coeff n =
      ∑ k ∈ Finset.range K, x.coeff (n - k) * PowerSeries.coeff k h := by
  have hx := laurent_eq_single_mul_ofPowerSeries x L hL
  have h1 : (x * HahnSeries.ofPowerSeries ℤ R h).coeff n =
      (HahnSeries.ofPowerSeries ℤ R
        ((PowerSeries.mk fun m => x.coeff ((m : ℤ) - L)) * h)).coeff (n + L) := by
    conv_lhs => rw [hx]
    rw [mul_assoc, ← map_mul, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]
  rw [h1, PowerSeries.coeff_coe]
  split_ifs with hneg
  · symm
    apply Finset.sum_eq_zero
    intro k _
    rw [hL (n - k) (by omega), zero_mul]
  · rw [PowerSeries.coeff_mul]
    have hNn : (((n + L).natAbs : ℕ) : ℤ) = n + L := Int.natAbs_of_nonneg (by omega)
    rw [← Finset.Nat.sum_antidiagonal_swap,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Prod.fst_swap, Prod.snd_swap, PowerSeries.coeff_mk]
    calc ∑ k ∈ Finset.range ((n + L).natAbs).succ,
          x.coeff ((((n + L).natAbs - k : ℕ) : ℤ) - L) * PowerSeries.coeff k h
        = ∑ k ∈ Finset.range ((n + L).natAbs).succ, x.coeff (n - k) * PowerSeries.coeff k h := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          congr 2
          omega
      _ = ∑ k ∈ Finset.range K, x.coeff (n - k) * PowerSeries.coeff k h := by
          apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
          intro k hk hk'
          rw [Finset.mem_range] at hk hk'
          rw [hL (n - k) (by omega), zero_mul]

end OModel

/-- **Tex 5626–5638 (PROVED).**  Modulo `2^M`, the partial sums of the convolution series for
`[tⁿ](y g)` over any finite set containing `{0, …, n + L}` are exact, where `-L` bounds the
negative support of `y mod 2^M`. -/
theorem toZModPow_sum_coeffZ_mul (y : OO) (g : PowerSeries ℤ_[2]) (n : ℤ) (M L : ℕ)
    (hL : ∀ j : ℤ, j < -(L : ℤ) → (proj M y).coeff j = 0) (S : Finset ℕ)
    (hS : Finset.range (n + L + 1).toNat ⊆ S) :
    PadicInt.toZModPow M (∑ k ∈ S, coeffZ y (n - k) * PowerSeries.coeff k g) =
      PadicInt.toZModPow M (coeffZ (y * algebraMap (PowerSeries ℤ_[2]) OO g) n) := by
  have hK' : n + L < ((n + L + 1).toNat : ℕ) := by omega
  rw [toZModPow_coeffZ, map_mul, proj_algebraMap,
    coeff_mul_ofPowerSeries_eq_sum (proj M y) _ L hL n _ hK', map_sum,
    ← Finset.sum_sdiff hS, Finset.sum_eq_zero (s := S \ Finset.range (n + L + 1).toNat),
    zero_add]
  · apply Finset.sum_congr rfl
    intro k _
    rw [map_mul, toZModPow_coeffZ, PowerSeries.coeff_map]
  · intro k hk
    rw [Finset.mem_sdiff, Finset.mem_range] at hk
    rw [map_mul, toZModPow_coeffZ, hL (n - k) (by omega), zero_mul]

/-- **Tex 5626–5638 (PROVED).**  Convolution with a power series `g ∈ Λ`:
`[tⁿ](y g) = ∑_{k ≥ 0} [t^{n-k}]y · [tᵏ]g`, a convergent series in `ℤ₂` (its terms tend to `0`
since `[t^{n-k}]y → 0` as `k → ∞`). -/
theorem hasSum_coeffZ_mul_algebraMap (y : OO) (g : PowerSeries ℤ_[2]) (n : ℤ) :
    HasSum (fun k : ℕ => coeffZ y (n - k) * PowerSeries.coeff k g)
      (coeffZ (y * algebraMap (PowerSeries ℤ_[2]) OO g) n) := by
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨L, hL⟩ := laurent_exists_coeff_eq_zero (proj M y)
  refine ⟨Finset.range (n + L + 1).toNat, fun S hS => ?_⟩
  have h := toZModPow_sum_coeffZ_mul y g n M L hL S hS
  rw [dist_eq_norm]
  have hmem : (∑ k ∈ S, coeffZ y (n - k) * PowerSeries.coeff k g) -
      coeffZ (y * algebraMap (PowerSeries ℤ_[2]) OO g) n ∈
      Ideal.span {((2 : ℕ) : ℤ_[2]) ^ M} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow _ M).mpr hmem
  calc _ ≤ ((2 : ℕ) : ℝ) ^ (-(M : ℤ)) := hnorm
    _ = (1 / 2 : ℝ) ^ M := by rw [zpow_neg, zpow_natCast, one_div, inv_pow, Nat.cast_ofNat]
    _ < ε := hM

/-- **Tex 5626–5638 (PROVED).**  The convolution series of `hasSum_coeffZ_mul_algebraMap`,
viewed in `ℚ₂`. -/
theorem hasSum_coeffZ_mul_algebraMap_padic (y : OO) (g : PowerSeries ℤ_[2]) (n : ℤ) :
    HasSum (fun k : ℕ => (coeffZ y (n - k) : ℚ_[2]) * ((PowerSeries.coeff k g : ℤ_[2]) : ℚ_[2]))
      (coeffZ (y * algebraMap (PowerSeries ℤ_[2]) OO g) n : ℚ_[2]) := by
  have := (hasSum_coeffZ_mul_algebraMap y g n).map (PadicInt.Coe.ringHom (p := 2))
    continuous_subtype_val
  simpa [Function.comp_def] using this

end ZInQ.Manuscript.RC.Determinant
