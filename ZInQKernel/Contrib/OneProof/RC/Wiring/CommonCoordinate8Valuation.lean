import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate8Reduction

/-!
# Theorem 5.3, Lane RC32 round 5: a Galois-invariant extension of `v_r` to `ℚ̄_r`

The named input `LocalGaloisDecomposition r hr` (`CommonCoordinate8Reduction.lean`) asks for a
valuation `w` of `ℚ̄_r` extending `v_r` with three properties (inv), (res), (dec). This file
constructs such a `w` and PROVES (inv) and (res) for it:

* `spectralValuation r hr` (definition): Mathlib's spectral norm of `ℚ̄_r` over `ℚ_r`
  (Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, 3.2.1/2 and 3.2.4/2), for the norm of `ℚ_r`
  attached to `v_r`, as an `ℝ≥0`-valued valuation (multiplicative because `ℚ_r` is complete);
* `extendsVr_spectralValuation`: it extends `v_r` (`spectralNorm_extends`);
* `spectralValuation_map_algEquiv`: it is `Gal(ℚ̄_r/ℚ_r)`-invariant (`spectralNorm_eq_of_equiv`);
* `spectralValuation_residue`: for every embedding `ι : ℚ̄ → ℚ̄_r`, every `w`-integral `y` is
  congruent to an element of `ι(ℤ̄)` modulo the maximal ideal of `w`. The minimal polynomial of `y`
  over `ℚ_r` has `v_r`-integral coefficients (its spectral value is `w(y) ≤ 1`); approximating them
  by integers (`ℚ` is dense in `ℚ_r`, and a `v_r`-integral rational number is an integer modulo
  `r`) gives a monic `g ∈ ℤ[X]` with `w(g(y)) < 1`; `g` splits over `ℚ̄` with roots in `ℤ̄`, so
  `g(y) = ∏ (y − ι α)` and some factor has `w(y − ι α) < 1`;
* `exists_invariant_extension`: the first three conjuncts of `LocalGaloisDecomposition`;
* `localGaloisDecomposition_of_spectral`: `LocalGaloisDecomposition r hr` from (dec) for the
  spectral valuation alone.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.AddressGenuine (Zbar)
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary (primeIdealQ)
open scoped WithZero NNReal Pointwise

variable {r : ℕ} {hr : r.Prime}

/-! ## Residues of a valuation extending `v_r` -/

section Residue

variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {w : Valuation (Qrbar r hr) Γ}

/-- An integer prime to `r` is a `w`-unit (PROVED). -/
theorem intCast_eq_one_of_not_dvd (hw : ExtendsVr w) {n : ℤ} (hn : ¬ (r : ℤ) ∣ n) :
    w (n : Qrbar r hr) = 1 :=
  le_antisymm (intCast_le_one hw n) (not_lt.mp fun h => hn ((intCast_lt_one_iff hw n).mp h))

/-- **A `w`-integral rational number is an integer modulo the maximal ideal of `w`** (PROVED): its
denominator is prime to `r`; multiply the numerator by an inverse of the denominator mod `r`. -/
theorem exists_intCast_sub_ratCast_lt_one (hw : ExtendsVr w) (q : ℚ)
    (hq : w (q : Qrbar r hr) ≤ 1) : ∃ n : ℤ, w ((q : Qrbar r hr) - n) < 1 := by
  have hqd : (q : Qrbar r hr) * ((q.den : ℤ) : Qrbar r hr) = (q.num : Qrbar r hr) := by
    exact_mod_cast congrArg (fun t : ℚ => (t : Qrbar r hr)) (Rat.mul_den_eq_num q)
  have hden : ¬ (r : ℤ) ∣ (q.den : ℤ) := by
    intro hd
    have hnum : ¬ (r : ℤ) ∣ q.num := by
      intro hn
      have h1 : r ∣ q.num.natAbs := Int.natCast_dvd.mp hn
      have h2 : r ∣ q.den := Int.natCast_dvd_natCast.mp hd
      have h3 : r ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h1 h2
      rw [q.reduced.gcd_eq_one] at h3
      exact hr.one_lt.ne' (Nat.dvd_one.mp h3)
    have h1 : w (q.num : Qrbar r hr) = 1 := intCast_eq_one_of_not_dvd hw hnum
    have h2 : w ((q.den : ℤ) : Qrbar r hr) < 1 := (intCast_lt_one_iff hw _).mpr hd
    have h3 : w ((q : Qrbar r hr) * ((q.den : ℤ) : Qrbar r hr)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hq) h2
    rw [hqd, h1] at h3
    exact lt_irrefl _ h3
  have hcop : IsCoprime (r : ℤ) (q.den : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hr).mpr
      fun h => hden (Int.natCast_dvd_natCast.mpr h))
  obtain ⟨u, t, hut⟩ := hcop
  refine ⟨q.num * t, ?_⟩
  have hD : w ((q.den : ℤ) : Qrbar r hr) = 1 := intCast_eq_one_of_not_dvd hw hden
  have key : ((q : Qrbar r hr) - ((q.num * t : ℤ) : Qrbar r hr)) * ((q.den : ℤ) : Qrbar r hr) =
      ((q.num * u * r : ℤ) : Qrbar r hr) := by
    have hut' := congrArg (fun z : ℤ => (z : Qrbar r hr)) hut
    push_cast at hut' hqd ⊢
    linear_combination hqd - (q.num : Qrbar r hr) * hut'
  have hlt : w ((q.num * u * r : ℤ) : Qrbar r hr) < 1 :=
    (intCast_lt_one_iff hw _).mpr (dvd_mul_left (r : ℤ) (q.num * u))
  rw [← key, map_mul, hD, mul_one] at hlt
  exact hlt

/-- `ℚ` is dense in `ℚ_r` (PROVED: Mathlib's `denseRange_algebraMap`). -/
theorem exists_ratCast_sub_lt_one_Qr (c : Qr r hr) :
    ∃ q : ℚ, (Valued.v : Valuation (Qr r hr) ℤᵐ⁰) (c - (q : Qr r hr)) < 1 := by
  obtain ⟨q, hq⟩ :=
    (HeightOneSpectrum.denseRange_algebraMap ℚ (primeIdealQ r hr)).exists_dist_lt c one_pos
  refine ⟨q, ?_⟩
  rw [dist_eq_norm, eq_ratCast] at hq
  exact Valued.toNormedField.norm_lt_one_iff.mp hq

/-- **A `v_r`-integral element of `ℚ_r` is an integer modulo the maximal ideal of `w`** (PROVED:
approximate it by a rational number, then the rational number by an integer). -/
theorem exists_intCast_sub_lt_one (hw : ExtendsVr w) (c : Qr r hr)
    (hc : (Valued.v : Valuation (Qr r hr) ℤᵐ⁰) c ≤ 1) :
    ∃ n : ℤ, w (algebraMap (Qr r hr) (Qrbar r hr) c - n) < 1 := by
  obtain ⟨q, hq⟩ := exists_ratCast_sub_lt_one_Qr c
  have h1 : w (algebraMap (Qr r hr) (Qrbar r hr) c - q) < 1 := by
    have h := (Valuation.IsEquiv.lt_one_iff_lt_one hw (x := c - (q : Qr r hr))).mpr hq
    rwa [Valuation.comap_apply, map_sub, map_ratCast] at h
  have h2 : w (algebraMap (Qr r hr) (Qrbar r hr) c) ≤ 1 := by
    have h := (Valuation.IsEquiv.le_one_iff_le_one hw (x := c)).mpr hc
    rwa [Valuation.comap_apply] at h
  have h3 : w (q : Qrbar r hr) ≤ 1 := by
    have h : (q : Qrbar r hr) = algebraMap (Qr r hr) (Qrbar r hr) c -
        (algebraMap (Qr r hr) (Qrbar r hr) c - q) := by ring
    rw [h]
    exact le_trans (w.map_sub _ _) (max_le h2 h1.le)
  obtain ⟨n, hn⟩ := exists_intCast_sub_ratCast_lt_one hw q h3
  refine ⟨n, ?_⟩
  have h : algebraMap (Qr r hr) (Qrbar r hr) c - n =
      (algebraMap (Qr r hr) (Qrbar r hr) c - q) + ((q : Qrbar r hr) - n) := by ring
  rw [h]
  exact lt_of_le_of_lt (w.map_add _ _) (max_lt h1 hn)

/-- **A monic integer polynomial nearly vanishing at `y`** (PROVED): if `y` is `w`-integral and a
root of a monic `f ∈ ℚ_r[X]` with `v_r`-integral coefficients, replacing the coefficients of `f`
below the leading one by integers congruent to them gives a monic `g ∈ ℤ[X]` with `w(g(y)) < 1`. -/
theorem exists_monic_aeval_lt_one (hw : ExtendsVr w) {y : Qrbar r hr} (hy : w y ≤ 1)
    {f : Polynomial (Qr r hr)} (hfm : f.Monic) (hf0 : Polynomial.aeval y f = 0)
    (hcoeff : ∀ i, (Valued.v : Valuation (Qr r hr) ℤᵐ⁰) (f.coeff i) ≤ 1) :
    ∃ g : Polynomial ℤ, g.Monic ∧ w (Polynomial.aeval y g) < 1 := by
  choose n hn using fun i => exists_intCast_sub_lt_one hw (f.coeff i) (hcoeff i)
  refine ⟨Polynomial.X ^ f.natDegree +
      ∑ i : Fin f.natDegree, Polynomial.C (n i) * Polynomial.X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  rw [hfm.as_sum] at hf0
  simp only [map_add, map_pow, Polynomial.aeval_X, map_sum, map_mul, Polynomial.aeval_C]
    at hf0 ⊢
  rw [Fin.sum_univ_eq_sum_range (fun i => algebraMap ℤ (Qrbar r hr) (n i) * y ^ i)]
  have key : y ^ f.natDegree +
      ∑ i ∈ Finset.range f.natDegree, algebraMap ℤ (Qrbar r hr) (n i) * y ^ i =
      ∑ i ∈ Finset.range f.natDegree, (algebraMap ℤ (Qrbar r hr) (n i) -
        algebraMap (Qr r hr) (Qrbar r hr) (f.coeff i)) * y ^ i := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    linear_combination hf0
  rw [key]
  refine Valuation.map_sum_lt w one_ne_zero fun i _ => ?_
  rw [map_mul, map_pow, Valuation.map_sub_swap, eq_intCast (algebraMap ℤ (Qrbar r hr))]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hy i)) (hn i)

/-- **Roots of monic integer polynomials** (PROVED): if `g ∈ ℤ[X]` is monic and `w(g(y)) < 1`, then
`w(y − ι x) < 1` for some `x ∈ ℤ̄`: `g = ∏ (X − α)` over `ℚ̄` with every root `α` in `ℤ̄`, so
`g(y) = ∏ (y − ι α)`. -/
theorem exists_Zbar_sub_lt_one_of_monic (ι : Qbar →ₐ[ℚ] Qrbar r hr) (y : Qrbar r hr)
    {g : Polynomial ℤ} (hg : g.Monic) (hgy : w (Polynomial.aeval y g) < 1) :
    ∃ x : Zbar, w (y - ι x) < 1 := by
  obtain ⟨s, hs, hint⟩ : ∃ s : Multiset Qbar,
      g.map (algebraMap ℤ Qbar) = (s.map fun a => Polynomial.X - Polynomial.C a).prod ∧
        ∀ a ∈ s, IsIntegral ℤ a :=
    ⟨(g.map (algebraMap ℤ Qbar)).roots,
      (IsAlgClosed.splits _).eq_prod_roots_of_monic (hg.map _), fun a ha =>
        ⟨g, hg, (Polynomial.mem_roots_map_of_injective (algebraMap ℤ Qbar).injective_int
          hg.ne_zero).mp ha⟩⟩
  have heval : Polynomial.aeval y g = (s.map fun a => y - ι a).prod := by
    have hmap : g.map (algebraMap ℤ (Qrbar r hr)) =
        (g.map (algebraMap ℤ Qbar)).map (ι : Qbar →+* Qrbar r hr) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext_int _ _
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmap, hs, Polynomial.map_multiset_prod,
      Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp
  rw [heval, map_multiset_prod, Multiset.map_map] at hgy
  by_contra hcon
  push Not at hcon
  refine absurd hgy (not_lt.mpr (Multiset.one_le_prod_of_one_le fun z hz => ?_))
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hz
  exact hcon ⟨a, hint a ha⟩

/-- **The residue property from integral minimal polynomials** (PROVED): if every `w`-integral `y`
has a minimal polynomial over `ℚ_r` with `v_r`-integral coefficients, then for every embedding
`ι : ℚ̄ → ℚ̄_r` every `w`-integral `y` is congruent to an element of `ι(ℤ̄)` modulo the maximal
ideal of `w`. -/
theorem residue_of_minpoly_coeff (hw : ExtendsVr w)
    (hmin : ∀ y : Qrbar r hr, w y ≤ 1 → ∀ i,
      (Valued.v : Valuation (Qr r hr) ℤᵐ⁰) ((minpoly (Qr r hr) y).coeff i) ≤ 1)
    (ι : Qbar →ₐ[ℚ] Qrbar r hr) (y : Qrbar r hr) (hy : w y ≤ 1) :
    ∃ x : Zbar, w (y - ι x) < 1 := by
  obtain ⟨g, hg, hgy⟩ := exists_monic_aeval_lt_one hw hy
    (minpoly.monic (Algebra.IsIntegral.isIntegral y)) (minpoly.aeval _ _) (hmin y hy)
  exact exists_Zbar_sub_lt_one_of_monic ι y hg hgy

end Residue

/-! ## The spectral valuation -/

section Spectral

/-- **The spectral valuation of `ℚ̄_r`** (definition): the spectral norm of `ℚ̄_r` over `ℚ_r`
(Mathlib's `spectralNorm`, for the norm of `ℚ_r` attached to `v_r`) as an `ℝ≥0`-valued valuation;
it is multiplicative since `ℚ_r` is complete (`spectralAlgNorm_mul`) and ultrametric
(`isNonarchimedean_spectralNorm`). -/
def spectralValuation (r : ℕ) (hr : r.Prime) : Valuation (Qrbar r hr) ℝ≥0 where
  toFun y := ⟨spectralNorm (Qr r hr) (Qrbar r hr) y, spectralNorm_nonneg y⟩
  map_zero' := NNReal.eq spectralNorm_zero
  map_one' := NNReal.eq spectralNorm_one
  map_mul' x y := NNReal.eq <|
    @spectralAlgNorm_mul (Qr r hr) (Valued.toNontriviallyNormedField _ ℤᵐ⁰) (Qrbar r hr)
      _ _ _ _ _ x y
  map_add_le_max' x y := le_max_iff.mpr (le_max_iff.mp (isNonarchimedean_spectralNorm x y))

theorem spectralValuation_apply (y : Qrbar r hr) :
    (spectralValuation r hr y : ℝ) = spectralNorm (Qr r hr) (Qrbar r hr) y := rfl

/-- On `ℚ_r` the spectral valuation is the norm (PROVED: `spectralNorm_extends`). -/
theorem spectralValuation_algebraMap (c : Qr r hr) :
    (spectralValuation r hr (algebraMap (Qr r hr) (Qrbar r hr) c) : ℝ) = ‖c‖ :=
  spectralNorm_extends c

/-- **The spectral valuation extends `v_r`** (PROVED): on `ℚ_r` it is the norm, a strictly
increasing function of `v_r`. -/
theorem extendsVr_spectralValuation : ExtendsVr (spectralValuation r hr) := by
  intro a b
  rw [Valuation.comap_apply, Valuation.comap_apply, ← NNReal.coe_le_coe,
    spectralValuation_algebraMap, spectralValuation_algebraMap]
  exact Valued.toNormedField.norm_le_iff

/-- **The spectral valuation is `Gal(ℚ̄_r/ℚ_r)`-invariant** (PROVED: `spectralNorm_eq_of_equiv`;
conjugates have the same minimal polynomial). -/
theorem spectralValuation_map_algEquiv (σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr)
    (y : Qrbar r hr) : spectralValuation r hr (σ y) = spectralValuation r hr y :=
  NNReal.eq (spectralNorm_eq_of_equiv σ y).symm

/-- **Spectrally integral elements have integral minimal polynomials** (PROVED:
`spectralValue_le_one_iff`). -/
theorem minpoly_coeff_le_one {y : Qrbar r hr} (hy : spectralValuation r hr y ≤ 1) (i : ℕ) :
    (Valued.v : Valuation (Qr r hr) ℤᵐ⁰) ((minpoly (Qr r hr) y).coeff i) ≤ 1 := by
  have h : spectralNorm (Qr r hr) (Qrbar r hr) y ≤ 1 := by
    rw [← spectralValuation_apply]
    exact_mod_cast hy
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral y))]
    at h
  exact Valued.toNormedField.norm_le_one_iff.mp (h i)

/-- **The residue property of the spectral valuation** (PROVED): for every embedding
`ι : ℚ̄ → ℚ̄_r`, every `y` with `w(y) ≤ 1` satisfies `w(y − ι x) < 1` for some `x ∈ ℤ̄`. -/
theorem spectralValuation_residue (ι : Qbar →ₐ[ℚ] Qrbar r hr) (y : Qrbar r hr)
    (hy : spectralValuation r hr y ≤ 1) : ∃ x : Zbar, spectralValuation r hr (y - ι x) < 1 :=
  residue_of_minpoly_coeff extendsVr_spectralValuation (fun _ hy' => minpoly_coeff_le_one hy')
    ι y hy

end Spectral

/-- **A Galois-invariant extension of `v_r` with residues from `ℤ̄`** (PROVED): the first three
conjuncts of `LocalGaloisDecomposition r hr`, by the spectral valuation. -/
theorem exists_invariant_extension (r : ℕ) (hr : r.Prime) :
    ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ) (w : Valuation (Qrbar r hr) Γ)
      (_hw : ExtendsVr w),
      (∀ (σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr) (y : Qrbar r hr), w (σ y) = w y) ∧
      (∀ (ι : Qbar →ₐ[ℚ] Qrbar r hr) (y : Qrbar r hr), w y ≤ 1 →
        ∃ x : Zbar, w (y - ι x) < 1) :=
  ⟨ℝ≥0, inferInstance, spectralValuation r hr, extendsVr_spectralValuation,
    spectralValuation_map_algEquiv, spectralValuation_residue⟩

/-- **`LocalGaloisDecomposition` from (dec) for the spectral valuation** (PROVED): (inv) and (res)
hold for `spectralValuation`, so only the extension of decomposition-group elements is needed. -/
theorem localGaloisDecomposition_of_spectral
    (hdec : ∀ (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ),
      g • centre (extendsVr_spectralValuation (r := r) (hr := hr)) ι =
        centre extendsVr_spectralValuation ι →
      ∃ σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr, ∀ x : Qbar, σ (ι x) = ι (g x)) :
    LocalGaloisDecomposition r hr :=
  ⟨ℝ≥0, inferInstance, spectralValuation r hr, extendsVr_spectralValuation,
    spectralValuation_map_algEquiv, spectralValuation_residue, hdec⟩

end ZInQ.Manuscript.RC.Wiring
