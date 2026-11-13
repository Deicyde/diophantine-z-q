import ZInQKernel.HDecomp.Conductor.LadicCond

/-! # unram-roots, metric part: inertia and roots of unity in `ℚ̄_p` (proved)

`inertiaSet` (from `LadicCond`) is the metric inertia group: `σ ∈ G_{ℚ_p}` with `‖σx − x‖ < 1`
for all `‖x‖ ≤ 1` in `ℚ̄_p = PadicAlgCl p`.

* `fix_of_mem_inertiaSet_of_pow_eq_one`: metric inertia fixes every root of unity of order prime to
  `p` (distinct such roots are at distance `1`).
* `mem_inertiaSet_of_fix`: an element of `G_{ℚ_p}` fixing every root of `X^{p^m} − X` (`m ≥ 1`) lies
  in the metric inertia group (every `x` with `‖x‖ ≤ 1` is congruent to such a root: the residue
  of `x` is algebraic over `𝔽_p`, so a root of `X^{p^m} − X` in the residue field, and the roots of
  `X^{p^m} − X` in `ℚ̄_p` reduce onto them).
-/

noncomputable section

namespace UnramRootsTask

open PkgI4 (GQp)
open LadicCond Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem norm_aut (σ : GQp p) (x : Kbar p) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem norm_natCast_eq_one {N : ℕ} (h : ¬ p ∣ N) : ‖(N : Kbar p)‖ = 1 := by
  have e : ((N : ℚ_[p]) : Kbar p) = (N : Kbar p) := map_natCast _ N
  rw [← e, PadicAlgCl.norm_extends]
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h)

theorem norm_add_le_max' (a b : Kbar p) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ :=
  IsUltrametricDist.norm_add_le_max a b

theorem norm_sub_le_max' (a b : Kbar p) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  exact (norm_add_le_max' a (-b)).trans (by rw [norm_neg])

theorem norm_sum_lt_one {ι : Type*} (s : Finset ι) (f : ι → Kbar p) (h : ∀ i ∈ s, ‖f i‖ < 1) :
    ‖∑ i ∈ s, f i‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (norm_add_le_max' _ _).trans_lt (max_lt (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- A root of unity of order prime to `p` congruent to `1` is `1`. -/
theorem eq_one_of_pow_eq_one {u : Kbar p} {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (hu : u ^ N = 1)
    (h1 : ‖u - 1‖ < 1) : u = 1 := by
  by_contra hne
  have hu1 : u - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hgeom : (∑ i ∈ Finset.range N, u ^ i) * (u - 1) = u ^ N - 1 := geom_sum_mul u N
  rw [hu, sub_self] at hgeom
  have hsum : ∑ i ∈ Finset.range N, u ^ i = 0 := (mul_eq_zero.mp hgeom).resolve_right hu1
  have hule : ‖u‖ ≤ 1 := by
    have : u = (u - 1) + 1 := by ring
    rw [this]
    exact (norm_add_le_max' _ _).trans (max_le h1.le (by rw [norm_one]))
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
      rw [this]
      refine (norm_add_le_max' _ _).trans_lt (max_lt ?_ h1)
      rw [norm_mul]
      calc ‖u‖ * ‖u ^ i - 1‖ ≤ 1 * ‖u ^ i - 1‖ :=
            mul_le_mul_of_nonneg_right hule (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact ih
  have hN1 : ‖(N : Kbar p)‖ = 1 := norm_natCast_eq_one hpN
  have : (N : Kbar p) = -∑ i ∈ Finset.range N, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  rw [this, norm_neg] at hN1
  exact absurd hN1 (norm_sum_lt_one _ _ fun i _ => hpow i).ne

/-- **Metric inertia fixes the roots of unity of order prime to `p`.** -/
theorem fix_of_mem_inertiaSet_of_pow_eq_one {σ : GQp p} (hσ : σ ∈ inertiaSet) {x : Kbar p}
    {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (hx : x ^ N = 1) : σ x = x := by
  have hxn : ‖x‖ = 1 := by
    have h := congrArg norm hx
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hN.ne').mp h
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxn
  have hy : (σ x) ^ N = 1 := by rw [← map_pow, hx, map_one]
  have hclose : ‖σ x - x‖ < 1 := hσ x hxn.le
  set u := σ x * x⁻¹ with hu
  have huN : u ^ N = 1 := by rw [hu, mul_pow, inv_pow, hy, hx, inv_one, mul_one]
  have hu1 : ‖u - 1‖ < 1 := by
    have : u - 1 = (σ x - x) * x⁻¹ := by rw [hu]; field_simp
    rw [this, norm_mul, norm_inv, hxn, inv_one, mul_one]
    exact hclose
  have := eq_one_of_pow_eq_one hN hpN huN hu1
  rw [hu] at this
  exact (mul_inv_eq_one₀ hx0).mp this

/-- Metric inertia fixes the roots of `X^M − X` when `p ∣ M`, `M > 1`. -/
theorem fix_of_mem_inertiaSet_of_pow_eq_self {σ : GQp p} (hσ : σ ∈ inertiaSet) {x : Kbar p}
    {M : ℕ} (hM : 1 < M) (hpM : p ∣ M) (hx : x ^ M = x) : σ x = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact map_zero σ
  have h1 : x ^ (M - 1) = 1 := by
    have : x ^ (M - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hM.le, one_mul, hx]
    exact mul_right_cancel₀ hx0 this
  refine fix_of_mem_inertiaSet_of_pow_eq_one hσ (by omega) ?_ h1
  intro hd
  have hp1 : p ∣ M - (M - 1) := Nat.dvd_sub hpM hd
  rw [Nat.sub_sub_self hM.le] at hp1
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hp1)

/-! ### The residue field of `ℚ̄_p` -/

/-- The unit ball of `ℚ̄_p` as a valuation subring. -/
abbrev OO (p : ℕ) [Fact p.Prime] : ValuationSubring (Kbar p) :=
  (PadicAlgCl.valued p).v.valuationSubring

theorem mem_OO {x : Kbar p} : x ∈ OO p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff]
  change ‖x‖₊ ≤ 1 ↔ _
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

theorem residue_eq_zero_iff (a : OO p) :
    IsLocalRing.residue (OO p) a = 0 ↔ ‖(a : Kbar p)‖ < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change ‖(a : Kbar p)‖₊ < 1 ↔ _
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]

/-- `ℤ_p → 𝒪_{ℚ̄_p}`. -/
def zpToOO (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* OO p :=
  ((algebraMap ℚ_[p] (Kbar p)).comp PadicInt.Coe.ringHom).codRestrict (OO p) (fun c => by
    rw [mem_OO]
    change ‖((c : ℚ_[p]) : Kbar p)‖ ≤ 1
    rw [PadicAlgCl.norm_extends]
    exact c.2)

theorem coe_zpToOO (c : ℤ_[p]) : ((zpToOO p c : OO p) : Kbar p) = algebraMap ℚ_[p] _ c := rfl

/-- **Every `x` with `‖x‖ ≤ 1` satisfies `‖x^{p^m} − x‖ < 1` for some `m ≥ 1`.** -/
theorem exists_pow_sub_lt_one {x : Kbar p} (hx : ‖x‖ ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ‖x ^ p ^ m - x‖ < 1 := by
  set k := IsLocalRing.ResidueField (OO p)
  set r := IsLocalRing.residue (OO p)
  have hp : p.Prime := Fact.out
  -- `k` has characteristic `p`
  have hpk : ((p : ℕ) : k) = 0 := by
    rw [← map_natCast r p, residue_eq_zero_iff]
    change ‖((p : OO p) : Kbar p)‖ < 1
    rw [show ((p : OO p) : Kbar p) = ((p : ℚ_[p]) : Kbar p) by simp, PadicAlgCl.norm_extends,
      Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 hpk
  -- the minimal polynomial of `x` has integral coefficients
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  set g := minpoly ℚ_[p] x with hg
  have hgm : g.Monic := minpoly.monic hint
  have hcoeff : ∀ n, ‖g.coeff n‖ ≤ 1 := by
    have : spectralValue g ≤ 1 := by
      have e : spectralNorm ℚ_[p] (Kbar p) x = spectralValue g := rfl
      rw [← e, PadicAlgCl.spectralNorm_eq]; exact hx
    exact (spectralValue_le_one_iff hgm).1 this
  have hlifts : g ∈ Polynomial.lifts (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨g.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨gZ, hgZ, -, hgZm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hgm
  set ψ : ℤ_[p] →+* k := r.comp (zpToOO p)
  set gk : k[X] := gZ.map ψ
  have hgk0 : gk ≠ 0 := (hgZm.map ψ).ne_zero
  set x' : OO p := ⟨x, mem_OO.mpr hx⟩
  set y : k := r x'
  -- `y` is a root of `gk`
  have hroot : gk.eval y = 0 := by
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ (r.comp (zpToOO p)) (r x') gZ = 0
    rw [← Polynomial.hom_eval₂]
    have : Polynomial.eval₂ (zpToOO p) x' gZ = 0 := by
      apply Subtype.ext
      change (OO p).subtype (Polynomial.eval₂ (zpToOO p) x' gZ) = 0
      rw [Polynomial.hom_eval₂]
      have e : (OO p).subtype.comp (zpToOO p) =
          (algebraMap ℚ_[p] (Kbar p)).comp PadicInt.Coe.ringHom := RingHom.ext fun _ => rfl
      rw [e, ← Polynomial.eval₂_map, hgZ]
      exact minpoly.aeval ℚ_[p] x
    rw [this, map_zero]
  -- the coefficients of `gk` are fixed by Frobenius
  have hψ : ∀ c : ℤ_[p], (ψ c) ^ p = ψ c := by
    intro c
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range c
    have h0 : ψ (c - n) = 0 := by
      change r (zpToOO p (c - n)) = 0
      rw [residue_eq_zero_iff, coe_zpToOO, PadicAlgCl.norm_extends]
      exact (PadicInt.mem_nonunits.mp hn :)
    have hc : ψ c = (n : k) := by
      rw [map_sub, sub_eq_zero, map_natCast] at h0; exact h0
    rw [hc, ← frobenius_def, map_natCast]
  have hfrob : ∀ z : k, gk.eval z = 0 → gk.eval (z ^ p) = 0 := by
    intro z hz
    have e : gk.map (frobenius k p) = gk := by
      ext n
      rw [Polynomial.coeff_map, frobenius_def, Polynomial.coeff_map, hψ]
    calc gk.eval (z ^ p) = (gk.map (frobenius k p)).eval (frobenius k p z) := by
          rw [e, frobenius_def]
      _ = frobenius k p (gk.eval z) := by
          rw [Polynomial.eval_map, Polynomial.eval, Polynomial.hom_eval₂, RingHom.comp_id]
      _ = 0 := by rw [hz, map_zero]
  have hall : ∀ i : ℕ, y ^ p ^ i ∈ {z : k | IsRoot gk z} := by
    intro i
    induction i with
    | zero => simpa using hroot
    | succ i ih =>
      rw [pow_succ, pow_mul]
      exact hfrob _ ih
  obtain ⟨i, j, hij, hyij⟩ := (Polynomial.finite_setOfPred_isRoot hgk0).exists_lt_map_eq_of_forall_mem hall
  refine ⟨j - i, by omega, ?_⟩
  have hy : y ^ p ^ (j - i) = y := by
    have hinj := (iterateFrobenius k p i).injective
    apply hinj
    rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, Nat.sub_add_cancel hij.le]
    exact hyij.symm
  have : r (x' ^ p ^ (j - i) - x') = 0 := by rw [map_sub, map_pow, hy, sub_self]
  rw [residue_eq_zero_iff] at this
  simpa using this

theorem norm_le_one_of_pow_eq_self {t : Kbar p} {M : ℕ} (hM : 1 < M) (ht : t ^ M = t) :
    ‖t‖ ≤ 1 := by
  by_contra h
  push Not at h
  have h1 : ‖t‖ ^ 1 < ‖t‖ ^ M := pow_lt_pow_right₀ h hM
  rw [pow_one, ← norm_pow, ht] at h1
  exact lt_irrefl _ h1

/-- If `‖x^M − x‖ < 1` then `x` is congruent to a root of `X^M − X`. -/
theorem exists_root_close {x : Kbar p} (hx : ‖x‖ ≤ 1) {M : ℕ} (hM : 1 < M)
    (hlt : ‖x ^ M - x‖ < 1) : ∃ t : Kbar p, t ^ M = t ∧ ‖x - t‖ < 1 := by
  set P : (Kbar p)[X] := X ^ M - X with hP
  have hPm : P.Monic := monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hM)
  have hprod : (P.roots.map fun a => X - C a).prod = P :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm IsAlgClosed.card_roots_eq_natDegree
  have heval : P.eval x = (P.roots.map fun a => x - a).prod := by
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    simp
  by_contra hne
  push Not at hne
  have hroot : ∀ a ∈ P.roots, ‖x - a‖ = 1 := by
    intro a ha
    have ha' : a ^ M = a := by
      have := (mem_roots hPm.ne_zero).1 ha
      simpa [P, sub_eq_zero] using this
    exact le_antisymm ((norm_sub_le_max' _ _).trans (max_le hx
      (norm_le_one_of_pow_eq_self hM ha'))) (hne a ha')
  have h1 : ‖P.eval x‖ = 1 := by
    rw [heval]
    change (normHom : Kbar p →*₀ ℝ) _ = 1
    rw [map_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_one
    intro c hc
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hc
    exact hroot a ha
  have : P.eval x = x ^ M - x := by simp [P]
  rw [this] at h1
  exact absurd h1 hlt.ne

/-- **An element of `G_{ℚ_p}` fixing the roots of every `X^{p^m} − X` (`m ≥ 1`) lies in the metric
inertia group.** -/
theorem mem_inertiaSet_of_fix {σ : GQp p}
    (h : ∀ m : ℕ, 0 < m → ∀ t : Kbar p, t ^ p ^ m = t → σ t = t) : σ ∈ inertiaSet := by
  intro x hx
  obtain ⟨m, hm, hlt⟩ := exists_pow_sub_lt_one hx
  have hM : 1 < p ^ m := Nat.one_lt_pow hm.ne' (Fact.out : p.Prime).one_lt
  obtain ⟨t, ht, hxt⟩ := exists_root_close hx hM hlt
  have hσt := h m hm t ht
  have e : σ x - x = σ (x - t) - (x - t) := by rw [map_sub, hσt]; ring
  rw [e]
  refine (norm_sub_le_max' _ _).trans_lt ?_
  rw [norm_aut, max_self]
  exact hxt

end UnramRootsTask
