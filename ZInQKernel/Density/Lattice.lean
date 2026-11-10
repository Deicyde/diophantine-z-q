import ZInQKernel.Density.PrimeTail
import ZInQKernel.Density.Description

/-!
# The lattice count for large `ℓ` (pd-paper Proposition 4.1)

`InClass p` (pd-lean-1, `Description.lean`) is the congruence class of Proposition 1.6
(`p ≡ 1 (mod 8)` and `p mod 7 ∈ {3, 5, 6}`), and `BadSetOf c ℓ` is the set `Bad_ℓ` of §2.1 for a function `c : ℕ → ℤ`
(the instance used is `c = cp`; see `PropD.lean`).

The count uses only the representation `p = c_p² + e²` of a class prime (Proposition 1.6(1)),
taken as the hypothesis `hrep`:

* `card_latticePts_le`: `#{(c, e) ∈ [−√N, √N]² : c ≠ 0, ℓ ∣ c, ℓ ∣ e² + 1} ≤ 8N/ℓ² + 4√N/ℓ`,
  and the set is empty if `ℓ > √N`;
* `card_badSet_le_latticePts`: `p ↦ (c_p, e_p)` embeds `Bad_ℓ ∩ [0, N]` into it;
* `sum_card_badSet_large_le` (Proposition 4.1): the sum over primes `ℓ` with `ℓ⁴ > N` is at most
  `20 N^{3/4}`.
-/

namespace ZInQ.Density

open Finset

/-- `Bad_ℓ` (§2.1) for a function `c : ℕ → ℤ`: the class primes `p` with `ℓ ∣ c p` and
`ℓ ∣ p + 1`. -/
def BadSetOf (c : ℕ → ℤ) (ℓ : ℕ) : Set ℕ :=
  {p | p.Prime ∧ InClass p ∧ (ℓ : ℤ) ∣ c p ∧ ℓ ∣ p + 1}

/-- The lattice points `(c, e) ∈ [−√N, √N]²` with `c ≠ 0`, `ℓ ∣ c` and `ℓ ∣ e² + 1`. -/
def latticePts (ℓ N : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(Nat.sqrt N : ℤ)) (Nat.sqrt N)) ×ˢ (Icc (-(Nat.sqrt N : ℤ)) (Nat.sqrt N))).filter
    (fun ce => ce.1 ≠ 0 ∧ (ℓ : ℤ) ∣ ce.1 ∧ (ℓ : ℤ) ∣ ce.2 ^ 2 + 1)

/-- A residue class modulo `ℓ` meets `[−s, s]` in at most `2s/ℓ + 1` integers. -/
theorem card_Icc_filter_modEq_le (s ℓ : ℕ) (hℓ : 0 < ℓ) (r : ℤ) :
    (((Icc (-(s : ℤ)) s).filter (fun x => x ≡ r [ZMOD ℓ])).card : ℝ) ≤ 2 * s / ℓ + 1 := by
  have hℓz : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  set q : ℕ := (2 * s) / ℓ with hq
  clear_value q
  have hmaps : ∀ x ∈ (Icc (-(s : ℤ)) s).filter (fun x => x ≡ r [ZMOD ℓ]),
      (x + s) / ℓ ∈ Icc (0 : ℤ) q := by
    intro x hx
    obtain ⟨hx1, -⟩ := mem_filter.1 hx
    obtain ⟨h1, h2⟩ := mem_Icc.1 hx1
    refine mem_Icc.2 ⟨Int.ediv_nonneg (by omega) hℓz.le, ?_⟩
    have : ((q : ℕ) : ℤ) = (2 * (s : ℤ)) / (ℓ : ℤ) := by
      rw [hq, Int.natCast_div]; push_cast; rfl
    exact (Int.ediv_le_ediv hℓz (show x + s ≤ 2 * (s : ℤ) by omega)).trans_eq this.symm
  have hinj : Set.InjOn (fun x : ℤ => (x + s) / ℓ)
      ((Icc (-(s : ℤ)) s).filter (fun x => x ≡ r [ZMOD ℓ])) := by
    intro x hx y hy hxy
    have hx' := (mem_filter.1 hx).2
    have hy' := (mem_filter.1 hy).2
    have hmod : (x + s) % ℓ = (y + s) % ℓ := (hx'.trans hy'.symm).add_right _
    have e1 := Int.mul_ediv_add_emod (x + s) ℓ
    have e2 := Int.mul_ediv_add_emod (y + s) ℓ
    simp only at hxy
    rw [hxy, hmod] at e1
    linarith
  have hcard := card_le_card_of_injOn _ hmaps hinj
  rw [Int.card_Icc] at hcard
  have h3 : ((q : ℤ) + 1 - 0).toNat = q + 1 := by omega
  rw [h3] at hcard
  have h4 : ((q : ℕ) : ℝ) ≤ 2 * s / ℓ := by
    rw [hq]
    exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := 2 * s) (n := ℓ)).trans (by push_cast; rfl)
  calc (((Icc (-(s : ℤ)) s).filter (fun x => x ≡ r [ZMOD ℓ])).card : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ 2 * s / ℓ + 1 := by push_cast; linarith

/-- The first coordinates: `#{c ∈ [−s, s] : c ≠ 0, ℓ ∣ c} ≤ 2s/ℓ`. -/
theorem card_first_le (s ℓ : ℕ) (hℓ : 0 < ℓ) :
    (((Icc (-(s : ℤ)) s).filter (fun c => c ≠ 0 ∧ (ℓ : ℤ) ∣ c)).card : ℝ) ≤ 2 * s / ℓ := by
  set A := (Icc (-(s : ℤ)) s).filter (fun c => c ≠ 0 ∧ (ℓ : ℤ) ∣ c) with hA
  set C := (Icc (-(s : ℤ)) s).filter (fun x => x ≡ 0 [ZMOD ℓ]) with hC
  have hsub : A ⊆ C.erase 0 := by
    intro c hc
    simp only [hA, mem_filter] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    exact mem_erase.2 ⟨h2, mem_filter.2 ⟨h1, Int.modEq_zero_iff_dvd.2 h3⟩⟩
  have h0 : (0 : ℤ) ∈ C := mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, Int.ModEq.refl 0⟩
  have hc := card_le_card hsub
  rw [card_erase_of_mem h0] at hc
  have hpos := card_pos.2 ⟨0, h0⟩
  have h5 := card_Icc_filter_modEq_le s ℓ hℓ 0
  have : (A.card : ℝ) + 1 ≤ (C.card : ℝ) := by exact_mod_cast (by omega)
  linarith

/-- The first coordinates are empty when `s < ℓ`. -/
theorem first_eq_empty (s ℓ : ℕ) (h : s < ℓ) :
    (Icc (-(s : ℤ)) s).filter (fun c => c ≠ 0 ∧ (ℓ : ℤ) ∣ c) = ∅ := by
  refine filter_eq_empty_iff.2 fun c hc ⟨h1, h2⟩ => ?_
  obtain ⟨k, rfl⟩ := h2
  have hk : k ≠ 0 := by rintro rfl; simp at h1
  obtain ⟨hc1, hc2⟩ := mem_Icc.1 hc
  have : (ℓ : ℤ) ≤ |(ℓ : ℤ) * k| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hk)
  have := abs_le.2 ⟨hc1, hc2⟩
  omega

/-- The second coordinates: `#{e ∈ [−s, s] : ℓ ∣ e² + 1} ≤ 2(2s/ℓ + 1)` for a prime `ℓ`. -/
theorem card_second_le (s ℓ : ℕ) (hℓ : ℓ.Prime) :
    (((Icc (-(s : ℤ)) s).filter (fun e => (ℓ : ℤ) ∣ e ^ 2 + 1)).card : ℝ) ≤
      2 * (2 * s / ℓ + 1) := by
  set B := (Icc (-(s : ℤ)) s).filter (fun e => (ℓ : ℤ) ∣ e ^ 2 + 1) with hB
  rcases B.eq_empty_or_nonempty with h | ⟨e₀, he₀⟩
  · rw [h, card_empty, Nat.cast_zero]; positivity
  have hℓz : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hsub : B ⊆ (Icc (-(s : ℤ)) s).filter (fun x => x ≡ e₀ [ZMOD ℓ]) ∪
      (Icc (-(s : ℤ)) s).filter (fun x => x ≡ -e₀ [ZMOD ℓ]) := by
    intro e he
    obtain ⟨he1, he2⟩ := mem_filter.1 he
    have h0 := (mem_filter.1 he₀).2
    have hd : (ℓ : ℤ) ∣ (e₀ - e) * (e₀ + e) := by
      have := dvd_sub h0 he2
      convert this using 1; ring
    rcases hℓz.dvd_or_dvd hd with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨he1, Int.modEq_iff_dvd.2 h⟩)
    · refine mem_union_right _ (mem_filter.2 ⟨he1, Int.modEq_iff_dvd.2 ?_⟩)
      have : -e₀ - e = -(e₀ + e) := by ring
      rw [this]; exact (dvd_neg).2 h
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have h1 := card_Icc_filter_modEq_le s ℓ hℓ.pos e₀
  have h2 := card_Icc_filter_modEq_le s ℓ hℓ.pos (-e₀)
  have : (B.card : ℝ) ≤ (((Icc (-(s : ℤ)) s).filter (fun x => x ≡ e₀ [ZMOD ℓ])).card : ℝ) +
      (((Icc (-(s : ℤ)) s).filter (fun x => x ≡ -e₀ [ZMOD ℓ])).card : ℝ) := by
    exact_mod_cast hc
  linarith

/-- **The lattice count.** `#latticePts ℓ N ≤ 8N/ℓ² + 4√N/ℓ` for a prime `ℓ`; the second term
can be dropped when `ℓ > √N` (then the set is empty). -/
theorem card_latticePts_le (ℓ N : ℕ) (hℓ : ℓ.Prime) :
    ((latticePts ℓ N).card : ℝ) ≤
      8 * N / (ℓ : ℝ) ^ 2 + (if ℓ ≤ Nat.sqrt N then 4 * Real.sqrt N / ℓ else 0) := by
  set s := Nat.sqrt N with hs
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.pos
  have hsub : latticePts ℓ N ⊆ (Icc (-(s : ℤ)) s).filter (fun c => c ≠ 0 ∧ (ℓ : ℤ) ∣ c) ×ˢ
      (Icc (-(s : ℤ)) s).filter (fun e => (ℓ : ℤ) ∣ e ^ 2 + 1) := by
    intro ce hce
    simp only [latticePts, mem_filter, mem_product] at hce
    simp only [mem_product, mem_filter]
    exact ⟨⟨hce.1.1, hce.2.1, hce.2.2.1⟩, hce.1.2, hce.2.2.2⟩
  have hc := card_le_card hsub
  rw [card_product] at hc
  have hN0 : (0 : ℝ) ≤ 8 * N / (ℓ : ℝ) ^ 2 := by positivity
  split_ifs with h
  · have h1 := card_first_le s ℓ hℓ.pos
    have h2 := card_second_le s ℓ hℓ
    have hsN : (s : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
    have hs2 : ((s : ℝ)) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
    have hA0 : (0 : ℝ) ≤ (((Icc (-(s : ℤ)) s).filter (fun c => c ≠ 0 ∧ (ℓ : ℤ) ∣ c)).card : ℝ) :=
      Nat.cast_nonneg _
    calc ((latticePts ℓ N).card : ℝ)
        ≤ (((Icc (-(s : ℤ)) s).filter (fun c => c ≠ 0 ∧ (ℓ : ℤ) ∣ c)).card : ℝ) *
          (((Icc (-(s : ℤ)) s).filter (fun e => (ℓ : ℤ) ∣ e ^ 2 + 1)).card : ℝ) := by
          exact_mod_cast hc
      _ ≤ (2 * s / ℓ) * (2 * (2 * s / ℓ + 1)) := by
          apply mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
      _ = 8 * (s : ℝ) ^ 2 / (ℓ : ℝ) ^ 2 + 4 * s / ℓ := by field_simp; ring
      _ ≤ 8 * N / (ℓ : ℝ) ^ 2 + 4 * Real.sqrt N / ℓ := by gcongr
  · rw [first_eq_empty s ℓ (by omega), card_empty, zero_mul] at hc
    have : latticePts ℓ N = ∅ := by
      rw [← card_eq_zero]; omega
    rw [this, card_empty, Nat.cast_zero, add_zero]
    exact hN0

open Classical in
/-- `p ↦ (c_p, e_p)` embeds `Bad_ℓ ∩ [0, N]` into the lattice points. -/
theorem card_badSet_le_latticePts (c : ℕ → ℤ)
    (hrep : ∀ p : ℕ, p.Prime → InClass p → ∃ e : ℤ, (p : ℤ) = c p ^ 2 + e ^ 2) (ℓ N : ℕ) :
    ((range (N + 1)).filter (· ∈ BadSetOf c ℓ)).card ≤ (latticePts ℓ N).card := by
  choose! e he using hrep
  refine card_le_card_of_injOn (fun p => (c p, e p)) ?_ ?_
  · intro p hp
    rw [mem_coe, mem_filter] at hp
    obtain ⟨hp1, hpr, hcl, hdc, hd1⟩ := hp
    rw [mem_coe]
    have hpN : p ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hp1)
    have hrp := he p hpr hcl
    have hsq : ∀ z : ℤ, z ^ 2 ≤ (p : ℤ) → -(Nat.sqrt N : ℤ) ≤ z ∧ z ≤ Nat.sqrt N := by
      intro z hz
      have h1 : z.natAbs ^ 2 ≤ N := by
        have : ((z.natAbs ^ 2 : ℕ) : ℤ) ≤ N := by
          push_cast; rw [sq_abs]; exact hz.trans (by exact_mod_cast hpN)
        exact_mod_cast this
      have h2 : z.natAbs ≤ Nat.sqrt N := Nat.le_sqrt'.2 h1
      have h3 : |z| ≤ (Nat.sqrt N : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h2
      exact abs_le.1 h3
    have hc0 : c p ≠ 0 := by
      intro h0
      rw [h0] at hrp
      have hp' : p = (e p).natAbs * (e p).natAbs := by
        have : ((p : ℕ) : ℤ) = (((e p).natAbs * (e p).natAbs : ℕ) : ℤ) := by
          push_cast; rw [← sq, sq_abs]; linarith
        exact_mod_cast this
      rw [hp'] at hpr
      rcases Nat.prime_mul_iff.1 hpr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] at h1 <;>
        exact Nat.not_prime_one h1
    unfold latticePts
    refine mem_filter.2 ⟨mem_product.2 ⟨mem_Icc.2 (hsq _ (by nlinarith [sq_nonneg (e p)])),
      mem_Icc.2 (hsq _ (by nlinarith [sq_nonneg (c p)]))⟩, hc0, hdc, ?_⟩
    have h1 : (ℓ : ℤ) ∣ (p : ℤ) + 1 := by exact_mod_cast hd1
    have h2 : (ℓ : ℤ) ∣ c p ^ 2 := dvd_pow hdc two_ne_zero
    have := dvd_sub h1 h2
    convert this using 1
    rw [hrp]; ring
  · intro p hp q hq hpq
    simp only [Prod.mk.injEq] at hpq
    have hp' := (mem_filter.1 (mem_coe.1 hp)).2
    have hq' := (mem_filter.1 (mem_coe.1 hq)).2
    have e1 := he p hp'.1 hp'.2.1
    have e2 := he q hq'.1 hq'.2.1
    rw [hpq.1, hpq.2] at e1
    exact_mod_cast e1.trans e2.symm

/-- `Σ_{ℓ ∈ F} ℓ^{−2} ≤ 2/(a + 1)` for a finite set `F` of naturals `> a`. -/
theorem sum_inv_sq_le_of_gt (a : ℕ) (F : Finset ℕ) (hF : ∀ ℓ ∈ F, a < ℓ) :
    ∑ ℓ ∈ F, (1 : ℝ) / (ℓ : ℝ) ^ 2 ≤ 2 / ((a : ℝ) + 1) := by
  set M := F.sup id with hM
  have hFM : F ⊆ range (M + 1) := fun ℓ hℓ =>
    mem_range.2 (Nat.lt_succ_of_le (le_sup (f := id) hℓ))
  have hterm : ∀ ℓ : ℕ, 0 < ℓ → (1 : ℝ) / (ℓ : ℝ) ^ 2 ≤ 2 * (1 / (ℓ : ℝ) - 1 / ((ℓ : ℝ) + 1)) := by
    intro ℓ hℓ
    have h : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
    have e2 : 2 * (1 / (ℓ : ℝ) - 1 / ((ℓ : ℝ) + 1)) = 2 / ((ℓ : ℝ) * ((ℓ : ℝ) + 1)) := by
      field_simp; ring
    rw [e2, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    nlinarith
  have hnn : ∀ m : ℕ, 0 ≤ (if a < m then (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) else 0) := by
    intro m
    split_ifs with h
    · have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      rw [sub_nonneg]; exact one_div_le_one_div_of_le this (by linarith)
    · exact le_rfl
  calc ∑ ℓ ∈ F, (1 : ℝ) / (ℓ : ℝ) ^ 2
      ≤ ∑ ℓ ∈ F, 2 * (if a < ℓ then (1 / (ℓ : ℝ) - 1 / ((ℓ : ℝ) + 1)) else 0) :=
        sum_le_sum fun ℓ hℓ => by simp only [hF ℓ hℓ, ↓reduceIte]; exact hterm ℓ (by have := hF ℓ hℓ; omega)
    _ = 2 * ∑ ℓ ∈ F, (if a < ℓ then (1 / (ℓ : ℝ) - 1 / ((ℓ : ℝ) + 1)) else 0) := by rw [mul_sum]
    _ ≤ 2 * ∑ m ∈ range (M + 1), (if a < m then (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) else 0) := by
        exact mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hFM fun m _ _ => hnn m) (by norm_num)
    _ = 2 * (1 / ((a : ℝ) + 1) - 1 / (max (M + 1) (a + 1) : ℕ)) := by rw [sum_tel_gt]
    _ ≤ 2 / ((a : ℝ) + 1) := by
        have : 0 ≤ 1 / ((max (M + 1) (a + 1) : ℕ) : ℝ) := by positivity
        rw [div_eq_mul_one_div 2]
        linarith

/-- The sum of the lattice counts over primes `ℓ` with `ℓ⁴ > N` is at most `20 N^{3/4}`. -/
theorem sum_card_latticePts_le {N : ℕ} (hN : 1 ≤ N) (F : Finset ℕ)
    (hF : ∀ ℓ ∈ F, ℓ.Prime ∧ N < ℓ ^ 4) :
    ∑ ℓ ∈ F, ((latticePts ℓ N).card : ℝ) ≤ 20 * (N : ℝ) ^ ((3 : ℝ) / 4) := by
  set s := Nat.sqrt N with hs
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set X : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hNr (by norm_num)
  have hX0 : 0 < X := by linarith
  have hXl : ∀ ℓ ∈ F, X < ℓ := by
    intro ℓ hℓ
    have h4 : (N : ℝ) < (ℓ : ℝ) ^ 4 := by exact_mod_cast (hF ℓ hℓ).2
    have e : ((1 : ℝ) / 4) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
    rw [hX, e]
    have h := Real.rpow_lt_rpow (by positivity) h4 (show (0 : ℝ) < ((4 : ℕ) : ℝ)⁻¹ by norm_num)
    rwa [Real.pow_rpow_inv_natCast (Nat.cast_nonneg ℓ) (by norm_num)] at h
  have hNX : (N : ℝ) / X = (N : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [div_eq_iff hX0.ne', hX, ← Real.rpow_add (by linarith),
      show (3 : ℝ) / 4 + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have hsqrt : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by positivity)
  -- the `1/ℓ²` part
  set a := ⌊X⌋₊ with ha
  have haX : X < (a : ℝ) + 1 := Nat.lt_floor_add_one X
  have hal : ∀ ℓ ∈ F, a < ℓ := by
    intro ℓ hℓ
    have : (a : ℝ) < ℓ := (Nat.floor_le hX0.le).trans_lt (hXl ℓ hℓ)
    exact_mod_cast this
  have hsum1 : ∑ ℓ ∈ F, (1 : ℝ) / (ℓ : ℝ) ^ 2 ≤ 2 / X := by
    refine (sum_inv_sq_le_of_gt a F hal).trans ?_
    exact div_le_div_of_nonneg_left (by norm_num) hX0 haX.le
  -- the `√N/ℓ` part
  have hsum2 : ∑ ℓ ∈ F, (if ℓ ≤ s then 4 * Real.sqrt N / ℓ else 0) ≤ 4 * N / X := by
    rw [← sum_filter]
    have hcardF : ((F.filter (· ≤ s)).card : ℝ) ≤ Real.sqrt N := by
      have : F.filter (· ≤ s) ⊆ Icc 1 s := by
        intro ℓ hℓ
        obtain ⟨h1, h2⟩ := mem_filter.1 hℓ
        exact mem_Icc.2 ⟨(hF ℓ h1).1.one_lt.le, h2⟩
      have := card_le_card this
      rw [Nat.card_Icc, Nat.add_sub_cancel] at this
      exact (Nat.cast_le.2 this).trans Real.nat_sqrt_le_real_sqrt
    calc ∑ ℓ ∈ F.filter (· ≤ s), 4 * Real.sqrt N / ℓ
        ≤ ∑ ℓ ∈ F.filter (· ≤ s), 4 * Real.sqrt N / X := by
          refine sum_le_sum fun ℓ hℓ => ?_
          exact div_le_div_of_nonneg_left (by positivity) hX0 (hXl ℓ (mem_filter.1 hℓ).1).le
      _ = ((F.filter (· ≤ s)).card : ℝ) * (4 * Real.sqrt N / X) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ Real.sqrt N * (4 * Real.sqrt N / X) := by gcongr
      _ = 4 * (Real.sqrt N * Real.sqrt N) / X := by ring
      _ = 4 * N / X := by rw [hsqrt]
  calc ∑ ℓ ∈ F, ((latticePts ℓ N).card : ℝ)
      ≤ ∑ ℓ ∈ F, (8 * N / (ℓ : ℝ) ^ 2 + (if ℓ ≤ s then 4 * Real.sqrt N / ℓ else 0)) :=
        sum_le_sum fun ℓ hℓ => card_latticePts_le ℓ N (hF ℓ hℓ).1
    _ = 8 * N * ∑ ℓ ∈ F, (1 : ℝ) / (ℓ : ℝ) ^ 2 +
          ∑ ℓ ∈ F, (if ℓ ≤ s then 4 * Real.sqrt N / ℓ else 0) := by
        rw [sum_add_distrib, mul_sum]; congr 1
        refine sum_congr rfl fun ℓ _ => by ring
    _ ≤ 8 * N * (2 / X) + 4 * N / X := by gcongr
    _ = 20 * ((N : ℝ) / X) := by ring
    _ = 20 * (N : ℝ) ^ ((3 : ℝ) / 4) := by rw [hNX]

open Classical in
/-- **Proposition 4.1, per prime.** `#(Bad_ℓ ∩ [0, N]) ≤ 8N/ℓ² + 4√N/ℓ`, and the second term
vanishes when `ℓ > √N` (indeed the whole count does). -/
theorem card_badSet_le (c : ℕ → ℤ)
    (hrep : ∀ p : ℕ, p.Prime → InClass p → ∃ e : ℤ, (p : ℤ) = c p ^ 2 + e ^ 2) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (N : ℕ) :
    (((range (N + 1)).filter (· ∈ BadSetOf c ℓ)).card : ℝ) ≤
      8 * N / (ℓ : ℝ) ^ 2 + (if ℓ ≤ Nat.sqrt N then 4 * Real.sqrt N / ℓ else 0) :=
  (Nat.cast_le.2 (card_badSet_le_latticePts c hrep ℓ N)).trans (card_latticePts_le ℓ N hℓ)

open Classical in
/-- **Proposition 4.1.** For `N ≥ 1` and a finite set `F` of primes `ℓ` with `ℓ⁴ > N`,
`Σ_{ℓ ∈ F} #(Bad_ℓ ∩ [0, N]) ≤ 20 N^{3/4}`. -/
theorem sum_card_badSet_large_le (c : ℕ → ℤ)
    (hrep : ∀ p : ℕ, p.Prime → InClass p → ∃ e : ℤ, (p : ℤ) = c p ^ 2 + e ^ 2) {N : ℕ}
    (hN : 1 ≤ N) (F : Finset ℕ) (hF : ∀ ℓ ∈ F, ℓ.Prime ∧ N < ℓ ^ 4) :
    ∑ ℓ ∈ F, (((range (N + 1)).filter (· ∈ BadSetOf c ℓ)).card : ℝ) ≤
      20 * (N : ℝ) ^ ((3 : ℝ) / 4) :=
  (sum_le_sum fun ℓ _ => Nat.cast_le.2 (card_badSet_le_latticePts c hrep ℓ N)).trans
    (sum_card_latticePts_le hN F hF)

end ZInQ.Density
