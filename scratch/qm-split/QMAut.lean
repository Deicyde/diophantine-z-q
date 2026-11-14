import TailK

/-!
# qm-split, rows H-61 `QMAutCard` and H-63 `ALFixedPoints`

Both rows (`HDec.HeckeRest.QMAutCard`, `HDec.HeckeRest.ALFixedPoints`, leaf-fold4 chain `TailG.lean`
l.9932, l.9958; imported) are proved from one published-form leaf `QMCentralizerCM` (the description of
`End_𝒪(A)` at points of `X₆`: `ℤ`, or an order `Φ⁻¹(𝒪)` optimally embedded by some `Φ : k → B`, `k`
imaginary quadratic) by computation:

* §1 imaginary quadratic fields: a non-rational element has negative discriminant (`disc_neg`), from
  `IsTotallyComplex` (a nonnegative discriminant makes every complex embedding real);
* §2 elements of `B`: `x² − trd(x) x + nrd(x) = 0`; for `R = Φ⁻¹(𝒪)` every unit is `±1` or a root of
  `u² + 1`, `u² ∓ u + 1` (`unit_cases`: `nrd = 1` on units, `trd ∈ ℤ`, `trd² < 4`);
* §3 counting `Rˣ` (`4`, `6`, `2`) and the exclusivity of the three CM types;
* §4 `QMIso q q ≃ (com q)ˣ`, transport along `com q ≃+* R`, and the two rows.

Check: `scratch/qm-split/chk.sh scratch/qm-split/QMAut.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMSplit.Aut

open NumberField

/-! ## §1 Imaginary quadratic fields -/

section Imag

variable {k : Type} [Field k] [NumberField k] [IsTotallyComplex k] (hk : Module.finrank ℚ k = 2)
include hk

/-- In a quadratic field, a non-rational `y` spans with `1`. -/
theorem span_two {y : k} (hy : ∀ c : ℚ, y ≠ algebraMap ℚ k c) (x : k) :
    ∃ a b : ℚ, x = algebraMap ℚ k a + algebraMap ℚ k b * y := by
  have hni : ¬ LinearIndependent ℚ ![(1 : k), y, x] := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [hk] at this; simp at this
  rw [Fintype.not_linearIndependent_iff] at hni
  obtain ⟨g, hg, i, hi⟩ := hni
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  by_cases h2 : g 2 = 0
  · exfalso
    rw [h2, zero_smul, add_zero] at hg
    by_cases h1 : g 1 = 0
    · rw [h1, zero_smul, add_zero, smul_eq_zero] at hg
      rcases hg with hg | hg
      · fin_cases i <;> simp_all
      · exact one_ne_zero hg
    · apply hy (-(g 0) / g 1)
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hg
      have hg1 : algebraMap ℚ k (g 1) ≠ 0 := by simpa using h1
      field_simp
      simp only [map_neg, map_div₀]
      field_simp
      linear_combination hg
  · refine ⟨-(g 0) / g 2, -(g 1) / g 2, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_one] at hg
    have hg2 : algebraMap ℚ k (g 2) ≠ 0 := by simpa using h2
    simp only [map_neg, map_div₀]
    field_simp
    linear_combination hg

/-- **A non-rational element of an imaginary quadratic field has negative discriminant.** -/
theorem disc_neg {y : k} (hy : ∀ c : ℚ, y ≠ algebraMap ℚ k c) {t n : ℚ}
    (h : y * y - algebraMap ℚ k t * y + algebraMap ℚ k n = 0) : t ^ 2 < 4 * n := by
  by_contra hle
  push Not at hle
  obtain ⟨φ⟩ : Nonempty (k →+* ℂ) := inferInstance
  apply IsTotallyComplex.complexEmbedding_not_isReal φ
  rw [ComplexEmbedding.isReal_iff]
  -- `φ y` is real
  have hφy : (starRingEnd ℂ) (φ y) = φ y := by
    have hq := congrArg φ h
    simp only [map_sub, map_add, map_mul, map_zero, eq_ratCast, map_ratCast] at hq
    set z := φ y
    set D : ℝ := t ^ 2 - 4 * n
    have hle' : ((4 * n : ℚ) : ℝ) ≤ ((t ^ 2 : ℚ) : ℝ) := by exact_mod_cast hle
    have hD : 0 ≤ D := by simp only [D]; push_cast at hle' ⊢; linarith
    have hsq : (2 * z - t) ^ 2 = ((Real.sqrt D : ℝ) : ℂ) ^ 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hD]
      simp only [D]; push_cast
      linear_combination 4 * hq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · have : z = ((t + Real.sqrt D) / 2 : ℝ) := by
        push_cast; linear_combination h1 / 2
      rw [this, Complex.conj_ofReal]
    · have : z = ((t - Real.sqrt D) / 2 : ℝ) := by
        push_cast; linear_combination h1 / 2
      rw [this, Complex.conj_ofReal]
  ext x
  obtain ⟨a, b, rfl⟩ := span_two hk hy x
  rw [ComplexEmbedding.conjugate_coe_eq]
  simp only [map_add, map_mul, eq_ratCast, map_ratCast, hφy]

/-- No element of an imaginary quadratic field squares to a nonnegative non-square rational. -/
theorem no_real_sqrt {y : k} {c : ℚ} (hc : 0 ≤ c) (hns : ∀ a : ℚ, a * a ≠ c)
    (h : y * y = algebraMap ℚ k c) : False := by
  have hy : ∀ a : ℚ, y ≠ algebraMap ℚ k a := by
    rintro a rfl
    apply hns a
    exact (algebraMap ℚ k).injective (by rw [map_mul, h])
  have := disc_neg hk hy (t := 0) (n := -c) (by rw [h]; simp)
  linarith

end Imag


/-! ## §2 Elements of `B` and units of `Φ⁻¹(𝒪)` -/

abbrev B := LeafQM.B

/-- The reduced norm of `B = (2, −3)`. -/
def nrd (x : B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem nrd_mul (x y : B) : nrd (x * y) = nrd x * nrd y := by
  simp [nrd]; ring

theorem quat_sq (x : B) : x * x - (2 * x.re) • x + (nrd x) • (1 : B) = 0 := by
  ext <;> simp [nrd] <;> ring

theorem nrd_algebraMap (c : ℚ) : nrd (algebraMap ℚ B c) = c ^ 2 := by
  simp [nrd]

theorem O_int {x : B} (hx : x ∈ LeafQM.O) : (∃ z : ℤ, nrd x = z) ∧ (∃ z : ℤ, 2 * x.re = z) := by
  obtain ⟨n, rfl⟩ := hx
  refine ⟨⟨n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2), ?_⟩,
    ⟨2 * n 0 + n 2, ?_⟩⟩ <;> simp [nrd, LeafQM.ofInt] <;> ring

section Order

variable {k : Type} [Field k] [NumberField k] [IsTotallyComplex k] (hk : Module.finrank ℚ k = 2)
  (Φ : k →ₐ[ℚ] B)
include hk

theorem Φ_rel (y : k) :
    y * y - algebraMap ℚ k (2 * (Φ y).re) * y + algebraMap ℚ k (nrd (Φ y)) = 0 := by
  apply Φ.toRingHom.injective
  have := quat_sq (Φ y)
  rw [← Algebra.smul_def, Algebra.algebraMap_eq_smul_one]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_add, map_mul, map_smul, map_one,
    map_zero]
  exact this

theorem nrd_pos {y : k} (hy : y ≠ 0) : 0 < nrd (Φ y) := by
  by_cases hr : ∃ c : ℚ, y = algebraMap ℚ k c
  · obtain ⟨c, rfl⟩ := hr
    rw [AlgHom.commutes, nrd_algebraMap]
    have : c ≠ 0 := by rintro rfl; simp at hy
    positivity
  · push Not at hr
    have := disc_neg hk hr (Φ_rel hk Φ y)
    nlinarith [sq_nonneg (2 * (Φ y).re)]

/-- **Units of `Φ⁻¹(𝒪)`.** Every unit is `±1` or a root of `u² + 1`, `u² − u + 1` or `u² + u + 1`. -/
theorem unit_cases (u : (LeafQM.O.comap Φ.toRingHom)ˣ) :
    ((u : LeafQM.O.comap Φ.toRingHom) : k) = 1 ∨ ((u : LeafQM.O.comap Φ.toRingHom) : k) = -1 ∨
    ((u : LeafQM.O.comap Φ.toRingHom) : k) * u + 1 = 0 ∨
    ((u : LeafQM.O.comap Φ.toRingHom) : k) * u - u + 1 = 0 ∨
    ((u : LeafQM.O.comap Φ.toRingHom) : k) * u + u + 1 = 0 := by
  set y : k := ((u : LeafQM.O.comap Φ.toRingHom) : k)
  set y' : k := (((u⁻¹ : (LeafQM.O.comap Φ.toRingHom)ˣ) : LeafQM.O.comap Φ.toRingHom) : k)
  have hyy' : y * y' = 1 := congrArg Subtype.val u.mul_inv
  have hy0 : y ≠ 0 := by rintro h; rw [h, zero_mul] at hyy'; exact zero_ne_one hyy'
  have hy'0 : y' ≠ 0 := by rintro h; rw [h, mul_zero] at hyy'; exact zero_ne_one hyy'
  have hyO : Φ y ∈ LeafQM.O := (u : LeafQM.O.comap Φ.toRingHom).2
  have hy'O : Φ y' ∈ LeafQM.O := ((u⁻¹ : (LeafQM.O.comap Φ.toRingHom)ˣ) : LeafQM.O.comap Φ.toRingHom).2
  obtain ⟨⟨z, hz⟩, ⟨m, hm⟩⟩ := O_int hyO
  obtain ⟨⟨z', hz'⟩, -⟩ := O_int hy'O
  have hzz : (z : ℚ) * z' = 1 := by
    rw [← hz, ← hz', ← nrd_mul, ← map_mul, hyy', map_one]
    simp [nrd]
  have hzpos : (0 : ℚ) < z := hz ▸ nrd_pos hk Φ hy0
  have hz1 : z = 1 := by
    have h1 : z * z' = 1 := by exact_mod_cast hzz
    have h2 : 0 < z := by exact_mod_cast hzpos
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with h | h <;> [exact h; omega]
  have hrel := Φ_rel hk Φ y
  rw [hm, hz, hz1] at hrel
  by_cases hr : ∃ c : ℚ, y = algebraMap ℚ k c
  · obtain ⟨c, hc⟩ := hr
    have hc2 : c ^ 2 = 1 := by
      rw [← nrd_algebraMap, ← AlgHom.commutes Φ, ← hc, hz, hz1]; simp
    have hcc : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.1 hcc with h | h
    · left; rw [hc, show c = 1 by linear_combination h, map_one]
    · right; left; rw [hc, show c = -1 by linear_combination h, map_neg, map_one]
  · push Not at hr
    have hd := disc_neg hk hr hrel
    have hm2 : m ^ 2 < 4 := by
      have : ((m : ℚ)) ^ 2 < 4 := by simpa using hd
      exact_mod_cast this
    have : m = -1 ∨ m = 0 ∨ m = 1 := by
      have h1 : m < 2 := by nlinarith
      have h2 : -2 < m := by nlinarith
      omega
    rcases this with rfl | rfl | rfl
    · right; right; right; right
      have := hrel; simp at this; linear_combination this
    · right; right; left
      have := hrel; simp at this; linear_combination this
    · right; right; right; left
      have := hrel; simp at this; linear_combination this

end Order


/-! ## §3 Counting units; exclusivity of the CM types -/

theorem not_sq (s : ℚ) (c : ℤ) (hc : ¬ IsSquare c) (h : s * s = c) : False := by
  have h1 : IsSquare (c : ℚ) := ⟨s, by rw [← h]⟩
  rw [Rat.isSquare_iff] at h1
  simp at h1
  exact hc h1

theorem card_units_of_list {k : Type} [Field k] (R : Subring k) (L : List k) (hL : L.Nodup)
    (hinv : ∀ x ∈ L, ∃ x' ∈ L, x * x' = 1) (hmem : ∀ x ∈ L, x ∈ R)
    (hall : ∀ u : Rˣ, ((u : R) : k) ∈ L) : Nat.card Rˣ = L.length := by
  classical
  let f : Rˣ → k := fun u => ((u : R) : k)
  have hf : Function.Injective f := by
    intro u v h; apply Units.ext; apply Subtype.ext; exact h
  rw [← Nat.card_range_of_injective hf]
  have hrange : Set.range f = (L.toFinset : Set k) := by
    ext x
    simp only [Set.mem_range, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨u, rfl⟩; exact hall u
    · intro hx
      obtain ⟨x', hx', hxx'⟩ := hinv x hx
      exact ⟨⟨⟨x, hmem x hx⟩, ⟨x', hmem x' hx'⟩, Subtype.ext hxx',
        Subtype.ext (by rw [mul_comm]; exact hxx')⟩, rfl⟩
  rw [hrange, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]

/-- `a + b r`. -/
def ev {k : Type} [Field k] [Algebra ℚ k] (r : k) (p : ℚ × ℚ) : k :=
  algebraMap ℚ k p.1 + algebraMap ℚ k p.2 * r

theorem ev_inj {k : Type} [Field k] [Algebra ℚ k] {r : k} (hr : ∀ c : ℚ, r ≠ algebraMap ℚ k c) :
    Function.Injective (ev r) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [ev] at h
  by_cases hb : b = b'
  · subst hb
    have : algebraMap ℚ k a = algebraMap ℚ k a' := by linear_combination h
    rw [(algebraMap ℚ k).injective this]
  · exfalso
    apply hr ((a' - a) / (b - b'))
    have hb' : algebraMap ℚ k (b - b') ≠ 0 := by
      rw [ne_eq, map_eq_zero]; exact sub_ne_zero.mpr hb
    rw [map_div₀]
    field_simp
    simp only [map_sub]
    linear_combination h

section CountK

variable {k : Type} [Field k] [NumberField k] [IsTotallyComplex k] (hk : Module.finrank ℚ k = 2)
include hk

theorem excl_4_3 {r s : k} (hr : r * r = -1) (hs : s * s - s + 1 = 0) : False :=
  no_real_sqrt hk (y := r * (2 * s - 1)) (c := 3) (by norm_num)
    (fun a h => not_sq a 3 (by decide +kernel) (by exact_mod_cast h))
    (by simp; linear_combination (4 * s * s - 4 * s + 1) * hr - 4 * hs)


theorem excl_4_24 {r s : k} (hr : r * r = -1) (hs : s * s = -6) : False :=
  no_real_sqrt hk (y := r * s) (c := 6) (by norm_num)
    (fun a h => not_sq a 6 (by decide +kernel) (by exact_mod_cast h))
    (by simp; linear_combination s * s * hr - hs)

theorem excl_3_24 {r s : k} (hr : r * r - r + 1 = 0) (hs : s * s = -6) : False :=
  no_real_sqrt hk (y := (2 * r - 1) * s) (c := 18) (by norm_num)
    (fun a h => not_sq a 18 (by decide +kernel) (by exact_mod_cast h))
    (by simp; linear_combination 4 * s * s * hr + (-3) * hs)

theorem not_rat_4 {r : k} (hr : r * r = -1) : ∀ c : ℚ, r ≠ algebraMap ℚ k c := by
  rintro c rfl
  have : c * c = -1 := (algebraMap ℚ k).injective (by simpa using hr)
  nlinarith [sq_nonneg c]

theorem not_rat_3 {r : k} (hr : r * r - r + 1 = 0) : ∀ c : ℚ, r ≠ algebraMap ℚ k c := by
  rintro c rfl
  have : c * c - c + 1 = 0 := (algebraMap ℚ k).injective (by simpa using hr)
  nlinarith [sq_nonneg (c - 1/2)]

theorem one_ne_neg_one' : (1 : k) ≠ -1 := by
  intro h
  have : (2 : k) = 0 := by linear_combination h
  exact two_ne_zero this

variable (Φ : k →ₐ[ℚ] B)

open Classical in
/-- **The unit count of `R = Φ⁻¹(𝒪)`**: `4` with a square root of `−1`, `6` with a root of
`x² − x + 1`, `2` otherwise. -/
theorem card_units_R :
    Nat.card (LeafQM.O.comap Φ.toRingHom)ˣ =
      if (∃ r ∈ LeafQM.O.comap Φ.toRingHom, r * r = -1) then 4
      else if (∃ r ∈ LeafQM.O.comap Φ.toRingHom, r * r - r + 1 = 0) then 6 else 2 := by
  set R := LeafQM.O.comap Φ.toRingHom
  have hU := unit_cases hk Φ
  split_ifs with h4 h3
  · obtain ⟨r, hrR, hr⟩ := h4
    have hnr := not_rat_4 hk hr
    have e : ([(1, 0), (-1, 0), (0, 1), (0, -1)] : List (ℚ × ℚ)).map (ev r) = [1, -1, r, -r] := by
      simp [ev]
    rw [card_units_of_list R [1, -1, r, -r]]
    · rfl
    · rw [← e]; exact List.Nodup.map (ev_inj hnr) (by decide)
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨1, by simp, by ring⟩
      · exact ⟨-1, by simp, by ring⟩
      · exact ⟨-x, by simp, by linear_combination -hr⟩
      · exact ⟨r, by simp, by linear_combination -hr⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact R.one_mem
      · exact R.neg_mem R.one_mem
      · exact hrR
      · exact R.neg_mem hrR
    · intro u
      set y : k := ((u : R) : k)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hU u with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · have : (y - r) * (y + r) = 0 := by linear_combination h - hr
        rcases mul_eq_zero.1 this with h' | h'
        · exact Or.inr (Or.inr (Or.inl (by linear_combination h')))
        · exact Or.inr (Or.inr (Or.inr (by linear_combination h')))
      · exact (excl_4_3 hk hr h).elim
      · exact (excl_4_3 hk hr (s := -y) (by linear_combination h)).elim
  · obtain ⟨r, hrR, hr⟩ := h3
    have hnr := not_rat_3 hk hr
    have e : ([(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)] : List (ℚ × ℚ)).map (ev r) =
        [1, -1, r, -r, 1 - r, -1 + r] := by
      simp [ev]; ring_nf
    rw [card_units_of_list R [1, -1, r, -r, 1 - r, -1 + r]]
    · rfl
    · rw [← e]; exact List.Nodup.map (ev_inj hnr) (by decide)
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by simp, by ring⟩
      · exact ⟨-1, by simp, by ring⟩
      · exact ⟨1 - x, by simp, by linear_combination -hr⟩
      · exact ⟨-1 + r, by simp, by linear_combination -hr⟩
      · exact ⟨r, by simp, by linear_combination -hr⟩
      · exact ⟨-r, by simp, by linear_combination -hr⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact R.one_mem
      · exact R.neg_mem R.one_mem
      · exact hrR
      · exact R.neg_mem hrR
      · exact R.sub_mem R.one_mem hrR
      · exact R.add_mem (R.neg_mem R.one_mem) hrR
    · intro u
      set y : k := ((u : R) : k)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hU u with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact (excl_4_3 hk (r := y) (by linear_combination h) hr).elim
      · have : (y - r) * (y - (1 - r)) = 0 := by linear_combination h - hr
        rcases mul_eq_zero.1 this with h' | h'
        · exact Or.inr (Or.inr (Or.inl (by linear_combination h')))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination h')))))
      · have : (y + r) * (y - (-1 + r)) = 0 := by linear_combination h - hr
        rcases mul_eq_zero.1 this with h' | h'
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by linear_combination h'))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linear_combination h')))))
  · push Not at h4 h3
    rw [card_units_of_list R [1, -1]]
    · rfl
    · simp [one_ne_neg_one' hk]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨1, by simp, by ring⟩
      · exact ⟨-1, by simp, by ring⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact R.one_mem
      · exact R.neg_mem R.one_mem
    · intro u
      set y : k := ((u : R) : k)
      have hyR : y ∈ R := (u : R).2
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hU u with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact (h4 y hyR (by linear_combination h)).elim
      · exact (h3 y hyR h).elim
      · exact (h3 (-y) (R.neg_mem hyR) (by linear_combination h)).elim

end CountK


/-! ## §4 Automorphisms of a QM pair; the leaf; the rows -/

section Iso

open CategoryTheory LeafQM.AV PkgI3

variable {K : Type} [Field K] {A : AbVar K}

theorem mem_com_of {q : QMStr A} (f : AbVar.End A)
    (h : ∀ a : LeafQM.O, (q.iota a).hom ≫ f.hom = f.hom ≫ (q.iota a).hom) : f ∈ com q := by
  rw [com, Subring.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  exact AbVar.Hom.ext' (h a).symm

theorem comm_of_mem_com {q : QMStr A} {f : AbVar.End A} (hf : f ∈ com q) (a : LeafQM.O) :
    (q.iota a).hom ≫ f.hom = f.hom ≫ (q.iota a).hom := by
  rw [com, Subring.mem_centralizer_iff] at hf
  have := congrArg AbVar.Hom.hom (hf (q.iota a) ⟨a, rfl⟩)
  exact this.symm

/-- **`Aut(A, ι) = End_𝒪(A)^×`.** -/
def isoUnitEquiv (q : QMStr A) : QMIso q q ≃ (com q)ˣ where
  toFun G :=
    { val := ⟨G.φ, mem_com_of G.φ G.equivariant⟩
      inv := ⟨G.ψ, mem_com_of G.ψ G.symm.equivariant⟩
      val_inv := Subtype.ext (AbVar.Hom.ext' G.right)
      inv_val := Subtype.ext (AbVar.Hom.ext' G.left) }
  invFun u :=
    { φ := (u.val : AbVar.End A)
      ψ := (u.inv : AbVar.End A)
      left := congrArg AbVar.Hom.hom (congrArg Subtype.val u.inv_val)
      right := congrArg AbVar.Hom.hom (congrArg Subtype.val u.val_inv)
      equivariant := comm_of_mem_com u.val.2 }
  left_inv G := rfl
  right_inv u := Units.ext rfl

end Iso

section Transport

variable {S T : Type} [Ring S] [Ring T] (e : S ≃+* T)

theorem ex_iff (P : ∀ {R : Type} [Ring R], R → Prop) (hP : ∀ x, P x ↔ P (e x)) :
    (∃ x : S, P x) ↔ ∃ y : T, P y :=
  ⟨fun ⟨x, hx⟩ => ⟨e x, (hP x).1 hx⟩, fun ⟨y, hy⟩ => ⟨e.symm y, (hP _).2 (by simpa using hy)⟩⟩

end Transport

open LeafQM.AV PkgI3 in
/-- The three CM predicates as statements about the ring `com q`. -/
theorem cm_iff {K : Type} [Field K] {A : AbVar K} (q : QMStr A) :
    (HasCM4 q ↔ ∃ x : com q, x * x = -1) ∧ (HasCM3 q ↔ ∃ x : com q, x * x - x + 1 = 0) ∧
      (HasCM24 q ↔ ∃ x : com q, x * x = -6) := by
  refine ⟨⟨fun ⟨φ, hφ, h⟩ => ⟨⟨φ, hφ⟩, Subtype.ext h⟩,
      fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩⟩,
    ⟨fun ⟨φ, hφ, h⟩ => ⟨⟨φ, hφ⟩, Subtype.ext h⟩,
      fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩⟩,
    ⟨fun ⟨φ, hφ, h⟩ => ⟨⟨φ, hφ⟩, Subtype.ext h⟩,
      fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩⟩⟩

theorem ex4_iff {S T : Type} [Ring S] [Ring T] (e : S ≃+* T) :
    (∃ x : S, x * x = -1) ↔ ∃ y : T, y * y = -1 :=
  ⟨fun ⟨x, hx⟩ => ⟨e x, by rw [← map_mul, hx, map_neg, map_one]⟩,
   fun ⟨y, hy⟩ => ⟨e.symm y, by rw [← map_mul, hy, map_neg, map_one]⟩⟩

theorem ex3_iff {S T : Type} [Ring S] [Ring T] (e : S ≃+* T) :
    (∃ x : S, x * x - x + 1 = 0) ↔ ∃ y : T, y * y - y + 1 = 0 :=
  ⟨fun ⟨x, hx⟩ => ⟨e x, by rw [← map_mul, ← map_sub, ← map_one e, ← map_add, hx, map_zero]⟩,
   fun ⟨y, hy⟩ => ⟨e.symm y, by rw [← map_mul, ← map_sub, ← map_one e.symm, ← map_add, hy, map_zero]⟩⟩

theorem ex24_iff {S T : Type} [Ring S] [Ring T] (e : S ≃+* T) :
    (∃ x : S, x * x = -6) ↔ ∃ y : T, y * y = -6 :=
  ⟨fun ⟨x, hx⟩ => ⟨e x, by rw [← map_mul, hx, map_neg, map_ofNat]⟩,
   fun ⟨y, hy⟩ => ⟨e.symm y, by rw [← map_mul, hy, map_neg, map_ofNat]⟩⟩

theorem sub_ex_iff {k : Type} [Field k] (R : Subring k) :
    ((∃ x : R, x * x = -1) ↔ ∃ r ∈ R, r * r = -1) ∧
    ((∃ x : R, x * x - x + 1 = 0) ↔ ∃ r ∈ R, r * r - r + 1 = 0) ∧
    ((∃ x : R, x * x = -6) ↔ ∃ r ∈ R, r * r = -6) := by
  refine ⟨⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩,
      fun ⟨r, hr, h⟩ => ⟨⟨r, hr⟩, Subtype.ext h⟩⟩,
    ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩,
      fun ⟨r, hr, h⟩ => ⟨⟨r, hr⟩, Subtype.ext h⟩⟩,
    ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, congrArg Subtype.val hx⟩,
      fun ⟨r, hr, h⟩ => ⟨⟨r, hr⟩, Subtype.ext h⟩⟩⟩

/-- **LEAF (CM points on the Shimura curve `X₆ = X₀⁶(1)`: the centralizer of the QM).** For an abelian
surface `A/ℚ̄` with QM `ι : 𝒪 ↪ End(A)` by the maximal order `𝒪` of the indefinite quaternion algebra
`B = (2, −3)` of discriminant `6`, the centralizer `End_𝒪(A) = com(ι)` is either `ℤ`, or isomorphic to
the order `Φ⁻¹(𝒪)` of an imaginary quadratic field `k` for some `ℚ`-embedding `Φ : k → B` (an optimal
embedding; `(A, ι)` is then a CM point by `Φ⁻¹(𝒪)`).

Sources (UNVERIFIED locators, no network): Shimura, *Construction of class fields and zeta functions of
algebraic curves*, Ann. of Math. 85 (1967), §§1-3 (for `A_τ = ℂ²/ι(𝒪)(τ,1)ᵀ`,
`End_𝒪(A_τ) = Φ_τ(k) ∩ 𝒪` with `Φ_τ(k)` the commutant of the fixed point `τ`); Jordan, *Arithmetic of
a quaternion algebra*, thesis, Harvard 1981, §3; González–Rotger, *Non-elliptic Shimura curves of genus
one*, J. Math. Soc. Japan 58 (2006), §5 (CM points by an order `S` ↔ optimal embeddings `S ↪ 𝒪`);
Rotger, Crelle 561 (2003), §2. Form: the printed description over `ℂ`, here over `ℚ̄`; the passage
`ℚ̄ → ℂ` keeps `End` (T11(b), the bundle's textbook leaf) and is not re-proved here, so the `ℚ̄` form is
a specialization only up to that comparison (flag). Not stronger: the optimal embedding is existential
and `B ≅ B^op` preserves `𝒪`. -/
def QMCentralizerCM : Prop :=
  ∀ (A : PkgI3.AbVar (AlgebraicClosure ℚ)), A.dim = 2 → ∀ q : LeafQM.AV.QMStr A,
    Nonempty (LeafQM.AV.com q ≃+* ℤ) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k), IsTotallyComplex k ∧ Module.finrank ℚ k = 2 ∧
      ∃ Φ : k →ₐ[ℚ] B, Nonempty (LeafQM.AV.com q ≃+* LeafQM.O.comap Φ.toRingHom)

open LeafQM.AV PkgI3 Classical in
/-- **Row H-61 from the leaf.** -/
theorem qmAutCard_of (h : QMCentralizerCM) : HDec.HeckeRest.QMAutCard := by
  intro A hA q
  have hcard : Nat.card (QMIso q q) = Nat.card (com q)ˣ := Nat.card_congr (isoUnitEquiv q)
  obtain ⟨h4i, h3i, h24i⟩ := cm_iff q
  rcases h A hA q with he | ⟨k, _, _, hkc, hk2, Φ, he⟩
  · obtain ⟨e⟩ := he
    have n4 : ¬ HasCM4 q := by
      rw [h4i, ex4_iff e]; rintro ⟨y, hy⟩; nlinarith [sq_nonneg y]
    have n3 : ¬ HasCM3 q := by
      rw [h3i, ex3_iff e]; rintro ⟨y, hy⟩; nlinarith [sq_nonneg (2 * y - 1)]
    have n24 : ¬ HasCM24 q := by
      rw [h24i, ex24_iff e]; rintro ⟨y, hy⟩; nlinarith [sq_nonneg y]
    refine ⟨?_, fun h => n4 h.1, fun h => n4 h.1, fun h => n3 h.1⟩
    rw [if_neg n4, if_neg n3, hcard, Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  · obtain ⟨e⟩ := he
    haveI := hkc
    set R := LeafQM.O.comap Φ.toRingHom
    obtain ⟨s4, s3, s24⟩ := sub_ex_iff R
    have e4 : HasCM4 q ↔ ∃ r ∈ R, r * r = -1 := by rw [h4i, ex4_iff e, s4]
    have e3 : HasCM3 q ↔ ∃ r ∈ R, r * r - r + 1 = 0 := by rw [h3i, ex3_iff e, s3]
    have e24 : HasCM24 q ↔ ∃ r ∈ R, r * r = -6 := by rw [h24i, ex24_iff e, s24]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcard, Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv, card_units_R hk2 Φ]
      by_cases c4 : HasCM4 q
      · rw [if_pos c4, if_pos (e4.1 c4)]
      · rw [if_neg c4, if_neg (fun h => c4 (e4.2 h))]
        by_cases c3 : HasCM3 q
        · rw [if_pos c3, if_pos (e3.1 c3)]
        · rw [if_neg c3, if_neg (fun h => c3 (e3.2 h))]
    · rintro ⟨a, b⟩
      obtain ⟨r, -, hr⟩ := e4.1 a; obtain ⟨s, -, hs⟩ := e3.1 b
      exact excl_4_3 hk2 hr hs
    · rintro ⟨a, b⟩
      obtain ⟨r, -, hr⟩ := e4.1 a; obtain ⟨s, -, hs⟩ := e24.1 b
      exact excl_4_24 hk2 hr hs
    · rintro ⟨a, b⟩
      obtain ⟨r, -, hr⟩ := e3.1 a; obtain ⟨s, -, hs⟩ := e24.1 b
      exact excl_3_24 hk2 hr hs

end HDec.QMSplit.Aut

#print axioms HDec.QMSplit.Aut.qmAutCard_of
