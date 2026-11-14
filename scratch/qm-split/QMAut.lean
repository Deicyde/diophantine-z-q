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
Rotger, Crelle 561 (2003), §2. Form: the printed description is over `ℂ` (`QMCentralizerCMC`, §8); this
`ℚ̄` form is PROVED from it and the bundle's textbook leaf T11(b) in §8 (`qmCentralizerCM_of`). Not stronger: the optimal embedding is existential
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


/-! ## §5 `ALFixedPoints`: computations in `B` -/

/-- Anisotropy: `3c² = 2e² + 2b² + 6d²` over `ℤ` forces `e = 0` (descent mod 3). -/
theorem aniso_m2 : ∀ (n : ℕ) (e b c d : ℤ), e.natAbs = n → 3 * c ^ 2 = 2 * e ^ 2 + 2 * b ^ 2 + 6 * d ^ 2 → e = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e b c d hn h
    have key : ∀ x y z w : ZMod 3, 3 * z ^ 2 = 2 * x ^ 2 + 2 * y ^ 2 + 6 * w ^ 2 → x = 0 ∧ y = 0 := by
      decide
    obtain ⟨he, hb⟩ := key (e : ZMod 3) (b : ZMod 3) (c : ZMod 3) (d : ZMod 3) (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) h)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at he hb
    obtain ⟨e', rfl⟩ := he
    obtain ⟨b', rfl⟩ := hb
    push_cast at h hn
    have h' : c ^ 2 = 6 * e' ^ 2 + 6 * b' ^ 2 + 2 * d ^ 2 := by linarith
    have key2 : ∀ x y z w : ZMod 3, x ^ 2 = 6 * z ^ 2 + 6 * w ^ 2 + 2 * y ^ 2 → x = 0 ∧ y = 0 := by decide
    obtain ⟨hc, hd⟩ := key2 (c : ZMod 3) (d : ZMod 3) (e' : ZMod 3) (b' : ZMod 3) (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 3) h')
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc hd
    obtain ⟨c', rfl⟩ := hc
    obtain ⟨d', rfl⟩ := hd
    push_cast at h'
    have h'' : 3 * c' ^ 2 = 2 * e' ^ 2 + 2 * b' ^ 2 + 6 * d' ^ 2 := by linarith
    by_cases he0 : e' = 0
    · simp [he0]
    · have hlt : e'.natAbs < n := by
        rw [← hn, Int.natAbs_mul]; simp; omega
      exact absurd (ih _ hlt e' b' c' d' rfl h'') he0

open QuaternionAlgebra in
/-- No element of `B` squares to `−2` (`ℚ(√−2)` does not embed in `B`: `3` splits in it). -/
theorem no_sq_neg2 (x : B) : x * x ≠ -2 := by
  intro hx
  have hq := quat_sq x
  rw [hx] at hq
  have h0 := congrArg QuaternionAlgebra.re hq
  have h1 := congrArg QuaternionAlgebra.imI hq
  have h2 := congrArg QuaternionAlgebra.imJ hq
  have h3 := congrArg QuaternionAlgebra.imK hq
  simp [nrd, re_ofNat, imI_ofNat, imJ_ofNat, imK_ofNat] at h0 h1 h2 h3
  by_cases hre : x.re = 0
  · rw [hre] at h0
    set E : ℤ := ((x.imI.den * x.imJ.den * x.imK.den : ℕ) : ℤ)
    have hE : (E : ℚ) ≠ 0 := by simp [E]
    obtain ⟨b, hb⟩ : ∃ z : ℤ, (z : ℚ) = x.imI * E :=
      ⟨x.imI.num * (x.imJ.den * x.imK.den : ℕ), by
        simp only [E]; push_cast; rw [← Rat.mul_den_eq_num x.imI]; ring⟩
    obtain ⟨c, hc⟩ : ∃ z : ℤ, (z : ℚ) = x.imJ * E :=
      ⟨x.imJ.num * (x.imI.den * x.imK.den : ℕ), by
        simp only [E]; push_cast; rw [← Rat.mul_den_eq_num x.imJ]; ring⟩
    obtain ⟨d, hd⟩ : ∃ z : ℤ, (z : ℚ) = x.imK * E :=
      ⟨x.imK.num * (x.imI.den * x.imJ.den : ℕ), by
        simp only [E]; push_cast; rw [← Rat.mul_den_eq_num x.imK]; ring⟩
    have hint : 3 * c ^ 2 = 2 * E ^ 2 + 2 * b ^ 2 + 6 * d ^ 2 := by
      have : (3 * c ^ 2 : ℚ) = 2 * E ^ 2 + 2 * b ^ 2 + 6 * d ^ 2 := by
        rw [hb, hc, hd]; linear_combination (E : ℚ) ^ 2 * h0
      exact_mod_cast this
    exact hE (by exact_mod_cast aniso_m2 _ E b c d rfl hint)
  · have hI : x.imI = 0 := h1.resolve_left hre
    have hJ : x.imJ = 0 := h2.resolve_left hre
    have hK : x.imK = 0 := h3.resolve_left hre
    rw [hI, hJ, hK] at h0
    nlinarith [sq_nonneg x.re]


/-- `x ∈ 𝒪`, `x² = −3` ⇒ `(1 + x)/2 ∈ 𝒪` (`𝒪 ⊗ ℤ₂` is the maximal order of the local division algebra,
which contains the cube roots of unity). -/
theorem half_mem_of_sq_neg3 {x : B} (hxO : x ∈ LeafQM.O) (hx : x * x = -3) :
    ((1 : ℚ) / 2) • (1 + x) ∈ LeafQM.O := by
  have hq := quat_sq x
  rw [hx] at hq
  have h0 := congrArg QuaternionAlgebra.re hq
  have h1 := congrArg QuaternionAlgebra.imI hq
  have h2 := congrArg QuaternionAlgebra.imJ hq
  have h3 := congrArg QuaternionAlgebra.imK hq
  simp [nrd, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat] at h0 h1 h2 h3
  have hre : x.re = 0 := by
    by_contra hre
    rw [h1.resolve_left hre, h2.resolve_left hre, h3.resolve_left hre] at h0
    nlinarith [sq_nonneg x.re]
  obtain ⟨n, rfl⟩ := hxO
  simp only [LeafQM.ofInt] at hre h0
  have hn2 : n 2 = -2 * n 0 := by
    have : ((n 2 : ℤ) : ℚ) = -2 * n 0 := by linarith
    exact_mod_cast this
  rw [hre] at h0
  have hQ : 3 * n 0 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2) = 3 := by
    have e : ((n 2 : ℤ) : ℚ) = -2 * n 0 := by exact_mod_cast hn2
    have : (3 * (n 0 : ℚ) ^ 2 - 2 * ((n 1 : ℚ) ^ 2 + n 1 * n 3 + n 3 ^ 2)) = 3 := by
      rw [e] at h0; linear_combination h0
    exact_mod_cast this
  -- parities
  have k1 : ∀ a b c : ZMod 2, 3 * a ^ 2 - 2 * (b ^ 2 + b * c + c ^ 2) = 3 → a - 1 = 0 := by decide
  have ho := k1 (n 0) (n 1) (n 3) (by exact_mod_cast congrArg (Int.cast : ℤ → ZMod 2) hQ)
  have ho' : ((n 0 - 1 : ℤ) : ZMod 2) = 0 := by push_cast; exact ho
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ho'
  obtain ⟨a, ha⟩ := ho'
  have hQ' : n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2 = 6 * a ^ 2 + 6 * a := by
    have e : n 0 = 2 * a + 1 := by push_cast at ha; linarith
    rw [e] at hQ; linarith
  have k2 : ∀ b c : ZMod 2, b ^ 2 + b * c + c ^ 2 = 0 → b = 0 ∧ c = 0 := by decide
  obtain ⟨hb, hc⟩ := k2 (n 1) (n 3) (by
    have := congrArg (Int.cast : ℤ → ZMod 2) hQ'
    push_cast at this
    rw [this, show (6 : ZMod 2) = 0 from rfl]; ring)
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hb hc
  obtain ⟨b, hb⟩ := hb
  obtain ⟨d, hd⟩ := hc
  refine ⟨![a + 1, b, -(2 * a + 1), d], ?_⟩
  have e0 : (n 0 : ℚ) = 2 * a + 1 := by push_cast at ha; exact_mod_cast (by linarith : n 0 = 2 * a + 1)
  have e1 : (n 1 : ℚ) = 2 * b := by push_cast at hb; exact_mod_cast hb
  have e3 : (n 3 : ℚ) = 2 * d := by push_cast at hd; exact_mod_cast hd
  have e2 : (n 2 : ℚ) = -2 * (2 * a + 1) := by rw [← e0]; exact_mod_cast hn2
  ext <;> simp [LeafQM.ofInt, e0, e1, e2, e3] <;> ring

/-! ## §6 `ALFixedPoints`: the twist data and the case analysis -/

section TwistData

open LeafQM.AV PkgI3

/-- From `(A, ι ∘ α) ≅ (A, ι)` with `α` conjugation by `τ` (`τ² = c` central): elements `V, W` of
`End_𝒪(A)` with `V² = c W` and `W` a unit (`V = φ ι(τ)`, `W = φ²`). -/
theorem twist_data {A : AbVar (AlgebraicClosure ℚ)} (q : QMStr A) (α : LeafQM.O ≃+* LeafQM.O)
    (τ : LeafQM.O) (c : ℤ) (hατ : α τ = τ) (hcomm : ∀ a, α a * τ = τ * a) (hαα : ∀ a, α (α a) = a)
    (hττ : τ * τ = (c : LeafQM.O)) (G : QMIso (q.twist α) q) :
    ∃ V W Winv : com q, V * V = (c : com q) * W ∧ W * Winv = 1 := by
  set φ : AbVar.End A := G.φ
  set ψ : AbVar.End A := G.ψ
  have eq1 : ∀ a, φ * q.iota (α a) = q.iota a * φ := fun a => AbVar.Hom.ext' (G.equivariant a)
  have eq2 : ∀ a, ψ * q.iota a = q.iota (α a) * ψ := fun a => AbVar.Hom.ext' (G.symm.equivariant a)
  have hφψ : φ * ψ = 1 := AbVar.Hom.ext' G.right
  have hψφ : ψ * φ = 1 := AbVar.Hom.ext' G.left
  have memc : ∀ z : AbVar.End A, (∀ a, q.iota a * z = z * q.iota a) → z ∈ com q := by
    intro z hz
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    exact hz a
  have hW : φ * φ ∈ com q := memc _ fun a => by
    rw [← mul_assoc, ← eq1, mul_assoc, ← eq1, hαα, mul_assoc]
  have hWi : ψ * ψ ∈ com q := memc _ fun a => by
    have h1 := eq2 (α a)
    rw [hαα] at h1
    rw [mul_assoc, eq2, ← mul_assoc, ← h1, mul_assoc]
  have hV : φ * q.iota τ ∈ com q := memc _ fun a => by
    rw [← mul_assoc, ← eq1, mul_assoc, ← map_mul, hcomm, map_mul, mul_assoc]
  refine ⟨⟨_, hV⟩, ⟨_, hW⟩, ⟨_, hWi⟩, ?_, ?_⟩
  · apply Subtype.ext
    have h1 : q.iota τ * φ = φ * q.iota τ := by rw [← eq1, hατ]
    change φ * q.iota τ * (φ * q.iota τ) = ((c : com q) : AbVar.End A) * (φ * φ)
    rw [show ((c : com q) : AbVar.End A) = (c : AbVar.End A) by push_cast; rfl]
    calc φ * q.iota τ * (φ * q.iota τ) = φ * (q.iota τ * φ) * q.iota τ := by noncomm_ring
      _ = φ * φ * (q.iota (τ * τ)) := by rw [h1, map_mul]; noncomm_ring
      _ = (c : AbVar.End A) * (φ * φ) := by rw [hττ, map_intCast, (Int.cast_commute c _).eq]
  · apply Subtype.ext
    change φ * φ * (ψ * ψ) = 1
    calc φ * φ * (ψ * ψ) = φ * (φ * ψ) * ψ := by noncomm_ring
      _ = 1 := by rw [hφψ, mul_one, hφψ]

end TwistData


theorem nsq (c : ℤ) (hc : ¬ IsSquare c) : ∀ a : ℚ, a * a ≠ c :=
  fun a h => not_sq a c hc h

section ALArith

variable {k : Type} [Field k] [NumberField k] [IsTotallyComplex k] (hk : Module.finrank ℚ k = 2)
  (Φ : k →ₐ[ℚ] B)
include hk

theorem unit_cases' {w winv : k} (hw : w ∈ LeafQM.O.comap Φ.toRingHom)
    (hwi : winv ∈ LeafQM.O.comap Φ.toRingHom) (h : w * winv = 1) :
    w = 1 ∨ w = -1 ∨ w * w + 1 = 0 ∨ w * w - w + 1 = 0 ∨ w * w + w + 1 = 0 := by
  let U : (LeafQM.O.comap Φ.toRingHom)ˣ :=
    ⟨⟨w, hw⟩, ⟨winv, hwi⟩, Subtype.ext h, Subtype.ext (by rw [mul_comm]; exact h)⟩
  exact unit_cases hk Φ U

theorem al2 {v w winv : k} (hv : v ∈ LeafQM.O.comap Φ.toRingHom) (hw : w ∈ LeafQM.O.comap Φ.toRingHom)
    (hwi : winv ∈ LeafQM.O.comap Φ.toRingHom) (h : w * winv = 1) (hvv : v * v = 2 * w) :
    ∃ r ∈ LeafQM.O.comap Φ.toRingHom, r * r = -1 := by
  have negB : ∀ y : k, y * y = -2 → False := fun y hy =>
    no_sq_neg2 (Φ y) (by rw [← map_mul, hy, map_neg, map_ofNat])
  rcases unit_cases' hk Φ hw hwi h with h1 | h1 | h1 | h1 | h1
  · exact (no_real_sqrt hk (y := v) (c := 2) (by norm_num) (nsq 2 (by decide +kernel))
      (by rw [hvv, h1]; simp)).elim
  · exact (negB v (by rw [hvv, h1]; ring)).elim
  · exact ⟨w, hw, by linear_combination h1⟩
  · exact (negB (v * w) (by linear_combination w * w * hvv + 2 * (w + 1) * h1)).elim
  · exact (no_real_sqrt hk (y := v * w) (c := 2) (by norm_num) (nsq 2 (by decide +kernel))
      (by simp; linear_combination w * w * hvv + 2 * (w - 1) * h1)).elim

theorem al3 {v w winv : k} (hv : v ∈ LeafQM.O.comap Φ.toRingHom) (hw : w ∈ LeafQM.O.comap Φ.toRingHom)
    (hwi : winv ∈ LeafQM.O.comap Φ.toRingHom) (h : w * winv = 1) (hvv : v * v = -3 * w) :
    ∃ r ∈ LeafQM.O.comap Φ.toRingHom, r * r - r + 1 = 0 := by
  rcases unit_cases' hk Φ hw hwi h with h1 | h1 | h1 | h1 | h1
  · refine ⟨algebraMap ℚ k (1 / 2) * (1 + v), ?_, ?_⟩
    · show Φ (algebraMap ℚ k (1 / 2) * (1 + v)) ∈ LeafQM.O
      have hvO : Φ v ∈ LeafQM.O := hv
      have := half_mem_of_sq_neg3 hvO (by rw [← map_mul, hvv, h1, mul_one, map_neg, map_ofNat])
      rw [map_mul, AlgHom.commutes, map_add, map_one, ← Algebra.smul_def]
      exact this
    · rw [h1] at hvv
      simp only [map_div₀, map_one, map_ofNat]
      field_simp
      linear_combination hvv
  · exact (no_real_sqrt hk (y := v) (c := 3) (by norm_num) (nsq 3 (by decide +kernel))
      (by rw [hvv, h1]; simp)).elim
  · exact (no_real_sqrt hk (y := v * (1 + w)) (c := 6) (by norm_num) (nsq 6 (by decide +kernel))
      (by simp; linear_combination (1 + w) * (1 + w) * hvv + (-3 * w - 6) * h1)).elim
  · exact ⟨w, hw, h1⟩
  · exact ⟨-w, (LeafQM.O.comap Φ.toRingHom).neg_mem hw, by linear_combination h1⟩

theorem al6 {v w winv : k} (hv : v ∈ LeafQM.O.comap Φ.toRingHom) (hw : w ∈ LeafQM.O.comap Φ.toRingHom)
    (hwi : winv ∈ LeafQM.O.comap Φ.toRingHom) (h : w * winv = 1) (hvv : v * v = 6 * w) :
    ∃ r ∈ LeafQM.O.comap Φ.toRingHom, r * r = -6 := by
  rcases unit_cases' hk Φ hw hwi h with h1 | h1 | h1 | h1 | h1
  · exact (no_real_sqrt hk (y := v) (c := 6) (by norm_num) (nsq 6 (by decide +kernel))
      (by rw [hvv, h1]; simp)).elim
  · exact ⟨v, hv, by rw [hvv, h1]; ring⟩
  · exact (no_real_sqrt hk (y := v * (1 - w)) (c := 12) (by norm_num) (nsq 12 (by decide +kernel))
      (by simp; linear_combination (1 - w) * (1 - w) * hvv + (6 * w - 12) * h1)).elim
  · exact ⟨v * w, (LeafQM.O.comap Φ.toRingHom).mul_mem hv hw,
      by linear_combination w * w * hvv + 6 * (w + 1) * h1⟩
  · exact (no_real_sqrt hk (y := v * w) (c := 6) (by norm_num) (nsq 6 (by decide +kernel))
      (by simp; linear_combination w * w * hvv + 6 * (w - 1) * h1)).elim

end ALArith


section Conj

open LeafQM.AV.Pin.Exact LeafQM.AV.Pin.NormO

theorem conjO_facts (u : LeafQM.Bˣ) (hu : IsNorm u) (huO : (u : B) ∈ LeafQM.O) (c : ℤ)
    (huu : (u : B) * u = (c : B)) :
    conjO u hu ⟨u, huO⟩ = ⟨u, huO⟩ ∧ (∀ a, conjO u hu a * ⟨u, huO⟩ = ⟨u, huO⟩ * a) ∧
      (∀ a, conjO u hu (conjO u hu a) = a) ∧
      (⟨u, huO⟩ : LeafQM.O) * ⟨u, huO⟩ = (c : LeafQM.O) := by
  refine ⟨Subtype.ext ?_, fun a => Subtype.ext ?_, fun a => Subtype.ext ?_, Subtype.ext ?_⟩
  · simp [conjO_apply]
  · simp [conjO_apply, mul_assoc]
  · have hc : ((u : B) * u) * a = a * ((u : B) * u) := by rw [huu]; exact (Int.cast_commute c _)
    simp only [conjO_apply]
    calc (u : B) * ((u : B) * a * ((u⁻¹ : LeafQM.Bˣ) : B)) * ((u⁻¹ : LeafQM.Bˣ) : B)
        = ((u : B) * u * a) * (((u⁻¹ : LeafQM.Bˣ) : B) * ((u⁻¹ : LeafQM.Bˣ) : B)) := by noncomm_ring
      _ = (a * ((u : B) * u)) * (((u⁻¹ : LeafQM.Bˣ) : B) * ((u⁻¹ : LeafQM.Bˣ) : B)) := by rw [hc]
      _ = a := by simp [mul_assoc]
  · simp only [Subring.coe_mul]
    rw [huu]; push_cast; rfl

theorem tt1 : (tt 1 : B) = LeafQM.ofInt ei := rfl
theorem tt2 : (tt 2 : B) = LeafQM.ofInt ej := rfl
theorem tt3 : (tt 3 : B) = LeafQM.ofInt ei * LeafQM.ofInt ej := rfl

theorem tt_mem (k : Fin 4) (hk : k ≠ 0) : (tt k : B) ∈ LeafQM.O := by
  fin_cases k
  · exact absurd rfl hk
  · exact ⟨ei, rfl⟩
  · exact ⟨ej, rfl⟩
  · exact ⟨LeafQM.mulCoord ei ej, by show (tt 3 : B) = _; rw [tt3, LeafQM.ofInt_mul]⟩

theorem tt1_sq : (tt 1 : B) * tt 1 = ((2 : ℤ) : B) := by
  rw [tt1]; ext <;> simp [LeafQM.ofInt, ei, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num
theorem tt2_sq : (tt 2 : B) * tt 2 = ((-3 : ℤ) : B) := by
  rw [tt2]; ext <;> simp [LeafQM.ofInt, ej, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num
theorem tt3_sq : (tt 3 : B) * tt 3 = ((6 : ℤ) : B) := by
  rw [tt3]; ext <;> simp [LeafQM.ofInt, ei, ej, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

end Conj

theorem int_case (c : ℤ) (h1 : ¬ IsSquare c) (h2 : ¬ IsSquare (-c)) (v w wi : ℤ) (hv : v * v = c * w)
    (hw : w * wi = 1) : False := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hw with rfl | rfl
  · exact h1 ⟨v, by linarith⟩
  · exact h2 ⟨v, by linarith⟩

open LeafQM.AV PkgI3 LeafQM.AV.Pin.Exact in
/-- **Row H-63 from the leaf.** -/
theorem alFixedPoints_of (h : QMCentralizerCM) : HDec.HeckeRest.ALFixedPoints := by
  intro A hA q
  -- the twist data for `k = 1, 2, 3`
  have data : ∀ (kk : Fin 4) (c : ℤ), kk ≠ 0 → (tt kk : B) * tt kk = (c : B) →
      Nonempty (QMIso (q.twist (rep kk)) q) → ∃ V W Winv : com q, V * V = (c : com q) * W ∧ W * Winv = 1 := by
    intro kk c hk0 hsq ⟨G⟩
    obtain ⟨f1, f2, f3, f4⟩ := conjO_facts (tt kk) (tt_isNorm kk) (tt_mem kk hk0) c hsq
    exact twist_data q (rep kk) _ c f1 f2 f3 f4 G
  obtain ⟨h4i, h3i, h24i⟩ := cm_iff q
  rcases h A hA q with he | ⟨k, _, _, hkc, hk2, Φ, he⟩
  · obtain ⟨e⟩ := he
    have zc : ∀ (kk : Fin 4) (c : ℤ), kk ≠ 0 → (tt kk : B) * tt kk = (c : B) → ¬ IsSquare c → ¬ IsSquare (-c) →
        ¬ Nonempty (QMIso (q.twist (rep kk)) q) := by
      intro kk c hk0 hsq n1 n2 hG
      obtain ⟨V, W, Wi, hV, hW⟩ := data kk c hk0 hsq hG
      apply int_case c n1 n2 (e V) (e W) (e Wi)
      · rw [← map_mul, hV, map_mul, map_intCast, Int.cast_id]
      · rw [← map_mul, hW, map_one]
    refine ⟨fun hG => (zc 1 2 (by decide) tt1_sq (by decide +kernel) (by decide +kernel) hG).elim,
      fun hG => (zc 2 (-3) (by decide) tt2_sq (by decide +kernel) (by decide +kernel) hG).elim,
      fun hG => (zc 3 6 (by decide) tt3_sq (by decide +kernel) (by decide +kernel) hG).elim⟩
  · obtain ⟨e⟩ := he
    haveI := hkc
    set R := LeafQM.O.comap Φ.toRingHom
    obtain ⟨s4, s3, s24⟩ := sub_ex_iff R
    have e4 : HasCM4 q ↔ ∃ r ∈ R, r * r = -1 := by rw [h4i, ex4_iff e, s4]
    have e3 : HasCM3 q ↔ ∃ r ∈ R, r * r - r + 1 = 0 := by rw [h3i, ex3_iff e, s3]
    have e24 : HasCM24 q ↔ ∃ r ∈ R, r * r = -6 := by rw [h24i, ex24_iff e, s24]
    have tr : ∀ (kk : Fin 4) (c : ℤ), kk ≠ 0 → (tt kk : B) * tt kk = (c : B) →
        Nonempty (QMIso (q.twist (rep kk)) q) →
        ∃ v w wi : k, v ∈ R ∧ w ∈ R ∧ wi ∈ R ∧ w * wi = 1 ∧ v * v = c * w := by
      intro kk c hk0 hsq hG
      obtain ⟨V, W, Wi, hV, hW⟩ := data kk c hk0 hsq hG
      refine ⟨(e V : R), (e W : R), (e Wi : R), (e V).2, (e W).2, (e Wi).2, ?_, ?_⟩
      · have := congrArg Subtype.val (show e W * e Wi = 1 by rw [← map_mul, hW, map_one])
        exact this
      · have := congrArg Subtype.val (show e V * e V = (c : R) * e W by
          rw [← map_mul, hV, map_mul, map_intCast])
        rw [show ((((c : R) * e W : R)) : k) = (c : k) * (e W : R) by push_cast; rfl] at this
        exact this
    refine ⟨fun hG => ?_, fun hG => ?_, fun hG => ?_⟩
    · obtain ⟨v, w, wi, hv, hw, hwi, hww, hvv⟩ := tr 1 2 (by decide) tt1_sq hG
      exact e4.2 (al2 hk2 Φ hv hw hwi hww (by rw [hvv]; push_cast; ring))
    · obtain ⟨v, w, wi, hv, hw, hwi, hww, hvv⟩ := tr 2 (-3) (by decide) tt2_sq hG
      exact e3.2 (al3 hk2 Φ hv hw hwi hww (by rw [hvv]; push_cast; ring))
    · obtain ⟨v, w, wi, hv, hw, hwi, hww, hvv⟩ := tr 3 6 (by decide) tt3_sq hG
      exact e24.2 (al6 hk2 Φ hv hw hwi hww (by rw [hvv]; push_cast; ring))


/-! ## §7 Row H-42 `CMOptimalEmbedding` from the leaf -/

theorem isFractionRing_of_mul_mem {K : Type} [Field K] [CharZero K] (R : Subring K)
    (h : ∀ x : K, ∃ d : ℕ, d ≠ 0 ∧ (d : K) * x ∈ R) : IsFractionRing R K := by
  rw [IsFractionRing, isLocalization_iff]
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · have hy : (y : R) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    exact IsUnit.mk0 _ (by
      change ((y : R) : K) ≠ 0
      exact fun h0 => hy (Subtype.ext h0))
  · obtain ⟨d, hd, hdz⟩ := h z
    have hdR : (d : K) ∈ R := natCast_mem R d
    have hd0 : (⟨(d : K), hdR⟩ : R) ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_of_ne_zero (fun h0 => hd (by
        have h1 : ((d : ℕ) : K) = 0 := congrArg Subtype.val h0
        exact_mod_cast h1))
    refine ⟨(⟨(d : K) * z, hdz⟩, ⟨_, hd0⟩), ?_⟩
    change z * (d : K) = (d : K) * z
    ring
  · exact ⟨1, by simpa using Subtype.ext hxy⟩

theorem O_spans {x : B} : ∃ d : ℕ, d ≠ 0 ∧ (d : ℚ) • x ∈ LeafQM.O := by
  refine ⟨x.re.den * x.imI.den * x.imJ.den * x.imK.den, by positivity, ?_⟩
  set D : ℕ := x.re.den * x.imI.den * x.imJ.den * x.imK.den
  have hint : ∀ (q : ℚ) (n : ℕ), q.den ∣ n → ∃ z : ℤ, (z : ℚ) = (n : ℚ) * q := by
    intro q n hn
    obtain ⟨m, rfl⟩ := hn
    exact ⟨m * q.num, by push_cast; rw [← Rat.mul_den_eq_num q]; ring⟩
  obtain ⟨a, ha⟩ := hint x.re D ⟨x.imI.den * x.imJ.den * x.imK.den, by simp only [D]; ring⟩
  obtain ⟨b, hb⟩ := hint x.imI D ⟨x.re.den * x.imJ.den * x.imK.den, by simp only [D]; ring⟩
  obtain ⟨c, hc⟩ := hint x.imJ D ⟨x.re.den * x.imI.den * x.imK.den, by simp only [D]; ring⟩
  obtain ⟨d, hd⟩ := hint x.imK D ⟨x.re.den * x.imI.den * x.imJ.den, by simp only [D]; ring⟩
  refine ⟨![a - c, b - d, 2 * c, 2 * d], ?_⟩
  ext <;> simp [LeafQM.ofInt, ha, hb, hc, hd] <;> ring

theorem order_spans {k' : Type} [Field k'] [NumberField k'] (R' : Subring k')
    (hR' : R' ≤ (integralClosure ℤ k').toSubring) (hc : LeafQM.AV.conductor R' ≠ 0) (x : k') :
    ∃ d : ℕ, d ≠ 0 ∧ (d : k') * x ∈ R' := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ k').2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  set H := R'.toAddSubgroup.addSubgroupOf (integralClosure ℤ k').toSubring.toAddSubgroup
  have hidx : H.index = LeafQM.AV.conductor R' := rfl
  have hmem : (y • x) ∈ (integralClosure ℤ k').toSubring.toAddSubgroup := hyint
  have h1 := AddSubgroup.nsmul_index_mem H ⟨y • x, hmem⟩
  rw [AddSubgroup.mem_addSubgroupOf] at h1
  change H.index • (y • x) ∈ R' at h1
  set z : ℤ := (H.index : ℤ) * y
  have hz0 : z ≠ 0 := mul_ne_zero (by rw [hidx]; exact_mod_cast hc) hy0
  have hzx : (z : k') * x ∈ R' := by
    have e : (z : k') * x = H.index • (y • x) := by
      simp only [z, zsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
    rw [e]; exact h1
  refine ⟨z.natAbs, by simpa using hz0, ?_⟩
  have hcast : ((z.natAbs : ℕ) : k') = (z : k') ∨ ((z.natAbs : ℕ) : k') = -(z : k') := by
    rcases Int.natAbs_eq z with h | h
    · left; rw [← Int.cast_natCast, ← h]
    · right; rw [← Int.cast_natCast, show ((z.natAbs : ℤ)) = -z by omega, Int.cast_neg]
  rcases hcast with h | h
  · rw [h]; exact hzx
  · rw [h, neg_mul]; exact R'.neg_mem hzx

open LeafQM.AV in
/-- **Row H-42 from the leaf.** -/
theorem cmOptimalEmbedding_of (h : QMCentralizerCM) : HDec.FS5NoCM.CMOptimalEmbedding := by
  intro P k' _ _ _ hk2' R' hR' hc0 he'
  obtain ⟨e'⟩ := he'
  rcases h P.A P.surface P.q with he | ⟨k, _, _, hkc, hk2, Φ, he⟩
  · -- `R' ≅ ℤ` is impossible for an order of finite index in `𝓞_k'`
    exfalso
    obtain ⟨e⟩ := he
    have f : ℤ ≃+* R' := e.symm.trans e'
    have hall : ∀ r : R', ∃ n : ℤ, (r : k') = n := by
      intro r
      refine ⟨f.symm r, ?_⟩
      have h1 : f (f.symm r) = r := f.apply_symm_apply r
      have h2 : f (f.symm r) = ((f.symm r : ℤ) : R') := eq_intCast f _
      have h3 : r = ((f.symm r : ℤ) : R') := h1.symm.trans h2
      conv_lhs => rw [h3]
      push_cast; rfl
    -- a non-rational element of `k'`
    obtain ⟨x, hx⟩ : ∃ x : k', ∀ c : ℚ, x ≠ algebraMap ℚ k' c := by
      by_contra hno
      push Not at hno
      have : Module.finrank ℚ k' = 1 := by
        rw [finrank_eq_one_iff_of_nonzero' (1 : k') one_ne_zero]
        intro x; obtain ⟨c, rfl⟩ := hno x; exact ⟨c, by simp [Algebra.smul_def]⟩
      omega
    obtain ⟨d, hd, hdx⟩ := order_spans R' hR' hc0 x
    obtain ⟨n, hn⟩ := hall ⟨_, hdx⟩
    apply hx ((n : ℚ) / d)
    have hdk : (d : k') ≠ 0 := by exact_mod_cast hd
    simp only [map_div₀, map_intCast, map_natCast]
    field_simp
    rw [mul_comm]; exact hn
  · obtain ⟨e⟩ := he
    haveI := hkc
    set R := LeafQM.O.comap Φ.toRingHom
    let ψ : R' ≃+* R := e'.symm.trans e
    haveI : IsFractionRing R' k' := isFractionRing_of_mul_mem R' (order_spans R' hR' hc0)
    haveI : IsFractionRing R k := isFractionRing_of_mul_mem R (fun y => by
      obtain ⟨d, hd, hdy⟩ := O_spans (x := Φ y)
      refine ⟨d, hd, ?_⟩
      show Φ ((d : k) * y) ∈ LeafQM.O
      have e1 : Φ ((d : k) * y) = (d : ℚ) • Φ y := by
        rw [map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      rw [e1]; exact hdy)
    let σ : k' ≃+* k := IsFractionRing.ringEquivOfRingEquiv ψ
    have hσ : ∀ r : R', σ r = ψ r := fun r => IsFractionRing.ringEquivOfRingEquiv_algebraMap ψ r
    refine ⟨(Φ.toRingHom.comp σ.toRingHom).toRatAlgHom, ?_⟩
    ext x
    change x ∈ R' ↔ Φ (σ x) ∈ LeafQM.O
    constructor
    · intro hx
      have := hσ ⟨x, hx⟩
      change Φ (σ x) ∈ LeafQM.O
      rw [this]; exact (ψ ⟨x, hx⟩).2
    · intro hx
      let r : R := ⟨σ x, hx⟩
      have h1 := hσ (ψ.symm r)
      rw [RingEquiv.apply_symm_apply] at h1
      have : ((ψ.symm r : R') : k') = x := σ.injective h1
      rw [← this]; exact (ψ.symm r).2

/-! ## §8 The leaf in its printed setting (over `ℂ`) and the passage to `ℚ̄` by T11(b) -/

/-- **LEAF (`QMCentralizerCM` over `ℂ`, the printed setting).** Same statement as `QMCentralizerCM`, for
abelian surfaces with QM by `𝒪` over `ℂ` (Shimura 1967 §§1-3: `A_τ = ℂ²/ι(𝒪)(τ,1)ᵀ`,
`End_𝒪(A_τ) = Φ_τ(k) ∩ 𝒪`; Jordan 1981 §3; González–Rotger 2006 §5; locators UNVERIFIED). -/
def QMCentralizerCMC : Prop :=
  ∀ (A : PkgI3.AbVar ℂ), A.dim = 2 → ∀ q : LeafQM.AV.QMStr A,
    Nonempty (LeafQM.AV.com q ≃+* ℤ) ∨
    ∃ (k : Type) (_ : Field k) (_ : NumberField k), IsTotallyComplex k ∧ Module.finrank ℚ k = 2 ∧
      ∃ Φ : k →ₐ[ℚ] B, Nonempty (LeafQM.AV.com q ≃+* LeafQM.O.comap Φ.toRingHom)

open LeafQM.AV in
/-- **The `ℚ̄` form from the `ℂ` form and T11(b)** (the bundle's textbook leaf `T11b_Rigidity`: base change
`ℚ̄ → ℂ` is bijective on endomorphisms). The centralizer of `ι` corresponds to that of its base change. -/
theorem qmCentralizerCM_of (hC : QMCentralizerCMC) (hR : ZInQ.LeafPush2.T11b_Rigidity) :
    QMCentralizerCM := by
  intro A hA q
  let ιe : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) ℂ := ιe.toRingHom.toAlgebra
  let e := HDec.G0ModField.KernelField.endBC A ℂ
  have he : Function.Bijective e := by
    refine ⟨HDec.G0ModField.KernelField.endBC_injective A ℂ, fun g => ?_⟩
    obtain ⟨φ, ⟨hφ, hφe⟩, -⟩ := hR (AlgebraicClosure ℚ) ℂ A A g.hom inferInstance
    exact ⟨PkgI3.AbVar.Hom.mk' φ, PkgI3.AbVar.Hom.ext' hφe⟩
  let qC : QMStr (A.baseChange ℂ) := ⟨e.comp q.iota, he.1.comp q.injective⟩
  have hdim : (A.baseChange ℂ).dim = 2 := by rw [PkgI3.AbVar.dim_baseChange]; exact hA
  have hcom : com qC = (com q).map e := by
    ext ψ
    simp only [com, Subring.mem_centralizer_iff, Subring.mem_map, Set.mem_range]
    constructor
    · intro h
      obtain ⟨φ, rfl⟩ := he.2 ψ
      refine ⟨φ, ?_, rfl⟩
      rintro _ ⟨a, rfl⟩
      apply he.1
      rw [map_mul, map_mul]
      exact h _ ⟨a, rfl⟩
    · rintro ⟨φ, hφ, rfl⟩ _ ⟨a, rfl⟩
      change e (q.iota a) * e φ = e φ * e (q.iota a)
      rw [← map_mul, ← map_mul, hφ _ ⟨a, rfl⟩]
  let E : com q ≃+* com qC :=
    ((RingEquiv.ofBijective e he).subringMap (s := com q)).trans (RingEquiv.subringCongr hcom.symm)
  rcases hC (A.baseChange ℂ) hdim qC with hf | ⟨k, i1, i2, hk, hk2, Φ, hf⟩
  · obtain ⟨f⟩ := hf; exact Or.inl ⟨E.trans f⟩
  · obtain ⟨f⟩ := hf; exact Or.inr ⟨k, i1, i2, hk, hk2, Φ, ⟨E.trans f⟩⟩

/-- **Rows H-61, H-63, H-42 from the printed `ℂ`-form of the leaf and T11(b).** -/
theorem rows_of_C (hC : QMCentralizerCMC) (hR : ZInQ.LeafPush2.T11b_Rigidity) :
    HDec.HeckeRest.QMAutCard ∧ HDec.HeckeRest.ALFixedPoints ∧ HDec.FS5NoCM.CMOptimalEmbedding :=
  ⟨qmAutCard_of (qmCentralizerCM_of hC hR), alFixedPoints_of (qmCentralizerCM_of hC hR),
    cmOptimalEmbedding_of (qmCentralizerCM_of hC hR)⟩

end HDec.QMSplit.Aut

#print axioms HDec.QMSplit.Aut.qmCentralizerCM_of
#print axioms HDec.QMSplit.Aut.rows_of_C
#print axioms HDec.QMSplit.Aut.qmAutCard_of
#print axioms HDec.QMSplit.Aut.alFixedPoints_of
#print axioms HDec.QMSplit.Aut.cmOptimalEmbedding_of

example : HDec.QMSplit.Aut.QMCentralizerCMC → HDec.ZInQ.LeafPush2.T11b_Rigidity →
    HDec.HeckeRest.QMAutCard ∧ HDec.HeckeRest.ALFixedPoints ∧ HDec.FS5NoCM.CMOptimalEmbedding :=
  HDec.QMSplit.Aut.rows_of_C
