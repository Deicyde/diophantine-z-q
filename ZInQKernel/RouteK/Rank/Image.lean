import ZInQKernel.RouteK.Rank.Delta

/-!
# Kernel and image of the complete 2-descent map over `ℚ`

For `d : ℕ`, `d ≠ 0`, write `C_d = shortCurve (−d²)` over `ℚ` and `δ_d = deltaHom`.

* `deltaHom_ker`: the kernel of `δ_d` is exactly `2 C_d(ℚ)` (the range of `nsmulAddMonoidHom 2`).
  The torsion points are not in the kernel since `−1`, `2` and `−d` are not rational squares; at an
  affine point with `x, x − d` squares, `x + d` is a square too (`y² = x(x − d)(x + d)`), and the
  halving lemma applies.
* `sqfRep c`: the squarefree integer representative of a square class `c ∈ ℚ*/ℚ*²`.
* `selRep_mem_sel2`: the pair of representatives of `δ_d(P)` lies in `Sel2 d`, by Lemma 1.2
  (`Selmer.loc_iff_kummer`) over `ℚ` and the transport of `Loc` along `ℚ → ℝ`, `ℚ → ℚ_p`.
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent ZInQ.RouteK.Selmer

/-! ### Square classes of `ℚ` and squarefree integers -/

/-- Every nonzero integer has the square class of a squarefree integer. -/
theorem exists_squarefree_sqc_int {n : ℤ} (hn : n ≠ 0) :
    ∃ a : ℤ, Squarefree a ∧ sqc (a : ℚ) = sqc (n : ℚ) := by
  obtain ⟨a, b, -, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hn)
  refine ⟨n.sign * a, ?_, ?_⟩
  · rw [← Int.squarefree_natAbs, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn, one_mul,
      Int.natAbs_natCast]
    exact hsq
  · have hn' : (n : ℚ) = ((n.sign * a : ℤ) : ℚ) * (b : ℚ) ^ 2 := by
      have h1 : n = n.sign * (n.natAbs : ℤ) := (Int.sign_mul_natAbs n).symm
      have h2 : (n.natAbs : ℤ) = (b : ℤ) ^ 2 * a := by exact_mod_cast hab.symm
      rw [h2] at h1
      calc (n : ℚ) = (n.sign : ℚ) * ((b : ℚ) ^ 2 * a) := by exact_mod_cast h1
        _ = _ := by push_cast; ring
    rw [hn', sqc_mul_sq _ (by exact_mod_cast hb.ne')]

/-- Every nonzero rational has the square class of a squarefree integer. -/
theorem exists_squarefree_sqc {q : ℚ} (hq : q ≠ 0) :
    ∃ a : ℤ, Squarefree a ∧ sqc (a : ℚ) = sqc q := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  obtain ⟨a, ha, e⟩ := exists_squarefree_sqc_int (mul_ne_zero hnum (by exact_mod_cast q.den_ne_zero :
    (q.den : ℤ) ≠ 0))
  refine ⟨a, ha, ?_⟩
  rw [e]
  have hq' : q = ((q.num * q.den : ℤ) : ℚ) * (1 / (q.den : ℚ)) ^ 2 := by
    push_cast
    rw [show (q.num : ℚ) * q.den * (1 / (q.den : ℚ)) ^ 2 = q.num / q.den by field_simp]
    exact (Rat.num_div_den q).symm
  conv_rhs => rw [hq']
  rw [sqc_mul_sq _ (one_div_ne_zero hden)]

theorem exists_squarefree_sqc_class (c : SqClass ℚ) : ∃ a : ℤ, Squarefree a ∧ sqc (a : ℚ) = c := by
  obtain ⟨q, hq, rfl⟩ := SqClass.exists_eq_sqc c
  exact exists_squarefree_sqc hq

/-- The squarefree integer representative of a square class of `ℚ`. -/
noncomputable def sqfRep (c : SqClass ℚ) : ℤ := (exists_squarefree_sqc_class c).choose

theorem sqfRep_squarefree (c : SqClass ℚ) : Squarefree (sqfRep c) :=
  (exists_squarefree_sqc_class c).choose_spec.1

theorem sqc_sqfRep (c : SqClass ℚ) : sqc (sqfRep c : ℚ) = c :=
  (exists_squarefree_sqc_class c).choose_spec.2

theorem sqfRep_ne_zero (c : SqClass ℚ) : (sqfRep c : ℚ) ≠ 0 := by
  exact_mod_cast (sqfRep_squarefree c).ne_zero

theorem sqfRep_injective : Function.Injective sqfRep := fun c c' h => by
  rw [← sqc_sqfRep c, ← sqc_sqfRep c', h]

/-! ### Transport of `Loc` along field homomorphisms -/

theorem loc_map {K L : Type*} [Field K] [Field L] (f : K →+* L) {d a b : K} (h : Loc K d a b) :
    Loc L (f d) (f a) (f b) := by
  rcases h with ⟨ha, hb⟩ | ⟨x, h₁, h₂, h₃⟩
  · exact Or.inl ⟨ha.map f, hb.map f⟩
  · refine Or.inr ⟨f x, ?_, ?_, ?_⟩
    · simpa [map_div₀] using h₁.map f
    · simpa [map_div₀, map_sub] using h₂.map f
    · simpa [map_div₀, map_add, map_mul] using h₃.map f

theorem loc_cast_of_loc_rat {L : Type*} [Field L] [CharZero L] {d : ℕ} {a b : ℤ}
    (h : Loc ℚ (d : ℚ) (a : ℚ) (b : ℚ)) : Loc L (d : L) (a : L) (b : L) := by
  have := loc_map (Rat.castHom L) h
  simpa using this

/-! ### The kernel of `δ_d` over `ℚ` -/

variable {d : ℕ}

theorem rat_two_ne_zero : (2 : ℚ) ≠ 0 := two_ne_zero

theorem rat_d_ne_zero (hd : d ≠ 0) : (d : ℚ) ≠ 0 := by exact_mod_cast hd

theorem not_isSquare_two_rat : ¬IsSquare (2 : ℚ) := by
  intro h
  have := eq_one_of_squarefree_of_isSquare (z := 2) (Int.prime_two.squarefree) (by exact_mod_cast h)
  exact absurd this (by norm_num)

/-- `δ_d(P) = 1` iff `P ∈ 2 C_d(ℚ)`. -/
theorem delta_eq_one_iff (hd : d ≠ 0) (P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point) :
    delta (d : ℚ) P = 1 ↔ ∃ Q, 2 • Q = P := by
  have hd' : (d : ℚ) ≠ 0 := rat_d_ne_zero hd
  have hdpos : (0 : ℚ) < d := by positivity
  constructor
  swap
  · rintro ⟨Q, rfl⟩; exact delta_two_nsmul rat_two_ne_zero hd' Q
  intro h1
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨0, by simp; rfl⟩
  have hf := congrArg Prod.fst h1
  have hs := congrArg Prod.snd h1
  simp only [delta, Prod.fst_one, Prod.snd_one, kummerAt_some] at hf hs
  have heq : y ^ 2 = x * (x - d) * (x + d) := by
    have := (shortCurve_equation_iff _ x y).mp h.1; rw [this]; ring
  by_cases hx0 : x = 0
  · exfalso
    simp only [hx0, ↓reduceIte] at hf
    rw [show (3 : ℚ) * 0 ^ 2 + -(d : ℚ) ^ 2 = -(d : ℚ) ^ 2 by ring,
      sqc_eq_one_iff (delta_b_ne_zero hd')] at hf
    have := hf.nonneg
    nlinarith
  by_cases hx1 : x = d
  · exfalso
    simp only [hx1, ↓reduceIte] at hs
    rw [show (3 : ℚ) * (d : ℚ) ^ 2 + -(d : ℚ) ^ 2 = 2 * (d : ℚ) ^ 2 by ring,
      sqc_eq_one_iff (by positivity), isSquare_mul_sq_iff hd'] at hs
    exact not_isSquare_two_rat hs
  simp only [hx0, ↓reduceIte, sub_zero] at hf
  simp only [hx1, ↓reduceIte] at hs
  have hxd : x - d ≠ 0 := sub_ne_zero.mpr hx1
  obtain ⟨r₁, hr₁⟩ := (sqc_eq_one_iff hx0).mp hf
  obtain ⟨r₂, hr₂⟩ := (sqc_eq_one_iff hxd).mp hs
  by_cases hx2 : x + d = 0
  · exfalso
    have : x = -d := by linear_combination hx2
    have := (show IsSquare x from ⟨r₁, hr₁⟩).nonneg
    linarith
  have hr0 : r₁ * r₂ ≠ 0 := by
    intro h0
    apply mul_ne_zero hx0 hxd
    linear_combination (x - d) * hr₁ + r₁ * r₁ * hr₂ + (r₁ * r₂) * h0
  exact exists_two_nsmul_eq_of_squares rat_two_ne_zero hd' h (r₃ := y / (r₁ * r₂))
    (by rw [hr₁]; ring) (by rw [hr₂]; ring) (by
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hr0), heq]
      linear_combination (-(x + d) * (x - d)) * hr₁ - ((x + d) * r₁ * r₁) * hr₂)

/-! ### The image of `δ_d` lies in `Sel2 d` -/

theorem kummer_fst_ne_zero {K : Type*} [Field K] [DecidableEq K] {d : K} (_h2 : (2 : K) ≠ 0)
    (hd : d ≠ 0) (P : (shortCurve (-d ^ 2)).toAffine.Point) : (Selmer.kummer d P).1 ≠ 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [Selmer.kummer]
  simp only [Selmer.kummer]
  split_ifs with h0 h1 h3 <;> simp [*]

theorem kummer_snd_ne_zero {K : Type*} [Field K] [DecidableEq K] {d : K} (h2 : (2 : K) ≠ 0)
    (hd : d ≠ 0) (P : (shortCurve (-d ^ 2)).toAffine.Point) : (Selmer.kummer d P).2 ≠ 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [Selmer.kummer]
  simp only [Selmer.kummer]
  split_ifs with h0 h1 h3
  · simpa using hd
  · exact h2
  · exact mul_ne_zero (neg_ne_zero.mpr h2) hd
  · exact sub_ne_zero.mpr h1

/-- The pair of squarefree representatives of `δ_d(P)`. -/
noncomputable def selRep {d : ℕ} (P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point) : ℤ × ℤ :=
  (sqfRep (delta (d : ℚ) P).1, sqfRep (delta (d : ℚ) P).2)

theorem sqEq_sqfRep {q : ℚ} (hq : q ≠ 0) {c : SqClass ℚ} (hc : c = sqc q) :
    SqEq (sqfRep c : ℚ) q := by
  subst hc
  obtain ⟨w, hw, e⟩ := (sqc_eq_sqc_iff (sqfRep_ne_zero _) hq).mp (sqc_sqfRep _)
  exact ⟨w, hw, e⟩

/-- The covering of `selRep P` has the rational point coming from `P` (Lemma 1.2). -/
theorem loc_selRep {d : ℕ} (hd : d ≠ 0) (P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point) :
    Loc ℚ (d : ℚ) ((selRep P).1 : ℚ) ((selRep P).2 : ℚ) := by
  have hd' := rat_d_ne_zero hd
  have hk := delta_eq_sqc_kummer rat_two_ne_zero hd' P
  refine (loc_iff_kummer rat_two_ne_zero hd' (sqfRep_ne_zero _) (sqfRep_ne_zero _)).mpr
    ⟨P, ?_, ?_⟩
  · exact sqEq_sqfRep (kummer_fst_ne_zero rat_two_ne_zero hd' P) (congrArg Prod.fst hk)
  · exact sqEq_sqfRep (kummer_snd_ne_zero rat_two_ne_zero hd' P) (congrArg Prod.snd hk)

/-- **The image of the complete 2-descent map lies in the 2-Selmer group.** -/
theorem selRep_mem_sel2 {d : ℕ} (hd : d ≠ 0) (P : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point) :
    selRep P ∈ Sel2 d := by
  have h := loc_selRep hd P
  exact ⟨sqfRep_squarefree _, sqfRep_squarefree _, loc_cast_of_loc_rat h,
    fun p _ => loc_cast_of_loc_rat h⟩

theorem selRep_eq_iff {d : ℕ} (P Q : (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point) :
    selRep P = selRep Q ↔ delta (d : ℚ) P = delta (d : ℚ) Q := by
  constructor
  · intro h
    simp only [selRep, Prod.mk.injEq] at h
    exact Prod.ext (sqfRep_injective h.1) (sqfRep_injective h.2)
  · intro h; rw [selRep, selRep, h]

end ZInQ.RouteK.Rank
