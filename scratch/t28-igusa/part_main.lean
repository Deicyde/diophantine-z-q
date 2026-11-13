
section Main
variable {K : Type*} [Field K]

/-- `J` transforms correctly under the matrix `[[a, b], [c, d]]` (with `e = 1`). -/
def Good (J : (Fin 7 → K) → K) (n : ℕ) (a b c d : K) : Prop :=
  ∀ v, J (actC v a b c d 1) = (a * d - b * c) ^ (3 * n) * J v

theorem Good.mul {J : (Fin 7 → K) → K} {n : ℕ} {a b c d a' b' c' d' : K}
    (h : Good J n a b c d) (h' : Good J n a' b' c' d') :
    Good J n (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  intro v
  have e := actC_actC v a b c d 1 a' b' c' d' 1
  rw [mul_one] at e
  rw [← e, h', h, ← mul_assoc, ← mul_pow]; congr 1; ring

theorem Good.congr {J : (Fin 7 → K) → K} {n : ℕ} {a b c d a' b' c' d' : K}
    (h : Good J n a b c d) (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    Good J n a' b' c' d' := by subst ha hb hc hd; exact h

theorem IsInv.good {J : (Fin 7 → K) → K} {n : ℕ} (hJ : IsInv J n) (a b c d : K)
    (hdet : a * d - b * c ≠ 0) : Good J n a b c d := by
  have gD : ∀ s t, Good J n s 0 0 t := fun s t v => by rw [hJ.diag]; ring_nf
  have gU : ∀ u, Good J n 1 u 0 1 := fun u v => by rw [hJ.trans]; ring_nf; simp
  have gS : Good J n 0 1 1 0 := fun v => by
    rw [hJ.swap]; obtain ⟨m, hm⟩ := hJ.even
    rw [hm, show (0 * 0 - 1 * 1 : K) = -1 by ring, show 3 * (m + m) = 2 * (3 * m) by ring,
      pow_mul]; simp
  by_cases hc : c = 0
  · subst hc
    have ha : a ≠ 0 := by rintro rfl; simp at hdet
    exact ((gD a d).mul (gU (b / a))).congr (by ring) (by field_simp) (by ring) (by ring)
  · exact ((((gU (a / c)).mul gS).mul (gD c (b - a * d / c))).mul (gU (d / c))).congr
      (by field_simp; ring) (by field_simp; ring) (by ring) (by field_simp; ring)

/-- **Transformation law** (the `⇒` direction of T28, in general form). -/
theorem IsInv.sexticAct {J : (Fin 7 → K) → K} {n : ℕ} (hJ : IsInv J n) (f : Fin 7 → K)
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) (e : K) :
    J (sexticAct f M e) = (e * M.det ^ 3) ^ n * J f := by
  rw [Matrix.det_fin_two] at hM ⊢
  rw [sexticAct_eq, actC_scale, hJ.homog, hJ.good _ _ _ _ hM, mul_pow, ← pow_mul, mul_assoc,
    mul_comm 3 n]

variable [CharZero K]

theorem J2_sexticAct (f : Fin 7 → K) (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) (e : K) :
    J2 (sexticAct f M e) = (e * M.det ^ 3) ^ 2 * J2 f := J2R_isInv.sexticAct f M hM e
theorem J4_sexticAct (f : Fin 7 → K) (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) (e : K) :
    J4 (sexticAct f M e) = (e * M.det ^ 3) ^ 4 * J4 f := J4R_isInv.sexticAct f M hM e
theorem J6_sexticAct (f : Fin 7 → K) (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) (e : K) :
    J6 (sexticAct f M e) = (e * M.det ^ 3) ^ 6 * J6 f := J6R_isInv.sexticAct f M hM e
theorem J10_sexticAct (f : Fin 7 → K) (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) (e : K) :
    J10 (sexticAct f M e) = (e * M.det ^ 3) ^ 10 * J10 f := by
  rw [J10_eq, J10_eq]; exact J10R_isInv.sexticAct f M hM e

/-- **The `⇒` direction of `IgusaClebschSeparation`, proved** (any field of characteristic 0). -/
theorem igusa_forward (f g : Fin 7 → K)
    (h : ∃ M : Matrix (Fin 2) (Fin 2) K, M.det ≠ 0 ∧ ∃ e : K, e ≠ 0 ∧ g = sexticAct f M e) :
    ∃ r : K, r ≠ 0 ∧ J2 g = r * J2 f ∧ J4 g = r ^ 2 * J4 f ∧ J6 g = r ^ 3 * J6 f ∧
      J10 g = r ^ 5 * J10 f := by
  obtain ⟨M, hM, e, he, rfl⟩ := h
  refine ⟨(e * M.det ^ 3) ^ 2, by positivity, ?_, ?_, ?_, ?_⟩
  · exact J2_sexticAct f M hM e
  · rw [J4_sexticAct f M hM e, ← pow_mul]
  · rw [J6_sexticAct f M hM e, ← pow_mul]
  · rw [J10_sexticAct f M hM e, ← pow_mul]

end Main

/-- The `⇐` content of T28 with the scaling removed: equal Igusa invariants give equivalent
sextics. -/
def IgusaSeparationEq : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharZero L] (f g : Fin 7 → L),
    J10 f ≠ 0 → J10 g ≠ 0 → J2 g = J2 f → J4 g = J4 f → J6 g = J6 f → J10 g = J10 f →
      ∃ M : Matrix (Fin 2) (Fin 2) L, M.det ≠ 0 ∧ ∃ e : L, e ≠ 0 ∧ g = sexticAct f M e

theorem actC_unit {K : Type*} [Field K] (v : Fin 7 → K) (e : K) :
    actC v 1 0 0 1 e = fun i => e * v i := by
  funext i; fin_cases i <;> simp [actC] <;> ring

/-- **T28 reduces to its exact-equality form** (proved): the `⇒` direction is
`igusa_forward`, and the weighted scaling `r` is absorbed by `e` with `e² = r⁻¹`. -/
theorem igusaClebschSeparation_iff : IgusaClebschSeparation ↔ IgusaSeparationEq := by
  constructor
  · intro h L _ _ _ f g hf hg h2 h4 h6 h10
    exact (h L f g hf hg).2 ⟨1, one_ne_zero, by rw [h2]; ring, by rw [h4]; ring,
      by rw [h6]; ring, by rw [h10]; ring⟩
  · intro h L _ _ _ f g hf hg
    refine ⟨igusa_forward f g, ?_⟩
    rintro ⟨r, hr, h2, h4, h6, h10⟩
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq r⁻¹ (by norm_num : 0 < 2)
    have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hr (inv_eq_zero.mp hs.symm)
    set g' : Fin 7 → L := fun i => s * g i with hg'
    have hsr : s ^ 2 * r = 1 := by rw [hs]; field_simp
    have k2 : J2 g' = J2 f := by
      rw [J2_eq, J2R_homog, ← J2_eq, h2, ← mul_assoc, hsr, one_mul]
    have k4 : J4 g' = J4 f := by
      rw [J4_eq, J4R_homog, ← J4_eq, h4, ← mul_assoc, show s ^ 4 * r ^ 2 = (s ^ 2 * r) ^ 2 by ring,
        hsr, one_pow, one_mul]
    have k6 : J6 g' = J6 f := by
      rw [J6_eq, J6R_homog, ← J6_eq, h6, ← mul_assoc, show s ^ 6 * r ^ 3 = (s ^ 2 * r) ^ 3 by ring,
        hsr, one_pow, one_mul]
    have k10 : J10 g' = J10 f := by
      rw [J10_eq, J10R_homog, ← J10_eq, h10, ← mul_assoc,
        show s ^ 10 * r ^ 5 = (s ^ 2 * r) ^ 5 by ring, hsr, one_pow, one_mul]
    have hg'0 : J10 g' ≠ 0 := by rw [k10]; exact hf
    obtain ⟨M, hM, e, he, hMe⟩ := h L f g' hf hg'0 k2 k4 k6 k10
    refine ⟨M, hM, e * s⁻¹, mul_ne_zero he (inv_ne_zero hs0), ?_⟩
    have hgg : g = actC g' 1 0 0 1 s⁻¹ := by
      rw [actC_unit]; funext i; simp [hg', hs0]
    rw [hgg, hMe, sexticAct_eq, sexticAct_eq, actC_actC]
    congr 1 <;> ring
