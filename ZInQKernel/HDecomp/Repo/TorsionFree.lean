import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-repo/TorsionFree.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-repo, steps A6 and A8: `1 + 3 M_r(R)` is torsion-free; Minkowski's bound

* `CommCore.eq_one_of_pow_eq_one`: in a commutative ring in which `3` is a non-zero-divisor
  and `⋂ₙ 3ⁿ C = 0`, an element `A ≡ 1 (mod 3)` of finite order is `1`.
* `eq_one_of_pow_eq_one`: the same in any ring (applied in the commutative subalgebra `ℤ[y]`).
* `matrix_int_eq_one`, `matrix_padic_eq_one`: the same for `M_r(ℤ)` and `M_r(ℤ₃)` (N5 L468-470;
  h-b1 Lemma PR(ii) step 3: `ρ(I_v)` finite inside `1 + 3M₄(ℤ₃)` is trivial; A4's neatness).
* `injective_mod_three`, `card_le_three_pow`: a finite subgroup of `GL_r(ℤ)` injects into
  `GL_r(𝔽₃)`, so has order `≤ 3^(r²)` (N5 L551-553, step A8: `[E:ℚ] ≤ 3^{r²}`).
-/

namespace GlueRepo.TorsionFree

namespace CommCore

variable {C : Type*} [CommRing C]
variable (h3 : ∀ x : C, (3 : C) * x = 0 → x = 0)
variable (hsep : ∀ x : C, (∀ n : ℕ, ∃ y, x = (3 : C) ^ n * y) → x = 0)

theorem one_add_pow_expand (N : C) (m : ℕ) :
    ∃ Q : C, (1 + N) ^ m = 1 + (m : C) * N + N ^ 2 * Q := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨Q, hQ⟩ := ih
    exact ⟨(m : C) + Q + Q * N, by rw [pow_succ, hQ]; push_cast; ring⟩

include h3

theorem cancel_three_pow {n : ℕ} {x : C} (h : (3 : C) ^ n * x = 0) : x = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih => exact ih (h3 _ (by rw [← mul_assoc, ← pow_succ']; exact h))

/-- Step for `3 ∤ m`. -/
theorem step_coprime {m : ℕ} (hm : ¬ 3 ∣ m) {N : C} (hN : (1 + N) ^ m = 1) {k : ℕ} (hk : 1 ≤ k)
    {M : C} (hM : N = (3 : C) ^ k * M) : ∃ M', N = (3 : C) ^ (k + 1) * M' := by
  obtain ⟨Q, hQ⟩ := one_add_pow_expand N m
  rw [hN] at hQ
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h4 : (m : C) * M + 3 * ((3 : C) ^ j * M ^ 2 * Q) = 0 := by
    apply cancel_three_pow h3 (n := j + 1)
    rw [hM] at hQ
    linear_combination (-1 : C) * hQ
  obtain ⟨q, hq⟩ : ∃ q, m = 3 * q + 1 ∨ m = 3 * q + 2 := ⟨m / 3, by omega⟩
  set Y := (3 : C) ^ j * M ^ 2 * Q
  rcases hq with hq | hq
  · subst hq
    refine ⟨-Y - (q : C) * M, ?_⟩
    rw [hM]; push_cast at h4
    linear_combination (3 : C) ^ (j + 1) * h4
  · subst hq
    refine ⟨M + Y + (q : C) * M, ?_⟩
    rw [hM]; push_cast at h4
    linear_combination (-(3 : C) ^ (j + 1)) * h4

/-- Step for `m = 3`. -/
theorem step_three {N : C} (hN : (1 + N) ^ 3 = 1) {k : ℕ} (hk : 1 ≤ k)
    {M : C} (hM : N = (3 : C) ^ k * M) : ∃ M', N = (3 : C) ^ (k + 1) * M' := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h4 : M + 3 * ((3 : C) ^ j * M ^ 2 + (3 : C) ^ j * (3 : C) ^ j * M ^ 3) = 0 := by
    apply cancel_three_pow h3 (n := j + 2)
    rw [hM] at hN
    linear_combination hN
  refine ⟨-((3 : C) ^ j * M ^ 2 + (3 : C) ^ j * (3 : C) ^ j * M ^ 3), ?_⟩
  rw [hM]
  linear_combination (3 : C) ^ (j + 1) * h4

include hsep in
omit h3 in
/-- If every `3^k`-divisibility of `N` (`k ≥ 1`) improves to `3^{k+1}`, and `3 ∣ N`, then `N = 0`.
  -/
theorem eq_zero_of_step {N : C} (h1 : ∃ y, N = 3 * y)
    (hstep : ∀ k, 1 ≤ k → ∀ M, N = (3 : C) ^ k * M → ∃ M', N = (3 : C) ^ (k + 1) * M') : N = 0 := by
  apply hsep
  intro n
  induction n with
  | zero => exact ⟨N, by simp⟩
  | succ n ih =>
    rcases n with _ | n
    · obtain ⟨y, hy⟩ := h1; exact ⟨y, by simpa using hy⟩
    · obtain ⟨M, hM⟩ := ih
      exact hstep (n + 1) (by omega) M hM

include hsep in
theorem eq_one_of_pow_eq_one {A : C} (hA : ∃ y, A = 1 + 3 * y) {m : ℕ} (hm : 0 < m)
    (hAm : A ^ m = 1) : A = 1 := by
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' 3 (by norm_num)
  induction a generalizing A with
  | zero =>
    simp only [pow_zero, one_mul] at hAm
    obtain ⟨y, rfl⟩ := hA
    have : 3 * y = 0 := eq_zero_of_step hsep ⟨y, rfl⟩
      (fun k hk M hM => step_coprime h3 hb (by simpa using hAm) hk hM)
    rw [this, add_zero]
  | succ a ih =>
    have h3' : A ^ 3 = 1 := by
      apply ih
      · obtain ⟨y, rfl⟩ := hA
        exact ⟨3 * y + 9 * y ^ 2 + 9 * y ^ 3, by ring⟩
      · exact Nat.mul_pos (pow_pos (by norm_num) _) (Nat.pos_of_ne_zero (by rintro rfl; simp at hb))
      · rw [← pow_mul, ← hAm]; ring_nf
    obtain ⟨y, rfl⟩ := hA
    have : 3 * y = 0 := eq_zero_of_step hsep ⟨y, rfl⟩
      (fun k hk M hM => step_three h3 (by simpa using h3') hk hM)
    rw [this, add_zero]

end CommCore

section General

variable {S : Type*} [Ring S]

/-- The commutative subalgebra `ℤ[y]` of a ring. -/
instance adjoinCommRing (y : S) : CommRing (Algebra.adjoin ℤ ({y} : Set S)) :=
  { (inferInstance : Ring (Algebra.adjoin ℤ ({y} : Set S))) with
    mul_comm := fun a b => Subtype.ext <|
      (Algebra.commute_of_mem_adjoin_singleton_of_commute b.2
        (Algebra.commute_of_mem_adjoin_self a.2).symm).eq }

theorem eq_one_of_pow_eq_one
    (h3 : ∀ x : S, (3 : S) * x = 0 → x = 0)
    (hsep : ∀ x : S, (∀ n : ℕ, ∃ y, x = (3 : S) ^ n * y) → x = 0)
    {A : S} (hA : ∃ y, A = 1 + 3 * y) {m : ℕ} (hm : 0 < m) (hAm : A ^ m = 1) : A = 1 := by
  obtain ⟨y, rfl⟩ := hA
  let C := Algebra.adjoin ℤ ({y} : Set S)
  let y' : C := ⟨y, Algebra.self_mem_adjoin_singleton ℤ y⟩
  have h3c : ((3 : C) : S) = 3 := rfl
  have key : (1 + 3 * y' : C) = 1 := by
    apply CommCore.eq_one_of_pow_eq_one (C := C)
    · intro x hx
      exact Subtype.ext (h3 x (by simpa [h3c] using congrArg Subtype.val hx))
    · intro x hx
      refine Subtype.ext (hsep x fun n => ?_)
      obtain ⟨z, hz⟩ := hx n
      exact ⟨z, by simpa [h3c] using congrArg Subtype.val hz⟩
    · exact ⟨y', rfl⟩
    · exact hm
    · exact Subtype.ext (by simpa [y', h3c] using hAm)
  simpa [y', h3c] using congrArg Subtype.val key

end General

section Matrices

variable {r : ℕ} {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem three_pow_mul (n : ℕ) (y : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    ((3 : Matrix (Fin r) (Fin r) R) ^ n * y) i j = (3 : R) ^ n * y i j := by
  have : (3 : Matrix (Fin r) (Fin r) R) ^ n * y = (3 ^ n : ℕ) • y := by
    rw [nsmul_eq_mul]; push_cast; rfl
  rw [this, Matrix.smul_apply, nsmul_eq_mul]; push_cast; rfl

/-- `M_r(R)` satisfies the hypotheses of `eq_one_of_pow_eq_one` when `R` is a Noetherian domain
in which `3` is a nonzero nonunit (Krull's intersection theorem). -/
theorem matrix_eq_one (hR : (3 : R) ≠ 0) (hu : ¬ IsUnit (3 : R))
    {A : Matrix (Fin r) (Fin r) R} (hA : ∃ y, A = 1 + 3 * y) {m : ℕ} (hm : 0 < m)
    (hAm : A ^ m = 1) : A = 1 := by
  refine eq_one_of_pow_eq_one ?_ ?_ hA hm hAm
  · intro x hx
    ext i j
    have := congrFun (congrFun hx i) j
    rw [show (3 : Matrix (Fin r) (Fin r) R) * x = (3 : Matrix (Fin r) (Fin r) R) ^ 1 * x by
      rw [pow_one], three_pow_mul] at this
    simpa [hR] using this
  · intro x hx
    ext i j
    have hI : Ideal.span {(3 : R)} ≠ ⊤ := by
      rwa [Ne, Ideal.span_singleton_eq_top]
    have hmem : x i j ∈ ⨅ n : ℕ, Ideal.span {(3 : R)} ^ n := by
      rw [Ideal.mem_iInf]
      intro n
      obtain ⟨y, hy⟩ := hx n
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hy, three_pow_mul]
      exact dvd_mul_right _ _
    rw [Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {(3 : R)}) hI, Ideal.mem_bot] at hmem
    simpa using hmem

/-- `1 + 3M_r(ℤ)` is torsion-free. -/
theorem matrix_int_eq_one {A : Matrix (Fin r) (Fin r) ℤ} (hA : ∃ y, A = 1 + 3 * y) {m : ℕ}
    (hm : 0 < m) (hAm : A ^ m = 1) : A = 1 :=
  matrix_eq_one (by norm_num) (by rw [Int.isUnit_iff]; norm_num) hA hm hAm

/-- `1 + 3M_r(ℤ₃)` is torsion-free (N5 L468-470). -/
theorem matrix_padic_eq_one {A : Matrix (Fin r) (Fin r) ℤ_[3]} (hA : ∃ y, A = 1 + 3 * y)
    {m : ℕ} (hm : 0 < m) (hAm : A ^ m = 1) : A = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine matrix_eq_one (by norm_num) ?_ hA hm hAm
  rw [PadicInt.isUnit_iff, show ((3 : ℤ_[3])) = ((3 : ℕ) : ℤ_[3]) by norm_cast,
    PadicInt.norm_p]
  norm_num

/-- A subgroup of `GL_r(ℤ₃)` all of whose elements are `≡ 1 (mod 3)` and of finite order is
trivial (h-b1 Lemma PR(ii) step 3, with `H = ρ(I_v)`). -/
theorem padic_subgroup_trivial (H : Subgroup (GL (Fin r) ℤ_[3])) [Finite H]
    (hH : ∀ g ∈ H, ∃ y, (g : Matrix (Fin r) (Fin r) ℤ_[3]) = 1 + 3 * y) : H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hpow : (⟨g, hg⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
  have hm : 0 < Nat.card H := Nat.card_pos
  have h1 : g ^ Nat.card H = 1 := by
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val hpow
  apply Units.ext
  refine matrix_padic_eq_one (hH g hg) hm ?_
  simpa using congrArg Units.val h1

/-- Minkowski: a finite subgroup of `GL_r(ℤ)` injects into `GL_r(𝔽₃)`. -/
theorem injective_mod_three (G : Subgroup (GL (Fin r) ℤ)) [Finite G] :
    Function.Injective
      ((Matrix.GeneralLinearGroup.map (n := Fin r) (Int.castRingHom (ZMod 3))).comp G.subtype) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hdvd : ∀ i j, ∃ c : ℤ, ((g : GL (Fin r) ℤ) : Matrix (Fin r) (Fin r) ℤ) i j
      = (1 : Matrix (Fin r) (Fin r) ℤ) i j + 3 * c := by
    intro i j
    have := congrArg (fun h : GL (Fin r) (ZMod 3) => (h : Matrix (Fin r) (Fin r) (ZMod 3)) i j) hg
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, Units.val_one] at this
    have h2 : ((((g : GL (Fin r) ℤ) : Matrix (Fin r) (Fin r) ℤ) i j : ℤ) : ZMod 3)
        = (((1 : Matrix (Fin r) (Fin r) ℤ) i j : ℤ) : ZMod 3) := by
      by_cases hij : i = j <;> simpa [Matrix.GeneralLinearGroup.map, Matrix.one_apply, hij] using
          this
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨-c, by push_cast at hc; linarith⟩
  choose c hc using hdvd
  have hA : ∃ y, ((g : GL (Fin r) ℤ) : Matrix (Fin r) (Fin r) ℤ) = 1 + 3 * y := by
    refine ⟨Matrix.of c, ?_⟩
    ext i j
    rw [Matrix.add_apply, show (3 : Matrix (Fin r) (Fin r) ℤ) * Matrix.of c
      = (3 : Matrix (Fin r) (Fin r) ℤ) ^ 1 * Matrix.of c by rw [pow_one], three_pow_mul]
    simpa using hc i j
  have hpow : g ^ Nat.card G = 1 := pow_card_eq_one'
  have h1 : (g : GL (Fin r) ℤ) ^ Nat.card G = 1 := by
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val hpow
  apply Subtype.ext
  apply Units.ext
  simp only [OneMemClass.coe_one, Units.val_one]
  refine matrix_int_eq_one hA (Nat.card_pos (α := G)) ?_
  simpa using congrArg Units.val h1

/-- Minkowski's bound used in step A8: a finite subgroup of `GL_r(ℤ)` has order `≤ 3^(r²)`. -/
theorem card_le_three_pow (G : Subgroup (GL (Fin r) ℤ)) [Finite G] :
    Nat.card G ≤ 3 ^ (r ^ 2) := by
  have hinj : Function.Injective fun g : G =>
      (((Matrix.GeneralLinearGroup.map (n := Fin r) (Int.castRingHom (ZMod 3))).comp G.subtype) g :
        Matrix (Fin r) (Fin r) (ZMod 3)) :=
    fun a b h => injective_mod_three G (Units.ext h)
  calc Nat.card G ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod 3)) :=
        Nat.card_le_card_of_injective _ hinj
    _ = 3 ^ (r ^ 2) := by
        show Nat.card (Fin r → Fin r → ZMod 3) = _
        simp [Nat.card_fun, Nat.card_zmod, ← pow_mul, sq]

end Matrices

end GlueRepo.TorsionFree

