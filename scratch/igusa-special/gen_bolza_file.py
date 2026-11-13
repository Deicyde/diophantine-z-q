import sys; sys.path.insert(0, '.')
T = open('gen_T.lean').read()
Y = open('gen_yNe.lean').read()
C = open('gen_cls.lean').read()
J = open('gen_J10Ne.txt').read()
chunks = ', '.join('J10R%d' % i for i in range(10))
src = r'''import ZInQKernel.Contrib.T28.Special.Family

/-!
# T28, special locus: Bolza's criterion `det yv = 0 ⇒` extra involution (task igusa-special)

For the root normal form `Nr l m n = x(x-1)(x-l)(x-m)(x-n)` (a binary sextic with roots
`∞, 0, 1, l, m, n`), Clebsch's determinant factors over the fifteen synthemes of the six roots:
`det yv (Nr l m n) = (1/384433593750) · ∏ₛ Dₛ`, where `Dₛ` is the determinant of the three
quadratics `q₁, q₂, q₃` of the syntheme `s` (`det_yv_Nr`; computed in `scratch/igusa-special/t4.py`,
proved by `ring` through the elementary symmetric functions, `det_yv_Ne`). `Dₛ = 0` says that
`q₁, q₂, q₃` lie in a pencil, i.e. a Möbius involution swaps the roots in pairs; conjugating its
fixed points to `0, ∞` makes the sextic even (`clsN_odd*`), and an even sextic with `J₁₀ ≠ 0` is
equivalent to `E a b = x⁶ + a x⁴ + b x² + 1` (`even_to_E`). Result: `special_Nr`.
The fifteen synthemes fall into four orbits under permutations of `l, m, n`:
`(∞0)(1l)(mn)`, `(∞1)(0l)(mn)`, `(∞l)(01)(mn)`, `(∞l)(0m)(1n)` (`D1 … D4`).
No `sorry`, no `axiom`.
-/

namespace T28Special
open PkgI1

/-- `x(x-1)(x³ - e₁x² + e₂x - e₃)` as a binary sextic (root at `∞`). -/
def Ne {K : Type*} [Field K] (e1 e2 e3 : K) : Fin 7 → K :=
  ![0, e3, -(e2 + e3), e1 + e2, -(1 + e1), 1, 0]

/-- `x(x-1)(x-l)(x-m)(x-n)`: the binary sextic with roots `∞, 0, 1, l, m, n`. -/
def Nr {K : Type*} [Field K] (l m n : K) : Fin 7 → K :=
  Ne (l + m + n) (l * m + l * n + m * n) (l * m * n)

theorem Nr_eq_of {K : Type*} [Field K] {l m n l' m' n' : K} (h1 : l' + m' + n' = l + m + n)
    (h2 : l' * m' + l' * n' + m' * n' = l * m + l * n + m * n) (h3 : l' * m' * n' = l * m * n) :
    Nr l' m' n' = Nr l m n := by
  unfold Nr; rw [h1, h2, h3]

/-! ## Clebsch's determinant on the normal form -/

''' + T + '\n' + Y + r'''
set_option maxHeartbeats 40000000 in
theorem det_yv_Ne {K : Type*} [Field K] [CharZero K] (e1 e2 e3 : K) :
    (Matrix.of (yv (Ne e1 e2 e3))).det =
      ((1 : K) / 384433593750) * T1 e1 e2 e3 * T2 e1 e2 e3 * T3 e1 e2 e3 * T4 e1 e2 e3 := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, yv, Matrix.cons_val, y1c0_Ne, y1c1_Ne, y1c2_Ne, y2c0_Ne, y2c1_Ne,
    y2c2_Ne, y3c0_Ne, y3c1_Ne, y3c2_Ne, T1, T2, T3, T4]
  ring

/-! ## The fifteen synthemes -/

''' + C + r'''
theorem T1_Nr {K : Type*} [Field K] (l m n : K) :
    T1 (l + m + n) (l * m + l * n + m * n) (l * m * n) = D1 l m n * D1 m l n * D1 n l m := by
  simp only [T1, D1]; ring

theorem T2_Nr {K : Type*} [Field K] (l m n : K) :
    T2 (l + m + n) (l * m + l * n + m * n) (l * m * n) = D2 l m n * D2 m l n * D2 n l m := by
  simp only [T2, D2]; ring

theorem T3_Nr {K : Type*} [Field K] (l m n : K) :
    T3 (l + m + n) (l * m + l * n + m * n) (l * m * n) = D3 l m n * D3 m l n * D3 n l m := by
  simp only [T3, D3]; ring

theorem T4_Nr {K : Type*} [Field K] (l m n : K) :
    T4 (l + m + n) (l * m + l * n + m * n) (l * m * n) =
      D4 l m n * D4 l n m * D4 m l n * D4 m n l * D4 n l m * D4 n m l := by
  simp only [T4, D4]; ring

/-- **Clebsch's determinant on the root normal form is the product over the 15 synthemes.** -/
theorem det_yv_Nr {K : Type*} [Field K] [CharZero K] (l m n : K) :
    (Matrix.of (yv (Nr l m n))).det = ((1 : K) / 384433593750) *
      (D1 l m n * D1 m l n * D1 n l m) * (D2 l m n * D2 m l n * D2 n l m) *
      (D3 l m n * D3 m l n * D3 n l m) *
      (D4 l m n * D4 l n m * D4 m l n * D4 m n l * D4 n l m * D4 n m l) := by
  rw [Nr, det_yv_Ne, T1_Nr, T2_Nr, T3_Nr, T4_Nr]

/-! ## `J₁₀` -/

set_option maxHeartbeats 4000000 in
theorem J10_Ne {K : Type*} [Field K] (e1 e2 e3 : K) :
    J10 (Ne e1 e2 e3) =
    ''' + J + r''' := by
  rw [J10_eq]
  simp only [J10R, ''' + chunks + r''', Ne, Matrix.cons_val]
  ring

/-- `J₁₀` is `2⁸` times the discriminant. -/
theorem J10_Nr {K : Type*} [Field K] (l m n : K) :
    J10 (Nr l m n) = 256 * (l ^ 2 * m ^ 2 * n ^ 2 * (l - 1) ^ 2 * (m - 1) ^ 2 * (n - 1) ^ 2 *
      (l - m) ^ 2 * (l - n) ^ 2 * (m - n) ^ 2) := by
  rw [Nr, J10_Ne]; ring

theorem Nr_distinct {K : Type*} [Field K] {l m n : K} (h : J10 (Nr l m n) ≠ 0) :
    l ≠ 0 ∧ l ≠ 1 ∧ l ≠ m := by
  rw [J10_Nr] at h
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> apply h <;> ring

set_option maxHeartbeats 4000000 in
/-- A double root at `∞` kills `J₁₀`. -/
theorem J10_zero_56 {K : Type*} [Field K] (a : Fin 7 → K) (h5 : a 5 = 0) (h6 : a 6 = 0) :
    J10 a = 0 := by
  rw [J10_eq]
  simp only [J10R, ''' + chunks + r''', h5, h6]
  ring

set_option maxHeartbeats 4000000 in
/-- A double root at `0` kills `J₁₀`. -/
theorem J10_zero_01 {K : Type*} [Field K] (a : Fin 7 → K) (h0 : a 0 = 0) (h1 : a 1 = 0) :
    J10 a = 0 := by
  rw [J10_eq]
  simp only [J10R, ''' + chunks + r''', h0, h1]
  ring

/-! ## From an involution to the family `E a b` -/

/-- An even sextic with `J₁₀ ≠ 0` is equivalent to some `x⁶ + a x⁴ + b x² + 1`. -/
theorem even_to_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (g : Fin 7 → K)
    (h1 : g 1 = 0) (h3 : g 3 = 0) (h5 : g 5 = 0) (hJ : J10 g ≠ 0) : ∃ a b, Eqv g (E a b) := by
  have h6 : g 6 ≠ 0 := fun h => hJ (J10_zero_56 g h5 h)
  have h0 : g 0 ≠ 0 := fun h => hJ (J10_zero_01 g h h1)
  obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq (g 0 / g 6) (by norm_num : 0 < 6)
  have hk' : g 6 * k ^ 6 = g 0 := by rw [hk]; field_simp
  have hk0 : k ≠ 0 := by rintro rfl; apply h0; rw [← hk']; ring
  refine ⟨g 4 * k ^ 4 / g 0, g 2 * k ^ 2 / g 0,
    (Eqv.of_actC g k 0 0 1 (1 / g 0) (by simpa using hk0) (by simpa using h0)).of_eq ?_⟩
  have key : actC g k 0 0 1 (1 / g 0) = ![g 0 / g 0, g 1 * k / g 0, g 2 * k ^ 2 / g 0,
      g 3 * k ^ 3 / g 0, g 4 * k ^ 4 / g 0, g 5 * k ^ 5 / g 0, g 6 * k ^ 6 / g 0] := by
    funext i; fin_cases i <;> simp [actC, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring
  rw [key, h1, h3, h5, hk', div_self h0]
  funext i; fin_cases i <;> simp [E]

/-- An involution `x ↦ p + k/(x - p)` (`k ≠ 0`) whose conjugate makes `f` even gives `f ≅ E a b`. -/
theorem inv_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (f : Fin 7 → K)
    (hJ : J10 f ≠ 0) (p k : K) (hk : k ≠ 0)
    (hodd : ∀ s : K, s ^ 2 = k → actC f (s - p) (p + s) (-1) 1 1 1 = 0 ∧
      actC f (s - p) (p + s) (-1) 1 1 3 = 0 ∧ actC f (s - p) (p + s) (-1) 1 1 5 = 0) :
    ∃ a b, Eqv f (E a b) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq k (by norm_num : 0 < 2)
  have hs0 : s ≠ 0 := by rintro rfl; apply hk; rw [← hs]; ring
  have hE : Eqv f (actC f (s - p) (p + s) (-1) 1 1) := Eqv.of_actC _ _ _ _ _ _
    (by rw [show (s - p) * 1 - (p + s) * -1 = 2 * s by ring]; exact mul_ne_zero two_ne_zero hs0)
    one_ne_zero
  obtain ⟨o1, o3, o5⟩ := hodd s hs
  obtain ⟨a, b, hab⟩ := even_to_E _ o1 o3 o5 (hE.J10_ne_zero hJ)
  exact ⟨a, b, hE.trans hab⟩

theorem cls1_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (l m n : K)
    (hD : D1 l m n = 0) (hJ : J10 (Nr l m n) ≠ 0) : ∃ a b, Eqv (Nr l m n) (E a b) := by
  obtain ⟨hl0, -, -⟩ := Nr_distinct hJ
  exact inv_E _ hJ (P1 l m n) (K1 l m n) (by simpa [K1] using hl0)
    fun s hs => ⟨cls1_odd1 l m n s hs hD, cls1_odd3 l m n s hs hD, cls1_odd5 l m n s hs hD⟩

theorem cls2_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (l m n : K)
    (hD : D2 l m n = 0) (hJ : J10 (Nr l m n) ≠ 0) : ∃ a b, Eqv (Nr l m n) (E a b) := by
  obtain ⟨-, hl1, -⟩ := Nr_distinct hJ
  refine inv_E _ hJ (P2 l m n) (K2 l m n) ?_
    fun s hs => ⟨cls2_odd1 l m n s hs hD, cls2_odd3 l m n s hs hD, cls2_odd5 l m n s hs hD⟩
  rw [show K2 l m n = 1 - l by simp only [K2]; ring]
  exact sub_ne_zero.mpr (Ne.symm hl1)

theorem cls3_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (l m n : K)
    (hD : D3 l m n = 0) (hJ : J10 (Nr l m n) ≠ 0) : ∃ a b, Eqv (Nr l m n) (E a b) := by
  obtain ⟨hl0, hl1, -⟩ := Nr_distinct hJ
  refine inv_E _ hJ (P3 l m n) (K3 l m n) ?_
    fun s hs => ⟨cls3_odd1 l m n s hs hD, cls3_odd3 l m n s hs hD, cls3_odd5 l m n s hs hD⟩
  rw [show K3 l m n = l * (l - 1) by simp only [K3]; ring]
  exact mul_ne_zero hl0 (sub_ne_zero.mpr hl1)

theorem cls4_E {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (l m n : K)
    (hD : D4 l m n = 0) (hJ : J10 (Nr l m n) ≠ 0) : ∃ a b, Eqv (Nr l m n) (E a b) := by
  obtain ⟨hl0, -, hlm⟩ := Nr_distinct hJ
  refine inv_E _ hJ (P4 l m n) (K4 l m n) ?_
    fun s hs => ⟨cls4_odd1 l m n s hs hD, cls4_odd3 l m n s hs hD, cls4_odd5 l m n s hs hD⟩
  rw [show K4 l m n = l * (l - m) by simp only [K4]; ring]
  exact mul_ne_zero hl0 (sub_ne_zero.mpr hlm)

/-- Transport a class lemma along a permutation of the roots `l, m, n`. -/
theorem perm_E {K : Type*} [Field K] {l m n l' m' n' : K} (h1 : l' + m' + n' = l + m + n)
    (h2 : l' * m' + l' * n' + m' * n' = l * m + l * n + m * n) (h3 : l' * m' * n' = l * m * n)
    (hJ : J10 (Nr l m n) ≠ 0)
    (H : J10 (Nr l' m' n') ≠ 0 → ∃ a b, Eqv (Nr l' m' n') (E a b)) :
    ∃ a b, Eqv (Nr l m n) (E a b) := by
  rw [Nr_eq_of h1 h2 h3] at H; exact H hJ

/-- **Bolza's criterion on the normal form**: `det yv = 0` and `J₁₀ ≠ 0` give an extra
involution, hence an equivalence with some `x⁶ + a x⁴ + b x² + 1`. -/
theorem special_Nr {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] (l m n : K)
    (hdet : (Matrix.of (yv (Nr l m n))).det = 0) (hJ : J10 (Nr l m n) ≠ 0) :
    ∃ a b, Eqv (Nr l m n) (E a b) := by
  rw [det_yv_Nr] at hdet
  rcases mul_eq_zero.mp hdet with h | h4
  · rcases mul_eq_zero.mp h with h | h3
    · rcases mul_eq_zero.mp h with h | h2
      · rcases mul_eq_zero.mp h with h | h1
        · norm_num at h
        · rcases mul_eq_zero.mp h1 with h | h
          · rcases mul_eq_zero.mp h with h | h
            · exact cls1_E l m n h hJ
            · exact perm_E (by ring) (by ring) (by ring) hJ (cls1_E m l n h)
          · exact perm_E (by ring) (by ring) (by ring) hJ (cls1_E n l m h)
      · rcases mul_eq_zero.mp h2 with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact cls2_E l m n h hJ
          · exact perm_E (by ring) (by ring) (by ring) hJ (cls2_E m l n h)
        · exact perm_E (by ring) (by ring) (by ring) hJ (cls2_E n l m h)
    · rcases mul_eq_zero.mp h3 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact cls3_E l m n h hJ
        · exact perm_E (by ring) (by ring) (by ring) hJ (cls3_E m l n h)
      · exact perm_E (by ring) (by ring) (by ring) hJ (cls3_E n l m h)
  · rcases mul_eq_zero.mp h4 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · rcases mul_eq_zero.mp h with h | h
            · exact cls4_E l m n h hJ
            · exact perm_E (by ring) (by ring) (by ring) hJ (cls4_E l n m h)
          · exact perm_E (by ring) (by ring) (by ring) hJ (cls4_E m l n h)
        · exact perm_E (by ring) (by ring) (by ring) hJ (cls4_E m n l h)
      · exact perm_E (by ring) (by ring) (by ring) hJ (cls4_E n l m h)
    · exact perm_E (by ring) (by ring) (by ring) hJ (cls4_E n m l h)

end T28Special
'''
open('../../ZInQKernel/Contrib/T28/Special/Bolza.lean', 'w').write(src)
