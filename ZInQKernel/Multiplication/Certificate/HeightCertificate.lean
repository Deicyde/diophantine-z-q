import ZInQKernel.Multiplication.Certificate.Slope

/-!
# Semantics of the height certificate template

Blueprint: `multiplication/certificate/height-certificate-semantics.md`.

For a parameter vector `a ∈ ℚ³⁶` with inputs `Y_i = (a_{5i}, …, a_{5i+4})`, `a₁₅ = ℓ` and the
canonical codes `ι(c₀), …, ι(c₃)` in the coordinates `16, …, 35`:
`Rel_height_certificate(a)` holds iff

1. `Y_i = ι(n_i)` for some `n_i ∈ ℤ` (membership is a conjunct of the certificate), and
2. `HeightCert Y ℓ c`: there are `a_{ij}, b_i ∈ ℚ` with `b_i ≠ 0`, `b_i (Y_i)₁ = a_{i0}`,
   `b_i (Y_i)₂ = a_{i1}`, and each of the nine quantities
   `(a₁₀, a₁₁, b₁, a₂₀, a₂₁, b₂, a₃₀, a₃₁, b₃)` (`nineQ`) is a sum of three slopes `t` with
   `Slope(t, ℓ; c)` (`heightCertificate_rel_iff`).

Since the coordinates `(Y_i)₁, (Y_i)₂` of `ι(n)` are those of `x([n]P₀)` (zero for `n = 0`),
item 2 is the article's statement about `x_{i0}, x_{i1}`.
-/

namespace ZInQ.Mult

open MvPolynomial Syntax

/-- The nine rational quantities `(a₁₀, a₁₁, b₁, a₂₀, a₂₁, b₂, a₃₀, a₃₁, b₃)`. -/
def nineQ (A : Fin 3 → Fin 2 → ℚ) (b : Fin 3 → ℚ) : Fin 9 → ℚ :=
  ![A 0 0, A 0 1, b 0, A 1 0, A 1 1, b 1, A 2 0, A 2 1, b 2]

/-- The height-certificate predicate on three inputs `Y`: denominators `b_i ≠ 0` with
`b_i (Y_i)₁ = a_{i0}`, `b_i (Y_i)₂ = a_{i1}`, and each of the nine quantities a sum of three
slopes satisfying `Slope(·, ℓ; c)`. -/
def HeightCert (Y : Fin 3 → Fin 5 → ℚ) (ℓ : ℚ) (c : Fin 4 → ℤ) : Prop :=
  ∃ (A : Fin 3 → Fin 2 → ℚ) (b : Fin 3 → ℚ),
    (∀ i, b i ≠ 0 ∧ b i * Y i 1 = A i 0 ∧ b i * Y i 2 = A i 1) ∧
    ∀ k : Fin 9, ∃ s : Fin 3 → ℚ, s 0 + s 1 + s 2 = nineQ A b k ∧ ∀ l, SlopePred (s l) ℓ c

/-- A slope call of the certificate. -/
theorem height_slope_call (y : ℕ → ℚ) (ℓ : ℚ) (c : Fin 4 → ℤ) (hℓ : y 15 = ℓ)
    (hC : ∀ (i : Fin 4) (k : Fin 5), y (16 + (5 * i + k)) = iota (c i) k) (s w : ℕ) :
    (Formula.call slopeTemplate (Fin.append ![X s, X 15] (varArgs 16 20)) w).Lift y ↔
      SlopePred (y s) ℓ c := by
  rw [Formula.lift_call y slopeTemplate (Fin.append ![X s, X 15] (varArgs 16 20)) w]
  refine slope_rel_iff (y s) ℓ c _ ?_ ?_ fun i k => ?_
  · show ev y (Fin.append ![X s, X 15] (varArgs 16 20) (Fin.castAdd 20 0)) = y s
    rw [Fin.append_left]; simp
  · show ev y (Fin.append ![X s, X 15] (varArgs 16 20) (Fin.castAdd 20 1)) = ℓ
    rw [Fin.append_left]; simp [hℓ]
  · show ev y (Fin.append ![X s, X 15] (varArgs 16 20) (Fin.natAdd 2 ⟨5 * i + k, by omega⟩)) = _
    rw [Fin.append_right, ev_varArgs]
    exact hC i k

/-- A membership call of the certificate. -/
theorem height_member_call (y : ℕ → ℚ) (k w : ℕ) :
    (Formula.call memberTemplate (varPoint k) w).Lift y ↔ ∃ n : ℤ, pt y k = iota n := by
  rw [Formula.lift_call y memberTemplate (varPoint k) w]
  exact (rel_member_iff_iota _).trans
    (exists_congr fun n => iff_of_eq (congrArg (· = iota n) (ev_comp_varPoint y k)))

/-! ### The witnesses of a height certificate -/

/-- The variables of root `j` by position in its block of `11` (after the membership block). -/
noncomputable def hcRootVal (A : Fin 2 → ℚ) (b : ℚ) (r : ℕ) : ℚ :=
  if r = 7 then A 0 else if r = 8 then A 1 else if r = 9 then b else if r = 10 then b⁻¹ else 0

/-- An assignment of the variables of `height_certificate`: the parameters, the root variables
`a_{i0}, a_{i1}, b_i, b_i⁻¹` at `36 + 11i + 7, …, 36 + 11i + 10`, and the slopes `s_{k,l}` at
`69 + 3897k + l`. Block variables are `0`. -/
noncomputable def hcY (a : Fin 36 → ℚ) (A : Fin 3 → Fin 2 → ℚ) (b : Fin 3 → ℚ)
    (s : Fin 9 → Fin 3 → ℚ) (i : ℕ) : ℚ :=
  if h : i < 36 then a ⟨i, h⟩
  else if h : i < 69 then
    hcRootVal (A ⟨(i - 36) / 11, by omega⟩) (b ⟨(i - 36) / 11, by omega⟩) ((i - 36) % 11)
  else if h : i < 35142 then
    (if h' : (i - 69) % 3897 < 3 then s ⟨(i - 69) / 3897, by omega⟩ ⟨(i - 69) % 3897, h'⟩ else 0)
  else 0

section hcY

variable (a : Fin 36 → ℚ) (A : Fin 3 → Fin 2 → ℚ) (b : Fin 3 → ℚ) (s : Fin 9 → Fin 3 → ℚ)

theorem hcY_lt (i : Fin 36) : hcY a A b s i = a i := by
  rw [hcY, dite_eq_left i.isLt]

theorem hcY_root (j : Fin 3) {i r : ℕ} (hr : r < 11) (hi : i = 36 + 11 * j + r) :
    hcY a A b s i = hcRootVal (A j) (b j) r := by
  subst hi
  have hj := j.isLt
  rw [hcY, dite_eq_right (by omega), dite_eq_left (by omega)]
  have h1 : (36 + 11 * (j : ℕ) + r - 36) / 11 = j := by omega
  have h2 : (36 + 11 * (j : ℕ) + r - 36) % 11 = r := by omega
  rw [h2]
  have e : (⟨(36 + 11 * (j : ℕ) + r - 36) / 11, by omega⟩ : Fin 3) = j := Fin.ext h1
  rw [e]

theorem hcY_s (k : Fin 9) (l : Fin 3) {i : ℕ} (hi : i = 69 + 3897 * k + l) :
    hcY a A b s i = s k l := by
  subst hi
  have hk := k.isLt
  have hl := l.isLt
  rw [hcY, dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega),
    dite_eq_left (by omega)]
  have h1 : (⟨(69 + 3897 * (k : ℕ) + l - 69) / 3897, by omega⟩ : Fin 9) = k := Fin.ext (by
    simp only; omega)
  have h2 : (⟨(69 + 3897 * (k : ℕ) + l - 69) % 3897, by omega⟩ : Fin 3) = l := Fin.ext (by
    simp only; omega)
  rw [h1, h2]

end hcY

/-! ### The theorem -/

/-- **Semantics of the height certificate template.** -/
theorem heightCertificate_rel_iff (ℓ : ℚ) (c : Fin 4 → ℤ) (a : Fin 36 → ℚ) (hℓ : a 15 = ℓ)
    (hc : ∀ (i : Fin 4) (k : Fin 5), a ⟨16 + (5 * i + k), by omega⟩ = iota (c i) k) :
    heightTemplate.Rel a ↔
      (∃ n : Fin 3 → ℤ, ∀ (i : Fin 3) (k : Fin 5), a ⟨5 * i + k, by omega⟩ = iota (n i) k) ∧
        HeightCert (fun i k => a ⟨5 * i + k, by omega⟩) ℓ c := by
  rw [heightTemplate_rel_iff]
  have common : ∀ y : ℕ → ℚ, (∀ i : Fin 36, y i = a i) →
      y 15 = ℓ ∧ ∀ (i : Fin 4) (k : Fin 5), y (16 + (5 * i + k)) = iota (c i) k := by
    intro y hya
    refine ⟨(hya 15).trans hℓ, fun i k => ?_⟩
    rw [← hc i k]; exact hya ⟨16 + (5 * i + k), by omega⟩
  have hY : ∀ y : ℕ → ℚ, (∀ i : Fin 36, y i = a i) → ∀ (i : Fin 3) (k : Fin 5),
      a ⟨5 * i + k, by omega⟩ = y (5 * i + k) := fun y hya i k => (hya ⟨_, by omega⟩).symm
  constructor
  · rintro ⟨y, hya, hL⟩
    obtain ⟨hℓy, hCy⟩ := common y hya
    simp only [heightFormula, heightRootFormula, heightQuantityFormula, lift_and_append,
      lift_and_cons, lift_and_nil, and_true, lift_nzFormula, Formula.lift_eq, and_assoc, map_mul,
      map_add, ev_X, ev_varPoint, Fin.isValue, Fin.val_one, Fin.val_two, Nat.reduceAdd,
      height_slope_call y ℓ c hℓy hCy, height_member_call] at hL
    obtain ⟨⟨n0, hn0⟩, hb0, e00, e01, ⟨n1, hn1⟩, hb1, e10, e11, ⟨n2, hn2⟩, hb2, e20, e21, s0,
        c00, c01, c02, s1, c10, c11, c12, s2, c20, c21, c22, s3, c30, c31, c32, s4, c40, c41,
        c42, s5, c50, c51, c52, s6, c60, c61, c62, s7, c70, c71, c72, s8, c80, c81, c82⟩ := hL
    refine ⟨⟨![n0, n1, n2], fun i k => ?_⟩, ![![y 43, y 44], ![y 54, y 55], ![y 65, y 66]],
      ![y 45, y 56, y 67], fun i => ?_, fun k => ?_⟩
    · rw [hY y hya i k]
      fin_cases i
      exacts [congrFun hn0 k, congrFun hn1 k, congrFun hn2 k]
    · fin_cases i
      · refine ⟨left_ne_zero_of_mul_eq_one hb0, ?_, ?_⟩
        · exact (congrArg (y 45 * ·) (hY y hya 0 1)).trans e00
        · exact (congrArg (y 45 * ·) (hY y hya 0 2)).trans e01
      · refine ⟨left_ne_zero_of_mul_eq_one hb1, ?_, ?_⟩
        · exact (congrArg (y 56 * ·) (hY y hya 1 1)).trans e10
        · exact (congrArg (y 56 * ·) (hY y hya 1 2)).trans e11
      · refine ⟨left_ne_zero_of_mul_eq_one hb2, ?_, ?_⟩
        · exact (congrArg (y 67 * ·) (hY y hya 2 1)).trans e20
        · exact (congrArg (y 67 * ·) (hY y hya 2 2)).trans e21
    · fin_cases k
      · exact ⟨![y 69, y 70, y 71], s0, fun l => by fin_cases l; exacts [c00, c01, c02]⟩
      · exact ⟨![y 3966, y 3967, y 3968], s1, fun l => by fin_cases l; exacts [c10, c11, c12]⟩
      · exact ⟨![y 7863, y 7864, y 7865], s2, fun l => by fin_cases l; exacts [c20, c21, c22]⟩
      · exact ⟨![y 11760, y 11761, y 11762], s3, fun l => by fin_cases l; exacts [c30, c31, c32]⟩
      · exact ⟨![y 15657, y 15658, y 15659], s4, fun l => by fin_cases l; exacts [c40, c41, c42]⟩
      · exact ⟨![y 19554, y 19555, y 19556], s5, fun l => by fin_cases l; exacts [c50, c51, c52]⟩
      · exact ⟨![y 23451, y 23452, y 23453], s6, fun l => by fin_cases l; exacts [c60, c61, c62]⟩
      · exact ⟨![y 27348, y 27349, y 27350], s7, fun l => by fin_cases l; exacts [c70, c71, c72]⟩
      · exact ⟨![y 31245, y 31246, y 31247], s8, fun l => by fin_cases l; exacts [c80, c81, c82]⟩
  · rintro ⟨⟨n, hn⟩, A, b, hAb, hs⟩
    choose s hs using hs
    obtain ⟨y, hy⟩ : ∃ y, y = hcY a A b s := ⟨_, rfl⟩
    have hya : ∀ i : Fin 36, y i = a i := hy ▸ hcY_lt a A b s
    obtain ⟨hℓy, hCy⟩ := common y hya
    have hroot : ∀ (j : Fin 3) (i r : ℕ), r < 11 → i = 36 + 11 * j + r →
        y i = hcRootVal (A j) (b j) r := fun j i r hr hi => hy ▸ hcY_root a A b s j hr hi
    have hsv : ∀ (k : Fin 9) (l : Fin 3) (i : ℕ), i = 69 + 3897 * k + l → y i = s k l :=
      fun k l i hi => hy ▸ hcY_s a A b s k l hi
    have hpt : ∀ (j : Fin 3) (k : ℕ), k = 5 * j → pt y k = iota (n j) := by
      intro j k hk
      funext r
      rw [← hn j r, hY y hya j r]
      simp only [pt, hk]
    refine ⟨y, hya, ?_⟩
    simp only [heightFormula, heightRootFormula, heightQuantityFormula, lift_and_append,
      lift_and_cons, lift_and_nil, and_true, lift_nzFormula, Formula.lift_eq, and_assoc, map_mul,
      map_add, ev_X, ev_varPoint, Fin.isValue, Fin.val_one, Fin.val_two, Nat.reduceAdd,
      height_slope_call y ℓ c hℓy hCy, height_member_call]
    have hq : ∀ k : Fin 9, nineQ A b k = y (![43, 44, 45, 54, 55, 56, 65, 66, 67] k) := by
      intro k
      fin_cases k
      · exact (hroot 0 43 7 (by norm_num) rfl).symm
      · exact (hroot 0 44 8 (by norm_num) rfl).symm
      · exact (hroot 0 45 9 (by norm_num) rfl).symm
      · exact (hroot 1 54 7 (by norm_num) rfl).symm
      · exact (hroot 1 55 8 (by norm_num) rfl).symm
      · exact (hroot 1 56 9 (by norm_num) rfl).symm
      · exact (hroot 2 65 7 (by norm_num) rfl).symm
      · exact (hroot 2 66 8 (by norm_num) rfl).symm
      · exact (hroot 2 67 9 (by norm_num) rfl).symm
    exact ⟨⟨n 0, hpt 0 0 rfl⟩,
      by
        rw [hroot 0 45 9 (by norm_num) rfl, hroot 0 46 10 (by norm_num) rfl]
        exact mul_inv_cancel₀ (hAb 0).1,
      by
        rw [hroot 0 45 9 (by norm_num) rfl, hroot 0 43 7 (by norm_num) rfl]
        exact (congrArg (b 0 * ·) (hY y hya 0 1)).symm.trans (hAb 0).2.1,
      by
        rw [hroot 0 45 9 (by norm_num) rfl, hroot 0 44 8 (by norm_num) rfl]
        exact (congrArg (b 0 * ·) (hY y hya 0 2)).symm.trans (hAb 0).2.2,
      ⟨n 1, hpt 1 5 rfl⟩,
      by
        rw [hroot 1 56 9 (by norm_num) rfl, hroot 1 57 10 (by norm_num) rfl]
        exact mul_inv_cancel₀ (hAb 1).1,
      by
        rw [hroot 1 56 9 (by norm_num) rfl, hroot 1 54 7 (by norm_num) rfl]
        exact (congrArg (b 1 * ·) (hY y hya 1 1)).symm.trans (hAb 1).2.1,
      by
        rw [hroot 1 56 9 (by norm_num) rfl, hroot 1 55 8 (by norm_num) rfl]
        exact (congrArg (b 1 * ·) (hY y hya 1 2)).symm.trans (hAb 1).2.2,
      ⟨n 2, hpt 2 10 rfl⟩,
      by
        rw [hroot 2 67 9 (by norm_num) rfl, hroot 2 68 10 (by norm_num) rfl]
        exact mul_inv_cancel₀ (hAb 2).1,
      by
        rw [hroot 2 67 9 (by norm_num) rfl, hroot 2 65 7 (by norm_num) rfl]
        exact (congrArg (b 2 * ·) (hY y hya 2 1)).symm.trans (hAb 2).2.1,
      by
        rw [hroot 2 67 9 (by norm_num) rfl, hroot 2 66 8 (by norm_num) rfl]
        exact (congrArg (b 2 * ·) (hY y hya 2 2)).symm.trans (hAb 2).2.2,
      by rw [hsv 0 0 69 rfl, hsv 0 1 70 rfl, hsv 0 2 71 rfl, (hs 0).1]; exact hq 0,
      by rw [hsv 0 0 69 rfl]; exact (hs 0).2 0,
      by rw [hsv 0 1 70 rfl]; exact (hs 0).2 1,
      by rw [hsv 0 2 71 rfl]; exact (hs 0).2 2,
      by rw [hsv 1 0 3966 rfl, hsv 1 1 3967 rfl, hsv 1 2 3968 rfl, (hs 1).1]; exact hq 1,
      by rw [hsv 1 0 3966 rfl]; exact (hs 1).2 0,
      by rw [hsv 1 1 3967 rfl]; exact (hs 1).2 1,
      by rw [hsv 1 2 3968 rfl]; exact (hs 1).2 2,
      by rw [hsv 2 0 7863 rfl, hsv 2 1 7864 rfl, hsv 2 2 7865 rfl, (hs 2).1]; exact hq 2,
      by rw [hsv 2 0 7863 rfl]; exact (hs 2).2 0,
      by rw [hsv 2 1 7864 rfl]; exact (hs 2).2 1,
      by rw [hsv 2 2 7865 rfl]; exact (hs 2).2 2,
      by rw [hsv 3 0 11760 rfl, hsv 3 1 11761 rfl, hsv 3 2 11762 rfl, (hs 3).1]; exact hq 3,
      by rw [hsv 3 0 11760 rfl]; exact (hs 3).2 0,
      by rw [hsv 3 1 11761 rfl]; exact (hs 3).2 1,
      by rw [hsv 3 2 11762 rfl]; exact (hs 3).2 2,
      by rw [hsv 4 0 15657 rfl, hsv 4 1 15658 rfl, hsv 4 2 15659 rfl, (hs 4).1]; exact hq 4,
      by rw [hsv 4 0 15657 rfl]; exact (hs 4).2 0,
      by rw [hsv 4 1 15658 rfl]; exact (hs 4).2 1,
      by rw [hsv 4 2 15659 rfl]; exact (hs 4).2 2,
      by rw [hsv 5 0 19554 rfl, hsv 5 1 19555 rfl, hsv 5 2 19556 rfl, (hs 5).1]; exact hq 5,
      by rw [hsv 5 0 19554 rfl]; exact (hs 5).2 0,
      by rw [hsv 5 1 19555 rfl]; exact (hs 5).2 1,
      by rw [hsv 5 2 19556 rfl]; exact (hs 5).2 2,
      by rw [hsv 6 0 23451 rfl, hsv 6 1 23452 rfl, hsv 6 2 23453 rfl, (hs 6).1]; exact hq 6,
      by rw [hsv 6 0 23451 rfl]; exact (hs 6).2 0,
      by rw [hsv 6 1 23452 rfl]; exact (hs 6).2 1,
      by rw [hsv 6 2 23453 rfl]; exact (hs 6).2 2,
      by rw [hsv 7 0 27348 rfl, hsv 7 1 27349 rfl, hsv 7 2 27350 rfl, (hs 7).1]; exact hq 7,
      by rw [hsv 7 0 27348 rfl]; exact (hs 7).2 0,
      by rw [hsv 7 1 27349 rfl]; exact (hs 7).2 1,
      by rw [hsv 7 2 27350 rfl]; exact (hs 7).2 2,
      by rw [hsv 8 0 31245 rfl, hsv 8 1 31246 rfl, hsv 8 2 31247 rfl, (hs 8).1]; exact hq 8,
      by rw [hsv 8 0 31245 rfl]; exact (hs 8).2 0,
      by rw [hsv 8 1 31246 rfl]; exact (hs 8).2 1,
      by rw [hsv 8 2 31247 rfl]; exact (hs 8).2 2⟩

/-- The membership conjuncts of the certificate alone: accepted inputs are codes `ι(n_i)`,
whatever the shift points. -/
theorem heightTemplate_rel_members (a : Fin 36 → ℚ) (h : heightTemplate.Rel a) :
    ∃ n : Fin 3 → ℤ, ∀ (i : Fin 3) (k : Fin 5), a ⟨5 * i + k, by omega⟩ = iota (n i) k := by
  rw [heightTemplate_rel_iff] at h
  obtain ⟨y, hya, hL⟩ := h
  simp only [heightFormula, heightRootFormula, lift_and_append, lift_and_cons, lift_and_nil,
    and_true, height_member_call,
    and_assoc] at hL
  obtain ⟨⟨n0, hn0⟩, -, -, -, ⟨n1, hn1⟩, -, -, -, ⟨n2, hn2⟩, -⟩ := hL
  refine ⟨![n0, n1, n2], fun i k => ?_⟩
  rw [← hya ⟨5 * i + k, by omega⟩]
  fin_cases i
  exacts [congrFun hn0 k, congrFun hn1 k, congrFun hn2 k]

end ZInQ.Mult
