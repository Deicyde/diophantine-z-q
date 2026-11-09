import ZInQKernel.Assembly.Values.Lift
import ZInQKernel.Assembly.Values.Tests
import ZInQKernel.Compiler.Translation.Points
import ZInQKernel.Cleanup.NonzeroMultiples

/-!
# The gadgets `Z`, `IX`, `Div` on canonical codes

On a code `p` with value `ι(m)`, the gadget `Z(p, ζ)` says `[ζ] = z([m]P₀)` (with the inverse
witness of the ordinate norm when `m ≠ 0`), and `IX(p, v)` says `[v] = w([m]P₀)`. These use that
nonzero multiples of `P₀` are affine with nonzero coordinates (`admissible_of_ne_zero`).
We also record assignments written from lists of values.
-/

namespace ZInQ.Assembly

open Syntax MvPolynomial WeierstrassCurve WeierstrassCurve.Affine Compiler.Precision

/-- The norm `y₀² - 2y₁²` of the ordinate of a code. -/
def codeNormY (P : Fin 5 → ℚ) : ℚ := P 3 ^ 2 - 2 * P 4 ^ 2

theorem ev_norm_y (y : ℕ → ℚ) (p : Code) : ev y p.y.norm = codeNormY (evCode y p) := by
  simp [Pair.norm, Code.y, codeNormY, evCode]

theorem val_x (y : ℕ → ℚ) (p : Code) : Pair.val y p.x = ⟨evCode y p 1, evCode y p 2⟩ := rfl

theorem val_y (y : ℕ → ℚ) (p : Code) : Pair.val y p.y = ⟨evCode y p 3, evCode y p 4⟩ := rfl

/-- The norm of the ordinate of `ι(m)`, `m ≠ 0`, is nonzero. -/
theorem codeNormY_iota_ne_zero {m : ℤ} (hm : m ≠ 0) : codeNormY (iota m) ≠ 0 := by
  obtain ⟨x, y, h, e, -, hy⟩ := zsmul_genP0_affine hm
  rw [iota_def, e, pointCode_some, codeNormY]
  simp only [Matrix.cons_val]
  rw [← K0_ne_zero_iff_pairNorm]
  exact hy

theorem holds_isO_iota {y : ℕ → ℚ} {p : Code} {m : ℤ} (hp : evCode y p = iota m) :
    (isO p).Holds y ↔ m = 0 := by
  rw [holds_isO, hp, ← iota_zero]
  exact iota_injective.eq_iff

/-- **The local parameter on a canonical code.** -/
theorem holds_zFormula_iota {y : ℕ → ℚ} {p : Code} {ζ : Pair} {k : ℕ} {m : ℤ}
    (hp : evCode y p = iota m) :
    (zFormula p ζ k).Holds y ↔
      Pair.val y ζ = zIdx m ∧ (m ≠ 0 → codeNormY (iota m) * y k = 1) := by
  rw [holds_zFormula, holds_isO_iota hp, holds_nzFormula, ev_norm_y, hp]
  rcases eq_or_ne m 0 with rfl | hm
  · have h0 : ev y (p 0) = 1 := by
      have := congrFun hp 0; rw [iota_zero] at this; simpa [evCode] using this
    simp [h0, zIdx]
  · obtain ⟨x, yy, h, e, hx, hy⟩ := zsmul_genP0_affine hm
    have h0 : ev y (p 0) = 0 := by
      have := congrFun hp 0; simpa [evCode, iota_apply_zero_eq_zero_iff] using this.trans
        ((iota_apply_zero_eq_zero_iff m).2 hm)
    have hX : Pair.val y p.x = x := by
      rw [val_x, hp, iota_def, e]; rfl
    have hY : Pair.val y p.y = yy := by
      rw [val_y, hp, iota_def, e]; rfl
    simp only [hm, false_and, false_or, h0, true_and, hX, hY, zIdx, e, zPt_some]
    constructor
    · rintro ⟨hw, hz⟩
      exact ⟨by rw [eq_div_iff hy, mul_comm, hz], fun _ => hw⟩
    · rintro ⟨hz, hw⟩
      exact ⟨hw hm, by rw [hz, mul_div_cancel₀ _ hy]⟩

/-- **The inverse abscissa on a canonical code.** -/
theorem holds_ixFormula_iota {y : ℕ → ℚ} {p : Code} {v : Pair} {m : ℤ}
    (hp : evCode y p = iota m) : (ixFormula p v).Holds y ↔ Pair.val y v = wPt (m • genP0) := by
  rw [holds_ixFormula, hp, ← iota_zero, iota_injective.eq_iff]
  rcases eq_or_ne m 0 with rfl | hm
  · have h0 : ev y (p 0) = 1 := by
      have := congrFun hp 0; rw [iota_zero] at this; simpa [evCode] using this
    simp [h0]
  · obtain ⟨x, yy, h, e, hx, hy⟩ := zsmul_genP0_affine hm
    have h0 : ev y (p 0) = 0 := by
      have := congrFun hp 0; simpa [evCode] using this.trans
        ((iota_apply_zero_eq_zero_iff m).2 hm)
    have hX : Pair.val y p.x = x := by
      rw [val_x, hp, iota_def, e]; rfl
    simp only [hm, false_and, false_or, h0, true_and, hX, e, wPt_some]
    rw [eq_div_iff hx, mul_comm]

/-- **Division** `Div(n, d)` with quotient `q`: `[d] ≠ 0` with inverse witness and
`[d][q] = [n]`. -/
theorem holds_divFormula (y : ℕ → ℚ) (n d q : Pair) (k : ℕ) :
    (divFormula n d q k).Holds y ↔ ev y d.norm * y k = 1 ∧ Pair.val y d * Pair.val y q =
      Pair.val y n := by
  simp only [divFormula, Formula.holds_and, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, holds_nzFormula, holds_feq, Pair.val_mul]

/-- The division gadget in field terms. -/
theorem holds_divFormula_iff (y : ℕ → ℚ) (n d q : Pair) (k : ℕ) :
    (divFormula n d q k).Holds y ↔ ev y d.norm * y k = 1 ∧
      Pair.val y q = Pair.val y n / Pair.val y d := by
  rw [holds_divFormula]
  constructor
  · rintro ⟨h1, h2⟩
    have hd : Pair.val y d ≠ 0 := by
      rw [← ev_norm_ne_zero_iff]; intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
    exact ⟨h1, by rw [eq_div_iff hd, mul_comm, h2]⟩
  · rintro ⟨h1, h2⟩
    have hd : Pair.val y d ≠ 0 := by
      rw [← ev_norm_ne_zero_iff]; intro h; rw [h, zero_mul] at h1; exact zero_ne_one h1
    exact ⟨h1, by rw [h2, mul_div_cancel₀ _ hd]⟩

/-- The pair norm in terms of the value. -/
theorem ev_norm_eq (y : ℕ → ℚ) (u : Pair) :
    ev y u.norm = (Pair.val y u).re ^ 2 - 2 * (Pair.val y u).im ^ 2 := Pair.ev_norm y u

theorem pairNorm_ne_zero_of_ne_zero {z : K0} (hz : z ≠ 0) : z.re ^ 2 - 2 * z.im ^ 2 ≠ 0 := by
  rw [← K0_ne_zero_iff_pairNorm]; exact hz

/-! ### Assignments written from lists of values -/

/-- Overwrite `y` with the values of the list (the first entry for an index wins). -/
def writeVals (y : ℕ → ℚ) : List (ℕ × ℚ) → ℕ → ℚ
  | [] => y
  | (r, v) :: l => fun j => if j = r then v else writeVals y l j

@[simp] theorem writeVals_nil (y : ℕ → ℚ) : writeVals y [] = y := rfl

@[simp] theorem writeVals_cons (y : ℕ → ℚ) (r : ℕ) (v : ℚ) (l : List (ℕ × ℚ)) (j : ℕ) :
    writeVals y ((r, v) :: l) j = if j = r then v else writeVals y l j := rfl

theorem writeVals_of_not_mem (y : ℕ → ℚ) (l : List (ℕ × ℚ)) {j : ℕ} (h : ∀ e ∈ l, e.1 ≠ j) :
    writeVals y l j = y j := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨r, v⟩ := e
    rw [writeVals_cons, ite_eq_right (Ne.symm (h _ List.mem_cons_self))]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

theorem writeVals_of_mem (y : ℕ → ℚ) {l : List (ℕ × ℚ)} (hl : (l.map Prod.fst).Nodup) {r : ℕ}
    {v : ℚ} (h : (r, v) ∈ l) : writeVals y l r = v := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨r', v'⟩ := e
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    rw [writeVals_cons]
    rcases List.mem_cons.1 h with h' | h'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
      rw [ite_eq_left rfl]
    · rw [ite_eq_right]
      · exact ih hl.2 h'
      · rintro rfl; exact hl.1 ⟨(r, v), h', rfl⟩

open Translation in
/-- Reading back a point of `writePoints` under scalars written outside its range. -/
theorem evCode_writeVals_writePoints (y : ℕ → ℚ) {pts : List (ℕ × (Fin 5 → ℚ))}
    (hsep : (pts.map Prod.fst).Pairwise Separated) {r : ℕ} {P : Fin 5 → ℚ} (h : (r, P) ∈ pts)
    {l : List (ℕ × ℚ)} (hl : ∀ e ∈ l, e.1 < r ∨ r + 5 ≤ e.1) :
    evCode (writeVals (writePoints y pts) l) (varPoint r) = P := by
  funext i
  rw [evCode, ev_varPoint, writeVals_of_not_mem _ _ fun e he => by
    have := hl e he; have := i.isLt; omega]
  exact congrFun (writePoints_point y hsep h) i

end ZInQ.Assembly
