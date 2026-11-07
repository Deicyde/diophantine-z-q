import ZInQKernel.Syntax.Templates.Value
import ZInQKernel.Model.Generator

/-!
# Lifted formulas on codes

Helpers for reading the lifted formula `φ^*` of a value template: on formulas without call
atoms `φ^*` is `φ`, and the call atoms of `member` and `raw_add` evaluate their parameter codes.
-/

namespace ZInQ.Assembly

open Syntax MvPolynomial

/-- On a formula without call atoms, `φ^*(x)` is `φ(x)`. -/
theorem lift_iff_holds_of_callees_nil {φ : Formula} (h : φ.callees = []) (y : ℕ → ℚ) :
    φ.Lift y ↔ φ.Holds y := by
  induction φ using Formula.induct' with
  | eq a b => simp
  | atom f => simp
  | call τ g w => simp [Formula.callees] at h
  | and fs ih =>
    rw [Formula.callees_and, List.flatMap_eq_nil_iff] at h
    rw [Formula.lift_and, Formula.holds_and]
    exact forall₂_congr fun φ hφ => ih φ hφ (h φ hφ)
  | or fs ih =>
    rw [Formula.callees_or, List.flatMap_eq_nil_iff] at h
    rw [Formula.lift_or, Formula.holds_or]
    exact exists_congr fun φ => and_congr_right fun hφ => ih φ hφ (h φ hφ)

@[simp] theorem callees_feq (u v : Pair) : (feq u v).callees = [] := by
  simp [feq, Formula.callees]

@[simp] theorem callees_peq (p q : Code) : (peq p q).callees = [] := by
  simp only [peq, Formula.callees_and, List.flatMap_eq_nil_iff, List.mem_ofFn]
  rintro _ ⟨i, rfl⟩
  simp [Formula.callees]

@[simp] theorem callees_isO (p : Code) : (isO p).callees = [] := callees_peq _ _

@[simp] theorem callees_fin (p : Code) : (fin p).callees = [] := by simp [fin, Formula.callees]

@[simp] theorem callees_nzFormula (a : Poly) (c : ℕ) : (nzFormula a c).callees = [] := by simp [nzFormula, Formula.callees]

@[simp] theorem callees_posFormula (a : Poly) (c : ℕ) : (posFormula a c).callees = [] := by simp [posFormula, Formula.callees]

@[simp] theorem callees_zFormula (p : Code) (ζ : Pair) (k : ℕ) : (zFormula p ζ k).callees = [] := by
  simp [zFormula]

@[simp] theorem callees_ixFormula (p : Code) (v : Pair) : (ixFormula p v).callees = [] := by
  simp [ixFormula]

@[simp] theorem callees_divFormula (n d q : Pair) (k : ℕ) : (divFormula n d q k).callees = [] := by
  simp [divFormula]

theorem lift_peq (y : ℕ → ℚ) (p q : Code) : (peq p q).Lift y ↔ evCode y p = evCode y q := by
  rw [lift_iff_holds_of_callees_nil (callees_peq p q), holds_peq]

theorem lift_zFormula (y : ℕ → ℚ) (p : Code) (ζ : Pair) (k : ℕ) :
    (zFormula p ζ k).Lift y ↔ (zFormula p ζ k).Holds y :=
  lift_iff_holds_of_callees_nil (callees_zFormula p ζ k) y

theorem lift_ixFormula (y : ℕ → ℚ) (p : Code) (v : Pair) :
    (ixFormula p v).Lift y ↔ (ixFormula p v).Holds y :=
  lift_iff_holds_of_callees_nil (callees_ixFormula p v) y

theorem lift_divFormula (y : ℕ → ℚ) (n d q : Pair) (k : ℕ) :
    (divFormula n d q k).Lift y ↔ (divFormula n d q k).Holds y :=
  lift_iff_holds_of_callees_nil (callees_divFormula n d q k) y

theorem lift_posFormula (y : ℕ → ℚ) (a : Poly) (c : ℕ) :
    (posFormula a c).Lift y ↔ (posFormula a c).Holds y :=
  lift_iff_holds_of_callees_nil (callees_posFormula a c) y

theorem val_varPair (y : ℕ → ℚ) (k : ℕ) : Pair.val y (varPair k) = ⟨y k, y (k + 1)⟩ := by
  ext <;> simp [varPair]

/-- The call atom of `member` on a code. -/
theorem lift_member_call (y : ℕ → ℚ) (p : Code) (w : ℕ) :
    (Formula.call memberTemplate p w).Lift y ↔ memberTemplate.Rel (evCode y p) :=
  Formula.lift_call _ _ _ _

/-- The call atom of `raw_add` on three codes. -/
theorem lift_rawAdd_code (y : ℕ → ℚ) (p q r : Code) (w : ℕ) :
    (Formula.call rawAddTemplate (Fin.append (Fin.append p q) r) w).Lift y ↔
      rawAddTemplate.Rel (Fin.append (Fin.append (evCode y p) (evCode y q)) (evCode y r)) := by
  refine (Formula.lift_call _ _ _ _).trans ?_
  show rawAddTemplate.Rel
    (fun k : Fin (5 + 5 + 5) => ev y (Fin.append (Fin.append p q) r k)) ↔ _
  rw [ev_comp_append, ev_comp_append]
  rfl

/-- The values of a code with parameters `X_k, …, X_{k+4}`. -/
theorem evCode_varPoint (y : ℕ → ℚ) (k : ℕ) : evCode y (varPoint k) = fun i : Fin 5 => y (k + i) :=
  funext fun i => ev_varPoint y k i

/-- The values of `neg(p)` are `negCode` of the values of `p`. -/
theorem evCode_neg (y : ℕ → ℚ) (p : Code) : evCode y p.neg = negCode (evCode y p) := by
  funext i
  fin_cases i <;> simp [evCode, Code.neg, negCode]

/-- `neg(ι(m)) = ι(-m)`. -/
theorem evCode_neg_iota {y : ℕ → ℚ} {p : Code} {m : ℤ} (h : evCode y p = iota m) :
    evCode y p.neg = iota (-m) := by
  rw [evCode_neg, h, iota_neg]

/-- The code of `O`. -/
theorem evCode_O' (y : ℕ → ℚ) : evCode y Code.O = iota 0 := by
  rw [evCode_O, iota_zero]

/-- The values of a code depend only on the variables of its coordinates. -/
theorem evCode_congr {y y' : ℕ → ℚ} {p : Code} (h : ∀ i, ∀ j ∈ (p i).vars, y j = y' j) :
    evCode y p = evCode y' p :=
  funext fun i => ev_congr (h i)

/-- The generator point `(0, X_c, -145, X_{c+1}, X_{c+2})` at the generator constants is
`ι(1)`. -/
theorem evCode_genPoint {y : ℕ → ℚ} {c : ℕ} (h0 : y c = 1641 / 8) (h1 : y (c + 1) = -15465 / 4)
    (h2 : y (c + 2) = 87483 / 32) : evCode y (genPoint c) = iota 1 := by
  rw [iota_one]
  funext i
  fin_cases i <;> simp [evCode, genPoint, h0, h1, h2]

/-- The first coordinate of `ι(m)` is `0` exactly when `m ≠ 0`. -/
theorem iota_apply_zero_eq_zero_iff (m : ℤ) : iota m 0 = 0 ↔ m ≠ 0 := by
  rw [iota_def, pointCode_apply_zero]
  have : m • genP0 = 0 ↔ m = 0 := by
    constructor
    · intro h
      exact iota_injective (by rw [iota_def, h, iota_zero]; rfl)
    · rintro rfl; exact zero_zsmul _
  split_ifs with h <;> simp_all

end ZInQ.Assembly
