import ZInQKernel.Syntax.Constants.Expr
import ZInQKernel.Syntax.Constants.PrimorialLiteral
import ZInQ.ExplicitCutoffBounds

/-!
# The prescribed fixed constants

Blueprint: `syntax/constants/fixed-constants.md`.

The specification binds eighteen named fixed integer expressions, in this order:
`P0, W, Hproduct, Hmax, Ns, M, cstar, ell, F, D, G0, E0, R, Q, Bcm, Ccm, Aheight, T`.

* `FixedConst` enumerates them and `FixedConst.expr` is the expression bound to each name,
  node for node as in `library.fixedConstants` of the saved specification (in particular `P0`
  and `W` are the decimal literals stored there). Every expression refers only to earlier
  names (`FixedConst.expr_refs_lt`), and `FixedConst.value` evaluates the names in order.
* `Ps, W, Hcat, Hmax, Ns, M0, cstar, ell, F, D, G0, E0, R, Q, Bcm, Ccm, Aht, T` are the same
  constants as natural numbers, each defined by its formula in the table
  (`Ps = ∏_{p ≤ 324} p`, `W = 4 Ps`, …). `FixedConst.value_P0`, … identify the two; for `P0`
  and `W` this is the decimal check of `PrimorialLiteral.lean`.

None of these constants except `G0` is evaluated; all facts below are proved from the
defining equations.
-/

namespace ZInQ.Syntax

/-! ### The formulas of the table

Each formula is a function of the earlier constants. The named constants below are these
functions applied to the earlier named constants, and their defining equations (`Ns_eq`, …) are
instances of the generic equations `FixedFormula.Ns_eq`, …, proved for variables.

This indirection is what keeps the constants unevaluated: the kernel checks a definitional
unfolding of a closed arithmetic term such as `Ps * Hcat` by unfolding `HMul.hMul` to
`Nat.mul Ps Hcat` and then trying to evaluate both arguments to numerals. Unfolding `Ns` only
produces `FixedFormula.Ns Ps Hcat`, and the arithmetic is only ever unfolded with variables. -/

namespace FixedFormula

/-- `W = 4 P_s`. -/
def W (p : ℕ) : ℕ := 4 * p
/-- `N_s = P_s H_cat`. -/
def Ns (p h : ℕ) : ℕ := p * h
/-- `c_* = 4 M₀`. -/
def cstar (m : ℕ) : ℕ := 4 * m
/-- `ℓ = 12 P_s^2916 H_cat^732`. -/
def ell (p h : ℕ) : ℕ := 12 * (p ^ 2916 * h ^ 732)
/-- `D = F · 3^(256 F⁴)`. -/
def D (f : ℕ) : ℕ := f * 3 ^ (256 * f ^ 4)
/-- `E₀ = 10 (D G₀)²`. -/
def E0 (d g : ℕ) : ℕ := 10 * (d * g) ^ 2
/-- `R = max(D, H_max, c_*, 10¹²)`. -/
def R (d h c : ℕ) : ℕ := max (max (max d h) c) (10 ^ 12)
/-- `Q = R^(R E₀)`. -/
def Q (r e : ℕ) : ℕ := r ^ (r * e)
/-- `B_cm = D² 3^(21000 D²) + 1`. -/
def Bcm (d : ℕ) : ℕ := d ^ 2 * 3 ^ (21000 * d ^ 2) + 1
/-- `C_cm = 2 B_cm + 4096 ((1028 + 5D) + 84000 D²)`. -/
def Ccm (b d : ℕ) : ℕ := 2 * b + 4096 * ((1028 + 5 * d) + 84000 * d ^ 2)
/-- `A_ht = 2·10¹³ · max(1, C_cm, Q¹⁷)`. -/
def Aht (c q : ℕ) : ℕ := 2 * 10 ^ 13 * max (max 1 c) (q ^ 17)
/-- `T = (48 A_ht)¹³`. -/
def T (a : ℕ) : ℕ := (48 * a) ^ 13

theorem W_eq (p : ℕ) : W p = 4 * p := rfl
theorem Ns_eq (p h : ℕ) : Ns p h = p * h := rfl
theorem cstar_eq (m : ℕ) : cstar m = 4 * m := rfl
theorem ell_eq (p h : ℕ) : ell p h = 12 * (p ^ 2916 * h ^ 732) := rfl
theorem D_eq (f : ℕ) : D f = f * 3 ^ (256 * f ^ 4) := rfl
theorem E0_eq (d g : ℕ) : E0 d g = 10 * (d * g) ^ 2 := rfl
theorem R_eq (d h c : ℕ) : R d h c = max (max (max d h) c) (10 ^ 12) := rfl
theorem Q_eq (r e : ℕ) : Q r e = r ^ (r * e) := rfl
theorem Bcm_eq (d : ℕ) : Bcm d = d ^ 2 * 3 ^ (21000 * d ^ 2) + 1 := rfl
theorem Ccm_eq (b d : ℕ) : Ccm b d = 2 * b + 4096 * ((1028 + 5 * d) + 84000 * d ^ 2) := rfl
theorem Aht_eq (c q : ℕ) : Aht c q = 2 * 10 ^ 13 * max (max 1 c) (q ^ 17) := rfl
theorem T_eq (a : ℕ) : T a = (48 * a) ^ 13 := rfl

end FixedFormula

/-! ### The named constants -/

/-- `P_s = ∏_{p ≤ 324} p`. -/
def Ps : ℕ := primorial 324
/-- `W = 4 P_s`. -/
def W : ℕ := FixedFormula.W Ps
/-- `H_cat = catalogue_product(W, 22, 324)`. -/
noncomputable def Hcat : ℕ := catalogueProduct W 22 324
/-- `H_max = catalogue_max(W, 22, 324)`. -/
noncomputable def Hmax : ℕ := catalogueMax W 22 324
/-- `N_s = P_s H_cat`. -/
noncomputable def Ns : ℕ := FixedFormula.Ns Ps Hcat
/-- `M₀ = least_formal_multiple(N_s)`. -/
noncomputable def M0 : ℕ := leastFormalMultiple Ns
/-- `c_* = 4 M₀`. -/
noncomputable def cstar : ℕ := FixedFormula.cstar M0
/-- `ℓ = 12 P_s^2916 H_cat^732`. -/
noncomputable def ell : ℕ := FixedFormula.ell Ps Hcat
/-- `F = 324!`. -/
def F : ℕ := Nat.factorial 324
/-- `D = F · 3^(256 F⁴)`. -/
def D : ℕ := FixedFormula.D F
/-- `G₀ = 116064000000`. -/
def G0 : ℕ := 116064000000
/-- `E₀ = 10 (D G₀)²`. -/
def E0 : ℕ := FixedFormula.E0 D G0
/-- `R = max(D, H_max, c_*, 10¹²)`. -/
noncomputable def R : ℕ := FixedFormula.R D Hmax cstar
/-- `Q = R^(R E₀)`. -/
noncomputable def Q : ℕ := FixedFormula.Q R E0
/-- `B_cm = D² 3^(21000 D²) + 1`. -/
def Bcm : ℕ := FixedFormula.Bcm D
/-- `C_cm = 2 B_cm + 4096 ((1028 + 5D) + 84000 D²)`. -/
def Ccm : ℕ := FixedFormula.Ccm Bcm D
/-- `A_ht = 2·10¹³ · max(1, C_cm, Q¹⁷)`, the six-contact constant `H₆(S; R)`. -/
noncomputable def Aht : ℕ := FixedFormula.Aht Ccm Q
/-- `T = (48 A_ht)¹³`, the cutoff of the finite guard. -/
noncomputable def T : ℕ := FixedFormula.T Aht

/-! ### The defining equations -/

theorem Ps_eq : Ps = primorial 324 := rfl
theorem W_eq : W = 4 * Ps := FixedFormula.W_eq Ps
theorem Hcat_eq : Hcat = catalogueProduct W 22 324 := rfl
theorem Hmax_eq : Hmax = catalogueMax W 22 324 := rfl
theorem Ns_eq : Ns = Ps * Hcat := FixedFormula.Ns_eq Ps Hcat
theorem M0_eq : M0 = leastFormalMultiple Ns := rfl
theorem cstar_eq : cstar = 4 * M0 := FixedFormula.cstar_eq M0
theorem ell_eq : ell = 12 * (Ps ^ 2916 * Hcat ^ 732) := FixedFormula.ell_eq Ps Hcat
theorem F_eq : F = Nat.factorial 324 := rfl
theorem D_eq : D = F * 3 ^ (256 * F ^ 4) := FixedFormula.D_eq F
theorem G0_eq : G0 = 116064000000 := rfl
theorem E0_eq : E0 = 10 * (D * G0) ^ 2 := FixedFormula.E0_eq D G0
theorem R_eq : R = max (max (max D Hmax) cstar) (10 ^ 12) := FixedFormula.R_eq D Hmax cstar
theorem Q_eq : Q = R ^ (R * E0) := FixedFormula.Q_eq R E0
theorem Bcm_eq : Bcm = D ^ 2 * 3 ^ (21000 * D ^ 2) + 1 := FixedFormula.Bcm_eq D
theorem Ccm_eq : Ccm = 2 * Bcm + 4096 * ((1028 + 5 * D) + 84000 * D ^ 2) :=
  FixedFormula.Ccm_eq Bcm D
theorem Aht_eq : Aht = 2 * 10 ^ 13 * max (max 1 Ccm) (Q ^ 17) := FixedFormula.Aht_eq Ccm Q
theorem T_eq : T = (48 * Aht) ^ 13 := FixedFormula.T_eq Aht

/- None of these constants is ever evaluated: from here on the elaborator may only unfold them
through the equations above. -/
attribute [irreducible] Ps W Hcat Hmax Ns M0 cstar ell F D G0 E0 R Q Bcm Ccm Aht T

/-! ### The specification's constant table -/

/-- The eighteen named fixed constants of the specification, in specification order. -/
inductive FixedConst
  | P0 | W | Hproduct | Hmax | Ns | M | cstar | ell | F | D | G0 | E0 | R | Q | Bcm | Ccm
  | Aheight | T
  deriving DecidableEq, Repr

namespace FixedConst

/-- The position of a constant in the specification order. -/
def idx : FixedConst → ℕ
  | P0 => 0 | W => 1 | Hproduct => 2 | Hmax => 3 | Ns => 4 | M => 5 | cstar => 6 | ell => 7
  | F => 8 | D => 9 | G0 => 10 | E0 => 11 | R => 12 | Q => 13 | Bcm => 14 | Ccm => 15
  | Aheight => 16 | T => 17

/-- The name of a constant in the saved specification. -/
def name : FixedConst → String
  | P0 => "P0" | W => "W" | Hproduct => "Hproduct" | Hmax => "Hmax" | Ns => "Ns" | M => "M"
  | cstar => "cstar" | ell => "ell" | F => "F" | D => "D" | G0 => "G0" | E0 => "E0" | R => "R"
  | Q => "Q" | Bcm => "Bcm" | Ccm => "Ccm" | Aheight => "Aheight" | T => "T"

/-- The fixed integer expression bound to each name, as in the saved specification. -/
def expr : FixedConst → FixedExpr FixedConst
  | P0 => .literal
      19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570
  | W => .literal
      77445546562803292653885700217249280330651590450286255047627849656860049479426548716387789340974722678430125902516592961137599906280
  | Hproduct => .catalogueProduct (.ref W) (.literal 22) (.literal 324)
  | Hmax => .catalogueMax (.ref W) (.literal 22) (.literal 324)
  | Ns => .mul (.ref P0) (.ref Hproduct)
  | M => .leastFormalMultiple (.ref Ns)
  | cstar => .mul (.literal 4) (.ref M)
  | ell => .mul (.literal 12) (.mul (.pow (.ref P0) (.literal 2916)) (.pow (.ref Hproduct) (.literal 732)))
  | F => .factorial (.literal 324)
  | D => .mul (.ref F) (.pow (.literal 3) (.mul (.literal 256) (.pow (.ref F) (.literal 4))))
  | G0 => .literal 116064000000
  | E0 => .mul (.literal 10) (.pow (.mul (.ref D) (.ref G0)) (.literal 2))
  | R => .max (.ref D) [.ref Hmax, .ref cstar, .pow (.literal 10) (.literal 12)]
  | Q => .pow (.ref R) (.mul (.ref R) (.ref E0))
  | Bcm => .add (.mul (.pow (.ref D) (.literal 2))
      (.pow (.literal 3) (.mul (.literal 21000) (.pow (.ref D) (.literal 2))))) (.literal 1)
  | Ccm => .add (.mul (.literal 2) (.ref Bcm)) (.mul (.literal 4096)
      (.add (.add (.literal 1028) (.mul (.literal 5) (.ref D)))
        (.mul (.literal 84000) (.pow (.ref D) (.literal 2)))))
  | Aheight => .mul (.mul (.literal 2) (.pow (.literal 10) (.literal 13)))
      (.max (.literal 1) [.ref Ccm, .pow (.ref Q) (.literal 17)])
  | T => .pow (.mul (.literal 48) (.ref Aheight)) (.literal 13)

/-- Every expression refers only to earlier names. -/
theorem expr_refs_lt : ∀ c : FixedConst, ∀ d ∈ c.expr.refs, d.idx < c.idx := by
  intro c; cases c <;> decide

/-- The value of a named constant: its expression evaluated with the values of the earlier
names (references to later names, which do not occur, would read `0`). -/
noncomputable def value (c : FixedConst) : ℤ :=
  c.expr.val fun d => if _h : d.idx < c.idx then d.value else 0
termination_by c.idx

theorem value_eq (c : FixedConst) :
    c.value = c.expr.val fun d => if d.idx < c.idx then d.value else 0 := by
  rw [value]; rfl

/-- The value of a named constant is its expression evaluated at the values of all names. -/
theorem value_eq_val (c : FixedConst) : c.value = c.expr.val value := by
  rw [value_eq]
  exact FixedExpr.val_congr _ fun d hd => ite_eq_left (expr_refs_lt c d hd)

/-- The value map of the specification's fixed integer expressions (the `val` of the
constructor symbols): expressions are evaluated with the values of the named constants. -/
noncomputable def fixedVal (e : FixedExpr FixedConst) : ℤ := e.val value

theorem fixedVal_ref (c : FixedConst) : fixedVal (.ref c) = c.value := FixedExpr.val_ref _ c

/-! ### The values of the named constants -/

open FixedExpr

/-- Reduce `val value e = ↑n` along the shape of `e` with the transfer lemmas, closing
references with the hypotheses in context. Nothing is unfolded or evaluated. -/
macro "fixed_val" : tactic => `(tactic| repeat (first
  | exact val_literal_eq rfl
  | exact val_ref_eq (by assumption)
  | refine val_add_eq ?_ ?_
  | refine val_mul_eq ?_ ?_
  | refine val_pow_eq ?_ ?_
  | refine val_factorial_eq ?_
  | refine val_catalogueProduct_eq ?_ ?_ ?_
  | refine val_catalogueMax_eq ?_ ?_ ?_
  | refine val_leastFormalMultiple_eq ?_))

theorem value_P0 : P0.value = (Ps : ℤ) := by
  rw [value_eq_val, expr, val_literal, Ps_eq, primorial_324_eq]; rfl

theorem value_W : W.value = (Syntax.W : ℤ) := by
  rw [value_eq_val, expr, val_literal, W_eq, Ps_eq, four_mul_primorial_324_eq]; rfl

theorem value_Hproduct : Hproduct.value = (Hcat : ℤ) := by
  have := value_W
  rw [value_eq_val, expr, Hcat_eq]; fixed_val

theorem value_Hmax : Hmax.value = (Syntax.Hmax : ℤ) := by
  have := value_W
  rw [value_eq_val, expr, Hmax_eq]; fixed_val

theorem value_Ns : Ns.value = (Syntax.Ns : ℤ) := by
  have := value_P0; have := value_Hproduct
  rw [value_eq_val, expr, Ns_eq]; fixed_val

theorem value_M : M.value = (M0 : ℤ) := by
  have := value_Ns
  rw [value_eq_val, expr, M0_eq]; fixed_val

theorem value_cstar : cstar.value = (Syntax.cstar : ℤ) := by
  have := value_M
  rw [value_eq_val, expr, cstar_eq]; fixed_val

theorem value_ell : ell.value = (Syntax.ell : ℤ) := by
  have := value_P0; have := value_Hproduct
  rw [value_eq_val, expr, ell_eq]; fixed_val

theorem value_F : F.value = (Syntax.F : ℤ) := by
  rw [value_eq_val, expr, F_eq]; fixed_val

theorem value_D : D.value = (Syntax.D : ℤ) := by
  have := value_F
  rw [value_eq_val, expr, D_eq]; fixed_val

theorem value_G0 : G0.value = (Syntax.G0 : ℤ) := by
  rw [value_eq_val, expr, G0_eq]; fixed_val

theorem value_E0 : E0.value = (Syntax.E0 : ℤ) := by
  have := value_D; have := value_G0
  rw [value_eq_val, expr, E0_eq]; fixed_val

theorem value_R : R.value = (Syntax.R : ℤ) := by
  have := value_D; have := value_Hmax; have := value_cstar
  rw [value_eq_val, expr, R_eq]
  refine val_max_three_eq ?_ ?_ ?_ ?_ <;> fixed_val

theorem value_Q : Q.value = (Syntax.Q : ℤ) := by
  have := value_R; have := value_E0
  rw [value_eq_val, expr, Q_eq]; fixed_val

theorem value_Bcm : Bcm.value = (Syntax.Bcm : ℤ) := by
  have := value_D
  rw [value_eq_val, expr, Bcm_eq]; fixed_val

theorem value_Ccm : Ccm.value = (Syntax.Ccm : ℤ) := by
  have := value_D; have := value_Bcm
  rw [value_eq_val, expr, Ccm_eq]; fixed_val

theorem value_Aheight : Aheight.value = (Aht : ℤ) := by
  have := value_Ccm; have := value_Q
  rw [value_eq_val, expr, Aht_eq]
  refine val_mul_eq ?_ (val_max_two_eq ?_ ?_ ?_) <;> fixed_val

theorem value_T : T.value = (Syntax.T : ℤ) := by
  have := value_Aheight
  rw [value_eq_val, expr, T_eq]; fixed_val

end FixedConst

end ZInQ.Syntax
