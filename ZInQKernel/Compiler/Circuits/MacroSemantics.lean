import ZInQKernel.Compiler.Circuits.Compilation
import ZInQKernel.Compiler.Circuits.Gadgets
import ZInQ.BinomialDigit
import ZInQ.BitwiseMacros
import ZInQKernel.Compiler.Exponential.PowerEquations

/-!
# Semantics of the natural macros

For every gadget and macro of the natural constructions, run from counter `c₀` on argument
polynomials whose variables lie in a set `U` below `c₀` and which take natural values at
natural points, the private-witness statement
`∃ y : [c₀, c₁) → ℕ, φ holds naturally at x[y]` is equivalent to the listed relation of the
argument values (`MSpec`):

| macro | relation |
| --- | --- |
| `lt a b` | `a < b` |
| `divides a b` | `a ∣ b` |
| `congruent a M b` | `a ≡ b [MOD M]` |
| `odd x` | `x` odd |
| `alpha X b N` | the alpha formula (C.2) |
| `power P Q R` (flat) | the power formula (C.3) |
| `power P Q R` (hierarchical) | `P = Q ^ R`, given the power-template semantics |
| `binomial C N K` | `C = choose N K` |
| `orthogonal a b` | `a AND b = 0` |
| `mask a b` | `a AND b = a` |
| `bitAnd z x y` | `z = x AND y` |

The alpha and power relations are stated as the formulas `AlphaFormula`, `PowerFormula`
(the alpha and power formulas of the exponential section); that these mean `X = α_b(N)` and
`P = Q^R` is the content of the exponential section. The macros above `power` are proved for
either mode from the hypothesis `PowerSpec τ mode` that the power macro means `P = Q^R`.

(Blueprint: `compiler/natural/formulas/macro-semantics.md`.)
-/

set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

variable {τ : ExPoly}

/-! ### Tools -/

theorem zv_update {x : ℕ → ℕ} {c z : ℕ} {f : Poly} {U : Set ℕ} (hf : VarsIn f (· ∈ U))
    (hc : c ∉ U) : zv (Function.update x c z) f = zv x f :=
  zv_congr fun i hi => Function.update_of_ne (fun (h : i = c) => hc (h ▸ hf i hi)) _ _

theorem nv_update {x : ℕ → ℕ} {c z : ℕ} {f : Poly} {U : Set ℕ} (hf : VarsIn f (· ∈ U))
    (hc : c ∉ U) : nv (Function.update x c z) f = nv x f := by
  rw [nv, nv, zv_update hf hc]

theorem notMem_of_lt {U : Set ℕ} {c : ℕ} (hU : ∀ i ∈ U, i < c) : c ∉ U :=
  fun h => lt_irrefl c (hU c h)

/-- A fresh variable at the front of a construction, state form. -/
theorem Spec.fresh_bind {f : Ex → NM NForm} {U : Set ℕ} {s : State} {R : (ℕ → ℕ) → Prop}
    (h : Spec ((f (Natural.fresh s).1 (Natural.fresh s).2).1.toFormula τ) (insert s.next U)
      (Natural.fresh s).2.next (f (Natural.fresh s).1 (Natural.fresh s).2).2.next R) :
    Spec (((Natural.fresh >>= f) s).1.toFormula τ) U s.next ((Natural.fresh >>= f) s).2.next
      fun x => ∃ z, R (Function.update x s.next z) := by
  rw [fresh_apply_next] at h
  exact Spec.fresh h

@[simp] theorem note_apply_next (k : MacroKind) (s : State) : (note k s).2.next = s.next := rfl

/-- Logging a macro does not change its specification, state form. -/
theorem Spec.note_bind {k : MacroKind} {f : Unit → NM NForm} {U : Set ℕ} {s : State}
    {R : (ℕ → ℕ) → Prop}
    (h : Spec ((f () (note k s).2).1.toFormula τ) U (note k s).2.next (f () (note k s).2).2.next R) :
    Spec (((note k >>= f) s).1.toFormula τ) U s.next ((note k >>= f) s).2.next R := h

theorem note_lt {U : Set ℕ} {s : State} {k : MacroKind} (hs : ∀ i ∈ U, i < s.next) :
    ∀ i ∈ U, i < (note k s).2.next := hs

theorem MSpec.note_bind {k : MacroKind} {f : Unit → NM NForm} {U : Set ℕ} {R : (ℕ → ℕ) → Prop}
    (h : MSpec τ (f ()) U R) : MSpec τ (note k >>= f) U R := fun s hs => h (note k s).2 hs

@[simp] theorem constant_apply_poly (c : ℤ) (s : State) : (constant c s).1.poly = C c := rfl

@[simp] theorem constant_apply_next (c : ℤ) (s : State) : (constant c s).2.next = s.next :=
  ((IsExpr.constant c) s).2.1

/-- An expression construction at the front of a construction, state form. -/
theorem Spec.expr_bind {m : NM Ex} {P : Poly} {f : Ex → NM NForm} {U : Set ℕ} {s : State}
    {R : (ℕ → ℕ) → Prop} (hm : IsExpr m P)
    (h : Spec ((f (m s).1 (m s).2).1.toFormula τ) U (m s).2.next (f (m s).1 (m s).2).2.next R) :
    Spec (((m >>= f) s).1.toFormula τ) U s.next ((m >>= f) s).2.next R := by
  rw [(hm s).2.1] at h
  exact h

theorem fresh_next_lt {U : Set ℕ} {s : State} (hs : ∀ i ∈ U, i < s.next) :
    ∀ i ∈ insert s.next U, i < (fresh s).2.next := by
  rw [fresh_apply_next]; exact insert_lt hs

/-- An atom `a ≐ b` with the polynomials of `a, b` given. -/
theorem MSpec.eq' {a b : Ex} {A B : Poly} {U : Set ℕ} (ha : a.poly = A) (hb : b.poly = B)
    (hA : VarsIn A (· ∈ U)) (hB : VarsIn B (· ∈ U)) :
    MSpec τ (Pure.pure (.eq a b)) U fun x => zv x A = zv x B := by
  have := MSpec.eq τ (a := a) (b := b) (U := U) (ha ▸ hA) (hb ▸ hB)
  rwa [ha, hb] at this

theorem IsNat.C_of_nonneg {c : ℤ} (hc : 0 ≤ c) : IsNat (C c) := fun x => by simpa using hc

@[simp] theorem nv_C_two (x : ℕ → ℕ) : nv x (C 2) = 2 := by simp [nv]

@[simp] theorem nv_C_three (x : ℕ → ℕ) : nv x (C 3) = 3 := by simp [nv]

@[simp] theorem nv_C_four (x : ℕ → ℕ) : nv x (C 4) = 4 := by simp [nv]

@[simp] theorem nv_C_one (x : ℕ → ℕ) : nv x (C 1) = 1 := by simp [nv]

@[simp] theorem nv_C_zero (x : ℕ → ℕ) : nv x (C 0) = 0 := by simp [nv]

attribute [simp] nv_X

theorem nv_two_mul {f : Poly} (hf : IsNat f) (x : ℕ → ℕ) : nv x (C 2 * f) = 2 * nv x f := by
  rw [nv_mul (IsNat.C_of_nonneg (by norm_num)) hf, nv_C_two]

@[simp] theorem nv_X_mul_X (x : ℕ → ℕ) (i j : ℕ) : nv x (X i * X j) = x i * x j := by
  rw [nv_mul (IsNat.X i) (IsNat.X j), nv_X, nv_X]

theorem VarsIn.mem_insert {f : Poly} {U : Set ℕ} {c : ℕ} (h : VarsIn f (· ∈ U)) :
    VarsIn f (· ∈ insert c U) := h.mono fun _ hi => Set.mem_insert_of_mem _ hi

set_option hygiene false in
/-- Normalizes the polynomial of an expression handle. -/
macro "poly_simp" h:ident : tactic =>
  `(tactic| simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.prod_cons,
      List.prod_nil, add_zero, mul_one, fresh_apply_poly, *] at $h:ident)

set_option hygiene false in
/-- Closes variable-range side goals. -/
macro "vars_tac" : tactic =>
  `(tactic| ((try (simp only [fresh_apply_next, fresh_apply_poly, constant_apply_next,
      constant_apply_poly, note_apply_next] at *)); repeat (first
      | with_reducible exact VarsIn.ofNat _ _
      | with_reducible exact VarsIn.C _ _
      | with_reducible exact VarsIn.zero _
      | with_reducible exact VarsIn.one _
      | (with_reducible apply VarsIn.X; simp; omega)
      | (with_reducible apply VarsIn.X; simp)
      | with_reducible apply VarsIn.add
      | with_reducible apply VarsIn.mul
      | with_reducible apply VarsIn.pow
      | with_reducible apply VarsIn.neg
      | with_reducible assumption
      | exact VarsIn.mono (by with_reducible assumption) (fun _ hi => by simp [hi]))))

set_option hygiene false in
/-- Closes natural-value side goals. -/
macro "isnat_tac" : tactic =>
  `(tactic| ((try (simp only [fresh_apply_poly, constant_apply_poly])); repeat (first
      | assumption
      | with_reducible exact IsNat.X _
      | with_reducible exact IsNat.C_of_nonneg (by norm_num)
      | with_reducible apply IsNat.add
      | with_reducible apply IsNat.mul)))

/-! ### The equational gadgets -/

theorem lt_spec {U : Set ℕ} {A B : Poly} (hA : VarsIn A (· ∈ U)) (hB : VarsIn B (· ∈ U))
    (hAn : IsNat A) (hBn : IsNat B) {a b : Ex} (ha : a.poly = A) (hb : b.poly = B) :
    MSpec τ (lt a b) U fun x => nv x A < nv x B := by
  intro s hs
  refine (Spec.note_bind (Spec.fresh_bind (R := ?R) ?h1)).congr ?h2
  case h1 =>
    refine MSpec.expr_bind (U := insert s.next U) (IsExpr.constant 1) (fun one hone => ?_) _
      (fresh_next_lt (note_lt hs))
    refine MSpec.expr_bind (IsExpr.addL _) (fun e he => ?_)
    poly_simp he
    exact MSpec.eq' (U := insert s.next U) hb he (VarsIn.mem_insert hB) (by
      apply VarsIn.add; exact VarsIn.mem_insert hA; apply VarsIn.add; exact VarsIn.C _ _; apply VarsIn.X; simp)
  case h2 =>
    intro x
    simp only [note_apply_next]
    have hc := notMem_of_lt hs
    simp only [zv_update hA hc, zv_update hB hc, zv_add, zv_C, zv_X, Function.update_self,
      hAn.zv_eq, hBn.zv_eq]
    rw [← lt_gadget_iff]
    exact exists_congr fun z => by omega

theorem divides_spec {U : Set ℕ} {A B : Poly} (hA : VarsIn A (· ∈ U)) (hB : VarsIn B (· ∈ U))
    (hAn : IsNat A) (hBn : IsNat B) {a b : Ex} (ha : a.poly = A) (hb : b.poly = B) :
    MSpec τ (divides a b) U fun x => nv x A ∣ nv x B := by
  intro s hs
  refine (Spec.note_bind (Spec.fresh_bind (R := ?R) ?h1)).congr ?h2
  case h1 =>
    refine MSpec.expr_bind (U := insert s.next U) (IsExpr.mulL _) (fun e he => ?_) _
      (fresh_next_lt (note_lt hs))
    poly_simp he
    exact MSpec.eq' (U := insert s.next U) hb he (by vars_tac) (by vars_tac)
  case h2 =>
    intro x
    simp only [note_apply_next]
    have hc := notMem_of_lt hs
    simp only [zv_update hA hc, zv_update hB hc, zv_mul, zv_X, Function.update_self,
      hAn.zv_eq, hBn.zv_eq]
    exact exists_congr fun z => by norm_cast

theorem congruent_spec {U : Set ℕ} {A M B : Poly} (hA : VarsIn A (· ∈ U))
    (hM : VarsIn M (· ∈ U)) (hB : VarsIn B (· ∈ U)) (hAn : IsNat A) (hMn : IsNat M)
    (hBn : IsNat B) {a m b : Ex} (ha : a.poly = A) (hm : m.poly = M) (hb : b.poly = B) :
    MSpec τ (congruent a m b) U fun x => nv x A ≡ nv x B [MOD nv x M] := by
  intro s hs
  refine (Spec.note_bind (Spec.fresh_bind (R := ?R) ?h1)).congr ?h2
  case h1 =>
    refine Spec.fresh_bind (R := ?R2) ?h3
    case h3 =>
    refine MSpec.expr_bind (U := insert (fresh (note .congruent s).2).2.next (insert s.next U)) (IsExpr.mulL _)
      (fun e1 he1 => ?_) _ (fresh_next_lt (fresh_next_lt (note_lt hs)))
    refine MSpec.expr_bind (IsExpr.addL _) (fun l hl => ?_)
    refine MSpec.expr_bind (IsExpr.mulL _) (fun e2 he2 => ?_)
    refine MSpec.expr_bind (IsExpr.addL _) (fun r hr => ?_)
    poly_simp hl
    poly_simp hr
    exact MSpec.eq' (U := insert (fresh (note .congruent s).2).2.next (insert s.next U)) hl hr (by vars_tac)
      (by vars_tac)
  case h2 =>
    intro x
    simp only [note_apply_next]
    have hc := notMem_of_lt hs
    have hc1 : s.next + 1 ∉ insert s.next U := notMem_of_lt (insert_lt hs)
    simp only [fresh_apply_next, note_apply_next]
    simp only [zv_update (VarsIn.mem_insert hA) hc1, zv_update (VarsIn.mem_insert hB) hc1,
      zv_update (VarsIn.mem_insert hM) hc1, zv_update hA hc, zv_update hB hc, zv_update hM hc,
      zv_add, zv_mul, zv_X, Function.update_self, hAn.zv_eq, hBn.zv_eq, hMn.zv_eq]
    simp only [Function.update_of_ne (show s.next ≠ s.next + 1 by omega), Function.update_self]
    rw [← congr_gadget_iff]
    exact exists_congr fun z => exists_congr fun z' => by norm_cast

theorem odd_spec {U : Set ℕ} {A : Poly} (hA : VarsIn A (· ∈ U)) (hAn : IsNat A) {a : Ex}
    (ha : a.poly = A) : MSpec τ (odd a) U fun x => Odd (nv x A) := by
  intro s hs
  refine (Spec.note_bind (Spec.fresh_bind (R := ?R) ?h1)).congr ?h2
  case h1 =>
    refine MSpec.expr_bind (U := insert s.next U) (IsExpr.scale 2 _) (fun e1 he1 => ?_) _
      (fresh_next_lt (note_lt hs))
    refine MSpec.expr_bind (IsExpr.constant 1) (fun one hone => ?_)
    refine MSpec.expr_bind (IsExpr.addL _) (fun e he => ?_)
    poly_simp he
    exact MSpec.eq' (U := insert s.next U) ha he (by vars_tac) (by vars_tac)
  case h2 =>
    intro x
    simp only [note_apply_next]
    have hc := notMem_of_lt hs
    simp only [zv_update hA hc, zv_add, zv_mul, zv_C, zv_X, Function.update_self, hAn.zv_eq]
    rw [← odd_gadget_iff]
    exact exists_congr fun z => by omega

/-! ### The alpha macro -/

/-- The alpha formula (C.2) of the exponential section, with natural witnesses
`r, s, t, u, v, w, x, y`. -/
abbrev AlphaFormula (X b N : ℕ) : Prop := AlphaPower.AlphaEqns X b N

theorem zv_update_ge {f : Poly} {U : Set ℕ} {n : ℕ} (hf : VarsIn f (· ∈ U))
    (hU : ∀ i ∈ U, i < n) {x : ℕ → ℕ} {c z : ℕ} (hc : n ≤ c) :
    zv (Function.update x c z) f = zv x f :=
  zv_update hf fun h => by have := hU c h; omega

theorem nv_update_ge {f : Poly} {U : Set ℕ} {n : ℕ} (hf : VarsIn f (· ∈ U))
    (hU : ∀ i ∈ U, i < n) {x : ℕ → ℕ} {c z : ℕ} (hc : n ≤ c) :
    nv (Function.update x c z) f = nv x f := by
  rw [nv, nv, zv_update_ge hf hU hc]

theorem alpha_spec {U : Set ℕ} {XP BP NP : Poly} (hX : VarsIn XP (· ∈ U)) (hB : VarsIn BP (· ∈ U))
    (hN : VarsIn NP (· ∈ U)) (hXn : IsNat XP) (hBn : IsNat BP) (hNn : IsNat NP) {X b N : Ex}
    (hXe : X.poly = XP) (hbe : b.poly = BP) (hNe : N.poly = NP) :
    MSpec τ (alpha X b N) U fun x => AlphaFormula (nv x XP) (nv x BP) (nv x NP) := by
  intro s hs
  apply Spec.congr
  · apply Spec.note_bind
    apply Spec.fresh_bind; apply Spec.fresh_bind; apply Spec.fresh_bind; apply Spec.fresh_bind
    apply Spec.fresh_bind; apply Spec.fresh_bind; apply Spec.fresh_bind; apply Spec.fresh_bind
    apply MSpec.expr_bind (IsExpr.constant 1)
    · intro one hone
      apply MSpec.expr_bind (IsExpr.constant 2)
      intro two htwo
      apply MSpec.andM
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.constant 3); intro c3 hc3
        exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) hc3 hbe
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.mulL _); intro e1 he1
        apply MSpec.expr_bind (IsExpr.addL _); intro e2 he2
        apply MSpec.expr_bind (IsExpr.square _); intro e3 he3
        apply MSpec.expr_bind (IsExpr.square _); intro e4 he4
        apply MSpec.expr_bind (IsExpr.addL _); intro e5 he5
        poly_simp he2; poly_simp he5
        exact MSpec.eq' he2 he5 (by vars_tac) (by vars_tac)
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.mulL _); intro e1 he1
        apply MSpec.expr_bind (IsExpr.addL _); intro e2 he2
        apply MSpec.expr_bind (IsExpr.square _); intro e3 he3
        apply MSpec.expr_bind (IsExpr.square _); intro e4 he4
        apply MSpec.expr_bind (IsExpr.addL _); intro e5 he5
        poly_simp he2; poly_simp he5
        exact MSpec.eq' he2 he5 (by vars_tac) (by vars_tac)
      apply List.Forall₂.cons
      · exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) rfl rfl
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.square _); intro e1 he1
        exact divides_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) he1 rfl
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.scale 2 _); intro e1 he1
        apply MSpec.expr_bind (IsExpr.addL _); intro e2 he2
        apply MSpec.expr_bind (IsExpr.mulL _); intro e3 he3
        poly_simp he2; poly_simp he3
        exact MSpec.eq' he2 he3 (by vars_tac) (by vars_tac)
      apply List.Forall₂.cons
      · exact congruent_spec (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac)
          (by isnat_tac) (by isnat_tac) hbe rfl rfl
      apply List.Forall₂.cons
      · exact congruent_spec (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac)
          (by isnat_tac) (by isnat_tac) htwo rfl rfl
      apply List.Forall₂.cons
      · exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) htwo rfl
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.mulL _); intro e1 he1
        apply MSpec.expr_bind (IsExpr.addL _); intro e2 he2
        apply MSpec.expr_bind (IsExpr.square _); intro e3 he3
        apply MSpec.expr_bind (IsExpr.square _); intro e4 he4
        apply MSpec.expr_bind (IsExpr.addL _); intro e5 he5
        poly_simp he2; poly_simp he5
        exact MSpec.eq' he2 he5 (by vars_tac) (by vars_tac)
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.scale 2 _); intro e1 he1
        poly_simp he1
        exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) he1 rfl
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.scale 2 _); intro e1 he1
        poly_simp he1
        exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) he1 rfl
      apply List.Forall₂.cons
      · exact congruent_spec (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac)
          (by isnat_tac) (by isnat_tac) rfl rfl hXe
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.scale 2 _); intro e1 he1
        poly_simp he1
        exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) he1 rfl
      apply List.Forall₂.cons
      · exact congruent_spec (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac)
          (by isnat_tac) (by isnat_tac) rfl rfl hNe
      exact List.Forall₂.nil
    · exact fresh_next_lt (fresh_next_lt (fresh_next_lt (fresh_next_lt (fresh_next_lt
        (fresh_next_lt (fresh_next_lt (fresh_next_lt (note_lt hs))))))))
  · intro x
    simp (disch := omega) only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, fresh_apply_next, fresh_apply_poly, note_apply_next, zv_update_ge hB hs, zv_update_ge hX hs,
      zv_update_ge hN hs, nv_update_ge hB hs, nv_update_ge hX hs, nv_update_ge hN hs, zv_add,
      zv_mul, zv_X, zv_C, nv_two_mul hXn, nv_two_mul hNn, nv_X, nv_X_mul_X, nv_C_two, nv_C_three]
    simp only [Function.update_apply, Nat.add_assoc, Nat.reduceAdd, Nat.add_left_cancel_iff,
      Nat.left_eq_add, Nat.add_eq_left, OfNat.ofNat_ne_zero, reduceCtorEq, ite_true, ite_false,
      Nat.reduceEqDiff, hXn.zv_eq, hBn.zv_eq, hNn.zv_eq]
    constructor
    · rintro ⟨r, s', t, u, v, w, x', y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
        h14, h15⟩
      refine ⟨r, s', t, u, v, w, x', y, h1, ?_, ?_, h4, by rwa [sq], ?_, h7.symm, h8.symm, h9, ?_,
        h11, h12, h13, h14, h15⟩
      · exact_mod_cast (by linear_combination -h2 : ((u : ℤ) ^ 2 + t ^ 2 = 1 + nv x BP * u * t))
      · exact_mod_cast (by linear_combination -h3 : ((s' : ℤ) ^ 2 + r ^ 2 = 1 + nv x BP * s' * r))
      · exact_mod_cast h6
      · exact_mod_cast (by linear_combination -h10 : ((x' : ℤ) ^ 2 + y ^ 2 = 1 + w * x' * y))
    · rintro ⟨r, s', t, u, v, w, x', y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
        h14, h15⟩
      refine ⟨r, s', t, u, v, w, x', y, h1, ?_, ?_, h4, by rwa [← sq], ?_, h7.symm, h8.symm, h9, ?_,
        h11, h12, h13, h14, h15⟩
      · have h2' : ((u ^ 2 + t ^ 2 : ℕ) : ℤ) = ((1 + nv x BP * u * t : ℕ) : ℤ) := by rw [h2]
        push_cast at h2'
        linear_combination -h2'
      · have h3' : ((s' ^ 2 + r ^ 2 : ℕ) : ℤ) = ((1 + nv x BP * s' * r : ℕ) : ℤ) := by rw [h3]
        push_cast at h3'
        linear_combination -h3'
      · exact_mod_cast h6
      · have h10' : ((x' ^ 2 + y ^ 2 : ℕ) : ℤ) = ((1 + w * x' * y : ℕ) : ℤ) := by rw [h10]
        push_cast at h10'
        linear_combination -h10'

/-! ### The flat power macro -/

/-- The power formula (C.3) of the exponential section. -/
abbrev PowerFormula (P Q R : ℕ) : Prop := AlphaPower.PowEqns P Q R

theorem powerFlat_spec {U : Set ℕ} {PP QP RP : Poly} (hP : VarsIn PP (· ∈ U))
    (hQ : VarsIn QP (· ∈ U)) (hR : VarsIn RP (· ∈ U)) (hPn : IsNat PP) (hQn : IsNat QP)
    (hRn : IsNat RP) {P Q R : Ex} (hPe : P.poly = PP) (hQe : Q.poly = QP) (hRe : R.poly = RP) :
    MSpec τ (powerFlat P Q R) U fun x => PowerFormula (nv x PP) (nv x QP) (nv x RP) := by
  intro s hs
  apply Spec.congr
  · apply Spec.expr_bind (IsExpr.constant 0)
    apply Spec.expr_bind (IsExpr.constant 1)
    apply Spec.fresh_bind; apply Spec.fresh_bind; apply Spec.fresh_bind; apply Spec.fresh_bind
    apply Spec.fresh_bind
    apply MSpec.orM
    · apply List.Forall₂.cons
      · apply MSpec.andM
        apply List.Forall₂.cons
        · exact MSpec.eq' hQe rfl (by vars_tac) (by vars_tac)
        apply List.Forall₂.cons
        · exact MSpec.eq' hRe rfl (by vars_tac) (by vars_tac)
        apply List.Forall₂.cons
        · exact MSpec.eq' hPe rfl (by vars_tac) (by vars_tac)
        exact List.Forall₂.nil
      apply List.Forall₂.cons
      · apply MSpec.andM
        apply List.Forall₂.cons
        · exact MSpec.eq' hQe rfl (by vars_tac) (by vars_tac)
        apply List.Forall₂.cons
        · exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) rfl hRe
        apply List.Forall₂.cons
        · exact MSpec.eq' hPe rfl (by vars_tac) (by vars_tac)
        exact List.Forall₂.nil
      apply List.Forall₂.cons
      · apply MSpec.andM
        apply List.Forall₂.cons
        · exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) rfl hQe
        apply List.Forall₂.cons
        · apply MSpec.expr_bind (IsExpr.constant 4); intro c4 hc4
          apply MSpec.expr_bind (IsExpr.addL _); intro e1 he1
          apply MSpec.expr_bind (IsExpr.addL _); intro e2 he2
          poly_simp he1; poly_simp he2
          exact alpha_spec (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac)
            (by isnat_tac) rfl he1 he2
        apply List.Forall₂.cons
        · apply MSpec.expr_bind (IsExpr.square _); intro e1 he1
          apply MSpec.expr_bind (IsExpr.constant 2); intro c2 hc2
          apply MSpec.expr_bind (IsExpr.addL _); intro e2 he2
          poly_simp he2
          exact MSpec.eq' rfl he2 (by vars_tac) (by vars_tac)
        apply List.Forall₂.cons
        · apply MSpec.expr_bind (IsExpr.square _); intro e1 he1
          apply MSpec.expr_bind (IsExpr.addL _); intro e2 he2
          apply MSpec.expr_bind (IsExpr.mulL _); intro e3 he3
          poly_simp he2; poly_simp he3
          exact MSpec.eq' he2 he3 (by vars_tac) (by vars_tac)
        apply List.Forall₂.cons
        · exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) hPe rfl
        apply List.Forall₂.cons
        · exact alpha_spec (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac)
            (by isnat_tac) rfl rfl hRe
        apply List.Forall₂.cons
        · apply MSpec.expr_bind (IsExpr.addL _); intro e1 he1
          poly_simp he1
          exact alpha_spec (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac)
            (by isnat_tac) rfl rfl he1
        apply List.Forall₂.cons
        · apply MSpec.expr_bind (IsExpr.mulL _); intro e1 he1
          apply MSpec.expr_bind (IsExpr.addL _); intro e2 he2
          apply MSpec.expr_bind (IsExpr.mulL _); intro e3 he3
          apply MSpec.expr_bind (IsExpr.addL _); intro e4 he4
          poly_simp he2; poly_simp he4
          exact congruent_spec (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac)
            (by isnat_tac) (by isnat_tac) he2 rfl he4
        exact List.Forall₂.nil
      exact List.Forall₂.nil
    · exact fresh_next_lt (fresh_next_lt (fresh_next_lt (fresh_next_lt (fresh_next_lt
        (by simpa using hs)))))
  · intro x
    simp only [fresh_apply_next, constant_apply_next, constant_apply_poly, fresh_apply_poly]
    simp (disch := first | omega | (isnat_tac; done)) only [List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left,
      nv_add, nv_mul, zv_update_ge hP hs, zv_update_ge hQ hs, zv_update_ge hR hs,
      nv_update_ge hP hs, nv_update_ge hQ hs, nv_update_ge hR hs, zv_add, zv_mul, zv_X, zv_C,
      nv_X, nv_X_mul_X, nv_C_two, nv_C_three, nv_C_four, nv_C_zero, nv_C_one]
    simp only [Function.update_apply, Nat.add_assoc, Nat.reduceAdd, Nat.add_left_cancel_iff,
      Nat.left_eq_add, Nat.add_eq_left, OfNat.ofNat_ne_zero, reduceCtorEq, ite_true, ite_false,
      Nat.reduceEqDiff, hPn.zv_eq, hQn.zv_eq, hRn.zv_eq]
    unfold PowerFormula AlphaPower.PowEqns
    constructor
    · rintro ⟨b, m, a0, a1, a2, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨hQ, h1, h2, h3, h4, h5, h6, h7⟩⟩
      · exact Or.inl ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩
      · exact Or.inr (Or.inl ⟨by exact_mod_cast h1, h2, by exact_mod_cast h3⟩)
      · refine Or.inr (Or.inr ⟨hQ, b, m, a0, a1, a2, h1, ?_, ?_, h4, h5, h6, h7⟩)
        · exact_mod_cast (show ((b : ℕ) : ℤ) = ((a0 + nv x QP ^ 2 + 2 : ℕ) : ℤ) by
            push_cast; linear_combination h2)
        · exact_mod_cast (show ((m + nv x QP ^ 2 + 1 : ℕ) : ℤ) = ((b * nv x QP : ℕ) : ℤ) by
            push_cast; linear_combination h3)
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨hQ, b, m, a0, a1, a2, h1, h2, h3, h4, h5, h6, h7⟩)
      · exact ⟨0, 0, 0, 0, 0, Or.inl ⟨by exact_mod_cast h1, by exact_mod_cast h2,
          by exact_mod_cast h3⟩⟩
      · exact ⟨0, 0, 0, 0, 0, Or.inr (Or.inl ⟨by exact_mod_cast h1, h2, by exact_mod_cast h3⟩)⟩
      · refine ⟨b, m, a0, a1, a2, Or.inr (Or.inr ⟨hQ, h1, ?_, ?_, h4, h5, h6, h7⟩)⟩
        · have := congrArg (Nat.cast : ℕ → ℤ) h2
          push_cast at this
          linear_combination this
        · have := congrArg (Nat.cast : ℕ → ℤ) h3
          push_cast at this
          linear_combination this

/-! ### The power macro in either mode -/

/-- The power macro, in the given mode, means `P = Q ^ R` for argument polynomials with natural
values. -/
def PowerSpec (τ : ExPoly) (mode : PowerMode) : Prop :=
  ∀ (U : Set ℕ) (PP QP RP : Poly), VarsIn PP (· ∈ U) → VarsIn QP (· ∈ U) → VarsIn RP (· ∈ U) →
    IsNat PP → IsNat QP → IsNat RP → ∀ P Q R : Ex, P.poly = PP → Q.poly = QP → R.poly = RP →
      MSpec τ (power mode P Q R) U fun x => nv x PP = nv x QP ^ nv x RP

/-- The flat power macro means `P = Q ^ R` as soon as the power formula does. -/
theorem powerSpec_flat (h : ∀ P Q R : ℕ, PowerFormula P Q R ↔ P = Q ^ R) :
    PowerSpec τ .flat := by
  intro U PP QP RP hP hQ hR hPn hQn hRn P Q R hPe hQe hRe
  exact MSpec.note_bind ((powerFlat_spec hP hQ hR hPn hQn hRn hPe hQe hRe).congr fun x => h _ _ _)

/-- Natural parameter values `(a, b, c)` of a call. -/
def natArgs (a b c : ℕ) (p : ℕ) : Fin p → ℤ := fun i => (([a, b, c].getD i 0 : ℕ) : ℤ)

theorem callVals_eq_natArgs {x : ℕ → ℕ} {PP QP RP : Poly} (hPn : IsNat PP) (hQn : IsNat QP)
    (hRn : IsNat RP) (p : ℕ) :
    callVals x PP QP RP p = natArgs (nv x PP) (nv x QP) (nv x RP) p := by
  funext ⟨i, hi⟩
  simp only [callVals, callArgs, natArgs, getPoly]
  match i with
  | 0 => simp [hPn.zv_eq]
  | 1 => simp [hQn.zv_eq]
  | 2 => simp [hRn.zv_eq]
  | n + 3 => simp

/-- The natural semantics of a template with three parameters: some natural witnesses make it
vanish at natural `(P, Q, R)` exactly when `P = Q ^ R`. -/
def PowerTemplateSem (τ : ExPoly) : Prop :=
  ∀ P Q R : ℕ, ExNatRel τ (natArgs P Q R τ.params) ↔ P = Q ^ R

/-- **Hierarchical power calls.** If the template has the power semantics, a power call on a
private block means `P = Q ^ R`. -/
theorem powerSpec_hierarchical (hτ : τ.WF) (hw : τ.witnesses = powerWitnesses)
    (hsem : PowerTemplateSem τ) : PowerSpec τ .hierarchical := by
  intro U PP QP RP hP hQ hR hPn hQn hRn P Q R hPe hQe hRe
  refine MSpec.note_bind ?_
  have := callPower_spec hτ hw (P := P) (Q := Q) (R := R) (U := U) (hPe ▸ hP) (hQe ▸ hQ)
    (hRe ▸ hR)
  refine this.congr fun x => ?_
  rw [hPe, hQe, hRe, callVals_eq_natArgs hPn hQn hRn, hsem]

/-! ### Binomial coefficients and bits -/

theorem binomial_spec {mode : PowerMode} (hpow : PowerSpec τ mode) {U : Set ℕ} {CP NP KP : Poly}
    (hC : VarsIn CP (· ∈ U)) (hN : VarsIn NP (· ∈ U)) (hK : VarsIn KP (· ∈ U)) (hCn : IsNat CP)
    (hNn : IsNat NP) (hKn : IsNat KP) {C N K : Ex} (hCe : C.poly = CP) (hNe : N.poly = NP)
    (hKe : K.poly = KP) :
    MSpec τ (binomial mode C N K) U fun x => nv x CP = (nv x NP).choose (nv x KP) := by
  intro s hs
  apply Spec.congr
  · apply Spec.note_bind
    apply Spec.fresh_bind; apply Spec.fresh_bind; apply Spec.fresh_bind; apply Spec.fresh_bind
    apply Spec.fresh_bind
    apply MSpec.andM
    · apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.constant 2); intro c2 hc2
        apply MSpec.expr_bind (IsExpr.constant 1); intro c1 hc1
        apply MSpec.expr_bind (IsExpr.addL _); intro e1 he1
        poly_simp he1
        exact hpow _ _ _ _ (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac)
          (by isnat_tac) _ _ _ rfl hc2 he1
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.constant 1); intro c1 hc1
        apply MSpec.expr_bind (IsExpr.addL _); intro e1 he1
        poly_simp he1
        exact hpow _ _ _ _ (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac)
          (by isnat_tac) _ _ _ rfl he1 hNe
      apply List.Forall₂.cons
      · exact hpow _ _ _ _ (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac)
          (by isnat_tac) _ _ _ rfl rfl hKe
      apply List.Forall₂.cons
      · exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) hCe rfl
      apply List.Forall₂.cons
      · exact lt_spec (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) rfl rfl
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.mulL _); intro e1 he1
        apply MSpec.expr_bind (IsExpr.addL _); intro e2 he2
        apply MSpec.expr_bind (IsExpr.mulL _); intro e3 he3
        apply MSpec.expr_bind (IsExpr.addL _); intro e4 he4
        poly_simp he4
        exact MSpec.eq' rfl he4 (by vars_tac) (by vars_tac)
      exact List.Forall₂.nil
    · exact fresh_next_lt (fresh_next_lt (fresh_next_lt (fresh_next_lt (fresh_next_lt (note_lt hs)))))
  · intro x
    simp only [fresh_apply_next, fresh_apply_poly, note_apply_next]
    simp (disch := first | omega | (isnat_tac; done)) only [List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, nv_add, nv_mul, zv_update_ge hC hs,
      zv_update_ge hN hs, zv_update_ge hK hs, nv_update_ge hC hs, nv_update_ge hN hs,
      nv_update_ge hK hs, zv_add, zv_mul, zv_X, zv_C, nv_X, nv_C_two, nv_C_one]
    simp only [Function.update_apply, Nat.add_assoc, Nat.reduceAdd, Nat.add_left_cancel_iff,
      Nat.left_eq_add, Nat.add_eq_left, OfNat.ofNat_ne_zero, reduceCtorEq, ite_true, ite_false,
      Nat.reduceEqDiff, hCn.zv_eq, hNn.zv_eq, hKn.zv_eq]
    rw [← BinomialDigit.macro_holds_iff_choose]
    unfold BinomialDigit.macroHolds
    constructor
    · rintro ⟨b, t, p, q, r, h1, h2, h3, h4, h5, h6⟩
      refine ⟨b, t, p, q, r, h1, by rw [h2, add_comm], h3, h4, h5, ?_⟩
      exact_mod_cast (show ((t : ℕ) : ℤ) = ((p * (b * q + nv x CP) + r : ℕ) : ℤ) by
        push_cast; linear_combination h6)
    · rintro ⟨b, t, p, q, r, h1, h2, h3, h4, h5, h6⟩
      refine ⟨b, t, p, q, r, h1, by rw [h2, add_comm], h3, h4, h5, ?_⟩
      have := congrArg (Nat.cast : ℕ → ℤ) h6
      push_cast at this
      linear_combination this

theorem orthogonal_spec {mode : PowerMode} (hpow : PowerSpec τ mode) {U : Set ℕ} {AP BP : Poly}
    (hA : VarsIn AP (· ∈ U)) (hB : VarsIn BP (· ∈ U)) (hAn : IsNat AP) (hBn : IsNat BP)
    {a b : Ex} (hae : a.poly = AP) (hbe : b.poly = BP) :
    MSpec τ (orthogonal mode a b) U fun x => Nat.land (nv x AP) (nv x BP) = 0 := by
  intro s hs
  apply Spec.congr
  · apply Spec.note_bind
    apply Spec.fresh_bind
    apply MSpec.andM
    · apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.addL _); intro e1 he1
        poly_simp he1
        exact binomial_spec hpow (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac)
          (by isnat_tac) (by isnat_tac) rfl he1 hae
      apply List.Forall₂.cons
      · exact odd_spec (by vars_tac) (by isnat_tac) rfl
      exact List.Forall₂.nil
    · exact fresh_next_lt (note_lt hs)
  · intro x
    simp only [fresh_apply_next, fresh_apply_poly, note_apply_next]
    simp (disch := first | omega | (isnat_tac; done)) only [List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, nv_add, nv_update_ge hA hs, nv_update_ge hB hs,
      nv_X, Function.update_self]
    rw [← NaturalBitwiseMacros.orthogonal_iff_land_eq_zero]
    simp [NaturalBitwiseMacros.orthogonal, NaturalBitwiseMacros.odd_witness_iff_odd]

theorem mask_spec {mode : PowerMode} (hpow : PowerSpec τ mode) {U : Set ℕ} {AP BP : Poly}
    (hA : VarsIn AP (· ∈ U)) (hB : VarsIn BP (· ∈ U)) (hAn : IsNat AP) (hBn : IsNat BP)
    {a b : Ex} (hae : a.poly = AP) (hbe : b.poly = BP) :
    MSpec τ (mask mode a b) U fun x => Nat.land (nv x AP) (nv x BP) = nv x AP := by
  intro s hs
  apply Spec.congr
  · apply Spec.note_bind
    apply Spec.fresh_bind
    apply MSpec.andM
    · apply List.Forall₂.cons
      · exact binomial_spec hpow (by vars_tac) (by vars_tac) (by vars_tac) (by isnat_tac)
          (by isnat_tac) (by isnat_tac) rfl hbe hae
      apply List.Forall₂.cons
      · exact odd_spec (by vars_tac) (by isnat_tac) rfl
      exact List.Forall₂.nil
    · exact fresh_next_lt (note_lt hs)
  · intro x
    simp only [fresh_apply_next, fresh_apply_poly, note_apply_next]
    simp (disch := first | omega | (isnat_tac; done)) only [List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, nv_update_ge hA hs, nv_update_ge hB hs,
      nv_X, Function.update_self]
    rw [← NaturalBitwiseMacros.mask_iff_land_eq]
    simp [NaturalBitwiseMacros.mask, NaturalBitwiseMacros.odd_witness_iff_odd]

theorem bitAnd_spec {mode : PowerMode} (hpow : PowerSpec τ mode) {U : Set ℕ} {ZP XP YP : Poly}
    (hZ : VarsIn ZP (· ∈ U)) (hX : VarsIn XP (· ∈ U)) (hY : VarsIn YP (· ∈ U)) (hZn : IsNat ZP)
    (hXn : IsNat XP) (hYn : IsNat YP) {z x y : Ex} (hze : z.poly = ZP) (hxe : x.poly = XP)
    (hye : y.poly = YP) :
    MSpec τ (bitAnd mode z x y) U fun v => nv v ZP = Nat.land (nv v XP) (nv v YP) := by
  intro s hs
  apply Spec.congr
  · apply Spec.note_bind
    apply Spec.fresh_bind; apply Spec.fresh_bind
    apply MSpec.andM
    · apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.addL _); intro e1 he1
        poly_simp he1
        exact MSpec.eq' hxe he1 (by vars_tac) (by vars_tac)
      apply List.Forall₂.cons
      · apply MSpec.expr_bind (IsExpr.addL _); intro e1 he1
        poly_simp he1
        exact MSpec.eq' hye he1 (by vars_tac) (by vars_tac)
      apply List.Forall₂.cons
      · exact orthogonal_spec hpow (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) hze rfl
      apply List.Forall₂.cons
      · exact orthogonal_spec hpow (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) hze rfl
      apply List.Forall₂.cons
      · exact orthogonal_spec hpow (by vars_tac) (by vars_tac) (by isnat_tac) (by isnat_tac) rfl rfl
      exact List.Forall₂.nil
    · exact fresh_next_lt (fresh_next_lt (note_lt hs))
  · intro v
    simp only [fresh_apply_next, fresh_apply_poly, note_apply_next]
    simp (disch := first | omega | (isnat_tac; done)) only [List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, zv_update_ge hZ hs, zv_update_ge hX hs,
      zv_update_ge hY hs, nv_update_ge hZ hs, nv_update_ge hX hs, nv_update_ge hY hs, zv_add,
      zv_X, nv_X]
    simp only [Function.update_apply, Nat.add_assoc, Nat.reduceAdd, Nat.add_left_cancel_iff,
      Nat.left_eq_add, Nat.add_eq_left, OfNat.ofNat_ne_zero, reduceCtorEq, ite_true, ite_false,
      Nat.reduceEqDiff, hZn.zv_eq, hXn.zv_eq, hYn.zv_eq]
    rw [← NaturalBitwiseMacros.bit_and_iff_land_eq]
    simp only [NaturalBitwiseMacros.bit_and, NaturalBitwiseMacros.orthogonal_iff_land_eq_zero]
    constructor
    · rintro ⟨a, b, h1, h2, h3, h4, h5⟩
      exact ⟨a, b, by exact_mod_cast h1, by exact_mod_cast h2, h3, h4, h5⟩
    · rintro ⟨a, b, h1, h2, h3, h4, h5⟩
      exact ⟨a, b, by exact_mod_cast h1, by exact_mod_cast h2, h3, h4, h5⟩

/-! ### Final forms through the exponential section -/

/-- **Semantics of `alpha`.** `alpha(X, b, N)` means `b > 3` and `X = α_b(N)`. -/
theorem alpha_sem {U : Set ℕ} {XP BP NP : Poly} (hX : VarsIn XP (· ∈ U)) (hB : VarsIn BP (· ∈ U))
    (hN : VarsIn NP (· ∈ U)) (hXn : IsNat XP) (hBn : IsNat BP) (hNn : IsNat NP) {X b N : Ex}
    (hXe : X.poly = XP) (hbe : b.poly = BP) (hNe : N.poly = NP) :
    MSpec τ (alpha X b N) U fun x =>
      3 < nv x BP ∧ (nv x XP : ℤ) = AlphaPower.alphaZ (nv x BP) (nv x NP) :=
  (alpha_spec hX hB hN hXn hBn hNn hXe hbe hNe).congr fun _ => AlphaPower.alphaEqns_iff _ _ _

/-- **Semantics of the flat power macro.** `power(P, Q, R)` means `P = Q ^ R`. -/
theorem powerSpec_flat' : PowerSpec τ .flat :=
  powerSpec_flat fun P Q R => AlphaPower.powEqns_iff P Q R

end ZInQ.Compiler.Natural
