import ZInQKernel.Syntax.Templates
import ZInQKernel.Model.DivisionPolynomials
import ZInQKernel.Model.Generator

/-!
# Semantics of the fixed-scalar templates

Blueprint: `syntax/fixed-scalar-semantics.md`.

When the psi constructor is read as the normalized division-polynomial components
(`I.psi = psiComponent`), the fixed-scalar template `S_n` (`scalarTemplate I n`) relates, for
`n ≥ 1`, the code of a point `P ∈ 2E(K₀)` to the code of `[n]P` and to nothing else
(`scalarTemplate_rel_iff_pointCode`); on the codes of `2E(K₀) = ℤP₀` this reads
`Rel_{S_n}(ι(a), r) ↔ r = ι(na)` (`scalarTemplate_rel_iff_iota`).

The value `n` of the fixed expression `e` enters as an integer parameter of the template, as in
`ZInQKernel/Syntax/Templates/Multiply.lean`; it is never evaluated.
-/

namespace ZInQ.Syntax

open MvPolynomial WeierstrassCurve

variable {E : Type}

/-- The pair of psi nodes evaluates to `ψ_m(x(p), y(p))` when the psi constructor is read as the
component polynomials `Ψ_{m,c}`. -/
theorem val_psiPair (I : Constructors E) (hI : I.psi = psiComponent) (m : ℤ) (x : ℕ → ℚ)
    (p : Code) :
    Pair.val x (psiPair I m p) = psiEval genA m (Pair.val x p.x) (Pair.val x p.y) := by
  have key : ∀ c : Fin 2, ev x (bind₁ ![p 1, p 2, p 3, p 4] (I.psi m c)) =
      ![(psiEval genA m (Pair.val x p.x) (Pair.val x p.y)).re,
        (psiEval genA m (Pair.val x p.x) (Pair.val x p.y)).im] c := by
    intro c
    rw [hI, ev, eval₂Hom_bind₁, coe_eval₂Hom, psiComponent_eval]
    rfl
  ext
  · exact key 0
  · exact key 1

/-- The formula of `S_n` in field terms. -/
theorem holds_scalarFormula (I : Constructors E) (hI : I.psi = psiComponent) (n : ℤ) (p r : Code)
    (u : ℕ) (x : ℕ → ℚ) :
    (scalarFormula I n p r u).Holds x ↔
      (evCode x p = ![1, 0, 0, 0, 0] ∧ evCode x r = ![1, 0, 0, 0, 0]) ∨
        (ev x (p 0) = 0 ∧ ev x (r 0) = 0 ∧ ev x (psiPair I n p).norm * x u = 1 ∧
          psiEval genA n (Pair.val x p.x) (Pair.val x p.y) ^ 2 * Pair.val x r.x =
            Pair.val x p.x * psiEval genA n (Pair.val x p.x) (Pair.val x p.y) ^ 2 -
              psiEval genA (n + 1) (Pair.val x p.x) (Pair.val x p.y) *
                psiEval genA (n - 1) (Pair.val x p.x) (Pair.val x p.y) ∧
          2 * (psiEval genA n (Pair.val x p.x) (Pair.val x p.y) ^ 2) ^ 2 * Pair.val x r.y =
            psiEval genA (2 * n) (Pair.val x p.x) (Pair.val x p.y)) := by
  have h2 : (QuadraticAlgebra.C (ev x 2) : K0) = 2 := by
    rw [ev_ofNat]; exact QuadraticAlgebra.C_ofNat 2
  simp only [scalarFormula, Formula.holds_or, Formula.holds_and, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, holds_isO,
    holds_fin, holds_feq, holds_nzFormula, Pair.val_mul, Pair.val_sq, Pair.val_sub,
    Pair.val_smul, val_psiPair I hI, h2, ← sub_eq_add_neg]

/-- The codes of the parameter points of `S_n` at `assign 10 1 (code P, r) y`. -/
theorem evCode_assign_scalar (c r : Fin 5 → ℚ) (y : Fin 1 → ℚ) :
    evCode (assign 10 1 (Fin.append c r) y) (varPoint 0) = c ∧
      evCode (assign 10 1 (Fin.append c r) y) (varPoint 5) = r := by
  constructor
  · funext i
    simp only [evCode, ev_varPoint, zero_add]
    rw [assign_of_lt _ _ (by omega)]
    exact Fin.append_left c r i
  · funext i
    simp only [evCode, ev_varPoint]
    rw [assign_of_lt _ _ (by omega)]
    exact Fin.append_right c r i

/-- The pairs and the first coordinate of a code, read off its values. -/
theorem val_of_evCode {x : ℕ → ℚ} {p : Code} {c : Fin 5 → ℚ} (h : evCode x p = c) :
    Pair.val x p.x = ⟨c 1, c 2⟩ ∧ Pair.val x p.y = ⟨c 3, c 4⟩ ∧ ev x (p 0) = c 0 := by
  subst h
  exact ⟨rfl, rfl, rfl⟩

/-- A code is the code of the affine point `(X, Y)` exactly when its first coordinate is `0`
and its pairs are `X` and `Y`. -/
theorem eq_pointCode_some_iff (r : Fin 5 → ℚ) {X Y : K0} (h : genCurve.toAffine.Nonsingular X Y) :
    r = pointCode (.some X Y h) ↔ r 0 = 0 ∧ (⟨r 1, r 2⟩ : K0) = X ∧ (⟨r 3, r 4⟩ : K0) = Y :=
  ZInQ.eq_pointCode_some_iff h

/-- `[n]P ≠ O` for `n ≠ 0` and `O ≠ P ∈ 2E(K₀)`, since `2E(K₀) = ℤP₀` is torsion free. -/
theorem zsmul_ne_zero_of_mem_carrierD {n : ℤ} (hn : n ≠ 0) {P : genCurve.toAffine.Point}
    (hP : P ∈ carrierD) (hP0 : P ≠ 0) : n • P ≠ 0 := fun h =>
  hP0 (eq_zero_of_mem_carrierD_of_isOfFinAddOrder hP
    (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨n, hn, h⟩))

/-- The fixed-scalar formula at `(code P, r)` in field terms. -/
theorem holds_scalarFormula_assign (I : Constructors E) (hI : I.psi = psiComponent) (n : ℤ)
    (P : genCurve.toAffine.Point) (r : Fin 5 → ℚ) (y : Fin 1 → ℚ) :
    (scalarFormula I n (varPoint 0) (varPoint 5) 10).Holds
        (assign 10 1 (Fin.append (pointCode P) r) y) ↔
      (pointCode P = ![1, 0, 0, 0, 0] ∧ r = ![1, 0, 0, 0, 0]) ∨
        (pointCode P 0 = 0 ∧ r 0 = 0 ∧
          ((psiEval genA n ⟨pointCode P 1, pointCode P 2⟩ ⟨pointCode P 3, pointCode P 4⟩).re ^ 2 -
            2 * (psiEval genA n ⟨pointCode P 1, pointCode P 2⟩
              ⟨pointCode P 3, pointCode P 4⟩).im ^ 2) * y 0 = 1 ∧
          psiEval genA n ⟨pointCode P 1, pointCode P 2⟩ ⟨pointCode P 3, pointCode P 4⟩ ^ 2 *
              ⟨r 1, r 2⟩ =
            ⟨pointCode P 1, pointCode P 2⟩ *
                psiEval genA n ⟨pointCode P 1, pointCode P 2⟩ ⟨pointCode P 3, pointCode P 4⟩ ^ 2 -
              psiEval genA (n + 1) ⟨pointCode P 1, pointCode P 2⟩ ⟨pointCode P 3, pointCode P 4⟩ *
                psiEval genA (n - 1) ⟨pointCode P 1, pointCode P 2⟩
                  ⟨pointCode P 3, pointCode P 4⟩ ∧
          2 * (psiEval genA n ⟨pointCode P 1, pointCode P 2⟩
              ⟨pointCode P 3, pointCode P 4⟩ ^ 2) ^ 2 * ⟨r 3, r 4⟩ =
            psiEval genA (2 * n) ⟨pointCode P 1, pointCode P 2⟩
              ⟨pointCode P 3, pointCode P 4⟩) := by
  obtain ⟨hp, hr⟩ := evCode_assign_scalar (pointCode P) r y
  obtain ⟨hpx, hpy, hp0⟩ := val_of_evCode hp
  obtain ⟨hrx, hry, hr0⟩ := val_of_evCode hr
  have hnorm := Pair.ev_norm (assign 10 1 (Fin.append (pointCode P) r) y) (psiPair I n (varPoint 0))
  rw [← Pair.re_val, ← Pair.im_val, val_psiPair I hI, hpx, hpy] at hnorm
  have hu : assign 10 1 (Fin.append (pointCode P) r) y 10 = y 0 := assign_add 10 1 _ y 0
  rw [holds_scalarFormula I hI, hp, hr, hpx, hpy, hrx, hry, hp0, hr0, hnorm, hu]

/-- **Semantics of the fixed-scalar templates.** Let the psi constructor be read as the
component polynomials `Ψ_{m,c}`, let `n ≥ 1` (the value of the fixed expression), let `P ∈
2E(K₀)` and `r ∈ ℚ⁵`. Then `Rel_{S_n}(code P, r)` holds exactly when `r` is the code of
`[n]P`. -/
theorem scalarTemplate_rel_iff_pointCode (I : Constructors E) (hI : I.psi = psiComponent)
    {n : ℤ} (hn : 1 ≤ n) {P : genCurve.toAffine.Point} (hP : P ∈ carrierD) (r : Fin 5 → ℚ) :
    (scalarTemplate I n).Rel (Fin.append (pointCode P) r) ↔ r = pointCode (n • P) := by
  rw [scalarTemplate_rel_iff]
  simp only [holds_scalarFormula_assign I hI]
  rcases P with _ | ⟨X, Y, h⟩
  · -- `P = O`: only the first branch can hold.
    have hO : (Affine.Point.zero : genCurve.toAffine.Point) = 0 := rfl
    rw [hO, zsmul_zero, pointCode_zero]
    constructor
    · rintro ⟨y, h1 | h2⟩
      · exact h1.2
      · exact absurd h2.1 (by simp)
    · intro hr
      exact ⟨0, Or.inl ⟨rfl, hr⟩⟩
  · -- `P = (X, Y)`: only the second branch can hold, and `[n]P ≠ O`.
    have hne : n • (Affine.Point.some X Y h : genCurve.toAffine.Point) ≠ 0 :=
      zsmul_ne_zero_of_mem_carrierD (by omega) hP (Affine.Point.some_ne_zero h)
    obtain ⟨hmul1, hmul2⟩ := mulByN_formulas X Y h n (by omega)
    have hψ : psiEval genA n X Y ≠ 0 := fun h0 => hne (hmul1.mpr h0)
    obtain ⟨h', e'⟩ := hmul2 hne
    rw [e', eq_pointCode_some_iff]
    have hN : (psiEval genA n X Y).re ^ 2 - 2 * (psiEval genA n X Y).im ^ 2 ≠ 0 :=
      (K0_ne_zero_iff_pairNorm (psiEval genA n X Y).re (psiEval genA n X Y).im).1
        (by simpa using hψ)
    have hnotO : ¬ ![(0 : ℚ), X.re, X.im, Y.re, Y.im] = ![1, 0, 0, 0, 0] := fun h0 => by
      have := congrFun h0 0
      simp at this
    simp only [pointCode_some]
    have e1 : (⟨(![(0 : ℚ), X.re, X.im, Y.re, Y.im] : Fin 5 → ℚ) 1,
      (![(0 : ℚ), X.re, X.im, Y.re, Y.im] : Fin 5 → ℚ) 2⟩ : K0) = X := rfl
    have e2 : (⟨(![(0 : ℚ), X.re, X.im, Y.re, Y.im] : Fin 5 → ℚ) 3,
      (![(0 : ℚ), X.re, X.im, Y.re, Y.im] : Fin 5 → ℚ) 4⟩ : K0) = Y := rfl
    have e0 : (![(0 : ℚ), X.re, X.im, Y.re, Y.im] : Fin 5 → ℚ) 0 = 0 := rfl
    rw [e1, e2, e0]
    constructor
    · rintro ⟨y, h1 | ⟨-, h0, -, ex, ey⟩⟩
      · exact absurd h1.1 hnotO
      · refine ⟨h0, ?_, ?_⟩
        · apply mul_right_cancel₀ (pow_ne_zero 2 hψ)
          rw [sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hψ)]
          linear_combination ex
        · rw [eq_div_iff (mul_ne_zero two_ne_zero (pow_ne_zero 4 hψ))]
          linear_combination ey
    · rintro ⟨h0, ex, ey⟩
      refine ⟨fun _ => ((psiEval genA n X Y).re ^ 2 - 2 * (psiEval genA n X Y).im ^ 2)⁻¹,
        Or.inr ⟨rfl, h0, mul_inv_cancel₀ hN, ?_, ?_⟩⟩
      · have hinv := mul_inv_cancel₀ (pow_ne_zero 2 hψ)
        rw [ex, div_eq_mul_inv]
        linear_combination (-(psiEval genA (n + 1) X Y * psiEval genA (n - 1) X Y)) * hinv
      · have hinv := mul_inv_cancel₀ (mul_ne_zero (two_ne_zero (α := K0)) (pow_ne_zero 4 hψ))
        rw [ey, div_eq_mul_inv]
        linear_combination psiEval genA (2 * n) X Y * hinv

/-- **Fixed scalars on `2E(K₀) = ℤP₀`.** For `n ≥ 1`, `Rel_{S_n}(ι(a), r)` holds exactly when
`r = ι(na)`. -/
theorem scalarTemplate_rel_iff_iota (I : Constructors E) (hI : I.psi = psiComponent) {n : ℤ}
    (hn : 1 ≤ n) (a : ℤ) (r : Fin 5 → ℚ) :
    (scalarTemplate I n).Rel (Fin.append (iota a) r) ↔ r = iota (n * a) := by
  rw [iota_def, scalarTemplate_rel_iff_pointCode I hI hn
    (mem_carrierD_iff_exists_zsmul.mpr ⟨a, rfl⟩), smul_smul, iota_def]

end ZInQ.Syntax
