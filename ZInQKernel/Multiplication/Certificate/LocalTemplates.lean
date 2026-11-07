import ZInQKernel.Syntax.Templates.Core
import ZInQKernel.Multiplication.Certificate.Tests
import ZInQKernel.Multiplication.Local.Nonvanishing

/-!
# Semantics of the local-parameter, inverse-abscissa and logarithm templates

Blueprint: `multiplication/certificate/local-templates.md`.

For `Q ∈ E(K₀)` with code `pointCode Q` and rational pairs `ζ, v, λ` (`[u] = u₀ + u₁ s` is
`pairK u`):

1. `raw_z`: if `Q = O` or `y(Q) ≠ 0`, `Rel(code Q, ζ) ↔ [ζ] = z(Q)`; if `Q` is affine with
   `y(Q) = 0` the relation fails (`rawZ_rel_iff_of`, `rawZ_not_rel`).
2. `raw_inverse_x`: if `Q = O` or `x(Q) ≠ 0`, `Rel(code Q, v) ↔ [v] = 1/x(Q)`; if `Q` is affine
   with `x(Q) = 0` the relation fails.
3. `log25`: `Rel(ζ, λ) ↔ [λ] = L([ζ])` (`log25_rel_iff`).

For `Q = [n]P₀` the side conditions hold (`ZInQ.Mult.log25_z_ne_zero`), so the templates compute
`z(Q)`, `1/x(Q)` and `L(z(Q))` on the codes `ι(n)` (`rawZ_rel_iota`, `rawInverseX_rel_iota`).
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine Syntax

/-- The element `[u] = u₀ + u₁ s` of `K₀` of a rational pair. -/
def pairK (u : Fin 2 → ℚ) : K0 := ⟨u 0, u 1⟩

theorem K0_eta (u : K0) : (⟨u.re, u.im⟩ : K0) = u := rfl

/-- The first five coordinates of `code ‖ u` are the code. -/
theorem append_castLE_eq (c : Fin 5 → ℚ) (u : Fin 2 → ℚ) :
    (fun i : Fin 5 => (Fin.append c u : Fin 7 → ℚ) (Fin.castLE (by omega) i)) = c := by
  funext i; fin_cases i <;> rfl

/-- **The local parameter template**, both branches. -/
theorem rawZ_rel_iff (Q : genCurve.toAffine.Point) (ζ : Fin 2 → ℚ) :
    rawZTemplate.Rel (Fin.append (pointCode Q) ζ) ↔
      (Q = 0 ∧ pairK ζ = 0) ∨
        ∃ x y h, Q = Point.some x y h ∧ y ≠ 0 ∧ pairK ζ = -x / y := by
  rw [rawZTemplate_rel_iff_field, append_castLE_eq]
  rcases Q with _ | ⟨x, y, h⟩
  · have h0 : (Fin.append (pointCode Point.zero) ζ : Fin 7 → ℚ) 0 = 1 := rfl
    have hz : (⟨(Fin.append (pointCode Point.zero) ζ : Fin 7 → ℚ) 5,
        (Fin.append (pointCode Point.zero) ζ : Fin 7 → ℚ) 6⟩ : K0) = pairK ζ := rfl
    rw [h0, hz]
    constructor
    · rintro (⟨-, hζ⟩ | ⟨h1, -⟩)
      · exact Or.inl ⟨rfl, hζ⟩
      · exact absurd h1 one_ne_zero
    · rintro (⟨-, hζ⟩ | ⟨x, y, h, he, -⟩)
      · exact Or.inl ⟨rfl, hζ⟩
      · exact absurd he.symm (Point.some_ne_zero h)
  · have hne : pointCode (Point.some x y h) ≠ ![1, 0, 0, 0, 0] := fun he => by
      have := congrFun he 0; simp [pointCode] at this
    have h0 : (Fin.append (pointCode (Point.some x y h)) ζ : Fin 7 → ℚ) 0 = 0 := rfl
    have hx : (⟨(Fin.append (pointCode (Point.some x y h)) ζ : Fin 7 → ℚ) 1,
        (Fin.append (pointCode (Point.some x y h)) ζ : Fin 7 → ℚ) 2⟩ : K0) = x := rfl
    have hy : (⟨(Fin.append (pointCode (Point.some x y h)) ζ : Fin 7 → ℚ) 3,
        (Fin.append (pointCode (Point.some x y h)) ζ : Fin 7 → ℚ) 4⟩ : K0) = y := rfl
    have hz : (⟨(Fin.append (pointCode (Point.some x y h)) ζ : Fin 7 → ℚ) 5,
        (Fin.append (pointCode (Point.some x y h)) ζ : Fin 7 → ℚ) 6⟩ : K0) = pairK ζ := rfl
    rw [h0, hx, hy, hz]
    constructor
    · rintro (⟨he, -⟩ | ⟨-, hy0, hζ⟩)
      · exact absurd he hne
      · exact Or.inr ⟨x, y, h, rfl, hy0, hζ⟩
    · rintro (⟨he, -⟩ | ⟨x', y', h', he, hy0, hζ⟩)
      · exact absurd he (Point.some_ne_zero h)
      · obtain ⟨rfl, rfl⟩ := Point.some.inj he
        exact Or.inr ⟨rfl, hy0, hζ⟩

/-- **The local parameter template** when `Q = O` or `y(Q) ≠ 0`: `Rel(code Q, ζ) ↔ [ζ] = z(Q)`. -/
theorem rawZ_rel_iff_of (Q : genCurve.toAffine.Point)
    (hQ : ∀ x y h, Q = Point.some x y h → y ≠ 0) (ζ : Fin 2 → ℚ) :
    rawZTemplate.Rel (Fin.append (pointCode Q) ζ) ↔ pairK ζ = zOf Q := by
  rw [rawZ_rel_iff]
  rcases Q with _ | ⟨x, y, h⟩
  · constructor
    · rintro (⟨-, hζ⟩ | ⟨x, y, h, he, -⟩)
      · exact hζ
      · exact absurd he.symm (Point.some_ne_zero h)
    · intro hζ; exact Or.inl ⟨rfl, hζ⟩
  · constructor
    · rintro (⟨he, -⟩ | ⟨x', y', h', he, -, hζ⟩)
      · exact absurd he (Point.some_ne_zero h)
      · obtain ⟨rfl, rfl⟩ := Point.some.inj he
        exact hζ
    · intro hζ; exact Or.inr ⟨x, y, h, rfl, hQ x y h rfl, hζ⟩

/-- At an affine point with `y(Q) = 0` the local parameter template fails. -/
theorem rawZ_not_rel {x y : K0} (h : genCurve.toAffine.Nonsingular x y) (hy : y = 0)
    (ζ : Fin 2 → ℚ) : ¬ rawZTemplate.Rel (Fin.append (pointCode (Point.some x y h)) ζ) := by
  rw [rawZ_rel_iff]
  rintro (⟨he, -⟩ | ⟨x', y', h', he, hy0, -⟩)
  · exact Point.some_ne_zero h he
  · obtain ⟨rfl, rfl⟩ := Point.some.inj he
    exact hy0 hy

/-- **The inverse abscissa template**, both branches. -/
theorem rawInverseX_rel_iff (Q : genCurve.toAffine.Point) (v : Fin 2 → ℚ) :
    rawInverseXTemplate.Rel (Fin.append (pointCode Q) v) ↔
      (Q = 0 ∧ pairK v = 0) ∨ ∃ x y h, Q = Point.some x y h ∧ x * pairK v = 1 := by
  rw [rawInverseXTemplate_rel_iff_field, append_castLE_eq]
  rcases Q with _ | ⟨x, y, h⟩
  · have h0 : (Fin.append (pointCode Point.zero) v : Fin 7 → ℚ) 0 = 1 := rfl
    have hz : (⟨(Fin.append (pointCode Point.zero) v : Fin 7 → ℚ) 5,
        (Fin.append (pointCode Point.zero) v : Fin 7 → ℚ) 6⟩ : K0) = pairK v := rfl
    rw [h0, hz]
    constructor
    · rintro (⟨-, hv⟩ | ⟨h1, -⟩)
      · exact Or.inl ⟨rfl, hv⟩
      · exact absurd h1 one_ne_zero
    · rintro (⟨-, hv⟩ | ⟨x, y, h, he, -⟩)
      · exact Or.inl ⟨rfl, hv⟩
      · exact absurd he.symm (Point.some_ne_zero h)
  · have hne : pointCode (Point.some x y h) ≠ ![1, 0, 0, 0, 0] := fun he => by
      have := congrFun he 0; simp [pointCode] at this
    have h0 : (Fin.append (pointCode (Point.some x y h)) v : Fin 7 → ℚ) 0 = 0 := rfl
    have hx : (⟨(Fin.append (pointCode (Point.some x y h)) v : Fin 7 → ℚ) 1,
        (Fin.append (pointCode (Point.some x y h)) v : Fin 7 → ℚ) 2⟩ : K0) = x := rfl
    have hz : (⟨(Fin.append (pointCode (Point.some x y h)) v : Fin 7 → ℚ) 5,
        (Fin.append (pointCode (Point.some x y h)) v : Fin 7 → ℚ) 6⟩ : K0) = pairK v := rfl
    rw [h0, hx, hz]
    constructor
    · rintro (⟨he, -⟩ | ⟨-, hv⟩)
      · exact absurd he hne
      · exact Or.inr ⟨x, y, h, rfl, hv⟩
    · rintro (⟨he, -⟩ | ⟨x', y', h', he, hv⟩)
      · exact absurd he (Point.some_ne_zero h)
      · obtain ⟨rfl, rfl⟩ := Point.some.inj he
        exact Or.inr ⟨rfl, hv⟩

/-- **The inverse abscissa template** when `Q = O` or `x(Q) ≠ 0`: `Rel(code Q, v) ↔ [v] = ρ(Q)`. -/
theorem rawInverseX_rel_iff_of (Q : genCurve.toAffine.Point)
    (hQ : ∀ x y h, Q = Point.some x y h → x ≠ 0) (v : Fin 2 → ℚ) :
    rawInverseXTemplate.Rel (Fin.append (pointCode Q) v) ↔ pairK v = invX Q := by
  rw [rawInverseX_rel_iff]
  rcases Q with _ | ⟨x, y, h⟩
  · constructor
    · rintro (⟨-, hv⟩ | ⟨x, y, h, he, -⟩)
      · exact hv
      · exact absurd he.symm (Point.some_ne_zero h)
    · intro hv; exact Or.inl ⟨rfl, hv⟩
  · have hx := hQ x y h rfl
    constructor
    · rintro (⟨he, -⟩ | ⟨x', y', h', he, hv⟩)
      · exact absurd he (Point.some_ne_zero h)
      · obtain ⟨rfl, rfl⟩ := Point.some.inj he
        exact eq_inv_of_mul_eq_one_right hv
    · intro hv
      exact Or.inr ⟨x, y, h, rfl, by rw [hv, invX_some, mul_inv_cancel₀ hx]⟩

/-- At an affine point with `x(Q) = 0` the inverse abscissa template fails. -/
theorem rawInverseX_not_rel {x y : K0} (h : genCurve.toAffine.Nonsingular x y) (hx : x = 0)
    (v : Fin 2 → ℚ) :
    ¬ rawInverseXTemplate.Rel (Fin.append (pointCode (Point.some x y h)) v) := by
  rw [rawInverseX_rel_iff]
  rintro (⟨he, -⟩ | ⟨x', y', h', he, hv⟩)
  · exact Point.some_ne_zero h he
  · obtain ⟨rfl, rfl⟩ := Point.some.inj he
    rw [hx, zero_mul] at hv
    exact zero_ne_one hv

/-! ### The truncated logarithm -/

theorem Pair.val_smul_C (x : ℕ → ℚ) (c : ℤ) (u : Pair) :
    Pair.val x (Pair.smul (MvPolynomial.C c) u) = (c : K0) * Pair.val x u := by
  rw [Pair.val_smul, ev_C, QuadraticAlgebra.C_intCast]

/-- The pair polynomial `L(ζ)` represents the truncated logarithm: `[L(ζ)] = L([ζ])`. -/
theorem Pair.val_log25 (x : ℕ → ℚ) (ζ : Pair) :
    Pair.val x ζ.log25 = truncLog (genD ^ 2) (Pair.val x ζ) := by
  simp only [Pair.log25, Pair.log25Aux, log25Coeffs, Pair.val_add, Pair.val_smul_C, Pair.val_mul,
    Pair.val_pow, Pair.val_delta, Pair.val_one, Pair.val_zero]
  rw [truncLog_eq]
  push_cast
  ring

/-- **The truncated logarithm template**: `Rel(ζ, λ) ↔ [λ] = L([ζ])`. -/
theorem log25_rel_iff (ζ lam : Fin 2 → ℚ) :
    log25Template.Rel (Fin.append ζ lam) ↔ pairK lam = truncLog (genD ^ 2) (pairK ζ) := by
  rw [log25Template_rel_iff]
  have hv : ∀ y : Fin 0 → ℚ, Pair.val (assign 4 0 (Fin.append ζ lam) y) (varPair 0) = pairK ζ :=
    fun y => by
      ext
      · simp only [Pair.re_val, ev_varPair_fst]
        exact assign_of_lt (i := 0) (Fin.append ζ lam) y (by omega)
      · simp only [Pair.im_val, ev_varPair_snd]
        exact assign_of_lt (i := 1) (Fin.append ζ lam) y (by omega)
  have hl : ∀ y : Fin 0 → ℚ, Pair.val (assign 4 0 (Fin.append ζ lam) y) (varPair 2) = pairK lam :=
    fun y => by
      ext
      · simp only [Pair.re_val, ev_varPair_fst]
        exact assign_of_lt (i := 2) (Fin.append ζ lam) y (by omega)
      · simp only [Pair.im_val, ev_varPair_snd]
        exact assign_of_lt (i := 3) (Fin.append ζ lam) y (by omega)
  simp only [holds_feq, Pair.val_log25, hv, hl]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨Fin.elim0, h.symm⟩⟩

/-! ### On the codes `ι(n)` -/

/-- A multiple `[n]P₀` is `O` or has `x, y ≠ 0`. -/
theorem zsmul_genP0_coords (n : ℤ) :
    ∀ x y h, n • genP0 = Point.some x y h → x ≠ 0 ∧ y ≠ 0 := by
  intro x y h he
  by_cases hn : n = 0
  · subst hn; rw [zero_zsmul] at he; exact absurd he.symm (Point.some_ne_zero h)
  · obtain ⟨x', y', h', he', hx, hy, -⟩ := log25_z_ne_zero hn
    rw [he'] at he
    obtain ⟨rfl, rfl⟩ := Point.some.inj he
    exact ⟨hx, hy⟩

/-- On `ι(n)`, `raw_z` computes `z([n]P₀)`. -/
theorem rawZ_rel_iota (n : ℤ) (ζ : Fin 2 → ℚ) :
    rawZTemplate.Rel (Fin.append (iota n) ζ) ↔ pairK ζ = zOf (n • genP0) :=
  rawZ_rel_iff_of _ (fun x y h he => (zsmul_genP0_coords n x y h he).2) ζ

/-- On `ι(n)`, `raw_inverse_x` computes `ρ([n]P₀)`. -/
theorem rawInverseX_rel_iota (n : ℤ) (v : Fin 2 → ℚ) :
    rawInverseXTemplate.Rel (Fin.append (iota n) v) ↔ pairK v = invX (n • genP0) :=
  rawInverseX_rel_iff_of _ (fun x y h he => (zsmul_genP0_coords n x y h he).1) v

end ZInQ.Mult
