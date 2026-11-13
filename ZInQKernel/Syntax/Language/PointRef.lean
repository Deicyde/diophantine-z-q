import ZInQKernel.Syntax.Language.Basic
import ZInQKernel.Hypotheses.MordellWeil

/-!
# Point references

In a model-evaluation recipe with generator variable indices `g₀, g₁, g₂`, a point reference
`r ≥ -3` stands for five polynomials: the variables `X_r, …, X_{r+4}` for `r ≥ 0`, the code
`(1,0,0,0,0)` of `O` for `r = -1`, and the generator codes `(0, X_{g₀}, -145, ±X_{g₁}, ±X_{g₂})`
for `r = -2, -3`. Every model-evaluation recipe conjoins the three generator constraints
`8X_{g₀} - 1641`, `4X_{g₁} + 15465`, `32X_{g₂} - 87483`; under them the references `-1, -2, -3`
take the values `(1,0,0,0,0)`, `codeP0` and `codeNegP0`.
-/

namespace ZInQ.Syntax

open MvPolynomial

/-- The five polynomials of a point reference. References below `-3` do not occur; they are
read as five zeros. -/
noncomputable def pointRef (g : Fin 3 → ℕ) : ℤ → Fin 5 → Poly
  | .ofNat r => fun i => X (r + i)
  | .negSucc 0 => ![1, 0, 0, 0, 0]
  | .negSucc 1 => ![0, X (g 0), -145, X (g 1), X (g 2)]
  | .negSucc 2 => ![0, X (g 0), -145, -X (g 1), -X (g 2)]
  | .negSucc (_ + 3) => fun _ => 0

/-- The five polynomials of a point reference, as a list. -/
noncomputable def pointRefList (g : Fin 3 → ℕ) (r : ℤ) : List Poly := List.ofFn (pointRef g r)

theorem pointRef_natCast (g : Fin 3 → ℕ) (r : ℕ) (i : Fin 5) :
    pointRef g r i = X (r + i) := rfl

theorem pointRef_neg_one (g : Fin 3 → ℕ) : pointRef g (-1) = ![1, 0, 0, 0, 0] := rfl

theorem pointRef_neg_two (g : Fin 3 → ℕ) :
    pointRef g (-2) = ![0, X (g 0), -145, X (g 1), X (g 2)] := rfl

theorem pointRef_neg_three (g : Fin 3 → ℕ) :
    pointRef g (-3) = ![0, X (g 0), -145, -X (g 1), -X (g 2)] := rfl

/-- The generator constraints of a model-evaluation recipe. -/
noncomputable def generatorConstraints (g : Fin 3 → ℕ) : List Poly :=
  [8 * X (g 0) - 1641, 4 * X (g 1) + 15465, 32 * X (g 2) - 87483]

/-- The rational values of a code of five polynomials. -/
noncomputable def evCode (x : ℕ → ℚ) (p : Fin 5 → Poly) : Fin 5 → ℚ := fun i => ev x (p i)

/-- The code `ι(1)` of `P₀ = ((1641 - 1160 s)/8, (-123720 + 87483 s)/32)`. -/
def codeP0 : Fin 5 → ℚ := ![0, 1641 / 8, -145, -15465 / 4, 87483 / 32]

/-- The code `ι(-1)` of `-P₀`. -/
def codeNegP0 : Fin 5 → ℚ := ![0, 1641 / 8, -145, 15465 / 4, -87483 / 32]

/-- The generator constraints vanish exactly at the cached generator coordinates. -/
theorem generatorConstraints_eq_zero_iff (g : Fin 3 → ℕ) (x : ℕ → ℚ) :
    (∀ c ∈ generatorConstraints g, ev x c = 0) ↔
      x (g 0) = 1641 / 8 ∧ x (g 1) = -15465 / 4 ∧ x (g 2) = 87483 / 32 := by
  simp only [generatorConstraints, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, map_sub, map_add, map_mul, ev_X, map_ofNat]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2⟩
    rw [h0, h1, h2]
    norm_num

/-- **Values of the point references.** Under the generator constraints the references
`-1, -2, -3` evaluate to the codes of `O`, `P₀` and `-P₀`. -/
theorem pointRef_eval_generator (g : Fin 3 → ℕ) (x : ℕ → ℚ)
    (h : ∀ c ∈ generatorConstraints g, ev x c = 0) :
    evCode x (pointRef g (-1)) = ![1, 0, 0, 0, 0] ∧ evCode x (pointRef g (-2)) = codeP0 ∧
      evCode x (pointRef g (-3)) = codeNegP0 := by
  obtain ⟨h0, h1, h2⟩ := (generatorConstraints_eq_zero_iff g x).1 h
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;>
    simp [evCode, pointRef_neg_one, pointRef_neg_two, pointRef_neg_three, codeP0, codeNegP0,
      h0, h1, h2] <;> norm_num

/-- The coordinates encoded by `codeP0` are those of `P₀`:
`1641/8 - 145 s = (1641 - 1160 s)/8` and `-15465/4 + (87483/32) s = (-123720 + 87483 s)/32`. -/
theorem codeP0_coordinates :
    (⟨codeP0 1, codeP0 2⟩ : K0) = (1641 - 1160 * sqrt2) / 8 ∧
      (⟨codeP0 3, codeP0 4⟩ : K0) = (-123720 + 87483 * sqrt2) / 32 := by
  constructor
  · rw [eq_div_iff (by norm_num)]
    ext <;> simp [codeP0, sqrt2, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]; norm_num
  · rw [eq_div_iff (by norm_num)]
    ext <;> simp [codeP0, sqrt2, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]; norm_num

end ZInQ.Syntax
