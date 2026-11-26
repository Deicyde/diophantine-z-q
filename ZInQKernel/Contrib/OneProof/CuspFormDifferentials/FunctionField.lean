import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Core
import ZInQKernel.Contrib.OneProof.RC.X0Model.Section
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Hom.Rat

/-! P1, the printed leaf for Route B: the function field of `X₀(N)` over `ℂ` is
`ℂ(j, j_N)`, `j_N(τ) = j(Nτ)`.

Source: F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in
Mathematics 228, Springer (2005), Section 7.5 "Function fields over C", beginning on
p. 279 of the 2005 printing (p. 283 in the corrected fourth printing, 2016). The section
title and page are confirmed from the publisher's table of contents. The page itself was
not read: no authorized copy of p. 279 was available, so the wording below is the
standard statement of the result (`ℂ(X₀(N)) = ℂ(j, j_N)`), its theorem number is
unverified, and the reading status is UNREAD.

Reading. A meromorphic function on `X₀(N)` is a meromorphic function `g` on `ℍ` that is
`Γ₀(N)`-invariant and meromorphic at every cusp. Meromorphy at the cusp `σ(∞)`,
`σ ∈ SL(2, ℤ)`, is the growth condition that `q_N^m · g(στ)` is bounded as `Im τ → ∞`
for some `m`, together with holomorphy of `g(στ)` for large `Im τ`. The printed equality
`ℂ(X₀(N)) = ℂ(j, j_N)` has a trivial inclusion; its content is that every such `g` is
a quotient `P(j, j_N) / Q(j, j_N)` of complex polynomials with `Q(j, j_N) ≠ 0`. This is
`DSFunctionFieldX0`, stated on punctured germs at every point of `ℍ`, the germs of `j`
and `j_N` being the images of the model's generators under `X0Model.fieldGerm`.

The Lean reading `P1` replaces the polynomials by elements `A`, `B` of
`ℂ ⊗[ℚ] ℚ(X₀(N))`, mapped to germs by the complex-linear extension `fieldGermC` of
`X0Model.fieldGerm`. The base change of `X₀(N)` to `ℂ` is `curveC N`, and its function
field is the fraction field of `ℂ ⊗[ℚ] ℚ(X₀(N))`; so `A / B` is an element of the
function field of `curveC N`. That identification is a remark, not a statement used
below. `p1_of_dsFunctionFieldX0` derives `P1` from the printed form, and
`dsFunctionFieldX0_proof` (in `FunctionFieldProof`) proves the printed form from the complex
cusp classification of the base, so the leaf is discharged. -/

noncomputable section

open Filter UpperHalfPlane ModularCurve ShimuraPointDict
open scoped Topology TensorProduct MatrixGroups

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open X0Model

variable (N : ℕ) [NeZero N]

/-- The complex scalar extension `ℂ ⊗[ℚ] ℚ(X₀(N))` of the model's function field. Its
fraction field is the function field of `curveC N`. -/
abbrev FieldC : Type := ℂ ⊗[ℚ] modularFunctionField N

/-- The first generator `j` of the model's function field. -/
def jField : modularFunctionField N := ⟨jq, jq_mem N⟩

/-- The second generator `j_N` of the model's function field. -/
def jNField : modularFunctionField N := ⟨jqN N, jqN_mem N⟩

/-- The rational structure on the local meromorphic field, through the constants. -/
instance ratAlgebraMeromorphicGerm (z : ℂ) : Algebra ℚ (MeromorphicGerm z) :=
  ((constantGerm z).comp (algebraMap ℚ ℂ)).toAlgebra

/-- The complex-linear extension of `X0Model.fieldGerm` to `ℂ ⊗[ℚ] ℚ(X₀(N))`. -/
def fieldGermC (τ : ℍ) : FieldC N →+* MeromorphicGerm (τ : ℂ) :=
  (Algebra.TensorProduct.lift (constantGerm (τ : ℂ)).toRatAlgHom
    (fieldGerm N τ).toRatAlgHom (fun _ _ => Commute.all _ _)).toRingHom

theorem fieldGermC_tmul (τ : ℍ) (c : ℂ) (a : modularFunctionField N) :
    fieldGermC N τ (c ⊗ₜ a) = constantGerm (τ : ℂ) c * fieldGerm N τ a := by
  change (Algebra.TensorProduct.lift _ _ _) (c ⊗ₜ a) = _
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

/-- The germ of `j` at a point of `ℍ`. -/
def jGerm (τ : ℍ) : MeromorphicGerm (τ : ℂ) := fieldGerm N τ (jField N)

/-- The germ of `j_N` at a point of `ℍ`. -/
def jNGerm (τ : ℍ) : MeromorphicGerm (τ : ℂ) := fieldGerm N τ (jNField N)

/-- Evaluation of a complex polynomial in two variables at the germs of `j` and `j_N`. -/
def polyGerm (τ : ℍ) : MvPolynomial (Fin 2) ℂ →+* MeromorphicGerm (τ : ℂ) :=
  MvPolynomial.eval₂Hom (constantGerm (τ : ℂ)) ![jGerm N τ, jNGerm N τ]

/-- A meromorphic function on `X₀(N)`, read as a function on `ℍ` (extended by any values
off `ℍ`): meromorphic on `ℍ`, `Γ₀(N)`-invariant, and meromorphic at every cusp `σ(∞)`,
meaning that `q_N^m · g(στ)` is bounded at `i∞` for some `m` and `g(στ)` is holomorphic
for large `Im τ`. -/
structure IsX0Function (g : ℂ → ℂ) : Prop where
  meromorphicOn : MeromorphicOn g {z : ℂ | 0 < z.im}
  invariant : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
    ∀ τ : ℍ, g (γ • τ : ℍ) = g τ
  cusp_growth : ∀ σ : SL(2, ℤ), ∃ m : ℕ,
    IsBoundedAtImInfty (fun τ : ℍ => Function.Periodic.qParam N τ ^ m * g (σ • τ : ℍ))
  cusp_holomorphic : ∀ σ : SL(2, ℤ), ∀ᶠ z : ℂ in comap Complex.im atTop,
    DifferentiableAt ℂ (fun w : ℂ => g (σ • ofComplex w : ℍ)) z

/-- **P1, printed form (Diamond–Shurman, GTM 228, §7.5, `ℂ(X₀(N)) = ℂ(j, j_N)`).** For
every `N ≥ 1`, every meromorphic function `g` on `X₀(N)` is a rational function of `j`
and `j_N(τ) = j(Nτ)` with complex coefficients: there are complex polynomials `P`, `Q` in
two variables with `Q(j, j_N) ≠ 0` and `g · Q(j, j_N) = P(j, j_N)` as meromorphic
functions, stated on the punctured germ at every point of `ℍ`. -/
def DSFunctionFieldX0 : Prop :=
  ∀ (N : ℕ) [NeZero N] (g : ℂ → ℂ), IsX0Function N g →
    ∃ P Q : MvPolynomial (Fin 2) ℂ, ∀ τ : ℍ, polyGerm N τ Q ≠ 0 ∧
      (g : PuncturedGerm (τ : ℂ)) * meromorphicIncl (τ : ℂ) (polyGerm N τ Q) =
        meromorphicIncl (τ : ℂ) (polyGerm N τ P)

/-- **P1, Lean reading.** Every meromorphic function on `X₀(N)` is, at every point of
`ℍ`, the extended `fieldGerm` of a quotient `A / B` with `A`, `B ∈ ℂ ⊗[ℚ] ℚ(X₀(N))`,
that is, of an element of the function field of `curveC N`. -/
def P1 : Prop :=
  ∀ g : ℂ → ℂ, IsX0Function N g →
    ∃ A B : FieldC N, ∀ τ : ℍ, fieldGermC N τ B ≠ 0 ∧
      (g : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGermC N τ A / fieldGermC N τ B)

/-- Evaluation of a polynomial at `1 ⊗ j` and `1 ⊗ j_N` inside `ℂ ⊗[ℚ] ℚ(X₀(N))`. -/
def polyField : MvPolynomial (Fin 2) ℂ →+* FieldC N :=
  MvPolynomial.eval₂Hom (algebraMap ℂ (FieldC N))
    ![(1 : ℂ) ⊗ₜ jField N, (1 : ℂ) ⊗ₜ jNField N]

theorem fieldGermC_polyField (τ : ℍ) (P : MvPolynomial (Fin 2) ℂ) :
    fieldGermC N τ (polyField N P) = polyGerm N τ P := by
  have h : (fieldGermC N τ).comp (polyField N) = polyGerm N τ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, polyField, polyGerm, MvPolynomial.eval₂Hom_C,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        fieldGermC_tmul, map_one, mul_one]
    · intro i
      fin_cases i <;>
        simp [polyField, polyGerm, fieldGermC_tmul, jGerm, jNGerm]
  exact congrArg (fun φ : MvPolynomial (Fin 2) ℂ →+* MeromorphicGerm (τ : ℂ) => φ P) h

/-- The printed form implies the Lean reading. -/
theorem p1_of_dsFunctionFieldX0 (h : DSFunctionFieldX0) : P1 N := by
  intro g hg
  obtain ⟨P, Q, hPQ⟩ := h N g hg
  refine ⟨polyField N P, polyField N Q, fun τ => ?_⟩
  obtain ⟨hQ, he⟩ := hPQ τ
  rw [fieldGermC_polyField, fieldGermC_polyField]
  refine ⟨hQ, ?_⟩
  let G : MeromorphicGerm (τ : ℂ) :=
    ⟨(g : PuncturedGerm (τ : ℂ)), g, rfl, hg.meromorphicOn τ τ.im_pos⟩
  have hG : G * polyGerm N τ Q = polyGerm N τ P := by
    apply (meromorphicIncl (τ : ℂ)).injective
    rw [map_mul]
    exact he
  have : G = polyGerm N τ P / polyGerm N τ Q := (eq_div_iff hQ).mpr hG
  rw [← this]
  rfl

end ZInQ.Manuscript.RC.CuspFormDifferentials
