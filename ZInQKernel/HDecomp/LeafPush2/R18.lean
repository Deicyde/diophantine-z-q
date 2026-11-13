import ZInQKernel.HDecomp.Faltings.Height
import ZInQKernel.HDecomp.ModCurves.Leaves

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from
`scratch/leaf-push2/LeafPush2.lean`, Part II and R18.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-!
# leaf-push2: concrete statements of R18, R22, R3 over the new definitions

Task leaf-push2 (2026-11-12). One file. Contents:

* Part I (copied from `scratch/def-faltings/Faltings.lean` §§1-18 and the H5 section, namespace
  renamed to `ZInQ.LeafPush2`; the local copy of `AbVar` is **replaced by the kernel's
  `PkgI3.AbVar`** (`ZInQKernel/HDecomp/Objects.lean`), so the stable Faltings height is defined on
  the same abelian varieties as the Jacobians of leaf-modcurves). Nothing in Part I is new.
* Part II (copied from `scratch/leaf-modcurves/ModCurveLeaves.lean` §D, §E, §G): curves, the
  Albanese predicate `IsJacobian`, the leaf `JacobianExists`, `IsBelyiFunction`.
* Part III (new): R18 (Javanpeykar), R22 (Pazuki), R3 (Lin–Yang), sanity theorems.
-/

namespace ZInQ.LeafPush2

open NumberField MeasureTheory

/-! Part I of the draft (def-faltings §§1-18 and H5, a verbatim copy) is imported from
`ZInQKernel.HDecomp.Faltings.Height`, namespace `ZInQ.DefFaltings`; the copies of
leaf-modcurves' curve definitions are `LeafModCurves`'s, from
`ZInQKernel.HDecomp.ModCurves.Leaves`. -/
open ZInQ.DefFaltings
open LeafModCurves (IsCurve IsJacobian JacobianExists IsBelyiFunction)

/-! # Part II. Curves, Jacobians, Belyi functions (copied from
`scratch/leaf-modcurves/ModCurveLeaves.lean` §D, §E, §G; definitions unchanged) -/

section CurvesSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-! ### New: the function field of a curve as a `K`-algebra -/

variable {K : Type} [Field K]

/-- The structure map `K → K(X)` of an integral `K`-scheme: `K = Γ(Spec K) → Γ(X) → K(X)`. -/
noncomputable def ffStructMap (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left] :
    K →+* X.left.functionField :=
  haveI : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ X.hom.appTop ≫
    X.left.germToFunctionField ⊤).hom

/-- `K(X)` as a `K`-algebra (a local instance-free definition; used through `letI`). -/
@[instance_reducible] noncomputable def ffAlgebra (X : Over (Spec (CommRingCat.of K))) [IsIntegral
    X.left] :
    Algebra K X.left.functionField :=
  (ffStructMap X).toAlgebra

end CurvesSec

/-! # Part III. The leaves R18, R22, R3 -/

section R18Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3

/-- **The bound of R18**: `13·10⁶ · g · d⁵`. -/
noncomputable def javanpeykarBound (g d : ℕ) : ℝ := 13 * 10 ^ 6 * g * d ^ 5

/-- **R18. Javanpeykar** (Algebra Number Theory 8 (2014), Thm 1.1.1, p. 90; arXiv:1403.6404v1
p. 1; height identification p. 98 / arXiv §2.3 p. 9; read by the locator audit,
docs/research/locators.md). Printed: for a smooth projective connected curve `X/ℚ̄` of genus
`g ≥ 1`, `h_Fal(X) ≤ 13·10⁶ · g · deg_B(X)⁵`, where `h_Fal(X)` is the stable Faltings height of
`Jac X` and `deg_B(X)` the least degree of a Belyi map `X → ℙ¹_ℚ̄`.

**Stated form (a consequence).** `X` is a smooth proper geometrically connected integral curve over
a number field `K` with a `K`-point `P₀`; `J` is its Jacobian (Albanese predicate, over the
kernel's `PkgI3.AbVar`); `g = dim J` (= genus `X`, Milne 1986 Prop. 2.1/Thm 1.1, UNVERIFIED
numbers; rv-blueprints §2 recommendation 5: state with `g := dim J`); `t ∈ K(X)` is a Belyi
function over `K` with `d = [K(X) : K(t)]`. Then `h_F^st(J) ≤ 13·10⁶ · g · d⁵`.

Why it is a consequence of the printed theorem:
* `X_ℚ̄` (any embedding `K ↪ ℚ̄`) is smooth projective connected of genus `g`; `J_ℚ̄ = Jac(X_ℚ̄)`
  (the Albanese property is stable under field extension; STANDARD, Milne 1986).
* A Belyi function over `K` is one over `ℚ̄` of the same degree (characteristic 0, `K`
  algebraically closed in `K(X)`), so `deg_B(X_ℚ̄) ≤ d`, and the bound is monotone in `d`.
* The stable height does not depend on the field of definition, and in either of the two
  normalizations in question (Faltings' `(i/2)^g`, Deligne's `(i/2π)^g`) the bound holds for
  `h_F`, since `h_D = h_F + (g/2) log π ≥ h_F` (rv-blueprints §1.2). A normalization without the
  `2^{-g}` factor would give `h = h_F − (g/2) log 2` and make this form stronger; the locator audit
  read Javanpeykar's height as the stable Faltings height (leaf-push2 review: RISK, low).
* **H5** (rv-blueprints F2): `stableFaltingsHeight` (an infimum over metrized smooth group
  models, `EReal`) equals the published height. Only the half "the Néron model over a semistable
  field is a metrized model with the published height" is used here (an upper bound on an
  infimum). The statement asserts in particular `stableFaltingsHeight J < ⊤`, which is part of
  that half (the published height is a real number). -/
def R18_Javanpeykar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K))) [IsCurve X]
    [IsIntegral X.left] (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K)
    (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ t : X.left.functionField,
      letI := ffAlgebra X
      IsBelyiFunction K X.left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d → 0 < d →
        stableFaltingsHeight J ≤ ((javanpeykarBound g d : ℝ) : EReal)

/-- The real-valued form: if the stable height is a real number `x`, then `x ≤ 13·10⁶ g d⁵`. -/
theorem R18_real (h : R18_Javanpeykar) (K : Type) [Field K] [NumberField K]
    (X : Over (Spec (CommRingCat.of K))) [IsCurve X] [IsIntegral X.left]
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X) (J : AbVar K) (aj : X ⟶ J.X)
    (hJ : IsJacobian X P₀ J aj) (g : ℕ) (hg : J.dim = (g : WithBot ℕ∞)) (hg1 : 1 ≤ g)
    (t : X.left.functionField)
    (ht : letI := ffAlgebra X; IsBelyiFunction K X.left.functionField t) (d : ℕ)
    (hd : letI := ffAlgebra X
      Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d) (hd0 : 0 < d)
    (x : ℝ) (hx : stableFaltingsHeight J = x) : x ≤ javanpeykarBound g d := by
  have := h K X P₀ J aj hJ g hg hg1 t ht d hd hd0
  rw [hx] at this
  exact_mod_cast this

/-- Sanity: the bound is positive for `g, d ≥ 1` (so the leaf is not of the form `h ≤ 0`). -/
theorem javanpeykarBound_pos {g d : ℕ} (hg : 1 ≤ g) (hd : 0 < d) : 0 < javanpeykarBound g d := by
  unfold javanpeykarBound
  have : (0 : ℝ) < g := by exact_mod_cast hg
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

/-- Monotonicity in the Belyi degree (the step "any Belyi map bounds the minimal Belyi degree"). -/
theorem javanpeykarBound_mono {g d d' : ℕ} (hdd : d ≤ d') :
    javanpeykarBound g d ≤ javanpeykarBound g d' := by
  unfold javanpeykarBound
  have : (d : ℝ) ≤ d' := by exact_mod_cast hdd
  have : (d : ℝ) ^ 5 ≤ (d' : ℝ) ^ 5 := pow_le_pow_left₀ (by positivity) this 5
  have h0 : (0 : ℝ) ≤ 13 * 10 ^ 6 * g := by positivity
  nlinarith

end R18Sec

/-! ## R22 (Pazuki): complex points, analytic uniformization, Siegel space, theta constants -/

end ZInQ.LeafPush2
