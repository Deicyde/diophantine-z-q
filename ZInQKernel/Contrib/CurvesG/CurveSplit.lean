import ZInQKernel.Contrib.CurvesG.RatPoint

/-! # curves-g: `CurveOfFunctionFieldQNoPoint` (T38 without its point clause) from three textbook facts

(A) a finite extension of `ℚ(T)` is the function field of a normal proper integral `ℚ`-scheme of
dimension 1; (B) a normal integral scheme of dimension 1, locally of finite type over `ℚ`, is smooth of
relative dimension 1; (C) a normal proper integral `ℚ`-scheme whose function field has constant field
`ℚ` is geometrically connected. The glue (`curveOfFunctionFieldQNoPoint_of_split`) is proved; with
`RatPoint.lean`, so is `X1Belyi.CurveOfFunctionFieldQ` from (A), (B), (C).
No `sorry`, no `axiom`. -/

noncomputable section

namespace ZInQ.Contrib.CurvesG

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi

/-- A scheme is normal: every stalk is an integrally closed domain (Mathlib has no normal schemes;
for an integral scheme the stalks are domains, so this is the usual notion, Stacks 033H). -/
def IsNormalScheme (X : Scheme) : Prop := ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

/-- **Leaf (A): the normal model of a function field.** A finite extension `F` of `ℚ(T)` is the
function field of a normal proper integral scheme `X` of dimension 1 over `ℚ`. Published: the
normalization of `ℙ¹_ℚ` in `F` (finite over `ℙ¹_ℚ` because `F/ℚ(T)` is separable and finite);
Stacks Project, *Algebraic Curves*, section "Curves and function fields" (Tag 0BXX, UNVERIFIED tag);
Hartshorne I.6.7-6.9 and II.6.7 (UNVERIFIED numbers). -/
def NormalModelOfFunctionFieldQ : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [FiniteDimensional Qj F],
    ∃ X : Over SpecQ, IsProper X.hom ∧ ∃ (_ : IsIntegral X.left), IsNormalScheme X.left ∧
      topologicalKrullDim X.left = 1 ∧ Nonempty (X.left.functionField ≃+* F)

/-- **Leaf (B): normal curves in characteristic 0 are smooth.** A normal integral scheme of dimension
1, locally of finite type over `ℚ`, is smooth of relative dimension 1 over `ℚ`. Published: its local
rings at closed points are one-dimensional normal noetherian local domains, i.e. discrete valuation
rings (Atiyah–Macdonald Prop. 9.2), so it is regular; a regular scheme locally of finite type over a
perfect field is smooth, of relative dimension the local dimension (Stacks Tag 00TV / Lemma 0B8X for
curves, UNVERIFIED tags). -/
def NormalCurveSmoothQ : Prop :=
  ∀ (X : Over SpecQ), LocallyOfFiniteType X.hom → ∀ (_ : IsIntegral X.left), IsNormalScheme X.left →
    topologicalKrullDim X.left = 1 → SmoothOfRelativeDimension 1 X.hom

/-- **Leaf (C): constant field `ℚ` gives geometric connectedness.** A normal proper integral scheme
`X` over `ℚ` whose function field is isomorphic to a field `F ⊇ ℚ(T)` in which `ℚ` is algebraically
closed is geometrically connected over `ℚ`. Published: `Γ(X, 𝒪_X)` is a finite `ℚ`-algebra and a
domain inside the function field, hence a field algebraic over `ℚ`, hence `ℚ`; a proper scheme over
a field `k` with `Γ(X, 𝒪_X) = k` is geometrically connected (Stacks Tag 0FD1, UNVERIFIED tag; EGA III
4.3.4 via Stein factorization). -/
def GeomConnectedOfConstantFieldQ : Prop :=
  ∀ (X : Over SpecQ), IsProper X.hom → ∀ (_ : IsIntegral X.left), IsNormalScheme X.left →
    ∀ (F : Type) [Field F] [Algebra Qj F], ConstantFieldIsQ F →
      Nonempty (X.left.functionField ≃+* F) → GeometricallyConnected X.hom

/-- **Reduction (proved): T38 without its point clause from (A), (B), (C).** -/
theorem curveOfFunctionFieldQNoPoint_of_split (hA : NormalModelOfFunctionFieldQ)
    (hB : NormalCurveSmoothQ) (hC : GeomConnectedOfConstantFieldQ) :
    CurveOfFunctionFieldQNoPoint := by
  intro F _ _ _ hF
  obtain ⟨X, hP, hI, hN, hd, he⟩ := hA F
  have : IsProper X.hom := hP
  have hS := hB X (by infer_instance) hI hN hd
  have hG := hC X hP hI hN F hF he
  exact ⟨X, ⟨hP, hS, hG⟩, hI, he⟩

/-- **Reduction (proved): T38 (`X1Belyi.CurveOfFunctionFieldQ`) from (A), (B), (C).** -/
theorem curveOfFunctionFieldQ_of_split (hA : NormalModelOfFunctionFieldQ)
    (hB : NormalCurveSmoothQ) (hC : GeomConnectedOfConstantFieldQ) :
    CurveOfFunctionFieldQ :=
  curveOfFunctionFieldQ_of_noPoint (curveOfFunctionFieldQNoPoint_of_split hA hB hC)

end ZInQ.Contrib.CurvesG
