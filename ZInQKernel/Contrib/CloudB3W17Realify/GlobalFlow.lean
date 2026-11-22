import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
# Global curves of canonical left-invariant vector fields

Partial Lie-theoretic infrastructure for W17. This file uses Mathlib's actual
`mulInvariantVectorField` and actual integral-curve predicates. Global existence
is proved from local existence and translation, not assumed. No compactness,
finite-dimensionality, exponential map, or joint parameter regularity is claimed.
-/

open Function Set
open scoped Manifold Topology

namespace CloudB3W17Realify

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section RealLieGroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I 3 G]

/-- The canonical left-invariant field is `C¹`. -/
theorem contMDiff_invariantField (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent 1 (fun g : G => (mulInvariantVectorField v g : TangentBundle I G)) := by
  let : LieGroup I (minSmoothness ℝ 3) G := by
    simpa using (inferInstance : LieGroup I 3 G)
  have h : ContMDiff I I.tangent 2
      (fun g : G => (mulInvariantVectorField v g : TangentBundle I G)) := by
    simpa using contMDiff_mulInvariantVectorField v
  exact h.of_le (by norm_num)

/-- Left translation sends the canonical field at `h` to the same field at `g*h`. -/
theorem mfderiv_mul_left_invariant (g h : G) (v : GroupLieAlgebra I G) :
    mfderiv I I (g * ·) h (mulInvariantVectorField v h) =
      mulInvariantVectorField v (g * h) := by
  unfold mulInvariantVectorField
  have hc := mfderiv_comp (I' := I) (1 : G)
    ((contMDiffAt_mul_left (I := I) (n := 3) (a := g) (b := h * 1)).mdifferentiableAt
      (by norm_num))
    ((contMDiffAt_mul_left (I := I) (n := 3) (a := h) (b := 1)).mdifferentiableAt
      (by norm_num))
  have heq : (g * ·) ∘ (h * ·) = ((g * h) * ·) := by
    funext x
    simp only [comp_apply, mul_assoc]
  rw [heq, mul_one] at hc
  exact congrArg (fun f => f v) hc.symm

/-- Translating an integral curve on a set preserves its canonical left-invariant field. -/
theorem isMIntegralCurveOn_mul_left (v : GroupLieAlgebra I G) {γ : ℝ → G} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ (mulInvariantVectorField v) s) (g : G) :
    IsMIntegralCurveOn (fun t => g * γ t) (mulInvariantVectorField v) s := by
  intro t ht
  have h := ((contMDiffAt_mul_left (I := I) (n := 3) (a := g) (b := γ t)).mdifferentiableAt
    (by norm_num)).hasMFDerivAt
    |>.comp_hasMFDerivWithinAt t (hγ t ht)
  apply h.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change mfderiv I I (g * ·) (γ t) (a • mulInvariantVectorField v (γ t)) =
    a • mulInvariantVectorField v (g * γ t)
  rw [map_smul, mfderiv_mul_left_invariant]

/-- Global curves also remain integral curves after left translation. -/
theorem isMIntegralCurve_mul_left (v : GroupLieAlgebra I G) {γ : ℝ → G}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (g : G) :
    IsMIntegralCurve (fun t => g * γ t) (mulInvariantVectorField v) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  exact isMIntegralCurveOn_mul_left v hγ g

/-- Canonical left-invariant fields are complete on boundaryless real Banach Lie groups. -/
theorem exists_global_invariantCurve [CompleteSpace E] [T2Space G] [BoundarylessManifold I G]
    (v : GroupLieAlgebra I G) (g : G) :
    ∃ γ : ℝ → G, γ 0 = g ∧ IsMIntegralCurve γ (mulInvariantVectorField v) := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
    (I := I) (x₀ := (1 : G)) (0 : ℝ) (contMDiff_invariantField v).contMDiffAt
  obtain ⟨ε, hε, hγε⟩ := isMIntegralCurveAt_iff'.mp hγ
  have hγε' : IsMIntegralCurveOn γ (mulInvariantVectorField v) (Ioo (-ε) ε) := by
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hγε
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn (contMDiff_invariantField v) hε
    (fun x => ⟨fun t => x * γ t, by simp only [hγ0, mul_one],
      isMIntegralCurveOn_mul_left v hγε' x⟩) g

/-- Two global curves of the canonical field agreeing once agree everywhere. -/
theorem invariantCurve_unique [T2Space G] [BoundarylessManifold I G]
    (v : GroupLieAlgebra I G) {γ δ : ℝ → G} {t₀ : ℝ}
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v))
    (hδ : IsMIntegralCurve δ (mulInvariantVectorField v)) (h₀ : γ t₀ = δ t₀) : γ = δ :=
  isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (contMDiff_invariantField v) hγ hδ h₀

/-- There is exactly one global canonical-field curve through every group point. -/
theorem existsUnique_global_invariantCurve [CompleteSpace E] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (g : G) :
    ∃! γ : ℝ → G, γ 0 = g ∧ IsMIntegralCurve γ (mulInvariantVectorField v) := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_invariantCurve v g
  refine ⟨γ, ⟨hγ0, hγ⟩, ?_⟩
  intro δ hδ
  exact invariantCurve_unique v hδ.2 hγ (hδ.1.trans hγ0.symm)

/-- The global canonical-field curve from the identity is a one-parameter subgroup. -/
theorem invariantCurve_add [T2Space G] [BoundarylessManifold I G]
    (v : GroupLieAlgebra I G) {γ : ℝ → G} (hγ0 : γ 0 = 1)
    (hγ : IsMIntegralCurve γ (mulInvariantVectorField v)) (s t : ℝ) :
    γ (s + t) = γ s * γ t := by
  have heq : γ ∘ (· + s) = (fun u => γ s * γ u) :=
    invariantCurve_unique v (hγ.comp_add s) (isMIntegralCurve_mul_left v hγ (γ s))
      (t₀ := 0) (by simp only [comp_apply, zero_add, hγ0, mul_one])
  simpa only [comp_apply, add_comm t s] using congrFun heq t

/-- Exact existence and uniqueness of a real one-parameter curve with velocity `v`. -/
theorem existsUnique_oneParameterCurve [CompleteSpace E] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) :
    ∃! γ : ℝ → G, γ 0 = 1 ∧ IsMIntegralCurve γ (mulInvariantVectorField v) :=
  existsUnique_global_invariantCurve v 1

/-- Package the canonical curve as an additive homomorphism into `Additive G`. -/
theorem exists_oneParameterSubgroup [CompleteSpace E] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) :
    ∃ γ : ℝ →+ Additive G,
      IsMIntegralCurve (fun t => Additive.toMul (γ t)) (mulInvariantVectorField v) := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_invariantCurve v 1
  refine ⟨{
    toFun := fun t => Additive.ofMul (γ t)
    map_zero' := hγ0
    map_add' := fun s t => invariantCurve_add v hγ0 hγ s t }, ?_⟩
  exact hγ

/-- The packaged one-parameter subgroup is unique among canonical-field curves. -/
theorem existsUnique_oneParameterSubgroup [CompleteSpace E] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) :
    ∃! γ : ℝ →+ Additive G,
      IsMIntegralCurve (fun t => Additive.toMul (γ t)) (mulInvariantVectorField v) := by
  obtain ⟨γ, hγ⟩ := exists_oneParameterSubgroup v
  refine ⟨γ, hγ, ?_⟩
  intro δ hδ
  have heq : (fun t => Additive.toMul (δ t)) = (fun t => Additive.toMul (γ t)) :=
    invariantCurve_unique v hδ hγ (t₀ := 0) (by simp only [map_zero])
  exact AddMonoidHom.ext (fun t => congrFun heq t)

end RealLieGroup

end CloudB3W17Realify
