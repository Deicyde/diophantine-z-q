import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Scalar restriction for manifolds with the same underlying model

This file supplies partial analytic infrastructure for W17, not a proof of
uniformization or GAGA. In particular a complex analytic manifold with its
existing charts is a real analytic manifold. No charted space or topology is
replaced. The general statements compare models whose underlying partial
equivalences agree; this also covers product self-models used by Lie groups.

The proofs use Mathlib's ordinary `ContDiffWithinAt.restrict_scalars`, including
its analytic (`ω`) case, and the definitions of manifold regularity in charts.
-/

open Set
open scoped Manifold ContDiff

namespace CloudB3W17Realify

section ScalarRestriction

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]
variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜' E H}
  {I' : ModelWithCorners 𝕜 F H'} {J' : ModelWithCorners 𝕜' F H'}
variable {n : ℕ∞ω}

omit [NormedAlgebra 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E] in
/-- Extended charts do not change when only the scalar field of a model changes. -/
theorem extChartAt_eq (hIJ : I.toPartialEquiv = J.toPartialEquiv) (x : M) :
    extChartAt I x = extChartAt J x := by
  change (chartAt H x).toPartialEquiv.trans I.toPartialEquiv =
    (chartAt H x).toPartialEquiv.trans J.toPartialEquiv
  rw [hIJ]

/-- Restrict scalars in a manifold structure, retaining its topology and atlas. -/
theorem isManifold_of_sameModel (hIJ : I.toPartialEquiv = J.toPartialEquiv)
    [IsManifold J n M] : IsManifold I n M := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have h := J.contDiffOn_extendCoordChange (n := n)
    (IsManifold.subset_maximalAtlas (I := J) (n := n) he)
    (IsManifold.subset_maximalAtlas (I := J) (n := n) he')
  rw [J.extendCoordChange_source, J.image_eq] at h
  have hfun : (I : H → E) = (J : H → E) := congrArg (fun p : PartialEquiv H E => (p : H → E)) hIJ
  have hinv : (I.symm : E → H) = (J.symm : E → H) :=
    congrArg (fun p : PartialEquiv H E => (p.symm : E → H)) hIJ
  simpa only [ModelWithCorners.extendCoordChange, PartialEquiv.coe_trans,
    OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, ModelWithCorners.toPartialEquiv_coe_symm,
    hfun, hinv, Function.comp_assoc]
    using h.restrict_scalars 𝕜

/-- Scalar restriction of regularity within a set at a point. -/
theorem contMDiffWithinAt_of_sameModel (hIJ : I.toPartialEquiv = J.toPartialEquiv)
    (hI'J' : I'.toPartialEquiv = J'.toPartialEquiv) {f : M → N} {s : Set M} {x : M}
    (hf : ContMDiffWithinAt J J' n f s x) : ContMDiffWithinAt I I' n f s x := by
  rw [contMDiffWithinAt_iff] at hf ⊢
  refine ⟨hf.1, ?_⟩
  have hfun : (I : H → E) = (J : H → E) := congrArg (fun p : PartialEquiv H E => (p : H → E)) hIJ
  simpa only [extChartAt_eq hIJ, extChartAt_eq hI'J', hfun]
    using hf.2.restrict_scalars 𝕜

/-- Scalar restriction of regularity at a point. -/
theorem contMDiffAt_of_sameModel (hIJ : I.toPartialEquiv = J.toPartialEquiv)
    (hI'J' : I'.toPartialEquiv = J'.toPartialEquiv) {f : M → N} {x : M}
    (hf : ContMDiffAt J J' n f x) : ContMDiffAt I I' n f x :=
  contMDiffWithinAt_of_sameModel hIJ hI'J' hf

/-- Scalar restriction of regularity on a set. -/
theorem contMDiffOn_of_sameModel (hIJ : I.toPartialEquiv = J.toPartialEquiv)
    (hI'J' : I'.toPartialEquiv = J'.toPartialEquiv) {f : M → N} {s : Set M}
    (hf : ContMDiffOn J J' n f s) : ContMDiffOn I I' n f s :=
  fun x hx => contMDiffWithinAt_of_sameModel hIJ hI'J' (hf x hx)

/-- Scalar restriction of global regularity. -/
theorem contMDiff_of_sameModel (hIJ : I.toPartialEquiv = J.toPartialEquiv)
    (hI'J' : I'.toPartialEquiv = J'.toPartialEquiv) {f : M → N}
    (hf : ContMDiff J J' n f) : ContMDiff I I' n f :=
  fun x => contMDiffAt_of_sameModel hIJ hI'J' (hf x)

end ScalarRestriction

section SelfModels

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N] {n : ℕ∞ω}

/-- A manifold modelled on a normed space restricts scalars with no change of charts. -/
theorem isManifold_self [IsManifold 𝓘(𝕜', E) n M] : IsManifold 𝓘(𝕜, E) n M :=
  isManifold_of_sameModel (𝕜' := 𝕜') (J := 𝓘(𝕜', E)) rfl

/-- Scalar restriction of maps between self-model manifolds. -/
theorem contMDiff_self {f : M → N} (hf : ContMDiff 𝓘(𝕜', E) 𝓘(𝕜', F) n f) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n f :=
  contMDiff_of_sameModel (I := 𝓘(𝕜, E)) (I' := 𝓘(𝕜, F))
    (J := 𝓘(𝕜', E)) (J' := 𝓘(𝕜', F)) rfl rfl hf

/-- A Lie monoid restricts scalars, including its manifold structure. -/
theorem contMDiffMul_self {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Mul G]
    [ContMDiffMul 𝓘(𝕜', E) n G] : ContMDiffMul 𝓘(𝕜, E) n G := by
  let : IsManifold 𝓘(𝕜, E) n G := isManifold_self (𝕜' := 𝕜')
  refine ⟨?_⟩
  exact contMDiff_of_sameModel
    (I := (𝓘(𝕜, E)).prod 𝓘(𝕜, E)) (I' := 𝓘(𝕜, E))
    (J := (𝓘(𝕜', E)).prod 𝓘(𝕜', E)) (J' := 𝓘(𝕜', E))
    rfl rfl (contMDiff_mul 𝓘(𝕜', E) n (G := G))

/-- A Lie additive monoid restricts scalars, including its manifold structure. -/
theorem contMDiffAdd_self {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Add G]
    [ContMDiffAdd 𝓘(𝕜', E) n G] : ContMDiffAdd 𝓘(𝕜, E) n G := by
  let : IsManifold 𝓘(𝕜, E) n G := isManifold_self (𝕜' := 𝕜')
  refine ⟨?_⟩
  exact contMDiff_of_sameModel
    (I := (𝓘(𝕜, E)).prod 𝓘(𝕜, E)) (I' := 𝓘(𝕜, E))
    (J := (𝓘(𝕜', E)).prod 𝓘(𝕜', E)) (J' := 𝓘(𝕜', E))
    rfl rfl (contMDiff_add 𝓘(𝕜', E) n (G := G))

/-- A Lie group restricts scalars, retaining topology, multiplication and charts. -/
theorem lieGroup_self {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup 𝓘(𝕜', E) n G] : LieGroup 𝓘(𝕜, E) n G := by
  let : ContMDiffMul 𝓘(𝕜, E) n G := contMDiffMul_self (𝕜' := 𝕜')
  refine ⟨?_⟩
  exact contMDiff_self (contMDiff_inv (I := 𝓘(𝕜', E)) (n := n))

/-- An additive Lie group restricts scalars, retaining topology, addition and charts. -/
theorem lieAddGroup_self {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [AddGroup G]
    [LieAddGroup 𝓘(𝕜', E) n G] : LieAddGroup 𝓘(𝕜, E) n G := by
  let : ContMDiffAdd 𝓘(𝕜, E) n G := contMDiffAdd_self (𝕜' := 𝕜')
  refine ⟨?_⟩
  exact contMDiff_self (contMDiff_neg (I := 𝓘(𝕜', E)) (n := n))

end SelfModels

end CloudB3W17Realify
