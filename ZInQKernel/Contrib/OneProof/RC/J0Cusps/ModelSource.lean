import ZInQKernel.Contrib.OneProof.RC.X0Branch.Overlap

/-! The source shared by the specialization and Jacobian arguments. The
structure morphism is the one used by the chart model, definitionally.
Tex 1785–1787 and 2937–2939; on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory ModularCurve
open ZInQ.Contrib.CloudW07JacobiansCurves ZInQ.Contrib.CurvesG

namespace ZInQ.Manuscript.RC.J0Cusps

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

/-- The underlying scheme over ℚ of `X0Branch.model N`. -/
abbrev source (N : ℕ) [NeZero N] : Over (Spec (.of ℚ)) :=
  Over.mk (X0Model.overQ N)

/-- The actual normalization is smooth of relative dimension one. -/
theorem model_smooth_one (N : ℕ) [NeZero N] :
    SmoothOfRelativeDimension 1 (source N).hom := by
  change SmoothOfRelativeDimension 1 (X0Model.overQ N)
  have := X0Model.proper N
  exact CurveSplit.normalCurveSmoothQ_of_regularSmooth
    ZInQ.Contrib.OneProof.RegularSmoothPerfect.regularSmoothPerfect_proof
    (Over.mk (X0Model.overQ N)) (by change LocallyOfFiniteType (X0Model.overQ N); infer_instance)
    (X0Model.integral N) (NormalModel.isNormalScheme_Xn (modularFunctionField N))
    (NormalModel.topologicalKrullDim_Xn (modularFunctionField N))


end ZInQ.Manuscript.RC.J0Cusps
