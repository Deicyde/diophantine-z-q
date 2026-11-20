import ZInQKernel.Contrib.OneProof.RC.CMScope.Field
import ZInQKernel.Contrib.OneProof.RC.PreparedParam.Parametrization

open AlgebraicGeometry CategoryTheory WeierstrassCurve
  ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.CMScope

open Classical in
/-- The rational evaluation in tex 2917 only needs descent of the single
point being evaluated. This is the pointwise step in
`PreparedParam.value_of_cmFieldOfDefinition` (c). -/
theorem value_of_cmPoint {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [NeZero (newformLevel E)] {X : X0Model (newformLevel E)}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ}
    (hπ : AlgebraicParametrizationAtScale E X f Lat κ)
    {H : Type} [Field H] [Algebra ℚ H] (ι : H →ₐ[ℚ] ℂ)
    (x : FieldPoint X.overQ H) {τ : UpperHalfPlane} (hx : x.map ι = X.complexPoint τ) :
    ∃ y : (E.baseChange H).toAffine.Point,
      Affine.Point.map (W' := E.toAffine) ι y = phiAn E f Lat κ τ := by
  obtain ⟨π, hπQ, -, hcompat⟩ := hπ
  let u := (x.comp π hπQ).val
  refine ⟨projectiveValue u, ?_⟩
  calc
    _ = projectiveValue (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ u) :=
      projectiveValue_map ι u
    _ = projectiveValue ((x.map ι).comp π hπQ).val := by
      simp only [u, FieldPoint.comp, FieldPoint.map, Category.assoc]
    _ = _ := (congrArg (fun z : FieldPoint X.overQ ℂ =>
      projectiveValue (z.comp π hπQ).val) hx).trans (hcompat _)

end ZInQ.Manuscript.RC.CMScope
