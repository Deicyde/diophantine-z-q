import ZInQKernel.Contrib.OneProof.ComplexDifferentialOverlap
import ZInQKernel.Contrib.OneProof.EtaleCurveDifferentialSections
import ZInQKernel.Contrib.OneProof.SphereHolomorphicDifferential
import ZInQKernel.Contrib.OneProof.ComplexRegularValueDetects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Geometrically.Smooth

/-! Regular differential sections induce holomorphic covectors on the
native complex points of a smooth curve. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Manifold

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {X : Over (Spec (CommRingCat.of ℂ))}
  [SmoothOfRelativeDimension 1 X.hom]

private theorem localChart_coord_eval (p q : ComplexPoint X)
    (hq : q ∈ (localChart X 1 p).source) :
    let D := localEtaleCoordinates X 1 p
    localChart X 1 p q 0 = Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0)) q := by
  let D := localEtaleCoordinates X 1 p
  have h := localChart_apply_component_eq_evaluate X 1 p q hq 0
  refine h.trans ?_
  have e : D.neighborhood = D.ambientCoordinateOpen := D.neighborhood.ι_image_top.symm
  have ht : D.ambientCoordinateSection 0 =
      X.left.presheaf.map (eqToHom e.symm).op (D.coordinateAlgHom (MvPolynomial.X 0)) := by
    unfold LocalEtaleCoordinates.ambientCoordinateSection LocalEtaleCoordinates.coordinateRingHomOnOpen
    change ((D.neighborhood.topIso.inv ≫ (D.neighborhood.ι.appIso ⊤).inv)
      (D.coordinateAlgHom (MvPolynomial.X 0))) = _
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  rw [ht]
  exact (evaluate_eq e _ q).symm

private def coordCoefficient (ω : Γ(X.hom.relativeDifferentials, ⊤)) (p : ComplexPoint X) :
    Γ(X.left, (localEtaleCoordinates X 1 p).neighborhood) :=
  ((localEtaleCoordinates X 1 p).existsUnique_smul_sectionsD
    (X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω)).exists.choose

private theorem coordCoefficient_spec (ω : Γ(X.hom.relativeDifferentials, ⊤)) (p : ComplexPoint X) :
    let D := localEtaleCoordinates X 1 p
    coordCoefficient ω p • X.hom.sectionsD D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0)) =
      X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω :=
  ((localEtaleCoordinates X 1 p).existsUnique_smul_sectionsD
    (X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω)).exists.choose_spec

/-- A regular algebraic differential induces a pointwise complex covector. -/
def covectorOfSection (ω : Γ(X.hom.relativeDifferentials, ⊤)) (p : ComplexPoint X) :
    TangentSpace 𝓘(ℂ, Fin 1 → ℂ) p →L[ℂ] ℂ :=
  let D := localEtaleCoordinates X 1 p
  Point.evaluate D.neighborhood (coordCoefficient ω p) p •
    mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ)
      (Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))) p

/-- In any algebraic expression of the section as a coefficient times
a differential, the covector is given by differentiating that expression. -/
theorem covectorOfSection_eq_of_expression (ω : Γ(X.hom.relativeDifferentials, ⊤))
    {U : X.left.Opens} (a b : Γ(X.left, U))
    (hU : a • X.hom.sectionsD U b =
      X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω)
    (p : ComplexPoint X) (hp : p.underlying ∈ U) :
    covectorOfSection ω p =
      Point.evaluate U a p •
        mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate U b) p :=
  evaluate_differential_expressions_eq ω (coordCoefficient ω p) _ a b
    (coordCoefficient_spec ω p) hU p (localEtaleCoordinates X 1 p).mem hp

/-- On a complex curve homeomorphic to the sphere, the holomorphic covector
of every regular differential section vanishes at every complex point. -/
theorem covectorOfSection_eq_zero_of_complex_sphere (e : ComplexPoint X ≃ₜ OnePoint ℂ)
    (ω : Γ(X.hom.relativeDifferentials, ⊤)) :
    ∀ p : ComplexPoint X, covectorOfSection ω p = 0 := by
  apply covector_eq_zero_of_holomorphic_local_coordinates_on_complex_sphere e
  intro p
  let D := localEtaleCoordinates X 1 p
  let L := localChart X 1 p
  let c := Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))
  let a : ℂ → ℂ := fun w => Point.evaluate D.neighborhood (coordCoefficient ω p) (L.symm fun _ => w)
  have hsrc : p ∈ L.source := mem_localChart_source X 1 p
  have hvec (y : ComplexPoint X) (hy : y ∈ L.source) :
      (fun _ : Fin 1 => c y) = L y := by
    funext i
    fin_cases i
    exact (localChart_coord_eval p y hy).symm
  refine ⟨L.source, c, a, L.open_source, hsrc, ?_, ?_, ?_⟩
  · intro y hy
    exact (mdifferentiableAt_evaluate _ y
      (mem_coordinateNeighborhood_of_mem_localChart_source X 1 p y hy) _).mdifferentiableWithinAt
  · have hAn := analyticAt_localChart_symm_evaluate X 1 p (L.map_source hsrc)
      D.neighborhood (coordCoefficient ω p) (by rw [L.left_inv hsrc]; exact D.mem)
    have hlin : AnalyticAt ℂ (fun w : ℂ => fun _ : Fin 1 => w) (c p) :=
      AnalyticAt.pi fun _ => analyticAt_id
    have hAn' : AnalyticAt ℂ
        (fun w => Point.evaluate D.neighborhood (coordCoefficient ω p) (L.symm w))
        (fun _ : Fin 1 => c p) := by
      rw [hvec p hsrc]
      exact hAn
    exact hAn'.comp hlin
  · intro y hy
    have hyU := mem_coordinateNeighborhood_of_mem_localChart_source X 1 p y hy
    rw [covectorOfSection_eq_of_expression ω _ _ (coordCoefficient_spec ω p) y hyU]
    have ha : a (c y) = Point.evaluate D.neighborhood (coordCoefficient ω p) y := by
      dsimp only [a]
      rw [hvec y hy, L.left_inv hy]
    rw [ha]
    ext v
    let z : ℂ := mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ) c y v
    change Point.evaluate D.neighborhood (coordCoefficient ω p) y * z =
      z * Point.evaluate D.neighborhood (coordCoefficient ω p) y
    exact mul_comm _ _

open scoped Topology in
/-- At its centre the chosen chart coordinate has a tangent direction in
which its derivative is one. -/
private theorem exists_coord_tangent (p : ComplexPoint X) :
    let D := localEtaleCoordinates X 1 p
    ∃ v : TangentSpace 𝓘(ℂ, Fin 1 → ℂ) p,
      mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ)
        (Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))) p v = (1 : ℂ) := by
  let I := 𝓘(ℂ, Fin 1 → ℂ)
  let c := extChartAt I p
  let D := localEtaleCoordinates X 1 p
  let t := Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))
  let l : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  let u : TangentSpace I (c p) := fun _ => 1
  let v : TangentSpace I p := mfderivWithin I I c.symm (Set.range I) (c p) u
  have hs : p ∈ c.source := mem_extChartAt_source p
  have he := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
    (I := I) (x := p) (y := p) hs
  have he' : mfderiv I I c p v = u := congrArg (fun L => L u) he
  have hd := l.hasFDerivAt.hasMFDerivAt.comp p
    (mdifferentiableAt_extChartAt (I := I) (x := p) (mem_chart_source _ _)).hasMFDerivAt
  have hEq : t =ᶠ[𝓝 p] l ∘ c := by
    filter_upwards [(localChart X 1 p).open_source.mem_nhds (mem_localChart_source X 1 p)] with q hq
    exact (localChart_coord_eval p q hq).symm
  have hd' := (hd.congr_of_eventuallyEq hEq).mfderiv
  refine ⟨v, ?_⟩
  change mfderiv I 𝓘(ℂ, ℂ) t p v = (1 : ℂ)
  rw [hd']
  change l (mfderiv I I c p v) = (1 : ℂ)
  rw [he']
  rfl

private theorem coordCoefficient_evaluate_eq_zero (ω : Γ(X.hom.relativeDifferentials, ⊤))
    (p : ComplexPoint X) (h : covectorOfSection ω p = 0) :
    Point.evaluate (localEtaleCoordinates X 1 p).neighborhood (coordCoefficient ω p) p = 0 := by
  let D := localEtaleCoordinates X 1 p
  obtain ⟨v, hv⟩ := exists_coord_tangent p
  have hval := congrArg (fun L => L v) h
  change (Point.evaluate D.neighborhood (coordCoefficient ω p) p •
    mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ)
      (Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))) p) v = 0 at hval
  rw [smul_apply, hv] at hval
  change Point.evaluate D.neighborhood (coordCoefficient ω p) p * 1 = 0 at hval
  exact (mul_one _).symm.trans hval

private theorem coefficient_eq_zero_of_covector_eq_zero
    (ω : Γ(X.hom.relativeDifferentials, ⊤)) (h : ∀ p, covectorOfSection ω p = 0)
    {x : X.left} (D : LocalEtaleCoordinates X 1 x) (a : Γ(X.left, D.neighborhood))
    (ha : a • X.hom.sectionsD D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0)) =
      X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω) : a = 0 := by
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : IsReduced X.left := Smooth.isReduced_of_field X.hom
  apply regularSection_eq_zero_of_evaluate_eq_zero D.isAffine a
  intro p hp
  let E := localEtaleCoordinates X 1 p
  obtain ⟨s, hs, hpW⟩ := D.isAffine.exists_basicOpen_le
    (⟨p.underlying, hp, E.mem⟩ : ↥(D.neighborhood ⊓ E.neighborhood)) hp
  let W := X.left.basicOpen s
  let B := D.restrictBasicOpen s hpW
  have hD : W ≤ D.neighborhood := X.left.basicOpen_le s
  have hE : W ≤ E.neighborhood := hs.trans inf_le_right
  let aW := X.left.presheaf.map (homOfLE hD).op a
  let bW := X.left.presheaf.map (homOfLE hE).op (coordCoefficient ω p)
  let dW := X.left.presheaf.map (homOfLE hE).op (E.coordinateAlgHom (MvPolynomial.X 0))
  let η := X.hom.sectionsD W (B.coordinateAlgHom (MvPolynomial.X 0))
  have hAW : aW • η = X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω :=
    restrict_differential_expression ω hD _ _ ha
  have hBW : bW • X.hom.sectionsD W dW =
      X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω :=
    restrict_differential_expression ω hE _ _ (coordCoefficient_spec ω p)
  obtain ⟨b, hb, -⟩ := B.existsUnique_smul_sectionsD (X.hom.sectionsD W dW)
  let b' : Γ(X.left, W) := b
  have hη : (bW * b') • η = X.hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω := by
    rw [mul_smul, show b' • η = _ from hb, hBW]
  have hab : aW = bW * b' :=
    (B.existsUnique_smul_sectionsD _).unique hAW hη
  have hb0 : Point.evaluate W bW p = 0 :=
    (Point.evaluate_res hE (coordCoefficient ω p) p hpW).symm.trans
      (coordCoefficient_evaluate_eq_zero ω p (h p))
  have hval (r : Γ(X.left, W)) :
      Point.evaluate W r p = (Point.evaluationHom W ⟨p, hpW⟩) r :=
    (Point.evaluationHom_apply W ⟨p, hpW⟩ r).symm
  rw [Point.evaluate_res hD a p hpW]
  change Point.evaluate W aW p = 0
  rw [hab, hval, map_mul, ← hval bW, hb0, zero_mul]

/-- If the covector of a regular differential vanishes at every complex
point, then the original section is zero. -/
theorem relativeDifferentialSection_eq_zero_of_covector_eq_zero
    (ω : Γ(X.hom.relativeDifferentials, ⊤)) (h : ∀ p, covectorOfSection ω p = 0) :
    ω = 0 := by
  let T := X.hom.relativeDifferentials
  let D (x : X.left) := AlgebraicGeometry.localEtaleCoordinates X 1 x
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨T.presheaf, T.isSheaf⟩
    (fun x => (D x).neighborhood) ⊤ (fun _ => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.mpr ⟨x, (D x).mem⟩) ω 0 fun x => ?_
  obtain ⟨a, ha, -⟩ := (D x).existsUnique_smul_sectionsD
    (T.presheaf.map (homOfLE le_top).op ω)
  have hz : a = 0 := coefficient_eq_zero_of_covector_eq_zero ω h (D x) a ha
  rw [map_zero, ← ha, hz, zero_smul]

/-- Every global regular differential on a smooth complex curve whose
complex points form a topological sphere is zero. -/
theorem relativeDifferentialSection_eq_zero_of_complex_sphere
    (e : ComplexPoint X ≃ₜ OnePoint ℂ) (ω : Γ(X.hom.relativeDifferentials, ⊤)) :
    ω = 0 :=
  relativeDifferentialSection_eq_zero_of_covector_eq_zero ω
    (covectorOfSection_eq_zero_of_complex_sphere e ω)

end AlgebraicGeometry.ComplexPoint

#print axioms AlgebraicGeometry.ComplexPoint.covectorOfSection_eq_zero_of_complex_sphere

#print axioms AlgebraicGeometry.ComplexPoint.relativeDifferentialSection_eq_zero_of_complex_sphere
