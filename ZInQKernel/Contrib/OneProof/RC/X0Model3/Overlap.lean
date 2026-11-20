import ZInQKernel.Contrib.OneProof.RC.X0Model3.AffineEval
import ZInQKernel.Contrib.OneProof.RC.X0Model3.Unramified
import ZInQKernel.Contrib.OneProof.RC.X0Model2.LocalSheets
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! Comparison of the valuative branches on the smooth curve.
Tex 2915–2919; on the spot, provenance (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve
open ZInQ.Contrib.CloudW07JacobiansCurves ZInQ.Contrib.CurvesG
open scoped Topology MatrixGroups

namespace ZInQ.Manuscript.RC.X0Model3

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

private theorem smooth_one (N : ℕ) [NeZero N] :
    SmoothOfRelativeDimension 1 (X0Model.overQ N) := by
  have := X0Model.proper N
  exact CurveSplit.normalCurveSmoothQ_of_regularSmooth
    ZInQ.Contrib.OneProof.RegularSmoothPerfect.regularSmoothPerfect_proof
    (Over.mk (X0Model.overQ N)) (by change LocallyOfFiniteType (X0Model.overQ N); infer_instance)
    (X0Model.integral N) (NormalModel.isNormalScheme_Xn (modularFunctionField N))
    (NormalModel.topologicalKrullDim_Xn (modularFunctionField N))

private theorem exists_etale_affine (N : ℕ) [NeZero N] (p : X0Model.curve N) :
    ∃ (U : (X0Model.curve N).Opens) (_ : IsAffineOpen U), p ∈ U ∧
      ∃ e : MvPolynomial (Fin 1) ℚ →+* Γ(X0Model.curve N, U), e.Etale := by
  let := smooth_one N
  obtain ⟨W, _, U, hU, hp, _, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := X0Model.overQ N) p
  have hW : W = ⊤ := le_antisymm le_top fun y _ => by
    rw [Subsingleton.elim y (X0Model.overQ N p)]
    exact ‹U ≤ (X0Model.overQ N) ⁻¹ᵁ W› hp
  subst W
  have h' := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (.of ℚ)).symm.commRingCatIsoToRingEquiv h
  obtain ⟨e, _, he⟩ := h'.exists_etale_mvPolynomial
  exact ⟨U, hU, hp, e, he⟩

private theorem etaleCoordinate_agree {A : Type} [CommRing A]
    (e : MvPolynomial (Fin 1) ℚ →+* A) {f g : A →+* ℂ}
    (h : f (e (MvPolynomial.X 0)) = g (e (MvPolynomial.X 0))) :
    f.comp e = g.comp e := by
  apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
  intro i
  rwa [Subsingleton.elim i 0]

private theorem j_not_eventually_constant (τ : UpperHalfPlane) :
    ¬ ∀ᶠ z in 𝓝 (τ : ℂ),
      X0Model.analyticJ (UpperHalfPlane.ofComplex z) = X0Model.analyticJ τ := by
  obtain ⟨U, hU, hl⟩ := X0Model2.exists_nhds_local_j_orbit τ
  have hτ : τ ∈ U := mem_of_mem_nhds hU
  have him : ((↑) : UpperHalfPlane → ℂ) '' U ∈ 𝓝 (τ : ℂ) := by
    rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq]
    exact image_mem_map hU
  intro he
  have hh : ∀ᶠ z in 𝓝 (τ : ℂ), z = (τ : ℂ) := by
    filter_upwards [he, him] with z hz hmem
    obtain ⟨w, hw, rfl⟩ := hmem
    rw [UpperHalfPlane.ofComplex_apply] at hz
    obtain ⟨s, hs, hw'⟩ := hl τ hτ w hw hz.symm
    rw [← hw', hs]
  have hfalse : ∀ᶠ z in 𝓝[≠] (τ : ℂ), False := by
    filter_upwards [hh.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hn
    exact hn hz
  obtain ⟨_, hf⟩ := hfalse.exists
  exact hf

private theorem holomorphic_match {f g : ℂ → ℂ} {a b : ℂ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g b) (hfg : f a = g b)
    (hnf : ¬ ∀ᶠ z in 𝓝 a, f z = f a) (hng : ¬ ∀ᶠ z in 𝓝 b, g z = g b)
    {V : Set ℂ} (hV : V ∈ 𝓝 b) :
    ∀ᶠ z in 𝓝[≠] a, ∃ w ∈ V, w ≠ b ∧ f z = g w := by
  have hopen := hg.eventually_constant_or_nhds_le_map_nhds.resolve_left hng
  have him : g '' V ∈ 𝓝 (f a) := by
    rw [hfg]
    exact hopen (image_mem_map hV)
  have hne := (hf.eventually_eq_or_eventually_ne analyticAt_const).resolve_left hnf
  filter_upwards [hne, (hf.continuousAt.eventually_mem him).filter_mono nhdsWithin_le_nhds] with
    z hza hmem
  obtain ⟨w, hw, hw'⟩ := hmem
  refine ⟨w, hw, ?_, hw'.symm⟩
  intro hab
  apply hza
  rw [← hw', hab, ← hfg]

/-- Two chart lifts at the same point have punctured local overlap in the
normalization. The second parameter can be taken in any prescribed neighborhood. -/
theorem eventually_overlap_of_complexPoint_eq (N : ℕ) [NeZero N] (τ σ : UpperHalfPlane)
    (h : X0Model.complexPoint N τ = X0Model.complexPoint N σ)
    (V : Set ℂ) (hV : V ∈ 𝓝 (σ : ℂ)) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), ∃ w ∈ V, w ≠ (σ : ℂ) ∧
      X0Model.complexPoint N (UpperHalfPlane.ofComplex z) =
        X0Model.complexPoint N (UpperHalfPlane.ofComplex w) := by
  obtain ⟨U, hU, hτ, e, he⟩ := exists_etale_affine N
    (X0Model.complexPoint N τ (default : Spec (.of ℂ)))
  have hσ : X0Model.complexPoint N σ (default : Spec (.of ℂ)) ∈ U := h ▸ hτ
  let R := MvPolynomial (Fin 1) ℚ
  let A := Γ(X0Model.curve N, U)
  let : Algebra R A := e.toAlgebra
  let : Algebra.Etale R A := RingHom.etale_algebraMap.mp he
  let f := chartEval N U τ hτ
  let g := chartEval N U σ hσ
  have hctr : f τ = g σ := by
    simp only [f, g, chartEval_center]
    exact affineEval_congr hτ hσ h
  obtain ⟨S, hS, T, hT, heq⟩ := eventually_eq_of_unramified (R := R) f g (τ : ℂ) (σ : ℂ)
    (fun r => (chartEval_analyticAt N U τ hτ r).continuousAt)
    (fun r => (chartEval_analyticAt N U σ hσ r).continuousAt) hctr
  let t := e (MvPolynomial.X 0)
  have hl (x y : ℂ) (hx : x ∈ S) (hy : y ∈ T)
      (hxU : X0Model.complexPoint N (UpperHalfPlane.ofComplex x) (default : Spec (.of ℂ)) ∈ U)
      (hyU : X0Model.complexPoint N (UpperHalfPlane.ofComplex y) (default : Spec (.of ℂ)) ∈ U)
      (hxy : f x t = g y t) :
      X0Model.complexPoint N (UpperHalfPlane.ofComplex x) =
        X0Model.complexPoint N (UpperHalfPlane.ofComplex y) := by
    apply affineEval_injective hU hxU hyU
    have hfg := heq x hx y hy (etaleCoordinate_agree e hxy)
    change chartEval N U τ hτ x = chartEval N U σ hσ y at hfg
    rwa [chartEval_at_mem N U τ hτ x hxU, chartEval_at_mem N U σ hσ y hyU] at hfg
  have hnf : ¬ ∀ᶠ x in 𝓝 (τ : ℂ), f x t = f τ t := by
    intro hh
    apply j_not_eventually_constant τ
    filter_upwards [hh, hS, eventually_chart_mem N τ U hτ] with x hx hxS hxU
    have hσU : X0Model.complexPoint N (UpperHalfPlane.ofComplex (σ : ℂ))
        (default : Spec (.of ℂ)) ∈ U := by simpa only [UpperHalfPlane.ofComplex_apply] using hσ
    have hpt := hl x (σ : ℂ) hxS (mem_of_mem_nhds hT) hxU hσU
      (hx.trans (congrArg (fun k : A →+* ℂ => k t) hctr))
    rw [UpperHalfPlane.ofComplex_apply, ← h] at hpt
    exact X0Model2.analyticJ_eq_of_complexPoint_eq N _ _ hpt
  have hng : ¬ ∀ᶠ y in 𝓝 (σ : ℂ), g y t = g σ t := by
    intro hh
    apply j_not_eventually_constant σ
    filter_upwards [hh, hT, eventually_chart_mem N σ U hσ] with y hy hyT hyU
    have hτU : X0Model.complexPoint N (UpperHalfPlane.ofComplex (τ : ℂ))
        (default : Spec (.of ℂ)) ∈ U := by simpa only [UpperHalfPlane.ofComplex_apply] using hτ
    have hpt := hl (τ : ℂ) y (mem_of_mem_nhds hS) hyT hτU hyU
      ((congrArg (fun k : A →+* ℂ => k t) hctr).trans hy.symm)
    rw [UpperHalfPlane.ofComplex_apply, h] at hpt
    exact X0Model2.analyticJ_eq_of_complexPoint_eq N _ _ hpt.symm
  have hmatch := holomorphic_match (chartEval_analyticAt N U τ hτ t)
    (chartEval_analyticAt N U σ hσ t) (congrArg (fun k : A →+* ℂ => k t) hctr) hnf hng
    (inter_mem (inter_mem hV hT) (eventually_chart_mem N σ U hσ))
  filter_upwards [hmatch, mem_nhdsWithin_of_mem_nhds hS,
    (eventually_chart_mem N τ U hτ).filter_mono nhdsWithin_le_nhds] with z hz hzS hzU
  obtain ⟨w, ⟨⟨hwV, hwT⟩, hwU⟩, hwσ, hzw⟩ := hz
  exact ⟨w, hwV, hwσ, hl z w hzS hwT hzU hwU hzw⟩


end ZInQ.Manuscript.RC.X0Model3
