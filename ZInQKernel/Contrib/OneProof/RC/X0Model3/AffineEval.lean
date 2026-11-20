import ZInQKernel.Contrib.OneProof.RC.X0Model.Section
import ZInQKernel.Contrib.OneProof.RC.X0Model2.Projection

/-! Regular functions on affine neighborhoods of the valuative chart.
Tex 2915–2919; on the spot, provenance (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve ShimuraPointDict
open ZInQ.Contrib.CloudW07JacobiansCurves
open scoped Topology

namespace ZInQ.Manuscript.RC.X0Model3

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

/-- An affine section evaluation of a complex scheme point. -/
def affineEval {X : Scheme.{0}} (p : Spec (.of ℂ) ⟶ X) (U : X.Opens)
    (hp : p (default : Spec (.of ℂ)) ∈ U) : Γ(X, U) →+* ℂ :=
  (X0Model.sectionMap p U (fun x _ => by
    rwa [Subsingleton.elim x (default : Spec (.of ℂ))])).hom

private theorem affineEval_factor {X : Scheme.{0}} (p : Spec (.of ℂ) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (hp : p (default : Spec (.of ℂ)) ∈ U) :
    Spec.map (CommRingCat.ofHom (affineEval p U hp)) ≫ hU.fromSpec = p := by
  have hu : ⊤ ≤ p ⁻¹ᵁ U := fun x _ => by rwa [Subsingleton.elim x (default : Spec (.of ℂ))]
  change Spec.map (p.appLE U ⊤ hu ≫ (Scheme.ΓSpecIso (.of ℂ)).hom) ≫ hU.fromSpec = p
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec p _
    (isAffineOpen_top _) hu, IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom,
    Iso.hom_inv_id_assoc]

theorem affineEval_congr {X : Scheme.{0}} {U : X.Opens}
    {p q : Spec (.of ℂ) ⟶ X} (hp : p (default : Spec (.of ℂ)) ∈ U)
    (hq : q (default : Spec (.of ℂ)) ∈ U) (h : p = q) :
    affineEval p U hp = affineEval q U hq := by
  subst q
  rfl

/-- On an affine open the values of its regular functions determine the point. -/
theorem affineEval_injective {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {p q : Spec (.of ℂ) ⟶ X} (hp : p (default : Spec (.of ℂ)) ∈ U)
    (hq : q (default : Spec (.of ℂ)) ∈ U)
    (h : affineEval p U hp = affineEval q U hq) : p = q := by
  rw [← affineEval_factor p hU hp, ← affineEval_factor q hU hq, h]

private theorem mem_basicOpen_iff_eval_ne_zero {X : Scheme.{0}} {U : X.Opens}
    (hU : IsAffineOpen U) (p : Spec (.of ℂ) ⟶ X) (hp : p (default : Spec (.of ℂ)) ∈ U)
    (r : Γ(X, U)) : p (default : Spec (.of ℂ)) ∈ X.basicOpen r ↔ affineEval p U hp r ≠ 0 := by
  conv_lhs =>
    rw [← affineEval_factor p hU hp, Scheme.Hom.comp_apply]
  change _ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r ↔ _
  rw [hU.fromSpec_preimage_basicOpen, Spec.map_apply]
  change affineEval p U hp r ∉ (default : Spec (.of ℂ)).asIdeal ↔ _
  rw [show (default : Spec (.of ℂ)) = (⊥ : PrimeSpectrum ℂ) from Subsingleton.elim _ _, PrimeSpectrum.asIdeal_bot,
    Ideal.mem_bot]

/-- The inverse image of the finite affine j-line. -/
abbrev finiteChart (N : ℕ) [NeZero N] : (X0Model.curve N).Opens :=
  X0Model2.jProjection N ⁻¹ᵁ NormalModel.chart 0

private theorem finiteChart_affine (N : ℕ) [NeZero N] : IsAffineOpen (finiteChart N) :=
  (NormalModel.isAffineOpen_chart 0).preimage (X0Model2.jProjection N)

private theorem chart_mem_finiteChart (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    X0Model.complexPoint N τ (default : Spec (.of ℂ)) ∈ finiteChart N := by
  rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, X0Model2.complexPoint_jProjection]
  change _ ∈ ((NormalModel.chart 0 : NormalModel.P.Opens) : Set NormalModel.P)
  rw [← (NormalModel.isAffineOpen_chart 0).range_fromSpec]
  unfold X0Model2.jLinePoint
  rw [Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

/-- The lift stays in any Zariski open containing its center when the parameter
varies in a sufficiently small complex neighborhood. -/
theorem eventually_chart_mem (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    (U : (X0Model.curve N).Opens) (h : X0Model.complexPoint N τ (default : Spec (.of ℂ)) ∈ U) :
    ∀ᶠ z in 𝓝 (τ : ℂ), X0Model.complexPoint N (UpperHalfPlane.ofComplex z)
      (default : Spec (.of ℂ)) ∈ U := by
  let V := finiteChart N
  have hV := finiteChart_affine N
  have hmem := chart_mem_finiteChart N τ
  let : Nonempty V := ⟨⟨_, hmem⟩⟩
  obtain ⟨r, hrU, hr⟩ := hV.exists_basicOpen_le (⟨_, h⟩ : U) hmem
  obtain ⟨g, _, _, hg⟩ := X0Model.sectionMeromorphicContinuation N V r
  have hgτ := hg τ hmem
  have hg₀ : g τ ≠ 0 := by
    rw [← hgτ.2]
    exact (mem_basicOpen_iff_eval_ne_zero hV _ hmem r).mp hr
  filter_upwards [hgτ.1.continuousAt.eventually (eventually_ne_nhds hg₀),
    UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz hzH
  let σ : UpperHalfPlane := ⟨z, hzH⟩
  rw [show UpperHalfPlane.ofComplex z = σ from UpperHalfPlane.ofComplex_apply σ]
  apply hrU
  apply (mem_basicOpen_iff_eval_ne_zero hV _ (chart_mem_finiteChart N σ) r).mpr
  rwa [show affineEval (X0Model.complexPoint N σ) V (chart_mem_finiteChart N σ) r =
    g z from (hg σ (chart_mem_finiteChart N σ)).2]

/-- A family of section evaluations based at a chart point. The extension outside
the preimage of the open has no effect on its germ at the chosen parameter. -/
def chartEval (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens) (τ : UpperHalfPlane)
    (h : X0Model.complexPoint N τ (default : Spec (.of ℂ)) ∈ U) (z : ℂ) :
    Γ(X0Model.curve N, U) →+* ℂ := by
  classical
  exact if hz : X0Model.complexPoint N (UpperHalfPlane.ofComplex z) (default : Spec (.of ℂ)) ∈ U
    then affineEval (X0Model.complexPoint N (UpperHalfPlane.ofComplex z)) U hz
    else affineEval (X0Model.complexPoint N τ) U h

@[simp] theorem chartEval_center (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens)
    (τ : UpperHalfPlane) (h : X0Model.complexPoint N τ (default : Spec (.of ℂ)) ∈ U) :
    chartEval N U τ h τ = affineEval (X0Model.complexPoint N τ) U h := by
  simp [chartEval, UpperHalfPlane.ofComplex_apply, h]

theorem chartEval_at_mem (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens)
    (τ : UpperHalfPlane) (h : X0Model.complexPoint N τ (default : Spec (.of ℂ)) ∈ U)
    (z : ℂ) (hz : X0Model.complexPoint N (UpperHalfPlane.ofComplex z)
      (default : Spec (.of ℂ)) ∈ U) :
    chartEval N U τ h z = affineEval (X0Model.complexPoint N (UpperHalfPlane.ofComplex z)) U hz := by
  rw [chartEval, dite_eq_left hz]

private theorem chartEval_local (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens)
    (τ : UpperHalfPlane) (h : X0Model.complexPoint N τ (default : Spec (.of ℂ)) ∈ U)
    (r : Γ(X0Model.curve N, U)) :
    let : Nonempty U := ⟨⟨_, h⟩⟩
    AnalyticAt ℂ (fun z => chartEval N U τ h z r) (τ : ℂ) ∧
      ((fun z => chartEval N U τ h z r) : PuncturedGerm (τ : ℂ)) =
        X0Model.meromorphicIncl (τ : ℂ) (X0Model.fieldGerm N τ
          (X0Model.functionField N ((X0Model.curve N).germToFunctionField U r))) := by
  let : Nonempty U := ⟨⟨_, h⟩⟩
  obtain ⟨g, _, hgg, hg⟩ := X0Model.sectionMeromorphicContinuation N U r
  have he : (fun z => chartEval N U τ h z r) =ᶠ[𝓝 (τ : ℂ)] g := by
    filter_upwards [eventually_chart_mem N τ U h,
      UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz hzH
    rw [chartEval_at_mem N U τ h z hz]
    simpa only [affineEval, UpperHalfPlane.ofComplex_apply_of_im_pos hzH] using
      (hg (UpperHalfPlane.ofComplex z) hz).2
  exact ⟨(hg τ h).1.congr he.symm, (Germ.coe_eq.mpr (he.filter_mono nhdsWithin_le_nhds)).trans
    (hgg τ)⟩

/-- Regular sections pulled back to the complex chart are holomorphic locally. -/
theorem chartEval_analyticAt (N : ℕ) [NeZero N] (U : (X0Model.curve N).Opens)
    (τ : UpperHalfPlane) (h : X0Model.complexPoint N τ (default : Spec (.of ℂ)) ∈ U)
    (r : Γ(X0Model.curve N, U)) :
    AnalyticAt ℂ (fun z => chartEval N U τ h z r) (τ : ℂ) :=
  (chartEval_local N U τ h r).1

/-- Regular section evaluations on the inverse image of the finite j-line. -/
def finitePointEval (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    Γ(X0Model.curve N, finiteChart N) →+* ℂ :=
  affineEval (X0Model.complexPoint N τ) (finiteChart N) (chart_mem_finiteChart N τ)

theorem finitePointEval_eq (N : ℕ) [NeZero N] (τ σ : UpperHalfPlane)
    (h : X0Model.complexPoint N τ = X0Model.complexPoint N σ) :
    finitePointEval N τ = finitePointEval N σ :=
  affineEval_congr (U := finiteChart N) (chart_mem_finiteChart N τ) (chart_mem_finiteChart N σ) h

/-- The second generator is a ratio of two fixed sections on the finite chart.
Their evaluations represent the analytic second coordinate near each parameter,
with a denominator that is nonzero on a sufficiently small punctured neighborhood. -/
theorem exists_analyticJN_ratio (N : ℕ) [NeZero N] :
    ∃ a b : Γ(X0Model.curve N, finiteChart N), ∀ τ : UpperHalfPlane,
      ∀ᶠ z in 𝓝[≠] (τ : ℂ),
        finitePointEval N (UpperHalfPlane.ofComplex z) a =
          X0Model.analyticJN N (UpperHalfPlane.ofComplex z) *
            finitePointEval N (UpperHalfPlane.ofComplex z) b ∧
        finitePointEval N (UpperHalfPlane.ofComplex z) b ≠ 0 := by
  let X := X0Model.curve N
  let U := finiteChart N
  have hU := finiteChart_affine N
  let : Nonempty U := ⟨⟨_, chart_mem_finiteChart N default⟩⟩
  let : IsIntegral X := X0Model.integral N
  let : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  let jN : modularFunctionField N := ⟨jqN N, jqN_mem N⟩
  obtain ⟨a, b, hb, hratio⟩ := IsFractionRing.div_surjective Γ(X, U) ((X0Model.functionField N).symm jN)
  change X.germToFunctionField U a / X.germToFunctionField U b = _ at hratio
  have hb' : X.germToFunctionField U b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hmul := (div_eq_iff hb').mp hratio
  refine ⟨a, b, fun τ => ?_⟩
  have hmem := chart_mem_finiteChart N τ
  obtain ⟨_, ha⟩ := chartEval_local N U τ hmem a
  obtain ⟨hbA, hbG⟩ := chartEval_local N U τ hmem b
  have hag : ((fun z => chartEval N U τ hmem z a) : PuncturedGerm (τ : ℂ)) =
      ((fun z => X0Model.analyticJN N (UpperHalfPlane.ofComplex z) *
        chartEval N U τ hmem z b) : PuncturedGerm (τ : ℂ)) := by
    rw [ha, hmul, map_mul, RingEquiv.apply_symm_apply, map_mul, map_mul]
    rw [X0Model.fieldGerm_jN, ← hbG]
    rfl
  have hne := hbA.eventually_eq_zero_or_eventually_ne_zero.resolve_left (fun hz => by
    have he := (Germ.coe_eq.mpr (hz.filter_mono nhdsWithin_le_nhds)).symm.trans hbG
    exact hb' (by
      apply (X0Model.functionField N).injective
      apply (X0Model.fieldGerm N τ).injective
      apply (X0Model.meromorphicIncl (τ : ℂ)).injective
      have he' : _ = (0 : PuncturedGerm (τ : ℂ)) := he.symm
      simpa only [map_zero] using he'))
  filter_upwards [Germ.coe_eq.mp hag, hne] with z hz hzb
  have hh : chartEval N U τ hmem z = finitePointEval N (UpperHalfPlane.ofComplex z) :=
    chartEval_at_mem N U τ hmem z (chart_mem_finiteChart N (UpperHalfPlane.ofComplex z))
  change chartEval N U τ hmem z a = _ * chartEval N U τ hmem z b at hz
  rw [hh] at hz hzb
  exact ⟨hz, hzb⟩


end ZInQ.Manuscript.RC.X0Model3
