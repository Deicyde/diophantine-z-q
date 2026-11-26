import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Core
import ZInQKernel.Contrib.OneProof.ComplexPointDerivation
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspAssignment
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.SlashActions

/-! Vanishing of the native value of a global differential at every cusp.

For `σ ∈ SL(2, ℤ)` the translated arc `z ↦ P (σ • z)` tends to an algebraic cusp
point `p₀` as `Im z → ∞`. Write `ω = a · d t` on an étale chart around `p₀`. For
large `Im z`, `(f_ω ∣[2] σ) z = a (P (σ • z)) · G' z` with `G z = t (P (σ • z))`.
Since `G` is holomorphic on a half plane and tends to `t p₀`, the Cauchy estimate
on unit circles gives `G' → 0`, and `a (P (σ • z)) → a p₀`. No periodicity,
`q`-expansion or removable singularity argument is needed.

The holomorphy of the analytic point map (`ArcPointHolomorphic`, statement K4 of
the route design) is an explicit hypothesis of every geometric statement below. -/

noncomputable section

open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter Metric Matrix.SpecialLinearGroup
open scoped Manifold Topology MatrixGroups ModularForm

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open J0Cusps

section Analytic

theorem extChart_eq (τ : ℍ) : (extChartAt 𝓘(ℂ) τ : ℍ → ℂ) = ((↑) : ℍ → ℂ) := by
  funext z; rfl

theorem mfderiv_coe_apply (τ : ℍ) (v : ℂ) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) ((↑) : ℍ → ℂ) τ v = v := by
  have h := mfderiv_extChartAt_self (I := 𝓘(ℂ)) (x := τ)
  rw [extChart_eq] at h
  rw [h]; rfl

theorem mfderiv_one_eq_deriv {φ : ℍ → ℂ} {τ : ℍ} (hφ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ τ) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) φ τ (1 : ℂ) = deriv (φ ∘ ofComplex) τ := by
  have hd : DifferentiableAt ℂ (φ ∘ ofComplex) τ := mdifferentiableAt_iff.mp hφ
  have he : φ = (φ ∘ ofComplex) ∘ ((↑) : ℍ → ℂ) := by
    funext z; simp [ofComplex_apply]
  have h1 := mfderiv_comp_apply (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (I'' := 𝓘(ℂ)) (x := τ)
    hd.mdifferentiableAt (mdifferentiable_coe τ) (1 : ℂ)
  rw [← he, mfderiv_coe_apply, mfderiv_eq_fderiv] at h1
  rw [h1]
  rfl

theorem deriv_tendsto_zero_atImInfty {G : ℂ → ℂ} {c : ℂ} {A : ℝ}
    (hd : ∀ w : ℂ, A < w.im → DifferentiableAt ℂ G w)
    (hG : Tendsto (fun τ : ℍ => G τ) atImInfty (𝓝 c)) :
    Tendsto (fun τ : ℍ => deriv G τ) atImInfty (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h2 : (0 : ℝ) < ε / 2 := half_pos hε
  obtain ⟨B, hB⟩ := (atImInfty_mem _).mp ((Metric.tendsto_nhds.mp hG) (ε / 2) h2)
  refine (atImInfty_mem _).mpr ?_
  refine ⟨max (B + 1) (max (A + 2) 2), fun τ hτ => ?_⟩
  have hτB : B + 1 ≤ τ.im := le_trans (le_max_left _ _) hτ
  have hτA : A + 2 ≤ τ.im := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hτ
  have hτ1 : 2 ≤ τ.im := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hτ
  have him : ∀ z ∈ closedBall (τ : ℂ) 1, τ.im - 1 ≤ z.im := by
    intro z hz
    have h1 : |z.im - (τ : ℂ).im| ≤ ‖z - τ‖ := by
      simpa using Complex.abs_im_le_norm (z - τ)
    rw [mem_closedBall, dist_eq_norm] at hz
    have := (abs_le.mp (h1.trans hz)).1
    simp only [coe_im] at this
    linarith
  have hdiff : DiffContOnCl ℂ (fun z => G z - c) (ball (τ : ℂ) 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ one_ne_zero]
    intro z hz
    exact ((hd z (by linarith [him z hz])).sub_const c).differentiableWithinAt
  have hbound : ∀ z ∈ sphere (τ : ℂ) 1, ‖G z - c‖ ≤ ε / 2 := by
    intro z hz
    have hzim : τ.im - 1 ≤ z.im := him z (sphere_subset_closedBall hz)
    have hpos : 0 < z.im := by linarith
    have := hB ⟨z, hpos⟩ (by change B ≤ z.im; linarith)
    have h' : dist (G z) c < ε / 2 := this
    rw [dist_eq_norm] at h'
    exact h'.le
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hdiff hbound
  rw [deriv_sub_const] at hest
  change dist (deriv G τ) 0 < ε
  rw [dist_zero_right]
  linarith

theorem det_mapGL_SL (σ : SL(2, ℤ)) : (mapGL ℝ σ).val.det = 1 :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) σ).prop

theorem slash_eq_mul_deriv {f φ α : ℍ → ℂ} (σ : SL(2, ℤ)) {A : ℝ}
    (hdiff : ∀ τ : ℍ, A ≤ τ.im → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ (σ • τ))
    (hexpr : ∀ τ : ℍ, A ≤ τ.im → f (σ • τ) = α (σ • τ) * deriv (φ ∘ ofComplex) (σ • τ : ℍ)) :
    let G : ℂ → ℂ := fun z => (φ ∘ ofComplex) ((mapGL ℝ σ • ofComplex z : ℍ) : ℂ)
    (∀ w : ℂ, max A 1 < w.im → DifferentiableAt ℂ G w) ∧
    (∀ τ : ℍ, G τ = φ (σ • τ)) ∧
    (∀ τ : ℍ, A ≤ τ.im → (f ∣[(2:ℤ)] σ) τ = α (σ • τ) * deriv G τ) := by
  intro G
  have hdet : 0 < (mapGL ℝ σ).val.det := by rw [det_mapGL_SL]; exact one_pos
  have hval (τ : ℍ) : G τ = φ (σ • τ) := by
    simp only [G, Function.comp_apply, ofComplex_apply]
    rfl
  have hder (τ : ℍ) (hτ : A ≤ τ.im) :
      HasDerivAt G (deriv (φ ∘ ofComplex) (σ • τ : ℍ) * ((mapGL ℝ σ).val.det / denom (mapGL ℝ σ) τ ^ 2)) τ := by
    have hm := (hasStrictDerivAt_smul hdet τ).hasDerivAt
    have hφd : DifferentiableAt ℂ (φ ∘ ofComplex) ((σ • τ : ℍ) : ℂ) :=
      mdifferentiableAt_iff.mp (hdiff τ hτ)
    have hpt : (((mapGL ℝ σ) • ofComplex (τ : ℂ) : ℍ) : ℂ) = ((σ • τ : ℍ) : ℂ) := by
      rw [ofComplex_apply]; rfl
    rw [← hpt] at hφd ⊢
    exact hφd.hasDerivAt.comp (τ : ℂ) hm
  refine ⟨fun w hw => ?_, hval, fun τ hτ => ?_⟩
  · have hw0 : 0 < w.im := lt_of_lt_of_le one_pos ((le_max_right A 1).trans hw.le)
    have := (hder ⟨w, hw0⟩ ((le_max_left A 1).trans hw.le)).differentiableAt
    exact this
  · rw [ModularForm.SL_slash_apply, (hder τ hτ).deriv, hexpr τ hτ, det_mapGL_SL]
    change α (σ • τ) * deriv (φ ∘ ofComplex) (σ • τ : ℍ) * denom (mapGL ℝ σ) τ ^ (-(2:ℤ)) = _
    rw [zpow_neg, zpow_two, ← sq]
    push_cast
    ring

end Analytic

variable (N : ℕ) [NeZero N]

/-- Statement K4: the analytic point map `τ ↦ P τ` is holomorphic. -/
def ArcPointHolomorphic : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N)

/-- The expression rule of K5, derived from K4: if `ω = a · d b` on `U` and `P τ ∈ U`, then
`f_ω(τ) = a (P τ) · (d/dτ) b (P τ)`. -/
theorem nativeValue_eq_of_expression_of_arcPoint (hK4 : ArcPointHolomorphic N)
    (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) {U : (curveC N).left.Opens}
    (a b : Γ((curveC N).left, U))
    (hU : a • (curveC N).hom.sectionsD U b =
      (curveC N).hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω)
    (τ : ℍ) (hτ : (arcPoint N τ).underlying ∈ U) :
    nativeValue N ω τ = Point.evaluate U a (arcPoint N τ) *
      deriv ((fun τ' => Point.evaluate U b (arcPoint N τ')) ∘ ofComplex) τ := by
  have hb : MDifferentiableAt 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) (Point.evaluate U b) (arcPoint N τ) :=
    ComplexPoint.mdifferentiableAt_evaluate U (arcPoint N τ) hτ b
  have hc : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ' => Point.evaluate U b (arcPoint N τ')) τ :=
    hb.comp τ (hK4 τ)
  rw [← mfderiv_one_eq_deriv hc]
  unfold nativeValue
  rw [ComplexPoint.covectorOfSection_eq_of_expression ω a b hU (arcPoint N τ) hτ]
  let z : ℂ := mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) (Point.evaluate U b) (arcPoint N τ)
    (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N) τ (1 : ℂ))
  change Point.evaluate U a (arcPoint N τ) * z = _
  congr 1
  exact (mfderiv_comp_apply (x := τ) hb (hK4 τ) (1 : ℂ)).symm

/-- Statement K7, assuming K4: for every global differential `ω` and every `σ ∈ SL(2, ℤ)`,
the weight-two slash of the native value by `σ` vanishes at `i∞`. -/
theorem nativeValue_slash_isZeroAtImInfty (hK4 : ArcPointHolomorphic N)
    (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) (σ : SL(2, ℤ)) :
    IsZeroAtImInfty ((nativeValue N ω) ∣[(2 : ℤ)] σ) := by
  let p₀ : ComplexPoint (curveC N) :=
    complexLift (extendPoint (algebraicCusp N (orbitOfSL N σ)))
  have hlim : Tendsto (fun z : ℍ => arcPoint N (σ • z)) atImInfty (𝓝 p₀) :=
    algebraicCusp_limit N σ
  let D := ComplexPoint.localEtaleCoordinates (curveC N) 1 p₀
  let U := D.neighborhood
  have hp₀ : p₀.underlying ∈ U := D.mem
  obtain ⟨a, ha, -⟩ := D.existsUnique_smul_sectionsD
    ((curveC N).hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω)
  let t := D.coordinateAlgHom (MvPolynomial.X 0)
  have hev (s : Γ((curveC N).left, U)) : ContinuousAt (Point.evaluate U s) p₀ :=
    (ComplexPoint.mdifferentiableAt_evaluate (d := 1) U p₀ hp₀ s).continuousAt
  have hmem : ∀ᶠ z in atImInfty, (arcPoint N (σ • z)).underlying ∈ U :=
    hlim ((Point.isOpen_overOpen U).mem_nhds hp₀)
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hmem
  let φ : ℍ → ℂ := fun τ' => Point.evaluate U t (arcPoint N τ')
  let α : ℍ → ℂ := fun τ' => Point.evaluate U a (arcPoint N τ')
  have hdiff : ∀ τ : ℍ, A ≤ τ.im → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ (σ • τ) := fun τ hτ =>
    (ComplexPoint.mdifferentiableAt_evaluate U _ (hA τ hτ) t).comp _ (hK4 _)
  have hexpr : ∀ τ : ℍ, A ≤ τ.im →
      nativeValue N ω (σ • τ) = α (σ • τ) * deriv (φ ∘ ofComplex) (σ • τ : ℍ) :=
    fun τ hτ => nativeValue_eq_of_expression_of_arcPoint N hK4 ω a t ha (σ • τ) (hA τ hτ)
  obtain ⟨hGd, hGv, hGs⟩ := slash_eq_mul_deriv σ hdiff hexpr
  have hφ : Tendsto (fun τ : ℍ => φ (σ • τ)) atImInfty (𝓝 (Point.evaluate U t p₀)) :=
    (hev t).tendsto.comp hlim
  have hα : Tendsto (fun τ : ℍ => α (σ • τ)) atImInfty (𝓝 (Point.evaluate U a p₀)) :=
    (hev a).tendsto.comp hlim
  have hG := deriv_tendsto_zero_atImInfty hGd (hφ.congr fun τ => (hGv τ).symm)
  have hprod := hα.mul hG
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [(atImInfty_mem _).mpr ⟨A, fun τ hτ => hτ⟩] with τ hτ
  exact (hGs τ hτ).symm

/-- The zero-at-cusps condition of a weight-two cusp form on `Γ₀(N)`, assuming K4. -/
theorem nativeValue_isZeroAt_cusps (hK4 : ArcPointHolomorphic N)
    (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) {c : OnePoint ℝ}
    (hc : IsCusp c (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    c.IsZeroAt (nativeValue N ω) 2 := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun σ _ =>
    nativeValue_slash_isZeroAtImInfty N hK4 ω σ

end ZInQ.Manuscript.RC.CuspFormDifferentials
