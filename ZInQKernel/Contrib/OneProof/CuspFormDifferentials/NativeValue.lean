import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.ArcAnalytic

/-! The native value `f_ω(τ)` of a global relative differential: its expression in
algebraic coordinates, its holomorphy on the upper half-plane, and its linearity in `ω`. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane
open scoped Topology Manifold

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

variable (N : ℕ) [NeZero N]

/-- The derivative of a holomorphic function on `ℍ`, in the direction `1`, is the
complex derivative of its extension through `ofComplex`. -/
theorem mfderiv_apply_one_eq_deriv {h : ℍ → ℂ} {τ : ℍ}
    (hd : DifferentiableAt ℂ (h ∘ ofComplex) (τ : ℂ)) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) h τ (1 : ℂ) = deriv (h ∘ ofComplex) (τ : ℂ) := by
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, H = h ∘ ofComplex := ⟨_, rfl⟩
  rw [← hH] at hd ⊢
  have hh : h = H ∘ UpperHalfPlane.coe := by
    funext σ
    simp [hH, ofComplex_apply]
  have hc : UpperHalfPlane.coe = (extChartAt 𝓘(ℂ) τ : ℍ → ℂ) := rfl
  have h1 : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) UpperHalfPlane.coe τ (ContinuousLinearMap.id ℂ ℂ) := by
    have := (mdifferentiable_coe τ).hasMFDerivAt
    rw [hc, mfderiv_extChartAt_self] at this
    rw [hc]
    exact this
  have h2 : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) H (τ : ℂ) (fderiv ℂ H (τ : ℂ)) :=
    hd.hasFDerivAt.hasMFDerivAt
  have h3 := h2.comp τ h1
  rw [hh, h3.mfderiv]
  change fderiv ℂ H (τ : ℂ) (1 : ℂ) = deriv H (τ : ℂ)
  exact fderiv_apply_one_eq_deriv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- K5, expression rule: if `ω` restricts on `U` to `a • d b` and `P τ ∈ U`, then
`f_ω(τ)` is the value of `a` at `P τ` times the derivative of `b` along `P`. -/
theorem nativeValue_eq_of_expression (ω : Γ((curveC N).hom.relativeDifferentials, ⊤))
    {U : (curveC N).left.Opens} (a b : Γ((curveC N).left, U))
    (hU : a • (curveC N).hom.sectionsD U b =
      (curveC N).hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω)
    (τ : ℍ) (hτ : (arcPoint N τ).underlying ∈ U) :
    nativeValue N ω τ = Point.evaluate U a (arcPoint N τ) *
      deriv (fun z : ℂ => Point.evaluate U b (arcPoint N (ofComplex z))) (τ : ℂ) := by
  unfold nativeValue
  have hcomp := (ComplexPoint.mdifferentiableAt_evaluate U _ hτ b).hasMFDerivAt.comp τ
    (mdifferentiable_arcPoint N τ).hasMFDerivAt
  have key := congrArg (fun L => L (1 : ℂ)) hcomp.mfderiv
  rw [ComplexPoint.covectorOfSection_eq_of_expression ω a b hU _ hτ]
  let w : ℂ := mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) (Point.evaluate U b) (arcPoint N τ)
    (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N) τ (1 : ℂ))
  change Point.evaluate U a (arcPoint N τ) * w = _
  have key' : w = mfderiv 𝓘(ℂ) 𝓘(ℂ) (Point.evaluate U b ∘ arcPoint N) τ (1 : ℂ) := key.symm
  rw [key']
  rw [mfderiv_apply_one_eq_deriv (h := Point.evaluate U b ∘ arcPoint N) (τ := τ)
    (arcPoint_evaluate N U b τ hτ).2.differentiableAt]
  rfl

/-- K5, holomorphy: the native value of every global differential is holomorphic on `ℍ`. -/
theorem mdifferentiable_nativeValue (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (nativeValue N ω) := by
  intro τ₀
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  let p := arcPoint N τ₀
  let D := localEtaleCoordinates (curveC N) 1 p.underlying
  obtain ⟨a, ha, -⟩ := D.existsUnique_smul_sectionsD
    ((curveC N).hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω)
  let b := D.coordinateAlgHom (MvPolynomial.X 0)
  have hp : p.underlying ∈ D.neighborhood := D.mem
  obtain ⟨hmem, hA⟩ := arcPoint_evaluate N D.neighborhood a τ₀ hp
  have hB := (arcPoint_evaluate N D.neighborhood b τ₀ hp).2
  have hq := hA.mul hB.deriv
  apply hq.differentiableAt.congr_of_eventuallyEq
  filter_upwards [eventually_ofComplex hmem, eventuallyEq_coe_comp_ofComplex τ₀.im_pos]
    with z hz hcz
  have hcz' : ((ofComplex z : ℍ) : ℂ) = z := hcz
  simp only [Function.comp_apply]
  rw [nativeValue_eq_of_expression N ω a b ha _ hz, hcz']
  rfl

/-! ### Linearity in the differential -/

/-- The structure map on global sections, `ℂ → Γ(𝒪, ⊤)`. -/
abbrev structureMap : ℂ →+* Γ((curveC N).left, ⊤) :=
  ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (curveC N).hom.appTop).hom

/-- The complex structure on global differentials, by restriction of scalars along the
structure map. -/
abbrev differentialsModule : Module ℂ Γ((curveC N).hom.relativeDifferentials, ⊤) :=
  Module.compHom _ (structureMap N)

private theorem evaluate_add {U : (curveC N).left.Opens} (a a' : Γ((curveC N).left, U))
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ U) :
    Point.evaluate U (a + a') q = Point.evaluate U a q + Point.evaluate U a' q := by
  rw [← Point.evaluationHom_apply U ⟨q, hq⟩, ← Point.evaluationHom_apply U ⟨q, hq⟩,
    ← Point.evaluationHom_apply U ⟨q, hq⟩, map_add]

private theorem evaluate_mul {U : (curveC N).left.Opens} (a a' : Γ((curveC N).left, U))
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ U) :
    Point.evaluate U (a * a') q = Point.evaluate U a q * Point.evaluate U a' q := by
  rw [← Point.evaluationHom_apply U ⟨q, hq⟩, ← Point.evaluationHom_apply U ⟨q, hq⟩,
    ← Point.evaluationHom_apply U ⟨q, hq⟩, map_mul]

private theorem evaluate_structureMap {U : (curveC N).left.Opens} (c : ℂ)
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ U) :
    Point.evaluate U ((curveC N).left.presheaf.map (homOfLE le_top).op (structureMap N c)) q =
      c := by
  have hs : (curveC N).left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (structureMap N c) =
      (curveC N).hom.specStructureMap U c := by
    rfl
  rw [hs]
  let : Algebra ℂ Γ((curveC N).left, U) := ((curveC N).hom.specStructureMap U).hom.toAlgebra
  exact (ComplexPoint.sectionEvaluationAlgHom_apply U q hq _).symm.trans
    ((ComplexPoint.sectionEvaluationAlgHom U q hq).commutes c)

/-- The coordinate expression of a global differential at the point of a parameter. -/
private theorem exists_expression (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) (τ : ℍ) :
    let D := localEtaleCoordinates (curveC N) 1 (arcPoint N τ).underlying
    ∃ a : Γ((curveC N).left, D.neighborhood),
      a • (curveC N).hom.sectionsD D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0)) =
        (curveC N).hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω :=
  (localEtaleCoordinates (curveC N) 1 (arcPoint N τ).underlying).existsUnique_smul_sectionsD
    _ |>.exists

/-- K5, additivity in the differential. -/
theorem nativeValue_add (ω ω' : Γ((curveC N).hom.relativeDifferentials, ⊤)) :
    nativeValue N (ω + ω') = nativeValue N ω + nativeValue N ω' := by
  funext τ
  let D := localEtaleCoordinates (curveC N) 1 (arcPoint N τ).underlying
  let b := D.coordinateAlgHom (MvPolynomial.X 0)
  have hp : (arcPoint N τ).underlying ∈ D.neighborhood := D.mem
  obtain ⟨a, ha⟩ := exists_expression N ω τ
  obtain ⟨a', ha'⟩ := exists_expression N ω' τ
  have hsum : (a + a') • (curveC N).hom.sectionsD D.neighborhood b =
      (curveC N).hom.relativeDifferentials.presheaf.map (homOfLE le_top).op (ω + ω') := by
    rw [add_smul, ha, ha', map_add]
  rw [Pi.add_apply, nativeValue_eq_of_expression N _ _ _ hsum τ hp,
    nativeValue_eq_of_expression N _ _ _ ha τ hp, nativeValue_eq_of_expression N _ _ _ ha' τ hp,
    evaluate_add N a a' _ hp, add_mul]

/-- K5, compatibility with scalars: multiplication by the constant `c` multiplies the
native value by `c`. -/
theorem nativeValue_smul (c : ℂ) (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) :
    nativeValue N (structureMap N c • ω) = c • nativeValue N ω := by
  funext τ
  let D := localEtaleCoordinates (curveC N) 1 (arcPoint N τ).underlying
  let b := D.coordinateAlgHom (MvPolynomial.X 0)
  have hp : (arcPoint N τ).underlying ∈ D.neighborhood := D.mem
  obtain ⟨a, ha⟩ := exists_expression N ω τ
  let cU := (curveC N).left.presheaf.map (homOfLE (le_top : D.neighborhood ≤ ⊤)).op
    (structureMap N c)
  have hsmul : (cU * a) • (curveC N).hom.sectionsD D.neighborhood b =
      (curveC N).hom.relativeDifferentials.presheaf.map (homOfLE le_top).op
        (structureMap N c • ω) := by
    rw [mul_smul, ha, Scheme.Modules.map_smul]
  rw [Pi.smul_apply, nativeValue_eq_of_expression N _ _ _ hsmul τ hp,
    nativeValue_eq_of_expression N _ _ _ ha τ hp, evaluate_mul N cU a _ hp,
    evaluate_structureMap N c _ hp, smul_eq_mul, mul_assoc]

/-- K5, linearity: `ω ↦ f_ω` is `ℂ`-linear for the complex structure on global
differentials given by the structure map. -/
def nativeValueLinear :
    letI := differentialsModule N
    Γ((curveC N).hom.relativeDifferentials, ⊤) →ₗ[ℂ] (ℍ → ℂ) :=
  letI := differentialsModule N
  { toFun := nativeValue N
    map_add' := nativeValue_add N
    map_smul' := fun c ω => nativeValue_smul N c ω }

theorem nativeValueLinear_apply (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) :
    nativeValueLinear N ω = nativeValue N ω := rfl

end ZInQ.Manuscript.RC.CuspFormDifferentials
