import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.RegularityCriterion
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Valuation
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.CuspVanishing
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Inverse
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.RouteBReduction

/-! K11 at cusps: the statement `K11Cusp` of `Regularity`, proved without hypotheses.

Let `p` be the limit of `P (σ • τ)` as `Im τ → ∞`, i.e. the cusp `σ(∞)`, and let
`x = p.underlying`, a closed point of `curveC N` whose local ring is a discrete valuation ring.
The argument stays on the complexified curve and uses the analytic local parameter
`q = exp (2πiτ/N)` at the cusp.

* Since `σ T^N σ⁻¹ ∈ Γ₀(N)`, the evaluation `τ ↦ h (P (σ • τ))` of a regular function `h` near
  `x` is `N`-periodic, holomorphic and bounded high in the upper half-plane, so it is a
  holomorphic function `cuspQ h` of `q` near `0` (removable singularities), with value `h(x)`
  at `0`.
* **Valuation scaling** (`exists_cusp_ramification_index`): there is `m ≥ 1` with
  `ord_{q=0} (cuspQ h) = m · v_x(h)`. Finiteness comes from the injectivity of the analytic
  chart at `p` and the non-constancy of the arc.
* **Chain rule** (`mfderiv_evaluate_eq_smul`, `deriv_cuspEval_eq_mul`): if `d r = r' · dt` for
  the chart coordinate `t`, then `(r ∘ P ∘ σ)′ = (r' ∘ P ∘ σ) · (t ∘ P ∘ σ)′`. Applied to a
  uniformizer, it bounds the `q`-order of `q · d(cuspQ t)/dq` by `m`.
* **Main inequality** (`cusp_addVal_le`): write the coefficient of `(A / B) · dj` with respect to
  `dt` as `α / β` with `α`, `β` in the local ring. High in the upper half-plane
  `(F ∣[2] σ) · (β ∘ P ∘ σ) = (α ∘ P ∘ σ) · (t ∘ P ∘ σ)′` (identity theorem, from the germ
  identity `F = (A / B) · j′` near one parameter). In `q`, the vanishing of `F ∣[2] σ` at `i∞`
  forces `m · v(α) + m - m · v(β) > 0`, hence `v(β) ≤ v(α)`, so the coefficient is regular at
  `x`.
* **Representation** (`representsDiffOn_of_ref`): `a · dt` with `a` regular at `x` represents
  `(A / B) · dj` on a neighbourhood of `x`; representatives of the same element agree wherever
  both are defined (`RepOn.restrict_eq`), since every nonempty open meets the arc.

The closedness of the cusp centre on the model over `ℚ` is not used. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Set UpperHalfPlane Topology
open scoped Manifold MatrixGroups ModularForm

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open J0Cusps

attribute [local instance] overSpecAlgebra

variable (N : ℕ) [NeZero N]

section CuspArc

variable (σ : SL(2, ℤ))

omit [NeZero N] in
theorem conj_T_pow_mem_Gamma0 :
    σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_T_zpow, Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

theorem arcPoint_smul_vadd_period (τ : ℍ) :
    arcPoint N (σ • ((N : ℝ) +ᵥ τ)) = arcPoint N (σ • τ) := by
  have h1 : ((N : ℝ) +ᵥ τ) = ModularGroup.T ^ (N : ℤ) • τ := by
    rw [UpperHalfPlane.modular_T_zpow_smul]; simp
  rw [h1, ← mul_smul, show σ * ModularGroup.T ^ (N : ℤ) =
    (σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹) * σ by group, mul_smul]
  exact arcPoint_smul_surj N _ (conj_T_pow_mem_Gamma0 N σ) _


/-- A regular function evaluated along the translated arc `z ↦ P (σ • z)`. -/
def cuspEval (U : (curveC N).left.Opens) (r : Γ((curveC N).left, U)) : ℂ → ℂ :=
  (fun τ : ℍ => Point.evaluate U r (arcPoint N (σ • τ))) ∘ ofComplex

theorem cuspEval_coe (U : (curveC N).left.Opens) (r : Γ((curveC N).left, U)) (τ : ℍ) :
    cuspEval N σ U r τ = Point.evaluate U r (arcPoint N (σ • τ)) := by
  simp [cuspEval]

theorem cuspEval_periodic (U : (curveC N).left.Opens) (r : Γ((curveC N).left, U)) :
    Function.Periodic (cuspEval N σ U r) (N : ℝ) :=
  periodic_comp_ofComplex fun τ => congrArg _ (arcPoint_smul_vadd_period N σ τ)

theorem cuspEval_eq_comp (U : (curveC N).left.Opens) (r : Γ((curveC N).left, U)) :
    cuspEval N σ U r = (fun z : ℂ => Point.evaluate U r (arcPoint N (ofComplex z))) ∘
      (fun z : ℂ => ((Matrix.SpecialLinearGroup.mapGL ℝ σ • ofComplex z : ℍ) : ℂ)) := by
  funext z
  simp only [cuspEval, Function.comp_apply, ofComplex_apply]
  rfl

theorem det_mapGL_pos : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ σ).val.det := by
  rw [det_mapGL_SL]; exact one_pos

theorem cuspEval_analyticAt (U : (curveC N).left.Opens) (r : Γ((curveC N).left, U)) (τ : ℍ)
    (hx : (arcPoint N (σ • τ)).underlying ∈ U) : AnalyticAt ℂ (cuspEval N σ U r) τ := by
  rw [cuspEval_eq_comp]
  have h1 := (arcPoint_evaluate N U r (σ • τ) hx).2
  have h2 := UpperHalfPlane.analyticAt_smul (det_mapGL_pos σ) τ
  refine AnalyticAt.comp ?_ h2
  simp only [ofComplex_apply]
  exact h1

/-- The function of the local parameter `q = exp (2πiz/N)` at the cusp. -/
def cuspQ (U : (curveC N).left.Opens) (r : Γ((curveC N).left, U)) : ℂ → ℂ :=
  Function.Periodic.cuspFunction (N : ℝ) (cuspEval N σ U r)

theorem period_pos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

theorem cuspQ_eq_of_ne_zero (U : (curveC N).left.Opens) (r : Γ((curveC N).left, U)) {q : ℂ}
    (hq : q ≠ 0) : cuspQ N σ U r q = cuspEval N σ U r (Function.Periodic.invQParam (N : ℝ) q) :=
  Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq

theorem cuspEval_eq_cuspQ (U : (curveC N).left.Opens) (r : Γ((curveC N).left, U)) (z : ℂ) :
    cuspEval N σ U r z = cuspQ N σ U r (Function.Periodic.qParam (N : ℝ) z) :=
  (Function.Periodic.eq_cuspFunction (period_pos N).ne' (cuspEval_periodic N σ U r) z).symm

variable {N σ} {p : ComplexPoint (curveC N)} (hp : IsCuspLimit N σ p)
include hp

theorem cusp_eventually_mem {U : (curveC N).left.Opens} (hx : p.underlying ∈ U) :
    ∀ᶠ z in comap Complex.im atTop, 0 < z.im ∧ (arcPoint N (σ • ofComplex z)).underlying ∈ U := by
  have h := hp ((Point.isOpen_overOpen U).mem_nhds hx)
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp h
  filter_upwards [preimage_mem_comap (Ici_mem_atTop (max A 1))] with z hz
  have hz' : max A 1 ≤ z.im := hz
  have hpos : 0 < z.im := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hz')
  refine ⟨hpos, ?_⟩
  rw [ofComplex_apply_of_im_pos hpos]
  exact hA _ ((le_max_left _ _).trans hz')

theorem cuspEval_eventually_differentiableAt {U : (curveC N).left.Opens} (hx : p.underlying ∈ U)
    (r : Γ((curveC N).left, U)) :
    ∀ᶠ z in comap Complex.im atTop, DifferentiableAt ℂ (cuspEval N σ U r) z := by
  filter_upwards [cusp_eventually_mem hp hx] with z ⟨hpos, hz⟩
  have := cuspEval_analyticAt N σ U r ⟨z, hpos⟩ (by rw [← ofComplex_apply_of_im_pos hpos]; exact hz)
  exact this.differentiableAt

theorem cuspEval_tendsto {U : (curveC N).left.Opens} (hx : p.underlying ∈ U)
    (r : Γ((curveC N).left, U)) :
    Tendsto (cuspEval N σ U r) (comap Complex.im atTop) (𝓝 (Point.evaluate U r p)) := by
  have hc : ContinuousAt (Point.evaluate U r) p :=
    (ComplexPoint.mdifferentiableAt_evaluate (d := 1) U p hx r).continuousAt
  exact (hc.tendsto.comp hp).comp tendsto_comap_im_ofComplex


theorem cuspQ_analyticAt {U : (curveC N).left.Opens} (hx : p.underlying ∈ U)
    (r : Γ((curveC N).left, U)) : AnalyticAt ℂ (cuspQ N σ U r) 0 := by
  have hper := cuspEval_periodic N σ U r
  have hhol := cuspEval_eventually_differentiableAt hp hx r
  have hbd : BoundedAtFilter (comap Complex.im atTop) (cuspEval N σ U r) :=
    (cuspEval_tendsto hp hx r).isBigO_one ℝ
  have h0 := Function.Periodic.differentiableAt_cuspFunction_zero (period_pos N) hper hhol hbd
  have hne := Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero
    (period_pos N) hper hhol
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  rw [eventually_nhdsWithin_iff] at hne
  filter_upwards [hne] with q hq
  by_cases h : q = 0
  · subst h; exact h0
  · exact hq h

theorem cuspQ_zero {U : (curveC N).left.Opens} (hx : p.underlying ∈ U)
    (r : Γ((curveC N).left, U)) : cuspQ N σ U r 0 = Point.evaluate U r p := by
  have hper := cuspEval_periodic N σ U r
  have hhol := cuspEval_eventually_differentiableAt hp hx r
  have hbd : BoundedAtFilter (comap Complex.im atTop) (cuspEval N σ U r) :=
    (cuspEval_tendsto hp hx r).isBigO_one ℝ
  have := Function.Periodic.tendsto_at_I_inf (period_pos N) hper hhol hbd
  have hne : (comap Complex.im atTop).NeBot := atTop_neBot.comap_of_surj Complex.im_surjective
  exact tendsto_nhds_unique this (cuspEval_tendsto hp hx r)


/-- Eventually near `q = 0` (punctured), the parameter `invQParam q` lies high in the upper
half-plane and its point lies in `U`. -/
theorem eventually_invQParam_mem {U : (curveC N).left.Opens} (hx : p.underlying ∈ U) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ), 0 < (Function.Periodic.invQParam (N : ℝ) q).im ∧
      (arcPoint N (σ • ofComplex (Function.Periodic.invQParam (N : ℝ) q))).underlying ∈ U :=
  (Function.Periodic.invQParam_tendsto (period_pos N)).eventually (cusp_eventually_mem hp hx)

end CuspArc


/-! ### Evaluation at a complex point -/

section PointEval

theorem complexPoint_underlying_mem_closedPoints (q : ComplexPoint (curveC N)) :
    q.underlying ∈ closedPoints (curveC N).left := by
  have : LocallyOfFiniteType (curveC N).hom := by
    have := SmoothOfRelativeDimension.smooth 1 (curveC N).hom
    infer_instance
  have hw : q.left ≫ (curveC N).hom = 𝟙 _ := by simpa using Over.w q
  exact (pointEquivClosedPoint (curveC N).hom ⟨q.left, hw⟩).2

theorem evaluate_mul' {U : (curveC N).left.Opens} (a b : Γ((curveC N).left, U))
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ U) :
    Point.evaluate U (a * b) q = Point.evaluate U a q * Point.evaluate U b q := by
  rw [← Point.evaluationHom_apply U ⟨q, hq⟩, ← Point.evaluationHom_apply U ⟨q, hq⟩,
    ← Point.evaluationHom_apply U ⟨q, hq⟩, map_mul]

theorem evaluate_pow' {U : (curveC N).left.Opens} (a : Γ((curveC N).left, U)) (k : ℕ)
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ U) :
    Point.evaluate U (a ^ k) q = Point.evaluate U a q ^ k := by
  rw [← Point.evaluationHom_apply U ⟨q, hq⟩, ← Point.evaluationHom_apply U ⟨q, hq⟩, map_pow]

theorem evaluate_sub' {U : (curveC N).left.Opens} (a b : Γ((curveC N).left, U))
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ U) :
    Point.evaluate U (a - b) q = Point.evaluate U a q - Point.evaluate U b q := by
  rw [← Point.evaluationHom_apply U ⟨q, hq⟩, ← Point.evaluationHom_apply U ⟨q, hq⟩,
    ← Point.evaluationHom_apply U ⟨q, hq⟩, map_sub]

theorem evaluate_zero' {U : (curveC N).left.Opens}
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ U) :
    Point.evaluate U (0 : Γ((curveC N).left, U)) q = 0 := by
  rw [← Point.evaluationHom_apply U ⟨q, hq⟩, map_zero]

theorem evaluate_ne_zero_of_isUnit' (U : (curveC N).left.Opens) (s : Γ((curveC N).left, U))
    (q : ComplexPoint (curveC N)) (hx : q.underlying ∈ U)
    (hs : IsUnit ((curveC N).left.presheaf.germ U _ hx s)) :
    Point.evaluate U s q ≠ 0 := by
  rw [Point.evaluate, dite_eq_left hx]
  exact (hs.map q.stalkHom.hom).ne_zero

theorem evaluate_eq_zero_of_not_isUnit' (U : (curveC N).left.Opens) (s : Γ((curveC N).left, U))
    (q : ComplexPoint (curveC N)) (hx : q.underlying ∈ U)
    (hs : ¬ IsUnit ((curveC N).left.presheaf.germ U _ hx s)) :
    Point.evaluate U s q = 0 := by
  rw [Point.evaluate, dite_eq_left hx]
  by_contra h
  exact hs (isUnit_of_map_unit q.stalkHom.hom _ (isUnit_iff_ne_zero.mpr h))

theorem chart_coord_eval' (p q : ComplexPoint (curveC N))
    (hq : q ∈ (ComplexPoint.localChart (curveC N) 1 p).source) :
    ComplexPoint.localChart (curveC N) 1 p q 0 =
      Point.evaluate (ComplexPoint.localEtaleCoordinates (curveC N) 1 p).neighborhood
        ((ComplexPoint.localEtaleCoordinates (curveC N) 1 p).coordinateAlgHom
          (MvPolynomial.X 0)) q := by
  let D := ComplexPoint.localEtaleCoordinates (curveC N) 1 p
  have h := ComplexPoint.localChart_apply_component_eq_evaluate (curveC N) 1 p q hq 0
  refine h.trans ?_
  have e : D.neighborhood = D.ambientCoordinateOpen := D.neighborhood.ι_image_top.symm
  have ht : D.ambientCoordinateSection 0 =
      (curveC N).left.presheaf.map (eqToHom e.symm).op
        (D.coordinateAlgHom (MvPolynomial.X 0)) := by
    unfold LocalEtaleCoordinates.ambientCoordinateSection
      LocalEtaleCoordinates.coordinateRingHomOnOpen
    change ((D.neighborhood.topIso.inv ≫ (D.neighborhood.ι.appIso ⊤).inv)
      (D.coordinateAlgHom (MvPolynomial.X 0))) = _
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  rw [ht]
  exact (ComplexPoint.evaluate_eq e _ q).symm

end PointEval

/-! ### The valuation at the cusp, through the parameter `q` -/

section CuspValuationQ

variable {N} {σ : SL(2, ℤ)} {p : ComplexPoint (curveC N)} (hp : IsCuspLimit N σ p)
include hp

omit hp in
theorem eventuallyEq_nhds_of_nhdsNE {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : f =ᶠ[𝓝[≠] (0 : ℂ)] g) : f =ᶠ[𝓝 0] g :=
  (hf.frequently_eq_iff_eventually_eq hg).mp h.frequently

theorem cuspQ_mul {U : (curveC N).left.Opens} (hx : p.underlying ∈ U)
    (a b : Γ((curveC N).left, U)) :
    cuspQ N σ U (a * b) =ᶠ[𝓝 0] cuspQ N σ U a * cuspQ N σ U b := by
  apply eventuallyEq_nhds_of_nhdsNE (cuspQ_analyticAt hp hx _)
    ((cuspQ_analyticAt hp hx a).mul (cuspQ_analyticAt hp hx b))
  filter_upwards [eventually_invQParam_mem hp hx, self_mem_nhdsWithin] with q ⟨_, hq⟩ hq0
  have hq0' : q ≠ 0 := hq0
  simp only [Pi.mul_apply, cuspQ_eq_of_ne_zero N σ _ _ hq0', cuspEval, Function.comp_apply]
  exact evaluate_mul' N a b _ hq

theorem cuspQ_pow {U : (curveC N).left.Opens} (hx : p.underlying ∈ U)
    (a : Γ((curveC N).left, U)) (k : ℕ) :
    cuspQ N σ U (a ^ k) =ᶠ[𝓝 0] cuspQ N σ U a ^ k := by
  apply eventuallyEq_nhds_of_nhdsNE (cuspQ_analyticAt hp hx _)
    ((cuspQ_analyticAt hp hx a).pow k)
  filter_upwards [eventually_invQParam_mem hp hx, self_mem_nhdsWithin] with q ⟨_, hq⟩ hq0
  have hq0' : q ≠ 0 := hq0
  simp only [Pi.pow_apply, cuspQ_eq_of_ne_zero N σ _ _ hq0', cuspEval, Function.comp_apply]
  exact evaluate_pow' N a k _ hq

theorem cuspQ_eventuallyEq_of_germ_eq {U V : (curveC N).left.Opens}
    (hU : p.underlying ∈ U) (hV : p.underlying ∈ V)
    (s : Γ((curveC N).left, U)) (t : Γ((curveC N).left, V))
    (h : (curveC N).left.presheaf.germ U _ hU s = (curveC N).left.presheaf.germ V _ hV t) :
    cuspQ N σ U s =ᶠ[𝓝 0] cuspQ N σ V t := by
  obtain ⟨W, hW, iU, iV, hst⟩ := TopCat.Presheaf.germ_eq _ _ hU hV s t h
  apply eventuallyEq_nhds_of_nhdsNE (cuspQ_analyticAt hp hU s) (cuspQ_analyticAt hp hV t)
  filter_upwards [eventually_invQParam_mem hp hW, self_mem_nhdsWithin] with q ⟨_, hq⟩ hq0
  have hq0' : q ≠ 0 := hq0
  rw [cuspQ_eq_of_ne_zero N σ _ _ hq0', cuspQ_eq_of_ne_zero N σ _ _ hq0']
  simp only [cuspEval, Function.comp_apply]
  rw [Point.evaluate_res iU.le s _ hq, Point.evaluate_res iV.le t _ hq]
  exact congrArg (fun r => Point.evaluate W r _) hst

theorem analyticOrderAt_cuspQ_of_germ_eq_zero {U : (curveC N).left.Opens}
    (hU : p.underlying ∈ U) (s : Γ((curveC N).left, U))
    (h : (curveC N).left.presheaf.germ U _ hU s = 0) :
    analyticOrderAt (cuspQ N σ U s) 0 = ⊤ := by
  rw [analyticOrderAt_congr (cuspQ_eventuallyEq_of_germ_eq hp hU hU s 0 (by rw [h, map_zero]))]
  apply analyticOrderAt_eq_top.mpr
  apply eventuallyEq_nhds_of_nhdsNE (cuspQ_analyticAt hp hU 0) analyticAt_const
  filter_upwards [eventually_invQParam_mem hp hU, self_mem_nhdsWithin] with q ⟨_, hq⟩ hq0
  have hq0' : q ≠ 0 := hq0
  rw [cuspQ_eq_of_ne_zero N σ _ _ hq0']
  simp only [cuspEval, Function.comp_apply]
  exact evaluate_zero' N _ hq

theorem analyticOrderAt_cuspQ_pow_mul {U : (curveC N).left.Opens} (hx : p.underlying ∈ U)
    (π u : Γ((curveC N).left, U)) (k : ℕ) (hu : Point.evaluate U u p ≠ 0) :
    analyticOrderAt (cuspQ N σ U (π ^ k * u)) 0 = k • analyticOrderAt (cuspQ N σ U π) 0 := by
  have hπ := cuspQ_analyticAt hp hx π
  have hu' := cuspQ_analyticAt hp hx u
  have e₁ : cuspQ N σ U (π ^ k * u) =ᶠ[𝓝 0] cuspQ N σ U π ^ k * cuspQ N σ U u := by
    filter_upwards [cuspQ_mul hp hx (π ^ k) u, cuspQ_pow hp hx π k] with z h₁ h₂
    rw [h₁, Pi.mul_apply, h₂, Pi.mul_apply]
  have h0 : analyticOrderAt (cuspQ N σ U u) 0 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (by rw [cuspQ_zero hp hx]; exact hu))
  rw [analyticOrderAt_congr e₁, analyticOrderAt_mul (hπ.pow k) hu', analyticOrderAt_pow hπ, h0,
    add_zero]

theorem analyticOrderAt_cuspQ_of_germ_eq {U U₀ U₁ : (curveC N).left.Opens}
    (hU : p.underlying ∈ U) (hU₀ : p.underlying ∈ U₀)
    (hU₁ : p.underlying ∈ U₁) (h : Γ((curveC N).left, U))
    (π : Γ((curveC N).left, U₀)) (u : Γ((curveC N).left, U₁)) (n : ℕ)
    (hu : IsUnit ((curveC N).left.presheaf.germ U₁ _ hU₁ u))
    (hh : (curveC N).left.presheaf.germ U _ hU h =
      (curveC N).left.presheaf.germ U₁ _ hU₁ u * (curveC N).left.presheaf.germ U₀ _ hU₀ π ^ n) :
    analyticOrderAt (cuspQ N σ U h) 0 = n • analyticOrderAt (cuspQ N σ U₀ π) 0 := by
  let V := U₀ ⊓ U₁
  have hV : p.underlying ∈ V := ⟨hU₀, hU₁⟩
  let π' := (curveC N).left.presheaf.map (homOfLE (inf_le_left : V ≤ U₀)).op π
  let u' := (curveC N).left.presheaf.map (homOfLE (inf_le_right : V ≤ U₁)).op u
  have gπ : (curveC N).left.presheaf.germ V _ hV π' = (curveC N).left.presheaf.germ U₀ _ hU₀ π :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gu : (curveC N).left.presheaf.germ V _ hV u' = (curveC N).left.presheaf.germ U₁ _ hU₁ u :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hg : (curveC N).left.presheaf.germ U _ hU h =
      (curveC N).left.presheaf.germ V _ hV (π' ^ n * u') := by
    rw [map_mul, map_pow, gπ, gu, hh, mul_comm]
  have hu' : Point.evaluate V u' p ≠ 0 :=
    evaluate_ne_zero_of_isUnit' N V u' p hV (by rw [gu]; exact hu)
  rw [analyticOrderAt_congr (cuspQ_eventuallyEq_of_germ_eq hp hU hV h _ hg),
    analyticOrderAt_cuspQ_pow_mul hp hV π' u' n hu',
    analyticOrderAt_congr (cuspQ_eventuallyEq_of_germ_eq hp hV hU₀ π' π gπ)]

/-- The translated arc is not eventually constant at the cusp: the chart coordinate, minus its
value at `p`, has finite order in `q`. -/
theorem analyticOrderAt_cuspQ_chart_ne_top :
    let D := ComplexPoint.localEtaleCoordinates (curveC N) 1 p
    let c := Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0)) p
    analyticOrderAt (cuspQ N σ D.neighborhood
      (D.coordinateAlgHom (MvPolynomial.X 0 - MvPolynomial.C c))) 0 ≠ ⊤ := by
  intro D c htop
  let t := D.coordinateAlgHom (MvPolynomial.X 0)
  let s := D.coordinateAlgHom (MvPolynomial.X 0 - MvPolynomial.C c)
  have hD : p.underlying ∈ D.neighborhood := D.mem
  have hzero := analyticOrderAt_eq_top.mp htop
  -- the coordinate is eventually constant along the translated arc
  have hev : ∀ᶠ τ in atImInfty, Point.evaluate D.neighborhood s (arcPoint N (σ • τ)) = 0 := by
    have h1 : ∀ᶠ z in comap Complex.im atTop, cuspQ N σ D.neighborhood s
        (Function.Periodic.qParam (N : ℝ) z) = 0 :=
      (Function.Periodic.qParam_tendsto (period_pos N)).eventually
        (hzero.filter_mono nhdsWithin_le_nhds)
    have h2 := (tendsto_coe_atImInfty).eventually h1
    filter_upwards [h2] with τ hτ
    rw [← cuspEval_eq_cuspQ, cuspEval_coe] at hτ
    exact hτ
  let L := ComplexPoint.localChart (curveC N) 1 p
  have hsrc : ∀ᶠ τ in atImInfty, arcPoint N (σ • τ) ∈ L.source :=
    hp (L.open_source.mem_nhds (ComplexPoint.mem_localChart_source (curveC N) 1 p))
  have hmem : ∀ᶠ τ in atImInfty, (arcPoint N (σ • τ)).underlying ∈ D.neighborhood :=
    hp ((Point.isOpen_overOpen D.neighborhood).mem_nhds hD)
  have hconst : ∀ᶠ τ in atImInfty, arcPoint N (σ • τ) = p := by
    filter_upwards [hev, hsrc, hmem] with τ h0 hs hm
    have hp' : p ∈ L.source := ComplexPoint.mem_localChart_source (curveC N) 1 p
    apply L.injOn hs hp'
    funext i
    fin_cases i
    change L (arcPoint N (σ • τ)) 0 = L p 0
    rw [chart_coord_eval' N p _ hs, chart_coord_eval' N p _ hp']
    have e : Point.evaluate D.neighborhood s (arcPoint N (σ • τ)) =
        Point.evaluate D.neighborhood t (arcPoint N (σ • τ)) - c := by
      simp only [s]
      rw [← ComplexPoint.sectionEvaluationAlgHom_apply _ _ hm,
        ← ComplexPoint.sectionEvaluationAlgHom_apply _ _ hm, ← AlgHom.comp_apply,
        ← AlgHom.comp_apply, map_sub, MvPolynomial.algHom_C, Algebra.algebraMap_self,
        RingHom.id_apply]
    rw [e] at h0
    exact sub_eq_zero.mp h0
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hconst
  let τ₀ : ℍ := ⟨((max A 1 + 1 : ℝ) : ℂ) * Complex.I, by simp; positivity⟩
  have hτ₀ : A < τ₀.im := by
    change A < (((max A 1 + 1 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero]
    linarith [le_max_left A 1]
  have hcont : Continuous fun w : ℍ => (σ⁻¹ • w).im := by
    have h1 : Continuous fun w : ℍ => ((σ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) • w :=
      continuous_const_smul _
    exact UpperHalfPlane.continuous_im.comp h1
  apply arcPoint_not_eventually_const N (σ • τ₀)
  have hopen : ∀ᶠ w in 𝓝 (σ • τ₀), A < (σ⁻¹ • w).im :=
    hcont.continuousAt.eventually (lt_mem_nhds (by
      show A < (σ⁻¹ • σ • τ₀).im
      rw [inv_smul_smul]; exact hτ₀))
  filter_upwards [hopen] with w hw
  have e1 : arcPoint N w = p := by
    have := hA (σ⁻¹ • w) hw.le
    simp only [Set.mem_ofPred_eq] at this
    rwa [smul_inv_smul] at this
  rw [e1, hA τ₀ hτ₀.le]


omit hp in
/-- The local ring at the underlying point of a complex point. -/
abbrev pointStalk (q : ComplexPoint (curveC N)) : CommRingCat :=
  (curveC N).left.presheaf.stalk q.underlying

omit hp in
theorem pointStalk_isDiscreteValuationRing (q : ComplexPoint (curveC N)) :
    ∃ _ : IsDomain (pointStalk q), IsDiscreteValuationRing (pointStalk q) :=
  Scheme.isDiscreteValuationRing_stalk_of_isClosed (curveC N).hom
    (complexPoint_underlying_mem_closedPoints N q)

/-- **Valuation scaling at the cusp.** There is `m ≥ 1` such that for every regular function
`h` near the cusp point `p`, the order at `q = 0` of `h` along the translated arc is
`m · v_p(h)`. -/
theorem exists_cusp_ramification_index [IsDomain (pointStalk p)]
    [IsDiscreteValuationRing (pointStalk p)] :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ (U : (curveC N).left.Opens) (hU : p.underlying ∈ U)
      (h : Γ((curveC N).left, U)),
      analyticOrderAt (cuspQ N σ U h) 0 =
        (m : ℕ∞) * IsDiscreteValuationRing.addVal (pointStalk p)
          ((curveC N).left.presheaf.germ U _ hU h) := by
  classical
  let x := p.underlying
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (pointStalk p)
  obtain ⟨U₀, hU₀, π, hπ⟩ := TopCat.Presheaf.exists_germ_eq _ ϖ
  have hπx : Point.evaluate U₀ π p = 0 :=
    evaluate_eq_zero_of_not_isUnit' N U₀ π p hU₀ (by rw [hπ]; exact hϖ.not_isUnit)
  have he1 : 1 ≤ analyticOrderAt (cuspQ N σ U₀ π) 0 := by
    rw [Order.one_le_iff_ne_zero]
    exact analyticOrderAt_ne_zero.mpr ⟨cuspQ_analyticAt hp hU₀ π, by
      rw [cuspQ_zero hp hU₀]; exact hπx⟩
  have hfact : ∀ (U : (curveC N).left.Opens) (hU : x ∈ U) (h : Γ((curveC N).left, U)),
      (curveC N).left.presheaf.germ U _ hU h ≠ 0 →
      ∃ n : ℕ, IsDiscreteValuationRing.addVal (pointStalk p)
          ((curveC N).left.presheaf.germ U _ hU h) = n ∧
        analyticOrderAt (cuspQ N σ U h) 0 =
          n • analyticOrderAt (cuspQ N σ U₀ π) 0 := by
    intro U hU h hne
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    obtain ⟨U₁, hU₁, u, hu⟩ := TopCat.Presheaf.exists_germ_eq _ (v : pointStalk p)
    refine ⟨n, IsDiscreteValuationRing.addVal_def _ v hϖ n hv, ?_⟩
    exact analyticOrderAt_cuspQ_of_germ_eq hp hU hU₀ hU₁ h π u n
      (by rw [hu]; exact v.isUnit) (by rw [hu, hπ]; exact hv)
  have hfin : analyticOrderAt (cuspQ N σ U₀ π) 0 ≠ ⊤ := by
    intro htop
    let D := ComplexPoint.localEtaleCoordinates (curveC N) 1 p
    let t := D.coordinateAlgHom (MvPolynomial.X 0)
    let c := Point.evaluate D.neighborhood t p
    let s : Γ((curveC N).left, D.neighborhood) :=
      D.coordinateAlgHom (MvPolynomial.X 0 - MvPolynomial.C c)
    have hD : x ∈ D.neighborhood := D.mem
    have hne := analyticOrderAt_cuspQ_chart_ne_top hp
    by_cases h0 : (curveC N).left.presheaf.germ D.neighborhood _ hD s = 0
    · exact hne (analyticOrderAt_cuspQ_of_germ_eq_zero hp hD s h0)
    · obtain ⟨n, -, hn⟩ := hfact D.neighborhood hD s h0
      rcases n with _ | n
      · -- `s` would be a unit at `p`, but it vanishes there
        have hs0 : Point.evaluate D.neighborhood s p = 0 := by
          simp only [s]
          rw [← ComplexPoint.sectionEvaluationAlgHom_apply _ _ hD, map_sub,
            MvPolynomial.algHom_C, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
            RingHom.id_apply, ComplexPoint.sectionEvaluationAlgHom_apply]
          exact sub_self _
        have hpos : 1 ≤ analyticOrderAt (cuspQ N σ D.neighborhood s) 0 := by
          rw [Order.one_le_iff_ne_zero]
          exact analyticOrderAt_ne_zero.mpr ⟨cuspQ_analyticAt hp hD s, by
            rw [cuspQ_zero hp hD]; exact hs0⟩
        rw [hn] at hpos
        simp at hpos
      · apply hne
        rw [hn, htop]
        simp
  lift analyticOrderAt (cuspQ N σ U₀ π) 0 to ℕ using hfin with e he
  refine ⟨e, by exact_mod_cast he1, fun U hU h => ?_⟩
  by_cases h0 : (curveC N).left.presheaf.germ U _ hU h = 0
  · rw [h0, AddValuation.map_zero]
    have hpos : (e : ℕ∞) ≠ 0 := by
      intro h; rw [h] at he1; simp at he1
    rw [ENat.mul_top hpos]
    exact analyticOrderAt_cuspQ_of_germ_eq_zero hp hU h h0
  · obtain ⟨n, hv, hn⟩ := hfact U hU h h0
    rw [hn, hv, nsmul_eq_mul, mul_comm]

end CuspValuationQ


/-! ### Coefficients with respect to the chart differential, and the chain rule -/

section Chart

variable {X : Over (Spec (CommRingCat.of ℂ))} [SmoothOfRelativeDimension 1 X.hom]

/-- On every subopen of the coordinate neighbourhood, a relative differential is a multiple of
`dt`. -/
theorem exists_smul_coordDiff {x : X.left} (D : LocalEtaleCoordinates X 1 x) {V : X.left.Opens}
    (hV : V ≤ D.neighborhood) (ω : Γ(X.hom.relativeDifferentials, V)) :
    ∃ a : Γ(X.left, V), a • coordDiff D hV = ω := by
  have hcov (y : V) : ∃ g : Γ(X.left, D.neighborhood),
      X.left.basicOpen g ≤ V ∧ (y : X.left) ∈ X.left.basicOpen g :=
    D.isAffine.exists_basicOpen_le y (hV y.2)
  choose g hgV hyg using hcov
  have hloc (y : V) := (existsUnique_smul_coordDiff_basicOpen D (g y) (hyg y)
    (resD (hgV y) ω)).exists
  choose b hb using hloc
  have hcompat : TopCat.Presheaf.IsCompatible X.left.presheaf
      (fun y => X.left.basicOpen (g y)) b := by
    intro i j
    have hle₁ : X.left.basicOpen (g i) ⊓ X.left.basicOpen (g j) ≤ X.left.basicOpen (g i) :=
      inf_le_left
    have hle₂ : X.left.basicOpen (g i) ⊓ X.left.basicOpen (g j) ≤ X.left.basicOpen (g j) :=
      inf_le_right
    have hD : X.left.basicOpen (g i) ⊓ X.left.basicOpen (g j) ≤ D.neighborhood :=
      hle₁.trans (X.left.basicOpen_le (g i))
    change resO hle₁ (b i) = resO hle₂ (b j)
    have t₁ : resO hle₁ (b i) • coordDiff D hD = resD (hle₁.trans (hgV i)) ω := by
      rw [show coordDiff D hD = resD hle₁ (coordDiff D (X.left.basicOpen_le (g i))) from
        (resD_coordDiff D _ hle₁).symm, ← resD_smul, hb i, resD_resD]
    have t₂ : resO hle₂ (b j) • coordDiff D hD = resD (hle₂.trans (hgV j)) ω := by
      rw [show coordDiff D hD = resD hle₂ (coordDiff D (X.left.basicOpen_le (g j))) from
        (resD_coordDiff D _ hle₂).symm, ← resD_smul, hb j, resD_resD]
    have hz : (resO hle₁ (b i) - resO hle₂ (b j)) • coordDiff D hD = 0 := by
      rw [sub_smul, t₁, t₂, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_smul_coordDiff_eq_zero D hD _ hz)
  have hcover : V ≤ iSup fun y => X.left.basicOpen (g y) := fun y hy =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyg ⟨y, hy⟩⟩
  obtain ⟨a₀, ha, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.left.sheaf
    (fun y => X.left.basicOpen (g y)) V (fun y => homOfLE (hgV y)) hcover b hcompat
  let a : Γ(X.left, V) := a₀
  refine ⟨a, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨X.hom.relativeDifferentials.presheaf,
      X.hom.relativeDifferentials.isSheaf⟩ (fun y => X.left.basicOpen (g y)) V
    (fun y => homOfLE (hgV y)) hcover _ _ fun y => ?_
  change resD (hgV y) (a • coordDiff D hV) = resD (hgV y) ω
  rw [resD_smul, resD_coordDiff]
  have : resO (hgV y) a = b y := ha y
  rw [this, ← hb y]

theorem mfderiv_evaluate_res' {U W : X.left.Opens} (h : W ≤ U)
    (a : Γ(X.left, U)) (q : ComplexPoint X) (hq : q.underlying ∈ W) :
    mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ)
      (Point.evaluate W (X.left.presheaf.map (homOfLE h).op a)) q =
    mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate U a) q := by
  have hEq : Point.evaluate W (X.left.presheaf.map (homOfLE h).op a) =ᶠ[𝓝 q]
      Point.evaluate U a := by
    filter_upwards [(Point.isOpen_overOpen (X := X) W).mem_nhds hq] with q' hq'
    exact (Point.evaluate_res h a q' hq').symm
  exact ((ComplexPoint.mdifferentiableAt_evaluate U q (h hq) a).hasMFDerivAt.congr_of_eventuallyEq
    hEq).mfderiv

/-- **Chain rule.** If `d r = r' · dt` on a subopen of the coordinate neighbourhood, the
holomorphic differential of `r` at a complex point is `r'` times that of `t`. -/
theorem mfderiv_evaluate_eq_smul {x : X.left} (D : LocalEtaleCoordinates X 1 x)
    {V : X.left.Opens} (hV : V ≤ D.neighborhood) (r r' : Γ(X.left, V))
    (hr : X.hom.sectionsD V r = r' • coordDiff D hV) (q : ComplexPoint X)
    (hq : q.underlying ∈ V) :
    mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate V r) q =
      Point.evaluate V r' q • mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ)
        (Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))) q := by
  obtain ⟨W, hW, hqW, hWV'⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := q.underlying) hq
  have hWV : W ≤ V := hWV'
  have hWD : W ≤ D.neighborhood := hWV.trans hV
  have h1 : X.hom.sectionsD W (resO hWV r) =
      resO hWV r' • X.hom.sectionsD W (resO hWD (D.coordinateAlgHom (MvPolynomial.X 0))) := by
    rw [X.hom.sectionsD_map hWV, X.hom.sectionsD_map hWD]
    change resD hWV (X.hom.sectionsD V r) = _
    rw [hr, resD_smul, resD_coordDiff]
  ext v
  have hpair := congrArg (ComplexPoint.differentialSectionPairing W hW q hqW v) h1
  rw [ComplexPoint.differentialSectionPairing_sectionsD,
    ComplexPoint.differentialSectionPairing_smul_sectionsD] at hpair
  rw [mfderiv_evaluate_res' hWV r q hqW, mfderiv_evaluate_res' hWD _ q hqW,
    ← Point.evaluate_res hWV r' q hqW] at hpair
  exact hpair

end Chart


/-! ### The chain rule along the arc and along the translated arc -/

section ArcChain

theorem deriv_arc_eq_mul {x : (curveC N).left} (D : LocalEtaleCoordinates (curveC N) 1 x)
    {V : (curveC N).left.Opens} (hV : V ≤ D.neighborhood) (r r' : Γ((curveC N).left, V))
    (hr : (curveC N).hom.sectionsD V r = r' • coordDiff D hV)
    (τ : ℍ) (hτ : (arcPoint N τ).underlying ∈ V) :
    deriv (fun z : ℂ => Point.evaluate V r (arcPoint N (ofComplex z))) τ =
      Point.evaluate V r' (arcPoint N τ) *
        deriv (fun z : ℂ => Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))
          (arcPoint N (ofComplex z))) τ := by
  have hτD : (arcPoint N τ).underlying ∈ D.neighborhood := hV hτ
  have hb := ComplexPoint.mdifferentiableAt_evaluate (d := 1) V (arcPoint N τ) hτ r
  have ht := ComplexPoint.mdifferentiableAt_evaluate (d := 1) D.neighborhood (arcPoint N τ) hτD
    (D.coordinateAlgHom (MvPolynomial.X 0))
  have hc1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ' => Point.evaluate V r (arcPoint N τ')) τ :=
    hb.comp τ (mdifferentiable_arcPoint N τ)
  have hc2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ' => Point.evaluate D.neighborhood
      (D.coordinateAlgHom (MvPolynomial.X 0)) (arcPoint N τ')) τ :=
    ht.comp τ (mdifferentiable_arcPoint N τ)
  have e1 := mfderiv_one_eq_deriv hc1
  have e2 := mfderiv_one_eq_deriv hc2
  have k1 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun τ' => Point.evaluate V r (arcPoint N τ')) τ (1 : ℂ) =
      mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) (Point.evaluate V r) (arcPoint N τ)
        (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N) τ (1 : ℂ)) :=
    mfderiv_comp_apply (x := τ) hb (mdifferentiable_arcPoint N τ) (1 : ℂ)
  have k2 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun τ' => Point.evaluate D.neighborhood
      (D.coordinateAlgHom (MvPolynomial.X 0)) (arcPoint N τ')) τ (1 : ℂ) =
      mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ) (Point.evaluate D.neighborhood
        (D.coordinateAlgHom (MvPolynomial.X 0))) (arcPoint N τ)
        (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N) τ (1 : ℂ)) :=
    mfderiv_comp_apply (x := τ) ht (mdifferentiable_arcPoint N τ) (1 : ℂ)
  change deriv ((fun τ' => Point.evaluate V r (arcPoint N τ')) ∘ ofComplex) τ =
    _ * deriv ((fun τ' => Point.evaluate D.neighborhood
      (D.coordinateAlgHom (MvPolynomial.X 0)) (arcPoint N τ')) ∘ ofComplex) τ
  rw [← e1, ← e2, k1, k2, mfderiv_evaluate_eq_smul D hV r r' hr _ hτ]
  rfl

theorem deriv_cuspEval_eq_mul (σ : SL(2, ℤ)) {x : (curveC N).left}
    (D : LocalEtaleCoordinates (curveC N) 1 x)
    {V : (curveC N).left.Opens} (hV : V ≤ D.neighborhood) (r r' : Γ((curveC N).left, V))
    (hr : (curveC N).hom.sectionsD V r = r' • coordDiff D hV)
    (τ : ℍ) (hτ : (arcPoint N (σ • τ)).underlying ∈ V) :
    deriv (cuspEval N σ V r) τ = cuspEval N σ V r' τ *
      deriv (cuspEval N σ D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))) τ := by
  have hτD : (arcPoint N (σ • τ)).underlying ∈ D.neighborhood := hV hτ
  have hG := (UpperHalfPlane.analyticAt_smul (det_mapGL_pos σ) τ).differentiableAt
  have hf1 := (arcPoint_evaluate N V r (σ • τ) hτ).2.differentiableAt
  have hf2 := (arcPoint_evaluate N D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))
    (σ • τ) hτD).2.differentiableAt
  have hpt : (((Matrix.SpecialLinearGroup.mapGL ℝ σ) • ofComplex (τ : ℂ) : ℍ) : ℂ) =
      ((σ • τ : ℍ) : ℂ) := by rw [ofComplex_apply]; rfl
  rw [← hpt] at hf1 hf2
  have e1 : deriv (cuspEval N σ V r) τ =
      deriv (fun z : ℂ => Point.evaluate V r (arcPoint N (ofComplex z)))
        (((Matrix.SpecialLinearGroup.mapGL ℝ σ) • ofComplex (τ : ℂ) : ℍ) : ℂ) *
      deriv (fun z : ℂ => (((Matrix.SpecialLinearGroup.mapGL ℝ σ) • ofComplex z : ℍ) : ℂ)) τ := by
    rw [cuspEval_eq_comp]; exact deriv_comp (τ : ℂ) hf1 hG
  have e2 : deriv (cuspEval N σ D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))) τ =
      deriv (fun z : ℂ => Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))
          (arcPoint N (ofComplex z)))
        (((Matrix.SpecialLinearGroup.mapGL ℝ σ) • ofComplex (τ : ℂ) : ℍ) : ℂ) *
      deriv (fun z : ℂ => (((Matrix.SpecialLinearGroup.mapGL ℝ σ) • ofComplex z : ℍ) : ℂ)) τ := by
    rw [cuspEval_eq_comp]; exact deriv_comp (τ : ℂ) hf2 hG
  rw [e1, e2, hpt, deriv_arc_eq_mul N D hV r r' hr (σ • τ) hτ, cuspEval_coe N σ V r' τ]
  ring

end ArcChain

/-! ### Representatives are determined by their analytic continuations -/

section Representatives

theorem exists_arcPoint_mem (W : (curveC N).left.Opens) (hW : (W : Set (curveC N).left).Nonempty) :
    ∃ τ : ℍ, (arcPoint N τ).underlying ∈ W := by
  have : LocallyOfFiniteType (curveC N).hom := by
    have := SmoothOfRelativeDimension.smooth 1 (curveC N).hom
    infer_instance
  have : JacobsonSpace (curveC N).left := LocallyOfFiniteType.jacobsonSpace (curveC N).hom
  obtain ⟨y, hyW, hyc⟩ := nonempty_inter_closedPoints hW W.isOpen.isLocallyClosed
  rcases closedPoint_eq_arcPoint_or_cusp N y hyc with ⟨τ, hτ⟩ | ⟨c, hc⟩
  · exact ⟨τ, hτ ▸ hyW⟩
  · obtain ⟨σ, rfl⟩ := orbitOfSL_surjective N c
    have hlim := algebraicCusp_limit N σ
    have hmem : cuspPoint N (orbitOfSL N σ) ∈ Point.overOpen W := by
      change (cuspPoint N (orbitOfSL N σ)).underlying ∈ W
      rw [hc]; exact hyW
    have hev : ∀ᶠ z in atImInfty, complexLift (interior N (σ • z)) ∈ Point.overOpen W :=
      hlim ((Point.isOpen_overOpen W).mem_nhds hmem)
    obtain ⟨z, hz⟩ := hev.exists
    exact ⟨σ • z, hz⟩

theorem germ_eq_zero_of_arc_eventually_zero {V : (curveC N).left.Opens} (r : Γ((curveC N).left, V))
    (τ₀ : ℍ) (hτ₀ : (arcPoint N τ₀).underlying ∈ V)
    (h : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), Point.evaluate V r (arcPoint N (ofComplex z)) = 0) :
    (curveC N).left.presheaf.germ V _ hτ₀ r = 0 := by
  obtain ⟨h₁, h₂⟩ := arcStalk_isDiscreteValuationRing N τ₀
  obtain ⟨e, he, hall⟩ := exists_ramification_index N τ₀
  have htop : analyticOrderAt (arcEval N V r) τ₀ = ⊤ := by
    rw [analyticOrderAt_eq_top]
    exact (arcEval_analyticAt N V r τ₀ hτ₀).frequently_zero_iff_eventually_zero.mp h.frequently
  rw [hall V hτ₀ r] at htop
  apply (IsDiscreteValuationRing.addVal_eq_top_iff).mp
  by_contra hv
  have hne : (e : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top e
  exact WithTop.mul_ne_top hne hv htop

theorem RepOn.restrict_eq {W W' : (curveC N).left.Opens} {A : FieldC N}
    {s : Γ((curveC N).left, W)} {s' : Γ((curveC N).left, W')}
    (hs : RepOn N W A s) (hs' : RepOn N W' A s')
    (hne : ((W ⊓ W' : (curveC N).left.Opens) : Set (curveC N).left).Nonempty) :
    (curveC N).left.presheaf.map (homOfLE (inf_le_left : W ⊓ W' ≤ W)).op s =
      (curveC N).left.presheaf.map (homOfLE (inf_le_right : W ⊓ W' ≤ W')).op s' := by
  have : IsIntegral (curveC N).left := curveC_isIntegral N
  obtain ⟨τ₀, hτ₀⟩ := exists_arcPoint_mem N (W ⊓ W') hne
  obtain ⟨G, hG, hGv⟩ := hs.exists_continuation
  obtain ⟨G', hG', hG'v⟩ := hs'.exists_continuation
  set d := (curveC N).left.presheaf.map (homOfLE (inf_le_left : W ⊓ W' ≤ W)).op s -
    (curveC N).left.presheaf.map (homOfLE (inf_le_right : W ⊓ W' ≤ W')).op s' with hd
  have hz : (curveC N).left.presheaf.germ (W ⊓ W') _ hτ₀ d = 0 := by
    apply germ_eq_zero_of_arc_eventually_zero N d τ₀ hτ₀
    have hGG : G =ᶠ[𝓝[≠] (τ₀ : ℂ)] G' := Germ.coe_eq.mp ((hG τ₀).trans (hG' τ₀).symm)
    have hev := nhdsWithin_le_nhds (a := (τ₀ : ℂ)) (s := {(τ₀ : ℂ)}ᶜ)
      (eventually_ofComplex (arcPoint_evaluate N (W ⊓ W') d τ₀ hτ₀).1)
    have hpos : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), 0 < z.im :=
      nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ₀.im_pos)
    filter_upwards [hGG, hev, hpos] with z hz1 hz2 hz3
    have hcz : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hz3]
    rw [hd, evaluate_sub' N _ _ _ hz2, ← Point.evaluate_res inf_le_left s _ hz2,
      ← Point.evaluate_res inf_le_right s' _ hz2, (hGv _ hz2.1).2, (hG'v _ hz2.2).2, hcz, hz1,
      sub_self]
  exact sub_eq_zero.mp (germ_injective_of_isIntegral _ _ hτ₀ (by rw [hz, map_zero]))

end Representatives


/-! ### Auxiliary facts for the main argument -/

section Aux

instance curveC_isIntegral_inst : IsIntegral (curveC N).left := curveC_isIntegral N

/-- Restriction to a nonempty subopen is injective on the integral curve. -/
theorem res_injective {W W' : (curveC N).left.Opens} (h : W' ≤ W)
    (hne : (W' : Set (curveC N).left).Nonempty) :
    Function.Injective ((curveC N).left.presheaf.map (homOfLE h).op) := by
  obtain ⟨y, hy⟩ := hne
  intro a b hab
  apply germ_injective_of_isIntegral _ y (h hy)
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE h) y hy a,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE h) y hy b, hab]

/-- The generic germ of a section on a nonempty open. -/
abbrev gK {U : (curveC N).left.Opens} (hU : (U : Set (curveC N).left).Nonempty)
    (r : Γ((curveC N).left, U)) : (curveC N).left.functionField :=
  (curveC N).left.presheaf.germ U (genericPoint (curveC N).left)
    (genericPoint_mem hU.some_mem) r

theorem gK_res {U V : (curveC N).left.Opens} (h : V ≤ U) (hV : (V : Set (curveC N).left).Nonempty)
    (hU : (U : Set (curveC N).left).Nonempty) (r : Γ((curveC N).left, U)) :
    gK N hV ((curveC N).left.presheaf.map (homOfLE h).op r) = gK N hU r :=
  TopCat.Presheaf.germ_res_apply _ (homOfLE h) _ _ r

theorem gK_mul {U : (curveC N).left.Opens} (hU : (U : Set (curveC N).left).Nonempty)
    (a b : Γ((curveC N).left, U)) : gK N hU (a * b) = gK N hU a * gK N hU b :=
  map_mul _ a b

theorem gK_zero {U : (curveC N).left.Opens} (hU : (U : Set (curveC N).left).Nonempty) :
    gK N hU (0 : Γ((curveC N).left, U)) = 0 :=
  map_zero _

theorem eq_of_gK_eq {U : (curveC N).left.Opens} (hU : (U : Set (curveC N).left).Nonempty)
    {a b : Γ((curveC N).left, U)} (h : gK N hU a = gK N hU b) : a = b :=
  germ_injective_of_isIntegral _ _ _ h

/-- Order in `q` of `q ↦ q · c · g'(q)`. -/
theorem meromorphicOrderAt_qderiv {g : ℂ → ℂ} (c : ℂ) (hc : c ≠ 0) {n : ℤ} (hn : n ≠ 0)
    (hg : meromorphicOrderAt g 0 = n) :
    meromorphicOrderAt (fun q => deriv g q * (q * c)) 0 = n := by
  have hmero : MeromorphicAt g 0 := meromorphicAt_of_meromorphicOrderAt_ne_zero (by
    rw [hg]; exact_mod_cast hn)
  have h1 := meromorphicOrderAt_deriv_eq_sub_one (by exact_mod_cast hn) hg
  have ha : AnalyticAt ℂ (fun q : ℂ => q * c) 0 := analyticAt_id.mul analyticAt_const
  have h2 : meromorphicOrderAt (fun q : ℂ => q * c) 0 = 1 := by
    rw [ha.meromorphicOrderAt_eq]
    have : analyticOrderAt (fun q : ℂ => q * c) 0 = ((1 : ℕ) : ℕ∞) := by
      rw [ha.analyticOrderAt_eq_natCast]
      exact ⟨fun _ => c, analyticAt_const, hc, Eventually.of_forall fun z => by simp⟩
    rw [this]; rfl
  have hm : (fun q => deriv g q * (q * c)) = deriv g * fun q : ℂ => q * c := rfl
  rw [hm, meromorphicOrderAt_mul hmero.deriv ha.meromorphicAt, h1, h2]
  norm_cast
  ring

/-- The derivative in `z` of a periodic function, in terms of its cusp function. -/
theorem deriv_eq_of_cuspFunction {f : ℂ → ℂ} (hf : Function.Periodic f (N : ℝ))
    {q : ℂ} (hq : q ≠ 0)
    (hd : DifferentiableAt ℂ (Function.Periodic.cuspFunction (N : ℝ) f) q) :
    deriv f (Function.Periodic.invQParam (N : ℝ) q) =
      deriv (Function.Periodic.cuspFunction (N : ℝ) f) q *
        (q * (2 * Real.pi * Complex.I / (N : ℝ))) := by
  have hfe : f = Function.Periodic.cuspFunction (N : ℝ) f ∘ Function.Periodic.qParam (N : ℝ) :=
    funext fun z => (Function.Periodic.eq_cuspFunction (period_pos N).ne' hf z).symm
  set z := Function.Periodic.invQParam (N : ℝ) q
  have hqz : Function.Periodic.qParam (N : ℝ) z = q :=
    Function.Periodic.qParam_right_inv (period_pos N).ne' hq
  have hqd : HasDerivAt (Function.Periodic.qParam (N : ℝ))
      (Function.Periodic.qParam (N : ℝ) z * (2 * Real.pi * Complex.I / (N : ℝ))) z := by
    have h0 : HasDerivAt (fun w : ℂ => 2 * ↑Real.pi * Complex.I * w / (((N : ℝ)) : ℂ))
        (2 * ↑Real.pi * Complex.I * 1 / (((N : ℝ)) : ℂ)) z :=
      ((hasDerivAt_id z).const_mul _).div_const _
    have h1 := h0.cexp
    rw [mul_one] at h1
    exact h1
  rw [← hqz] at hd
  have e : deriv f z = deriv (Function.Periodic.cuspFunction (N : ℝ) f ∘
      Function.Periodic.qParam (N : ℝ)) z := by rw [← hfe]
  rw [e, deriv_comp z hd hqd.differentiableAt, hqd.deriv, hqz]

end Aux


/-! ### Representing `(A / B) · dj` by `a · dt` -/

section Represent

theorem eq_of_empty {W : (curveC N).left.Opens} (hne : ¬ (W : Set (curveC N).left).Nonempty)
    (a b : Γ((curveC N).left, W)) : a = b := by
  refine TopCat.Sheaf.eq_of_locally_eq' (curveC N).left.sheaf (fun i : PEmpty.{1} => W) W
    (fun _ => 𝟙 _) (fun y hy => (hne ⟨y, hy⟩).elim) a b (fun i => i.elim)

/-- If `a · dt` agrees with `(A / B) · dj` on a reference open carrying representatives of
`A`, `B` and `1 ⊗ j`, then it represents `(A / B) · dj` on its whole domain. -/
theorem representsDiffOn_of_ref {x : (curveC N).left} (D : LocalEtaleCoordinates (curveC N) 1 x)
    {A B : FieldC N} {W W₁ : (curveC N).left.Opens} (hW : W ≤ D.neighborhood)
    (hW₁ : W₁ ≤ D.neighborhood) (hW₁ne : (W₁ : Set (curveC N).left).Nonempty)
    {sA sB cj c' : Γ((curveC N).left, W₁)} (hsA : RepOn N W₁ A sA) (hsB : RepOn N W₁ B sB)
    (hcj : RepOn N W₁ (jC N) cj) (hc' : (curveC N).hom.sectionsD W₁ cj = c' • coordDiff D hW₁)
    (a : Γ((curveC N).left, W))
    (ha : resO (inf_le_left : W ⊓ W₁ ≤ W) a * resO (inf_le_right : W ⊓ W₁ ≤ W₁) sB =
      resO (inf_le_right : W ⊓ W₁ ≤ W₁) sA * resO (inf_le_right : W ⊓ W₁ ≤ W₁) c') :
    RepresentsDiffOn N W (a • coordDiff D hW) A B := by
  intro W' hW' s b c hs hb hc _
  have hW'D : W' ≤ D.neighborhood := hW'.trans hW
  obtain ⟨c'', hc''⟩ := exists_smul_coordDiff D hW'D ((curveC N).hom.sectionsD W' c)
  have hL : b • resD hW' (a • coordDiff D hW) = (b * resO hW' a) • coordDiff D hW'D := by
    rw [resD_smul, resD_coordDiff, mul_smul]
  have hR : s • (curveC N).hom.sectionsD W' c = (s * c'') • coordDiff D hW'D := by
    rw [← hc'', mul_smul]
  change b • resD hW' (a • coordDiff D hW) = s • (curveC N).hom.sectionsD W' c
  rw [hL, hR]
  congr 1
  by_cases hne : (W' : Set (curveC N).left).Nonempty
  · let W'' := W' ⊓ W₁
    have hW''ne : (W'' : Set (curveC N).left).Nonempty := inter_nonempty hne hW₁ne
    have h₁ : W'' ≤ W' := inf_le_left
    have h₂ : W'' ≤ W₁ := inf_le_right
    have hD'' : W'' ≤ D.neighborhood := h₁.trans hW'D
    apply res_injective N h₁ hW''ne
    have es : resO h₁ s = resO h₂ sA := RepOn.restrict_eq N hs hsA hW''ne
    have eb : resO h₁ b = resO h₂ sB := RepOn.restrict_eq N hb hsB hW''ne
    have ec : resO h₁ c = resO h₂ cj := RepOn.restrict_eq N hc hcj hW''ne
    have ecoef : resO h₁ c'' = resO h₂ c' := by
      have t₁ : resO h₁ c'' • coordDiff D hD'' =
          (curveC N).hom.sectionsD W'' (resO h₁ c) := by
        rw [(curveC N).hom.sectionsD_map h₁]
        change _ = resD h₁ ((curveC N).hom.sectionsD W' c)
        rw [← hc'', resD_smul, resD_coordDiff]
      have t₂ : resO h₂ c' • coordDiff D hD'' =
          (curveC N).hom.sectionsD W'' (resO h₂ cj) := by
        rw [(curveC N).hom.sectionsD_map h₂]
        change _ = resD h₂ ((curveC N).hom.sectionsD W₁ cj)
        rw [hc', resD_smul, resD_coordDiff]
      have hz : (resO h₁ c'' - resO h₂ c') • coordDiff D hD'' = 0 := by
        rw [sub_smul, t₁, t₂, ec, sub_self]
      exact sub_eq_zero.mp (eq_zero_of_smul_coordDiff_eq_zero D hD'' _ hz)
    have h₃ : W'' ≤ W ⊓ W₁ := inf_le_inf_right _ hW'
    have ha' := congrArg (resO h₃) ha
    simp only [resO, map_mul] at ha' ⊢
    change resO h₃ (resO _ a) * resO h₃ (resO _ sB) =
      resO h₃ (resO _ sA) * resO h₃ (resO _ c') at ha'
    change resO h₁ b * resO h₁ (resO hW' a) = resO h₁ s * resO h₁ c''
    rw [resO_resO, resO_resO, resO_resO, resO_resO] at ha'
    rw [resO_resO, eb, es, ecoef]
    rw [mul_comm]
    exact ha'
  · exact eq_of_empty N hne _ _

end Represent


/-! ### Analytic identities near the cusp -/

section AnalyticIdentities

open ShimuraPointDict X0Model

/-- From the germ identity `F = (A / B) · j′`: `F · G_B = G_A · j′` near `w₀`, for meromorphic
continuations `G_A`, `G_B` of `A`, `B`. -/
theorem F_mul_eventuallyEq {A B : FieldC N} {F : ℍ → ℂ} {GA GB : ℂ → ℂ} (w₀ : ℍ)
    (hB : fieldGermC N w₀ B ≠ 0)
    (hF : ((F ∘ ofComplex : ℂ → ℂ) : PuncturedGerm (w₀ : ℂ)) =
      meromorphicIncl (w₀ : ℂ) (ratGerm N w₀ A B * jDerivGerm w₀))
    (hGA : (GA : PuncturedGerm (w₀ : ℂ)) = meromorphicIncl (w₀ : ℂ) (fieldGermC N w₀ A))
    (hGB : (GB : PuncturedGerm (w₀ : ℂ)) = meromorphicIncl (w₀ : ℂ) (fieldGermC N w₀ B)) :
    (fun z => (F ∘ ofComplex) z * GB z) =ᶠ[𝓝[≠] (w₀ : ℂ)] fun z => GA z * jDeriv z := by
  have hj : meromorphicIncl (w₀ : ℂ) (jDerivGerm w₀) = (jDeriv : PuncturedGerm (w₀ : ℂ)) := rfl
  have key : ((F ∘ ofComplex : ℂ → ℂ) : PuncturedGerm (w₀ : ℂ)) * (GB : PuncturedGerm (w₀ : ℂ)) =
      (GA : PuncturedGerm (w₀ : ℂ)) * (jDeriv : PuncturedGerm (w₀ : ℂ)) := by
    rw [hF, hGB, hGA, ← hj, ← map_mul, ← map_mul, ratGerm, mul_right_comm, div_mul_cancel₀ _ hB]
  exact Germ.coe_eq.mp key

/-- The chain rule identity for `j`: at a parameter whose point lies in an open of the chart
carrying a representative `c` of `1 ⊗ j` with `d c = c' · dt`, `j′ = c' · (t ∘ P)′`. -/
theorem jDeriv_eq_mul {x : (curveC N).left} (D : LocalEtaleCoordinates (curveC N) 1 x)
    {W : (curveC N).left.Opens} (hWD : W ≤ D.neighborhood) {c c' : Γ((curveC N).left, W)}
    (hc : RepOn N W (jC N) c) (hc' : (curveC N).hom.sectionsD W c = c' • coordDiff D hWD)
    (w : ℍ) (hw : (arcPoint N w).underlying ∈ W) :
    jDeriv w = Point.evaluate W c' (arcPoint N w) *
      deriv (fun z : ℂ => Point.evaluate D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0))
        (arcPoint N (ofComplex z))) w := by
  obtain ⟨GJ, hGJ, hvJ⟩ := hc.exists_continuation
  have hev : (fun z : ℂ => Point.evaluate W c (arcPoint N (ofComplex z))) =ᶠ[𝓝 (w : ℂ)] jFun := by
    filter_upwards [eventually_ofComplex (arcPoint_evaluate N W c w hw).1,
      isOpen_upperHalfPlaneSet.mem_nhds w.im_pos] with z hz hzpos
    obtain ⟨hanJ, hvalJ⟩ := hvJ (ofComplex z) hz
    rw [hvalJ]
    have hcz : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hzpos]
    have := eq_of_germ_eq hanJ (analyticAt_jFun (ofComplex z))
      ((hGJ (ofComplex z)).trans (fieldGermC_jC N (ofComplex z)))
    rw [hcz] at this ⊢
    exact this
  rw [← deriv_arc_eq_mul N D hWD c c' hc' w hw, hev.deriv_eq]
  rfl

theorem slash_two_apply (F : ℍ → ℂ) (σ : SL(2, ℤ)) (τ : ℍ) :
    (F ∣[(2 : ℤ)] σ) τ = F (σ • τ) *
      (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) τ ^ 2)⁻¹ := by
  rw [ModularForm.SL_slash_apply]
  change F (σ • τ) * UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) τ ^ (-(2:ℤ)) = _
  rw [zpow_neg]
  norm_cast

theorem deriv_cuspEval_eq (σ : SL(2, ℤ)) (U : (curveC N).left.Opens) (r : Γ((curveC N).left, U))
    (τ : ℍ) (hτ : (arcPoint N (σ • τ)).underlying ∈ U) :
    deriv (cuspEval N σ U r) τ =
      deriv (fun z : ℂ => Point.evaluate U r (arcPoint N (ofComplex z))) ((σ • τ : ℍ) : ℂ) *
        (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) τ ^ 2)⁻¹ := by
  have hG := (UpperHalfPlane.analyticAt_smul (det_mapGL_pos σ) τ).differentiableAt
  have hf1 := (arcPoint_evaluate N U r (σ • τ) hτ).2.differentiableAt
  have hpt : (((Matrix.SpecialLinearGroup.mapGL ℝ σ) • ofComplex (τ : ℂ) : ℍ) : ℂ) =
      ((σ • τ : ℍ) : ℂ) := by rw [ofComplex_apply]; rfl
  rw [← hpt] at hf1
  rw [cuspEval_eq_comp, deriv_comp (τ : ℂ) hf1 hG, hpt,
    UpperHalfPlane.deriv_smul (det_mapGL_pos σ), det_mapGL_SL]
  simp [div_eq_mul_inv]

end AnalyticIdentities


/-! ### The valuation inequality at the cusp -/

section MainInequality

open ShimuraPointDict X0Model

variable {N} {σ : SL(2, ℤ)} {p : ComplexPoint (curveC N)}

/-- **Main inequality.** Let `h = α / β` near the cusp point `p = σ(∞)` agree with the
coefficient of `(A / B) · dj` with respect to `dt` (expressed through representatives on an open
`W₀` met by the arc near every parameter). If `(A / B) · j′` is holomorphic near the cusp and its
weight-two slash by `σ` vanishes at `i∞`, then `v_p(β) ≤ v_p(α)`. -/
theorem cusp_addVal_le (hp : IsCuspLimit N σ p) [IsDomain (pointStalk p)]
    [IsDiscreteValuationRing (pointStalk p)]
    {A B : FieldC N} {F : ℍ → ℂ} (hB : ∀ τ : ℍ, fieldGermC N τ B ≠ 0)
    (hF : ∀ τ : ℍ, ((F ∘ ofComplex : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) =
      meromorphicIncl (τ : ℂ) (ratGerm N τ A B * jDerivGerm τ))
    (hdiff : ∀ᶠ τ in atImInfty, DifferentiableAt ℂ (F ∘ ofComplex) ((σ • τ : ℍ) : ℂ))
    (hzero : IsZeroAtImInfty (F ∣[(2 : ℤ)] σ))
    (D : LocalEtaleCoordinates (curveC N) 1 p.underlying)
    {W₀ : (curveC N).left.Opens}
    (hW₀ : ∀ τ₀ : ℍ, ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), (arcPoint N (ofComplex z)).underlying ∈ W₀)
    {sA sB cj : Γ((curveC N).left, W₀)} (hsA : RepOn N W₀ A sA) (hsB : RepOn N W₀ B sB)
    (hcj : RepOn N W₀ (jC N) cj)
    {c' : Γ((curveC N).left, W₀ ⊓ D.neighborhood)}
    (hc' : (curveC N).hom.sectionsD (W₀ ⊓ D.neighborhood) (resO inf_le_left cj) =
      c' • coordDiff D (inf_le_right : W₀ ⊓ D.neighborhood ≤ D.neighborhood))
    {V : (curveC N).left.Opens} (hxV : p.underlying ∈ V)
    (α β : Γ((curveC N).left, V))
    (hβ : (curveC N).left.presheaf.germ V _ hxV β ≠ 0)
    (hrel : ∀ w : ℍ, (arcPoint N w).underlying ∈ V → (arcPoint N w).underlying ∈ W₀ →
      (arcPoint N w).underlying ∈ D.neighborhood →
      Point.evaluate V α (arcPoint N w) * Point.evaluate W₀ sB (arcPoint N w) =
        Point.evaluate V β (arcPoint N w) * (Point.evaluate W₀ sA (arcPoint N w) *
          Point.evaluate (W₀ ⊓ D.neighborhood) c' (arcPoint N w))) :
    IsDiscreteValuationRing.addVal (pointStalk p) ((curveC N).left.presheaf.germ V _ hxV β) ≤
      IsDiscreteValuationRing.addVal (pointStalk p) ((curveC N).left.presheaf.germ V _ hxV α) := by
  classical
  by_cases hα : (curveC N).left.presheaf.germ V _ hxV α = 0
  · rw [hα, AddValuation.map_zero]; exact le_top
  set Dn := D.neighborhood with hDn
  set t := D.coordinateAlgHom (MvPolynomial.X 0) with ht
  have hxD : p.underlying ∈ Dn := D.mem
  -- a uniformizer near `p`, on an open of the chart, with its coefficient
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (pointStalk p)
  obtain ⟨Uπ, hUπ, π₀, hπ₀⟩ := TopCat.Presheaf.exists_germ_eq _ ϖ
  set V' := Uπ ⊓ Dn with hV'
  have hxV' : p.underlying ∈ V' := ⟨hUπ, hxD⟩
  have hV'D : V' ≤ Dn := inf_le_right
  set π := resO (inf_le_left : V' ≤ Uπ) π₀ with hπdef
  have hπg : (curveC N).left.presheaf.germ V' _ hxV' π = ϖ := by
    rw [hπdef, TopCat.Presheaf.germ_res_apply]; exact hπ₀
  obtain ⟨πc, hπc'⟩ := exists_smul_coordDiff D hV'D ((curveC N).hom.sectionsD V' π)
  have hπc := hπc'.symm
  -- the ramification index at the cusp
  obtain ⟨m, hm1, hm⟩ := exists_cusp_ramification_index hp (N := N)
  have hvϖ : IsDiscreteValuationRing.addVal (pointStalk p) ϖ = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer hϖ
  obtain ⟨vα, hvα⟩ : ∃ n : ℕ, IsDiscreteValuationRing.addVal (pointStalk p)
      ((curveC N).left.presheaf.germ V _ hxV α) = n :=
    ENat.ne_top_iff_exists.mp (fun h => hα (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)) |>.imp
      fun n hn => hn.symm
  obtain ⟨vβ, hvβ⟩ : ∃ n : ℕ, IsDiscreteValuationRing.addVal (pointStalk p)
      ((curveC N).left.presheaf.germ V _ hxV β) = n :=
    ENat.ne_top_iff_exists.mp (fun h => hβ (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)) |>.imp
      fun n hn => hn.symm
  rw [hvα, hvβ]
  norm_cast
  -- the functions of the parameter `q`
  set Aq := cuspQ N σ V α with hAq
  set Bq := cuspQ N σ V β with hBq
  set Pq := cuspQ N σ V' π with hPq
  set P'q := cuspQ N σ V' πc with hP'q
  set Tq := cuspQ N σ Dn t with hTq
  set c : ℂ := 2 * Real.pi * Complex.I / ((N : ℝ) : ℂ) with hcdef
  have hc0 : c ≠ 0 := by
    have hN : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (period_pos N).ne'
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero) hN
  set Dq : ℂ → ℂ := fun q => deriv Tq q * (q * c) with hDq
  have hAa : AnalyticAt ℂ Aq 0 := cuspQ_analyticAt hp hxV α
  have hBa : AnalyticAt ℂ Bq 0 := cuspQ_analyticAt hp hxV β
  have hPa : AnalyticAt ℂ Pq 0 := cuspQ_analyticAt hp hxV' π
  have hP'a : AnalyticAt ℂ P'q 0 := cuspQ_analyticAt hp hxV' πc
  have hTa : AnalyticAt ℂ Tq 0 := cuspQ_analyticAt hp hxD t
  have hDa : AnalyticAt ℂ Dq 0 := hTa.deriv.mul (analyticAt_id.mul analyticAt_const)
  have oA : meromorphicOrderAt Aq 0 = ((m * vα : ℕ) : ℤ) := by
    rw [hAa.meromorphicOrderAt_eq, hm V hxV α, hvα]; norm_cast
  have oB : meromorphicOrderAt Bq 0 = ((m * vβ : ℕ) : ℤ) := by
    rw [hBa.meromorphicOrderAt_eq, hm V hxV β, hvβ]; norm_cast
  have oP : meromorphicOrderAt Pq 0 = ((m : ℕ) : ℤ) := by
    rw [hPa.meromorphicOrderAt_eq, hm V' hxV' π, hπg, hvϖ]; norm_cast; simp
  -- the region high in the upper half-plane
  have hev1 : ∀ᶠ τ in atImInfty, (arcPoint N (σ • τ)).underlying ∈ V ⊓ V' :=
    hp ((Point.isOpen_overOpen (V ⊓ V')).mem_nhds (show p.underlying ∈ V ⊓ V' from ⟨hxV, hxV'⟩))
  obtain ⟨A₁, hA₁⟩ := (atImInfty_mem _).mp (hev1.and hdiff)
  set A₀ := max A₁ 1 with hA₀
  have hA₀pos : 0 < A₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hreg : ∀ z : ℂ, A₀ < z.im → 0 < z.im ∧
      (arcPoint N (σ • ofComplex z)).underlying ∈ V ∧
      (arcPoint N (σ • ofComplex z)).underlying ∈ V' ∧
      DifferentiableAt ℂ (F ∘ ofComplex) ((σ • ofComplex z : ℍ) : ℂ) := by
    intro z hz
    have hpos : 0 < z.im := hA₀pos.trans hz
    have h := hA₁ (ofComplex z) (by
      rw [ofComplex_apply_of_im_pos hpos]
      exact (le_max_left _ _).trans hz.le)
    exact ⟨hpos, h.1.1, h.1.2, h.2⟩
  have hqreg : ∀ᶠ q in 𝓝[≠] (0 : ℂ), A₀ < (Function.Periodic.invQParam (N : ℝ) q).im :=
    (Function.Periodic.invQParam_tendsto (period_pos N)).eventually
      (preimage_mem_comap (Ioi_mem_atTop A₀))
  have hqan : ∀ᶠ q in 𝓝 (0 : ℂ), AnalyticAt ℂ Pq q ∧ AnalyticAt ℂ Tq q :=
    hPa.eventually_analyticAt.and hTa.eventually_analyticAt
  -- the uniformizer relation in `q`
  have hπq : ∀ᶠ q in 𝓝[≠] (0 : ℂ), deriv Pq q * (q * c) = P'q q * Dq q := by
    filter_upwards [hqreg, nhdsWithin_le_nhds hqan, self_mem_nhdsWithin] with q hq hqa hq0
    have hq0' : q ≠ 0 := hq0
    obtain ⟨hpos, -, hV'q, -⟩ := hreg _ hq
    set z := Function.Periodic.invQParam (N : ℝ) q
    have hcz : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hpos]
    have e1 : deriv (cuspEval N σ V' π) z = deriv Pq q * (q * c) :=
      deriv_eq_of_cuspFunction N (cuspEval_periodic N σ V' π) hq0' hqa.1.differentiableAt
    have e2 : deriv (cuspEval N σ Dn t) z = Dq q :=
      deriv_eq_of_cuspFunction N (cuspEval_periodic N σ Dn t) hq0' hqa.2.differentiableAt
    have e3 := deriv_cuspEval_eq_mul N σ D hV'D π πc hπc (ofComplex z) hV'q
    rw [hcz] at e3
    have e4 : cuspEval N σ V' πc z = P'q q := (cuspQ_eq_of_ne_zero N σ V' πc hq0').symm
    rw [← e1, e3, e4, e2]
  have oPd : meromorphicOrderAt (fun q => deriv Pq q * (q * c)) 0 = ((m : ℕ) : ℤ) :=
    meromorphicOrderAt_qderiv c hc0 (by exact_mod_cast (show m ≠ 0 by omega)) oP
  have hsum : (((m : ℕ) : ℤ) : WithTop ℤ) =
      meromorphicOrderAt P'q 0 + meromorphicOrderAt Dq 0 := by
    rw [← oPd, meromorphicOrderAt_congr hπq]
    exact meromorphicOrderAt_mul hP'a.meromorphicAt hDa.meromorphicAt
  have hDtop : meromorphicOrderAt Dq 0 ≠ ⊤ := by
    intro h; rw [h, WithTop.add_top] at hsum; exact WithTop.coe_ne_top hsum
  have hPtop : meromorphicOrderAt P'q 0 ≠ ⊤ := by
    intro h; rw [h, WithTop.top_add] at hsum; exact WithTop.coe_ne_top hsum
  have hP'nonneg := hP'a.meromorphicOrderAt_nonneg
  lift meromorphicOrderAt Dq 0 to ℤ using hDtop with d hd
  lift meromorphicOrderAt P'q 0 to ℤ using hPtop with a ha
  have ha0 : 0 ≤ a := by exact_mod_cast hP'nonneg
  have hmad : (m : ℤ) = a + d := by exact_mod_cast hsum
  -- a parameter high up whose point lies in `W₀`
  have hcontinv : Continuous fun w : ℍ => (σ⁻¹ • w).im := by
    have h1 : Continuous fun w : ℍ => ((σ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) • w :=
      continuous_const_smul _
    exact UpperHalfPlane.continuous_im.comp h1
  obtain ⟨z₀, hz₀im, hz₀W⟩ : ∃ z₀ : ℍ, A₀ < z₀.im ∧ (arcPoint N (σ • z₀)).underlying ∈ W₀ := by
    let τ₁ : ℍ := ⟨((A₀ + 1 : ℝ) : ℂ) * Complex.I, by simp; linarith⟩
    have hτ₁ : A₀ < τ₁.im := by
      change A₀ < (((A₀ + 1 : ℝ) : ℂ) * Complex.I).im
      simp
    have h1 : ∀ᶠ w in 𝓝 (σ • τ₁), A₀ < (σ⁻¹ • w).im :=
      hcontinv.continuousAt.eventually (lt_mem_nhds (by
        show A₀ < (σ⁻¹ • σ • τ₁).im
        rw [inv_smul_smul]; exact hτ₁))
    have h1' := eventually_ofComplex h1
    obtain ⟨z, hz1, hz2⟩ := ((hW₀ (σ • τ₁)).and (nhdsWithin_le_nhds h1')).exists
    refine ⟨σ⁻¹ • ofComplex z, hz2, ?_⟩
    rw [smul_inv_smul]; exact hz1
  set w₀ : ℍ := σ • z₀ with hw₀
  obtain ⟨GA, hGA, hvA⟩ := hsA.exists_continuation
  obtain ⟨GB, hGB, hvB⟩ := hsB.exists_continuation
  have hGBne : ∀ᶠ y in 𝓝[≠] (w₀ : ℂ), GB y ≠ 0 := by
    refine (hvB w₀ hz₀W).1.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 => ?_
    apply hB w₀
    apply (meromorphicIncl (w₀ : ℂ)).injective
    rw [← hGB w₀, map_zero]
    exact Germ.coe_eq.mpr (h0.filter_mono nhdsWithin_le_nhds)
  have hQ : ∀ᶠ y in 𝓝[≠] (w₀ : ℂ), 0 < y.im ∧ (arcPoint N (ofComplex y)).underlying ∈ W₀ ∧
      (F ∘ ofComplex) y * GB y = GA y * jDeriv y ∧ GB y ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds w₀.im_pos),
      nhdsWithin_le_nhds (eventually_ofComplex (arcPoint_evaluate N W₀ sA w₀ hz₀W).1),
      F_mul_eventuallyEq N w₀ (hB w₀) (hF w₀) (hGA w₀) (hGB w₀), hGBne] with y h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  -- pull back along the Möbius map
  set G : ℂ → ℂ := fun z => ((Matrix.SpecialLinearGroup.mapGL ℝ σ • ofComplex z : ℍ) : ℂ)
    with hG
  have hGt : Tendsto G (𝓝[≠] (z₀ : ℂ)) (𝓝[≠] (w₀ : ℂ)) := by
    have hc : ContinuousAt G z₀ :=
      (UpperHalfPlane.analyticAt_smul (det_mapGL_pos σ) z₀).continuousAt
    have hGz₀ : G z₀ = w₀ := by simp only [hG, ofComplex_apply]; rfl
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by rw [← hGz₀]; exact hc.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds z₀.im_pos)] with z hz hzpos
    intro hGz
    apply hz
    have h1 : (Matrix.SpecialLinearGroup.mapGL ℝ σ • ofComplex z : ℍ) =
        Matrix.SpecialLinearGroup.mapGL ℝ σ • z₀ := UpperHalfPlane.ext hGz
    have h2 : ofComplex z = z₀ := smul_left_cancel _ h1
    have h3 : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hzpos]
    rw [← h3, h2]
    rfl
  set Lz : ℂ → ℂ := fun z => (F ∣[(2 : ℤ)] σ) (ofComplex z) * cuspEval N σ V β z with hLz
  set Rz : ℂ → ℂ := fun z => cuspEval N σ V α z * deriv (cuspEval N σ Dn t) z with hRz
  have hΩ : IsOpen {z : ℂ | A₀ < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hident : ∀ᶠ z in 𝓝[≠] (z₀ : ℂ), Lz z = Rz z := by
    filter_upwards [hGt.eventually hQ, nhdsWithin_le_nhds (hΩ.mem_nhds hz₀im)] with z hQz hzA
    obtain ⟨hpos, hVz, hV'z, -⟩ := hreg z hzA
    obtain ⟨τ, rfl⟩ : ∃ τ : ℍ, (τ : ℂ) = z := ⟨⟨z, hpos⟩, rfl⟩
    simp only [ofComplex_apply] at hVz hV'z
    have hGz : G τ = ((σ • τ : ℍ) : ℂ) := by simp only [hG, ofComplex_apply]; rfl
    rw [hGz] at hQz
    simp only [ofComplex_apply, Function.comp_apply] at hQz
    obtain ⟨-, hW₀w, hFw, hGBw⟩ := hQz
    set w := σ • τ with hw
    have hDw : (arcPoint N w).underlying ∈ Dn := hV'D hV'z
    have jD := jDeriv_eq_mul N D (inf_le_right : W₀ ⊓ Dn ≤ Dn) (hcj.res N inf_le_left) hc' w
      ⟨hW₀w, hDw⟩
    have eA := (hvA w hW₀w).2
    have eB := (hvB w hW₀w).2
    have hr := hrel w hVz hW₀w hDw
    have key : F w * Point.evaluate V β (arcPoint N w) =
        Point.evaluate V α (arcPoint N w) *
          deriv (fun z : ℂ => Point.evaluate Dn t (arcPoint N (ofComplex z))) w := by
      rw [← eB] at hGBw
      apply mul_right_cancel₀ hGBw
      rw [← eA, ← eB] at hFw
      linear_combination (Point.evaluate V β (arcPoint N w)) * hFw +
        (Point.evaluate V β (arcPoint N w)) * (Point.evaluate W₀ sA (arcPoint N w)) * jD -
        (deriv (fun z : ℂ => Point.evaluate Dn t (arcPoint N (ofComplex z))) w) * hr
    simp only [hLz, hRz, ofComplex_apply]
    rw [slash_two_apply, deriv_cuspEval_eq N σ Dn t τ hDw, cuspEval_coe, cuspEval_coe]
    rw [← hw]
    linear_combination
      (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) τ ^ 2)⁻¹ * key
  -- both sides are holomorphic high in the upper half-plane
  have hS : DifferentiableOn ℂ (fun y => (F ∣[(2 : ℤ)] σ) (ofComplex y)) {z : ℂ | A₀ < z.im} := by
    intro y hy
    obtain ⟨hpos', -, -, hdy⟩ := hreg y hy
    apply DifferentiableAt.differentiableWithinAt
    have heq : (fun y' => (F ∣[(2 : ℤ)] σ) (ofComplex y')) =ᶠ[𝓝 y] fun y' =>
        (F ∘ ofComplex) (G y') *
          (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) y' ^ 2)⁻¹ := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hpos'] with y' hy'
      rw [slash_two_apply]
      simp only [Function.comp_apply, hG, ofComplex_apply]
      congr 3
      rw [ofComplex_apply_of_im_pos hy']
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    have hGd := (UpperHalfPlane.analyticAt_smul (det_mapGL_pos σ) ⟨y, hpos'⟩).differentiableAt
    have hden : DifferentiableAt ℂ
        (fun y' => UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) y') y := by
      unfold UpperHalfPlane.denom; fun_prop
    have hden0 : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ σ) y ≠ 0 :=
      UpperHalfPlane.denom_ne_zero_of_im _ hpos'.ne'
    exact (hdy.comp y hGd).mul ((hden.pow 2).inv (pow_ne_zero 2 hden0))
  have hLa : AnalyticOnNhd ℂ Lz {z : ℂ | A₀ < z.im} := by
    intro z hz
    obtain ⟨hpos, hVz, -, -⟩ := hreg z hz
    have h1 := cuspEval_analyticAt N σ V β (ofComplex z) hVz
    rw [ofComplex_apply_of_im_pos hpos] at h1
    exact (hS.analyticAt (hΩ.mem_nhds hz)).mul h1
  have hRa : AnalyticOnNhd ℂ Rz {z : ℂ | A₀ < z.im} := by
    intro z hz
    obtain ⟨hpos, hVz, hV'z, -⟩ := hreg z hz
    have h1 := cuspEval_analyticAt N σ V α (ofComplex z) hVz
    have h2 := cuspEval_analyticAt N σ Dn t (ofComplex z) (hV'D hV'z)
    rw [ofComplex_apply_of_im_pos hpos] at h1 h2
    exact h1.mul h2.deriv
  have heq := hLa.eqOn_of_preconnected_of_frequently_eq hRa
    (convex_halfSpace_im_gt A₀).isPreconnected hz₀im hident.frequently
  -- transfer to the parameter `q`
  set Φ : ℂ → ℂ := fun q => (F ∣[(2 : ℤ)] σ) (ofComplex (Function.Periodic.invQParam (N : ℝ) q))
    with hΦ
  have hmainq : ∀ᶠ q in 𝓝[≠] (0 : ℂ), Φ q * Bq q = Aq q * Dq q := by
    filter_upwards [hqreg, nhdsWithin_le_nhds hqan, self_mem_nhdsWithin] with q hq hqa hq0
    have hq0' : q ≠ 0 := hq0
    have e := heq hq
    have e2 : deriv (cuspEval N σ Dn t) (Function.Periodic.invQParam (N : ℝ) q) = Dq q :=
      deriv_eq_of_cuspFunction N (cuspEval_periodic N σ Dn t) hq0' hqa.2.differentiableAt
    simp only [hLz, hRz] at e
    rw [e2, ← cuspQ_eq_of_ne_zero N σ V β hq0', ← cuspQ_eq_of_ne_zero N σ V α hq0'] at e
    exact e
  have hBne : ∀ᶠ q in 𝓝[≠] (0 : ℂ), Bq q ≠ 0 := by
    refine hBa.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 => ?_
    have htop : analyticOrderAt Bq 0 = ⊤ := analyticOrderAt_eq_top.mpr h0
    rw [hm V hxV β, hvβ] at htop
    exact WithTop.mul_ne_top (ENat.natCast_ne_top m) (ENat.natCast_ne_top vβ) htop
  set R : ℂ → ℂ := fun q => Aq q * Dq q / Bq q with hR
  have hRΦ : R =ᶠ[𝓝[≠] (0 : ℂ)] Φ := by
    filter_upwards [hmainq, hBne] with q h1 h2
    simp only [hR]
    rw [← h1, mul_div_cancel_right₀ _ h2]
  have hΦt : Tendsto Φ (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    Filter.Tendsto.comp (show Tendsto (F ∣[(2 : ℤ)] σ) atImInfty (𝓝 0) from hzero)
      (tendsto_comap_im_ofComplex.comp (Function.Periodic.invQParam_tendsto (period_pos N)))
  have hRm : MeromorphicAt R 0 := (hAa.meromorphicAt.mul hDa.meromorphicAt).div hBa.meromorphicAt
  have hpos := (tendsto_zero_iff_meromorphicOrderAt_pos hRm).mp (hΦt.congr' hRΦ.symm)
  have hRord : meromorphicOrderAt R 0 =
      meromorphicOrderAt Aq 0 + meromorphicOrderAt Dq 0 - meromorphicOrderAt Bq 0 := by
    have : R = (Aq * Dq) / Bq := rfl
    rw [this, meromorphicOrderAt_div (hAa.meromorphicAt.mul hDa.meromorphicAt) hBa.meromorphicAt,
      meromorphicOrderAt_mul hAa.meromorphicAt hDa.meromorphicAt]
  rw [hRord, oA, oB, ← hd] at hpos
  have hpos' : (0 : ℤ) < (m * vα : ℕ) + d - (m * vβ : ℕ) := by exact_mod_cast hpos
  have hlt : (m : ℤ) * vβ < m * (vα + 1) := by push_cast at hpos'; nlinarith
  have := lt_of_mul_lt_mul_left hlt (by positivity : (0 : ℤ) ≤ m)
  omega

end MainInequality


/-! ### K11 at cusps -/

section Assembly

open ShimuraPointDict X0Model

theorem algebraMap_germ_eq_gK {U : (curveC N).left.Opens} {x : (curveC N).left} (hx : x ∈ U)
    (r : Γ((curveC N).left, U)) :
    algebraMap ((curveC N).left.presheaf.stalk x) (curveC N).left.functionField
      ((curveC N).left.presheaf.germ U x hx r) = gK N ⟨x, hx⟩ r := by
  change ((curveC N).left.presheaf.stalkSpecializes _) ((curveC N).left.presheaf.germ U x hx r) = _
  exact TopCat.Presheaf.germ_stalkSpecializes_apply _ hx _ r

theorem evaluate_resO {U W : (curveC N).left.Opens} (h : W ≤ U) (r : Γ((curveC N).left, U))
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ W) :
    Point.evaluate W (resO h r) q = Point.evaluate U r q :=
  (Point.evaluate_res h r q hq).symm

/-- **K11 at cusps**, as stated in Route B: at the cusp `σ(∞)`, the rational differential
`(A / B) · dj` is regular when `F = (A / B) · j′` is holomorphic near the cusp and its
weight-two slash by `σ` vanishes at `i∞`. -/
theorem k11Cusp_holds : K11Cusp N := by
  intro σ p hp A B F hB hF hdiff hzero
  obtain ⟨hdom, hdvr⟩ := pointStalk_isDiscreteValuationRing (N := N) p
  let D := ComplexPoint.localEtaleCoordinates (curveC N) 1 p
  have hxD : p.underlying ∈ D.neighborhood := D.mem
  -- representatives over the preimage of a common affine open of the model
  obtain ⟨V₁, hV₁, h₁⟩ := exists_rep N A
  obtain ⟨V₂, hV₂, h₂⟩ := exists_rep N B
  obtain ⟨V₃, hV₃, h₃⟩ := exists_rep N (jC N)
  have hV₁₂ := nonempty_preirreducible_inter V₁.isOpen V₂.isOpen hV₁ hV₂
  obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (V₁ ⊓ V₂).isOpen V₃.isOpen hV₁₂ hV₃
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (x := y) (U := V₁ ⊓ V₂ ⊓ V₃) hy
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  let W₀ : (curveC N).left.Opens := toModel N ⁻¹ᵁ U
  have hWV (V : (X0Model.curve N).Opens) (hV : (U : Set (X0Model.curve N)) ⊆ V) :
      W₀ ≤ toModel N ⁻¹ᵁ V := fun x hx => hV hx
  obtain ⟨sA, hsA⟩ := h₁ W₀ (hWV V₁ fun x hx => (hUV hx).1.1)
  obtain ⟨sB, hsB⟩ := h₂ W₀ (hWV V₂ fun x hx => (hUV hx).1.2)
  obtain ⟨cj, hcj⟩ := h₃ W₀ (hWV V₃ fun x hx => (hUV hx).2)
  have hW₀ : ∀ τ₀ : ℍ, ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), (arcPoint N (ofComplex z)).underlying ∈ W₀ := by
    intro τ₀
    filter_upwards [eventually_complexPoint_mem_affine N U hU τ₀] with z hz
    show toModel N (arcPoint N (ofComplex z)).underlying ∈ U
    rw [toModel_underlying]; exact hz trivial
  let W₁ := W₀ ⊓ D.neighborhood
  have hW₁D : W₁ ≤ D.neighborhood := inf_le_right
  have hW₁W₀ : W₁ ≤ W₀ := inf_le_left
  obtain ⟨c', hc''⟩ := exists_smul_coordDiff D hW₁D
    ((curveC N).hom.sectionsD W₁ (resO hW₁W₀ cj))
  have hc' := hc''.symm
  have hW₁ne : (W₁ : Set (curveC N).left).Nonempty := by
    have hev : ∀ᶠ τ in atImInfty, (arcPoint N (σ • τ)).underlying ∈ D.neighborhood :=
      hp ((Point.isOpen_overOpen D.neighborhood).mem_nhds hxD)
    obtain ⟨τ₁, hτ₁⟩ := hev.exists
    have hev2 := (arcPoint_evaluate N D.neighborhood 0 (σ • τ₁) hτ₁).1
    obtain ⟨z, hz1, hz2⟩ :=
      ((hW₀ (σ • τ₁)).and (nhdsWithin_le_nhds (eventually_ofComplex hev2))).exists
    exact ⟨_, hz1, hz2⟩
  let sA1 := resO hW₁W₀ sA
  let sB1 := resO hW₁W₀ sB
  have hsB1 : gK N hW₁ne sB1 ≠ 0 := by
    intro h0
    obtain ⟨GB, hGB, hvB⟩ := hsB.exists_continuation
    obtain ⟨τ₀, hτ₀⟩ := exists_arcPoint_mem N W₁ hW₁ne
    have hz : sB1 = 0 := eq_of_gK_eq N hW₁ne (by rw [h0, gK_zero])
    apply hB τ₀
    apply (meromorphicIncl (τ₀ : ℂ)).injective
    rw [← hGB τ₀, map_zero]
    apply Germ.coe_eq.mpr
    have hev := nhdsWithin_le_nhds (a := (τ₀ : ℂ)) (s := {(τ₀ : ℂ)}ᶜ)
      (eventually_ofComplex (arcPoint_evaluate N W₁ sB1 τ₀ hτ₀).1)
    have hpos : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), 0 < z.im :=
      nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ₀.im_pos)
    filter_upwards [hev, hpos] with z hz1 hz2
    have hcz : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hz2]
    have e := (hvB (ofComplex z) (hW₁W₀ hz1)).2
    rw [← evaluate_resO N hW₁W₀ sB _ hz1] at e
    change Point.evaluate W₁ sB1 _ = _ at e
    rw [hz, evaluate_zero' N _ hz1, hcz] at e
    exact e.symm
  set h := gK N hW₁ne (sA1 * c') / gK N hW₁ne sB1 with hh
  have hhB : h * gK N hW₁ne sB1 = gK N hW₁ne (sA1 * c') := div_mul_cancel₀ _ hsB1
  -- `h` is a quotient of elements of the local ring at `p`
  obtain ⟨⟨α₀, β₀, hβ₀⟩, hαβ⟩ := IsLocalization.surj
    (nonZeroDivisors ((curveC N).left.presheaf.stalk p.underlying)) h
  simp only at hαβ
  have hβ₀ne : β₀ ≠ 0 := nonZeroDivisors.ne_zero hβ₀
  obtain ⟨Uα, hxUα, α₁, hα₁⟩ := TopCat.Presheaf.exists_germ_eq _ α₀
  obtain ⟨Uβ, hxUβ, β₁, hβ₁⟩ := TopCat.Presheaf.exists_germ_eq _ β₀
  let V := Uα ⊓ Uβ ⊓ D.neighborhood
  have hxV : p.underlying ∈ V := ⟨⟨hxUα, hxUβ⟩, hxD⟩
  have hVα : V ≤ Uα := inf_le_left.trans inf_le_left
  have hVβ : V ≤ Uβ := inf_le_left.trans inf_le_right
  let α := resO hVα α₁
  let β := resO hVβ β₁
  have hαg : (curveC N).left.presheaf.germ V _ hxV α = α₀ := by
    rw [TopCat.Presheaf.germ_res_apply]; exact hα₁
  have hβg : (curveC N).left.presheaf.germ V _ hxV β = β₀ := by
    rw [TopCat.Presheaf.germ_res_apply]; exact hβ₁
  have hVne : (V : Set (curveC N).left).Nonempty := ⟨_, hxV⟩
  -- the identity `α · s_B = β · s_A · c'` on `V ⊓ W₁`
  have hVW : ((V ⊓ W₁ : (curveC N).left.Opens) : Set (curveC N).left).Nonempty :=
    inter_nonempty hVne hW₁ne
  have hαK : gK N hVne α = h * gK N hVne β := by
    have e1 := algebraMap_germ_eq_gK N hxV α
    have e2 := algebraMap_germ_eq_gK N hxV β
    rw [hαg] at e1; rw [hβg] at e2
    rw [← e1, ← e2, hαβ]
  have hsec : resO (inf_le_left : V ⊓ W₁ ≤ V) α * resO (inf_le_right : V ⊓ W₁ ≤ W₁) sB1 =
      resO (inf_le_left : V ⊓ W₁ ≤ V) β *
        (resO (inf_le_right : V ⊓ W₁ ≤ W₁) sA1 * resO (inf_le_right : V ⊓ W₁ ≤ W₁) c') := by
    apply eq_of_gK_eq N hVW
    rw [gK_mul, gK_mul, gK_mul, gK_res N _ hVW hVne, gK_res N _ hVW hVne,
      gK_res N _ hVW hW₁ne, gK_res N _ hVW hW₁ne, gK_res N _ hVW hW₁ne, hαK,
      mul_right_comm, hhB, gK_mul]
    ring
  have hrel : ∀ w : ℍ, (arcPoint N w).underlying ∈ V → (arcPoint N w).underlying ∈ W₀ →
      (arcPoint N w).underlying ∈ D.neighborhood →
      Point.evaluate V α (arcPoint N w) * Point.evaluate W₀ sB (arcPoint N w) =
        Point.evaluate V β (arcPoint N w) * (Point.evaluate W₀ sA (arcPoint N w) *
          Point.evaluate (W₀ ⊓ D.neighborhood) c' (arcPoint N w)) := by
    intro w hwV hwW₀ hwD
    have hw : (arcPoint N w).underlying ∈ V ⊓ W₁ := ⟨hwV, hwW₀, hwD⟩
    have e := congrArg (fun r => Point.evaluate (V ⊓ W₁) r (arcPoint N w)) hsec
    simp only [evaluate_mul' N _ _ _ hw, evaluate_resO N _ _ _ hw] at e
    have e1 : Point.evaluate W₁ sB1 (arcPoint N w) = Point.evaluate W₀ sB (arcPoint N w) :=
      evaluate_resO N hW₁W₀ sB _ ⟨hwW₀, hwD⟩
    have e2 : Point.evaluate W₁ sA1 (arcPoint N w) = Point.evaluate W₀ sA (arcPoint N w) :=
      evaluate_resO N hW₁W₀ sA _ ⟨hwW₀, hwD⟩
    rw [e1, e2] at e
    exact e
  -- the valuation inequality, hence regularity of `h` at `p`
  have hβ : (curveC N).left.presheaf.germ V _ hxV β ≠ 0 := by rw [hβg]; exact hβ₀ne
  have hle := cusp_addVal_le hp hB hF hdiff hzero D hW₀ hsA hsB hcj hc' hxV α β hβ hrel
  rw [hαg, hβg, IsDiscreteValuationRing.addVal_le_iff_dvd] at hle
  obtain ⟨γ, hγ⟩ := hle
  have hreg : IsRegularFunctionAt h p.underlying := by
    rw [isRegularFunctionAt_iff]
    refine ⟨γ, ?_⟩
    have hinj := IsFractionRing.injective ((curveC N).left.presheaf.stalk p.underlying)
      (curveC N).left.functionField
    have hb0 : algebraMap _ (curveC N).left.functionField β₀ ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hβ₀ne
    apply mul_left_cancel₀ hb0
    rw [← map_mul, ← hγ, ← hαβ, mul_comm]
  obtain ⟨Ua, hxUa, a₀, ha₀⟩ := hreg
  -- the section `a · dt` near `p`
  let W := Ua ⊓ D.neighborhood
  have hWD : W ≤ D.neighborhood := inf_le_right
  have hWa : W ≤ Ua := inf_le_left
  have hxW : p.underlying ∈ W := ⟨hxUa, hxD⟩
  let a := resO hWa a₀
  refine ⟨W, hxW, a • coordDiff D hWD, ?_⟩
  have hWne : (W : Set (curveC N).left).Nonempty := ⟨_, hxW⟩
  have hWW : ((W ⊓ W₁ : (curveC N).left.Opens) : Set (curveC N).left).Nonempty :=
    inter_nonempty hWne hW₁ne
  have haK : gK N hWne a = h := by
    rw [gK_res N hWa hWne ⟨_, hxUa⟩]
    exact ha₀
  apply representsDiffOn_of_ref N D hWD hW₁D hW₁ne (hsA.res N hW₁W₀) (hsB.res N hW₁W₀)
    (hcj.res N hW₁W₀) hc' a
  apply eq_of_gK_eq N hWW
  rw [gK_mul, gK_mul, gK_res N _ hWW hWne, gK_res N _ hWW hW₁ne, gK_res N _ hWW hW₁ne,
    gK_res N _ hWW hW₁ne, haK, hhB, gK_mul]

/-- Route B with K8, K9 and K11 at cusps discharged: the identification of global
differentials with weight-two cusp forms, given the closed-point statement, K11 at arc points
and the global regularity statement. -/
theorem routeB_linearEquiv_of_K10_K11Arc_K12 (h10 : K10 N) (h11a : K11Arc N) (h12 : K12 N) :
    letI := differentialsModule N
    ∃ e : Γ((curveC N).hom.relativeDifferentials, ⊤) ≃ₗ[ℂ] CuspFormN N,
      (∀ ω τ, e ω τ = nativeValue N ω τ) ∧
        ∀ f, e.symm f = psi N (psiHypotheses N h10 h11a (k11Cusp_holds N) h12) f :=
  routeB_linearEquiv_of_points_regularity N h10 h11a (k11Cusp_holds N) h12

end Assembly

end ZInQ.Manuscript.RC.CuspFormDifferentials
