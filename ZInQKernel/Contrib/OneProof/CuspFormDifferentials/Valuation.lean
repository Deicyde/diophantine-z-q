import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Surjectivity

/-! Order of vanishing along the analytic arc at points of the upper half-plane.

For an open `U` containing the point `x = P τ` and a regular function `h` on `U`, the arc
gives the holomorphic germ `h ∘ P` at `τ`. If `h = π^k · u` with `u(x) ≠ 0`, then
`ord_τ (h ∘ P) = k · e` where `e = ord_τ (π ∘ P)`; if moreover `π(x) = 0` then `e ≥ 1`. For
the coordinate `t` of the chosen local étale coordinates at `x` (so that `t - t(x)` is the
local parameter of the chart), the ramification index `e = ord_τ (t ∘ P - t(x))` is finite
and at least one. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Set UpperHalfPlane Topology
open scoped Manifold

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

variable (N : ℕ) [NeZero N]

/-- A regular function on an open of the complexified curve, evaluated along the arc, in
the coordinate of `ℂ`. -/
def arcEval (U : (curveC N).left.Opens) (s : Γ((curveC N).left, U)) : ℂ → ℂ :=
  fun z => Point.evaluate U s (arcPoint N (ofComplex z))

theorem arcEval_analyticAt (U : (curveC N).left.Opens) (s : Γ((curveC N).left, U)) (τ : ℍ)
    (hx : (arcPoint N τ).underlying ∈ U) : AnalyticAt ℂ (arcEval N U s) (τ : ℂ) :=
  (arcPoint_evaluate N U s τ hx).2

theorem arcEval_coe (U : (curveC N).left.Opens) (s : Γ((curveC N).left, U)) (τ : ℍ) :
    arcEval N U s τ = Point.evaluate U s (arcPoint N τ) := by
  simp [arcEval, ofComplex_apply]

theorem eventually_mem_of_mem (U : (curveC N).left.Opens) (τ : ℍ)
    (hx : (arcPoint N τ).underlying ∈ U) :
    ∀ᶠ z in 𝓝 (τ : ℂ), (arcPoint N (ofComplex z)).underlying ∈ U := by
  obtain ⟨_, hev⟩ := (arcPoint_evaluate N U 0 τ hx)
  exact eventually_ofComplex (arcPoint_evaluate N U 0 τ hx).1

theorem arcEval_mul_eventuallyEq (U : (curveC N).left.Opens) (a b : Γ((curveC N).left, U))
    (τ : ℍ) (hx : (arcPoint N τ).underlying ∈ U) :
    arcEval N U (a * b) =ᶠ[𝓝 (τ : ℂ)] arcEval N U a * arcEval N U b := by
  filter_upwards [eventually_mem_of_mem N U τ hx] with z hz
  simp only [arcEval, Pi.mul_apply]
  rw [← Point.evaluationHom_apply U ⟨_, hz⟩, ← Point.evaluationHom_apply U ⟨_, hz⟩,
    ← Point.evaluationHom_apply U ⟨_, hz⟩, map_mul]

theorem arcEval_pow_eventuallyEq (U : (curveC N).left.Opens) (a : Γ((curveC N).left, U))
    (k : ℕ) (τ : ℍ) (hx : (arcPoint N τ).underlying ∈ U) :
    arcEval N U (a ^ k) =ᶠ[𝓝 (τ : ℂ)] arcEval N U a ^ k := by
  filter_upwards [eventually_mem_of_mem N U τ hx] with z hz
  simp only [arcEval, Pi.pow_apply]
  rw [← Point.evaluationHom_apply U ⟨_, hz⟩, ← Point.evaluationHom_apply U ⟨_, hz⟩, map_pow]

/-- **K11 (interior, scaling).** If `h = π^k · u` with `u` nonvanishing at `x = P τ`, the
order of `h ∘ P` at `τ` is `k` times the order of `π ∘ P`. -/
theorem analyticOrderAt_arcEval_pow_mul (U : (curveC N).left.Opens) (π u : Γ((curveC N).left, U))
    (k : ℕ) (τ : ℍ) (hx : (arcPoint N τ).underlying ∈ U)
    (hu : Point.evaluate U u (arcPoint N τ) ≠ 0) :
    analyticOrderAt (arcEval N U (π ^ k * u)) (τ : ℂ) =
      k • analyticOrderAt (arcEval N U π) (τ : ℂ) := by
  have hπ := arcEval_analyticAt N U π τ hx
  have hu' := arcEval_analyticAt N U u τ hx
  have e₁ : arcEval N U (π ^ k * u) =ᶠ[𝓝 (τ : ℂ)] arcEval N U π ^ k * arcEval N U u := by
    filter_upwards [arcEval_mul_eventuallyEq N U (π ^ k) u τ hx,
      arcEval_pow_eventuallyEq N U π k τ hx] with z h₁ h₂
    rw [h₁, Pi.mul_apply, h₂, Pi.mul_apply]
  have h0 : analyticOrderAt (arcEval N U u) (τ : ℂ) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (by rw [arcEval_coe]; exact hu))
  rw [analyticOrderAt_congr e₁, analyticOrderAt_mul (hπ.pow k) hu', analyticOrderAt_pow hπ, h0,
    add_zero]

/-- The order of `π ∘ P` at `τ` is at least one when `π` vanishes at `P τ`. -/
theorem one_le_analyticOrderAt_arcEval (U : (curveC N).left.Opens) (π : Γ((curveC N).left, U))
    (τ : ℍ) (hx : (arcPoint N τ).underlying ∈ U)
    (hπ : Point.evaluate U π (arcPoint N τ) = 0) :
    1 ≤ analyticOrderAt (arcEval N U π) (τ : ℂ) := by
  rw [Order.one_le_iff_ne_zero]
  exact analyticOrderAt_ne_zero.mpr ⟨arcEval_analyticAt N U π τ hx, by rw [arcEval_coe]; exact hπ⟩

private theorem chart_coord_eval (p q : ComplexPoint (curveC N))
    (hq : q ∈ (ComplexPoint.localChart (curveC N) 1 p).source) :
    ComplexPoint.localChart (curveC N) 1 p q 0 =
      Point.evaluate (ComplexPoint.localEtaleCoordinates (curveC N) 1 p).neighborhood
        ((ComplexPoint.localEtaleCoordinates (curveC N) 1 p).coordinateAlgHom (MvPolynomial.X 0)) q := by
  let D := ComplexPoint.localEtaleCoordinates (curveC N) 1 p
  have h := ComplexPoint.localChart_apply_component_eq_evaluate (curveC N) 1 p q hq 0
  refine h.trans ?_
  have e : D.neighborhood = D.ambientCoordinateOpen := D.neighborhood.ι_image_top.symm
  have ht : D.ambientCoordinateSection 0 =
      (curveC N).left.presheaf.map (eqToHom e.symm).op (D.coordinateAlgHom (MvPolynomial.X 0)) := by
    unfold LocalEtaleCoordinates.ambientCoordinateSection
      LocalEtaleCoordinates.coordinateRingHomOnOpen
    change ((D.neighborhood.topIso.inv ≫ (D.neighborhood.ι.appIso ⊤).inv)
      (D.coordinateAlgHom (MvPolynomial.X 0))) = _
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  rw [ht]
  exact (ComplexPoint.evaluate_eq e _ q).symm

/-- **K11 (interior, ramification index).** For the coordinate `t` of the chosen local
étale coordinates at `x = P τ`, the order `e` of `t ∘ P - t(x)` at `τ` satisfies
`1 ≤ e < ∞`. -/
theorem ramification_order_chart (τ : ℍ) :
    let p := arcPoint N τ
    let D := ComplexPoint.localEtaleCoordinates (curveC N) 1 p
    let t := D.coordinateAlgHom (MvPolynomial.X 0)
    1 ≤ analyticOrderAt (fun z => arcEval N D.neighborhood t z -
        Point.evaluate D.neighborhood t p) (τ : ℂ) ∧
      analyticOrderAt (fun z => arcEval N D.neighborhood t z -
        Point.evaluate D.neighborhood t p) (τ : ℂ) ≠ ⊤ := by
  intro p D t
  have hx : (arcPoint N τ).underlying ∈ D.neighborhood := D.mem
  have han : AnalyticAt ℂ (fun z => arcEval N D.neighborhood t z -
      Point.evaluate D.neighborhood t p) (τ : ℂ) :=
    (arcEval_analyticAt N D.neighborhood t τ hx).sub analyticAt_const
  refine ⟨?_, ?_⟩
  · rw [Order.one_le_iff_ne_zero]
    exact analyticOrderAt_ne_zero.mpr ⟨han, by simp [arcEval_coe, p]⟩
  · intro htop
    have hzero := analyticOrderAt_eq_top.mp htop
    let L := ComplexPoint.localChart (curveC N) 1 p
    have hsrc : ∀ᶠ σ in 𝓝 τ, arcPoint N σ ∈ L.source :=
      (mdifferentiable_arcPoint N).continuous.continuousAt.preimage_mem_nhds
        (L.open_source.mem_nhds (ComplexPoint.mem_localChart_source (curveC N) 1 p))
    apply arcPoint_not_eventually_const N τ
    filter_upwards [hsrc, eventually_coe hzero] with σ hσ hz
    have hp : p ∈ L.source := ComplexPoint.mem_localChart_source (curveC N) 1 p
    apply L.injOn hσ hp
    funext i
    fin_cases i
    change L (arcPoint N σ) 0 = L p 0
    rw [chart_coord_eval N p _ hσ, chart_coord_eval N p _ hp]
    have := sub_eq_zero.mp hz
    simpa [arcEval_coe] using this

/-! ### The valuation of the local ring at an arc point -/

section DVR

attribute [local instance] overSpecAlgebra

variable (τ : ℍ)

/-- The local ring of the complexified curve at `P τ`. -/
abbrev arcStalk : CommRingCat := (curveC N).left.presheaf.stalk (arcPoint N τ).underlying

theorem arcPoint_underlying_mem_closedPoints :
    (arcPoint N τ).underlying ∈ closedPoints (curveC N).left := by
  have : LocallyOfFiniteType (curveC N).hom := by
    have := SmoothOfRelativeDimension.smooth 1 (curveC N).hom
    infer_instance
  let p := arcPoint N τ
  have hw : p.left ≫ (curveC N).hom = 𝟙 _ := by simpa using Over.w p
  exact (pointEquivClosedPoint (curveC N).hom ⟨p.left, hw⟩).2

/-- The local ring at `P τ` is a discrete valuation ring. -/
theorem arcStalk_isDiscreteValuationRing :
    ∃ _ : IsDomain (arcStalk N τ), IsDiscreteValuationRing (arcStalk N τ) :=
  Scheme.isDiscreteValuationRing_stalk_of_isClosed (curveC N).hom
    (arcPoint_underlying_mem_closedPoints N τ)

theorem evaluate_eq_stalkHom (U : (curveC N).left.Opens) (s : Γ((curveC N).left, U))
    (hx : (arcPoint N τ).underlying ∈ U) :
    Point.evaluate U s (arcPoint N τ) =
      (arcPoint N τ).stalkHom ((curveC N).left.presheaf.germ U _ hx s) := by
  rw [Point.evaluate, dite_eq_left hx]

/-- Regular functions with the same germ at `P τ` have eventually equal evaluations along
the arc. -/
theorem arcEval_eventuallyEq_of_germ_eq {U V : (curveC N).left.Opens}
    (hU : (arcPoint N τ).underlying ∈ U) (hV : (arcPoint N τ).underlying ∈ V)
    (s : Γ((curveC N).left, U)) (t : Γ((curveC N).left, V))
    (h : (curveC N).left.presheaf.germ U _ hU s = (curveC N).left.presheaf.germ V _ hV t) :
    arcEval N U s =ᶠ[𝓝 (τ : ℂ)] arcEval N V t := by
  obtain ⟨W, hW, iU, iV, hst⟩ := TopCat.Presheaf.germ_eq _ _ hU hV s t h
  filter_upwards [eventually_mem_of_mem N W τ hW] with z hz
  simp only [arcEval]
  rw [Point.evaluate_res iU.le s _ hz, Point.evaluate_res iV.le t _ hz]
  exact congrArg (fun r => Point.evaluate W r (arcPoint N (ofComplex z))) hst

theorem evaluate_ne_zero_of_isUnit (U : (curveC N).left.Opens) (s : Γ((curveC N).left, U))
    (hx : (arcPoint N τ).underlying ∈ U)
    (hs : IsUnit ((curveC N).left.presheaf.germ U _ hx s)) :
    Point.evaluate U s (arcPoint N τ) ≠ 0 := by
  rw [evaluate_eq_stalkHom N τ U s hx]
  exact (hs.map (arcPoint N τ).stalkHom.hom).ne_zero

theorem evaluate_eq_zero_of_not_isUnit (U : (curveC N).left.Opens) (s : Γ((curveC N).left, U))
    (hx : (arcPoint N τ).underlying ∈ U)
    (hs : ¬ IsUnit ((curveC N).left.presheaf.germ U _ hx s)) :
    Point.evaluate U s (arcPoint N τ) = 0 := by
  rw [evaluate_eq_stalkHom N τ U s hx]
  by_contra h
  exact hs (isUnit_of_map_unit (arcPoint N τ).stalkHom.hom _ (isUnit_iff_ne_zero.mpr h))

/-- If the germ of `h` is `u · π^n` with `u` a unit, then `ord_τ (h ∘ P) = n · ord_τ (π ∘ P)`. -/
theorem analyticOrderAt_arcEval_of_germ_eq {U U₀ U₁ : (curveC N).left.Opens}
    (hU : (arcPoint N τ).underlying ∈ U) (hU₀ : (arcPoint N τ).underlying ∈ U₀)
    (hU₁ : (arcPoint N τ).underlying ∈ U₁) (h : Γ((curveC N).left, U))
    (π : Γ((curveC N).left, U₀)) (u : Γ((curveC N).left, U₁)) (n : ℕ)
    (hu : IsUnit ((curveC N).left.presheaf.germ U₁ _ hU₁ u))
    (hh : (curveC N).left.presheaf.germ U _ hU h =
      (curveC N).left.presheaf.germ U₁ _ hU₁ u * (curveC N).left.presheaf.germ U₀ _ hU₀ π ^ n) :
    analyticOrderAt (arcEval N U h) (τ : ℂ) = n • analyticOrderAt (arcEval N U₀ π) (τ : ℂ) := by
  let V := U₀ ⊓ U₁
  have hV : (arcPoint N τ).underlying ∈ V := ⟨hU₀, hU₁⟩
  let π' := (curveC N).left.presheaf.map (homOfLE (inf_le_left : V ≤ U₀)).op π
  let u' := (curveC N).left.presheaf.map (homOfLE (inf_le_right : V ≤ U₁)).op u
  have gπ : (curveC N).left.presheaf.germ V _ hV π' = (curveC N).left.presheaf.germ U₀ _ hU₀ π :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gu : (curveC N).left.presheaf.germ V _ hV u' = (curveC N).left.presheaf.germ U₁ _ hU₁ u :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hg : (curveC N).left.presheaf.germ U _ hU h =
      (curveC N).left.presheaf.germ V _ hV (π' ^ n * u') := by
    rw [map_mul, map_pow, gπ, gu, hh, mul_comm]
  have hu' : Point.evaluate V u' (arcPoint N τ) ≠ 0 :=
    evaluate_ne_zero_of_isUnit N τ V u' hV (by rw [gu]; exact hu)
  rw [analyticOrderAt_congr (arcEval_eventuallyEq_of_germ_eq N τ hU hV h _ hg),
    analyticOrderAt_arcEval_pow_mul N V π' u' n τ hV hu',
    analyticOrderAt_congr (arcEval_eventuallyEq_of_germ_eq N τ hV hU₀ π' π gπ)]

/-- **K11 (interior).** At `x = P τ` the arc scales the valuation of the local ring: there
is a ramification index `e ≥ 1` with `ord_τ (h ∘ P) = e · v_x(h)` for every regular function
`h` near `x` (both sides are `⊤` exactly when the germ of `h` is zero). -/
theorem exists_ramification_index [IsDomain (arcStalk N τ)]
    [IsDiscreteValuationRing (arcStalk N τ)] :
    ∃ e : ℕ, 1 ≤ e ∧ ∀ (U : (curveC N).left.Opens) (hU : (arcPoint N τ).underlying ∈ U)
      (h : Γ((curveC N).left, U)),
      analyticOrderAt (arcEval N U h) (τ : ℂ) =
        (e : ℕ∞) * IsDiscreteValuationRing.addVal (arcStalk N τ)
          ((curveC N).left.presheaf.germ U _ hU h) := by
  classical
  let x := (arcPoint N τ).underlying
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (arcStalk N τ)
  obtain ⟨U₀, hU₀, π, hπ⟩ := TopCat.Presheaf.exists_germ_eq _ ϖ
  have hπx : Point.evaluate U₀ π (arcPoint N τ) = 0 :=
    evaluate_eq_zero_of_not_isUnit N τ U₀ π hU₀ (by rw [hπ]; exact hϖ.not_isUnit)
  have he1 : 1 ≤ analyticOrderAt (arcEval N U₀ π) (τ : ℂ) :=
    one_le_analyticOrderAt_arcEval N U₀ π τ hU₀ hπx
  -- every germ is a unit times a power of `ϖ`
  have hfact : ∀ (U : (curveC N).left.Opens) (hU : x ∈ U) (h : Γ((curveC N).left, U)),
      (curveC N).left.presheaf.germ U _ hU h ≠ 0 →
      ∃ n : ℕ, IsDiscreteValuationRing.addVal (arcStalk N τ)
          ((curveC N).left.presheaf.germ U _ hU h) = n ∧
        analyticOrderAt (arcEval N U h) (τ : ℂ) =
          n • analyticOrderAt (arcEval N U₀ π) (τ : ℂ) := by
    intro U hU h hne
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    obtain ⟨U₁, hU₁, u, hu⟩ := TopCat.Presheaf.exists_germ_eq _ (v : arcStalk N τ)
    refine ⟨n, IsDiscreteValuationRing.addVal_def _ v hϖ n hv, ?_⟩
    exact analyticOrderAt_arcEval_of_germ_eq N τ hU hU₀ hU₁ h π u n
      (by rw [hu]; exact v.isUnit) (by rw [hu, hπ]; exact hv)
  -- the order of `π ∘ P` is finite, by comparison with the chart coordinate
  have hfin : analyticOrderAt (arcEval N U₀ π) (τ : ℂ) ≠ ⊤ := by
    intro htop
    let p := arcPoint N τ
    let D := ComplexPoint.localEtaleCoordinates (curveC N) 1 p
    let t := D.coordinateAlgHom (MvPolynomial.X 0)
    let c := Point.evaluate D.neighborhood t p
    let σ : Γ((curveC N).left, D.neighborhood) :=
      D.coordinateAlgHom (MvPolynomial.X 0 - MvPolynomial.C c)
    have hD : x ∈ D.neighborhood := D.mem
    have hσ : arcEval N D.neighborhood σ =ᶠ[𝓝 (τ : ℂ)]
        fun z => arcEval N D.neighborhood t z - c := by
      filter_upwards [eventually_mem_of_mem N D.neighborhood τ hD] with z hz
      simp only [arcEval, σ]
      rw [← ComplexPoint.sectionEvaluationAlgHom_apply _ _ hz,
        ← ComplexPoint.sectionEvaluationAlgHom_apply _ _ hz, ← AlgHom.comp_apply,
        ← AlgHom.comp_apply, map_sub, MvPolynomial.algHom_C, Algebra.algebraMap_self,
        RingHom.id_apply]
    obtain ⟨hσ1, hσfin⟩ := ramification_order_chart N τ
    rw [← analyticOrderAt_congr hσ] at hσ1 hσfin
    by_cases h0 : (curveC N).left.presheaf.germ D.neighborhood _ hD σ = 0
    · apply hσfin
      rw [analyticOrderAt_congr (arcEval_eventuallyEq_of_germ_eq N τ hD hD σ 0
        (by rw [h0, map_zero]))]
      apply analyticOrderAt_eq_top.mpr
      filter_upwards [eventually_mem_of_mem N D.neighborhood τ hD] with z hz
      simp only [arcEval]
      rw [← Point.evaluationHom_apply _ ⟨_, hz⟩, map_zero]
    · obtain ⟨n, -, hn⟩ := hfact D.neighborhood hD σ h0
      rw [hn, htop] at hσ1 hσfin
      rcases n with _ | n
      · simp at hσ1
      · exact hσfin (by simp)
  lift analyticOrderAt (arcEval N U₀ π) (τ : ℂ) to ℕ using hfin with e he
  refine ⟨e, by exact_mod_cast he1, fun U hU h => ?_⟩
  by_cases h0 : (curveC N).left.presheaf.germ U _ hU h = 0
  · rw [h0, AddValuation.map_zero]
    have hpos : (e : ℕ∞) ≠ 0 := by
      intro h; rw [h] at he1; simp at he1
    rw [ENat.mul_top hpos]
    rw [analyticOrderAt_congr (arcEval_eventuallyEq_of_germ_eq N τ hU hU h 0
      (by rw [h0, map_zero]))]
    apply analyticOrderAt_eq_top.mpr
    filter_upwards [eventually_mem_of_mem N U τ hU] with z hz
    simp only [arcEval]
    rw [← Point.evaluationHom_apply _ ⟨_, hz⟩, map_zero]
  · obtain ⟨n, hv, hn⟩ := hfact U hU h h0
    rw [hn, hv, nsmul_eq_mul, mul_comm]

/-- **K11 (interior), with the discrete valuation ring structure of the local ring.** -/
theorem arc_valuation_scaling :
    ∃ (_ : IsDomain (arcStalk N τ)) (_ : IsDiscreteValuationRing (arcStalk N τ)),
      ∃ e : ℕ, 1 ≤ e ∧ ∀ (U : (curveC N).left.Opens) (hU : (arcPoint N τ).underlying ∈ U)
        (h : Γ((curveC N).left, U)),
        analyticOrderAt (arcEval N U h) (τ : ℂ) =
          (e : ℕ∞) * IsDiscreteValuationRing.addVal (arcStalk N τ)
            ((curveC N).left.presheaf.germ U _ hU h) := by
  obtain ⟨h₁, h₂⟩ := arcStalk_isDiscreteValuationRing N τ
  exact ⟨h₁, h₂, exists_ramification_index N τ⟩

end DVR

end ZInQ.Manuscript.RC.CuspFormDifferentials
