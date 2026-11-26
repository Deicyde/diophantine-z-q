import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.RouteBAdapters

/-! K11 at arc points, from the discrete valuation ring structure of the local ring at
`P τ` and the scaling `ord_τ (h ∘ P) = e · v_x(h)` of the valuation along the arc. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane Topology Opposite
open scoped Manifold MatrixGroups

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open J0Cusps ShimuraPointDict

variable (N : ℕ) [NeZero N]

attribute [local instance] curveC_isIntegral overSpecAlgebra

/-- Regular functions on an empty open agree. -/
theorem section_eq_of_empty {W : (curveC N).left.Opens}
    (hW : ¬ (W : Set (curveC N).left).Nonempty) (u v : Γ((curveC N).left, W)) : u = v :=
  TopCat.Sheaf.eq_of_locally_eq' (curveC N).left.sheaf
    (fun _ : Empty => (⊥ : (curveC N).left.Opens)) W (fun i => i.elim)
    (fun x hx => (hW ⟨x, hx⟩).elim) u v (fun i => i.elim)

/-- A nonempty open of the complexified curve contains the points of the arc for all
parameters in a punctured neighbourhood of any point of `ℍ`. -/
theorem eventually_arc_mem_open (W : (curveC N).left.Opens)
    (hW : (W : Set (curveC N).left).Nonempty) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), (arcPoint N (ofComplex z)).underlying ∈ W := by
  obtain ⟨hd, hdvr⟩ := arcStalk_isDiscreteValuationRing N τ
  obtain ⟨e, he, hscale⟩ := exists_ramification_index N τ
  obtain ⟨Ux, hUx, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (arcPoint N τ).underlying) (U := ⊤) trivial
  obtain ⟨y, hy⟩ := inter_nonempty (U := Ux) (V := W) ⟨_, hxU⟩ hW
  obtain ⟨g, hgle, hyg⟩ := hUx.exists_basicOpen_le (⟨y, hy.2⟩ : W) hy.1
  have hg0 : (curveC N).left.presheaf.germ Ux _ hxU g ≠ 0 := by
    intro h0
    have hg : g = 0 := germ_injective_of_isIntegral (curveC N).left _ hxU (by rw [h0, map_zero])
    rw [hg, Scheme.basicOpen_zero] at hyg
    exact hyg
  have hfin : analyticOrderAt (arcEval N Ux g) (τ : ℂ) ≠ ⊤ := by
    rw [hscale Ux hxU g]
    refine WithTop.mul_ne_top (WithTop.coe_ne_top) ?_
    exact (IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hg0
  have hne : ∀ᶠ z in 𝓝[≠] (τ : ℂ), arcEval N Ux g z ≠ 0 :=
    (arcEval_analyticAt N Ux g τ hxU).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      fun h => hfin (analyticOrderAt_eq_top.mpr h)
  filter_upwards [hne, nhdsWithin_le_nhds (eventually_mem_of_mem N Ux τ hxU)] with z hz hzU
  exact hgle ((Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero g _ hzU).mpr hz)

/-- Representatives are unique. -/
theorem RepOn.unique {W : (curveC N).left.Opens} {A : FieldC N} {s s' : Γ((curveC N).left, W)}
    (hs : RepOn N W A s) (hs' : RepOn N W A s') : s = s' := by
  by_cases hne : (W : Set (curveC N).left).Nonempty
  · obtain ⟨z, hz⟩ := (eventually_arc_mem_open N W hne UpperHalfPlane.I).exists
    set τ : ℍ := ofComplex z
    obtain ⟨G, hG, hv⟩ := hs.exists_continuation
    obtain ⟨G', hG', hv'⟩ := hs'.exists_continuation
    have hzero : arcEval N W (s - s') =ᶠ[𝓝 (τ : ℂ)] 0 := by
      filter_upwards [eventually_mem_of_mem N W τ hz] with w hw
      simp only [arcEval, Pi.zero_apply]
      rw [← Point.evaluationHom_apply W ⟨_, hw⟩, map_sub, Point.evaluationHom_apply,
        Point.evaluationHom_apply, (hv _ hw).2, (hv' _ hw).2]
      exact sub_eq_zero.mpr (eq_of_germ_eq (hv _ hw).1 (hv' _ hw).1 ((hG _).trans (hG' _).symm))
    obtain ⟨hd, hdvr⟩ := arcStalk_isDiscreteValuationRing N τ
    obtain ⟨e, he, hscale⟩ := exists_ramification_index N τ
    have htop : analyticOrderAt (arcEval N W (s - s')) (τ : ℂ) = ⊤ :=
      analyticOrderAt_eq_top.mpr hzero
    rw [hscale W hz] at htop
    have hv0 : IsDiscreteValuationRing.addVal (arcStalk N τ)
        ((curveC N).left.presheaf.germ W _ hz (s - s')) = ⊤ := by
      by_contra h
      exact WithTop.mul_ne_top WithTop.coe_ne_top h htop
    have hg0 := (IsDiscreteValuationRing.addVal_eq_top_iff).mp hv0
    have := germ_injective_of_isIntegral (curveC N).left _ hz
      (show (curveC N).left.presheaf.germ W _ hz (s - s') =
        (curveC N).left.presheaf.germ W _ hz 0 by rw [hg0, map_zero])
    exact sub_eq_zero.mp this
  · exact section_eq_of_empty N hne s s'

/-- The derivative of a regular function along the arc, through the tangent of the arc. -/
theorem mfderiv_evaluate_arc (U : (curveC N).left.Opens) (b : Γ((curveC N).left, U)) (τ : ℍ)
    (hτ : (arcPoint N τ).underlying ∈ U) :
    mfderiv 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, ℂ) (Point.evaluate U b) (arcPoint N τ)
        (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N) τ (1 : ℂ)) =
      deriv (arcEval N U b) (τ : ℂ) := by
  have hcomp := (ComplexPoint.mdifferentiableAt_evaluate U _ hτ b).hasMFDerivAt.comp τ
    (mdifferentiable_arcPoint N τ).hasMFDerivAt
  have key := congrArg (fun L => L (1 : ℂ)) hcomp.mfderiv
  refine key.symm.trans ?_
  rw [mfderiv_apply_one_eq_deriv (h := Point.evaluate U b ∘ arcPoint N) (τ := τ)
    (arcPoint_evaluate N U b τ hτ).2.differentiableAt]
  rfl

/-- Two expressions `a · db = a' · db'` of one differential on an affine open give the same
analytic expression along the arc. -/
theorem arc_expression_eq {B : (curveC N).left.Opens} (hB : IsAffineOpen B)
    (a b a' b' : Γ((curveC N).left, B))
    (h : a • (curveC N).hom.sectionsD B b = a' • (curveC N).hom.sectionsD B b') (τ : ℍ)
    (hτ : (arcPoint N τ).underlying ∈ B) :
    Point.evaluate B a (arcPoint N τ) * deriv (arcEval N B b) (τ : ℂ) =
      Point.evaluate B a' (arcPoint N τ) * deriv (arcEval N B b') (τ : ℂ) := by
  have hpair := congrArg (ComplexPoint.differentialSectionPairing B hB (arcPoint N τ) hτ
    (mfderiv 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N) τ (1 : ℂ))) h
  rw [ComplexPoint.differentialSectionPairing_smul_sectionsD,
    ComplexPoint.differentialSectionPairing_smul_sectionsD] at hpair
  simp only [smul_apply] at hpair
  rw [mfderiv_evaluate_arc N B b τ hτ, mfderiv_evaluate_arc N B b' τ hτ] at hpair
  exact hpair

/-- A germ at `P τ` that vanishes at `P τ` has valuation at least one. -/
theorem one_le_addVal_of_evaluate_eq_zero (τ : ℍ) [IsDomain (arcStalk N τ)]
    [IsDiscreteValuationRing (arcStalk N τ)] {U : (curveC N).left.Opens}
    (hU : (arcPoint N τ).underlying ∈ U) (σ : Γ((curveC N).left, U))
    (hσ : Point.evaluate U σ (arcPoint N τ) = 0) :
    1 ≤ IsDiscreteValuationRing.addVal (arcStalk N τ)
      ((curveC N).left.presheaf.germ U _ hU σ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (arcStalk N τ)
  have hnu : ¬ IsUnit ((curveC N).left.presheaf.germ U _ hU σ) := fun hu =>
    evaluate_ne_zero_of_isUnit N τ U σ hU hu hσ
  have hmem : (curveC N).left.presheaf.germ U _ hU σ ∈ IsLocalRing.maximalIdeal (arcStalk N τ) :=
    hnu
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton] at hmem
  rw [← IsDiscreteValuationRing.addVal_uniformizer hϖ]
  exact (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr hmem

/-- The chart coordinate of the local étale coordinates at `P τ` is a uniformizer for the
arc: the order of `t ∘ P - t(P τ)` at `τ` is the ramification index `e`. -/
theorem chart_order_eq_ramification (τ : ℍ) [IsDomain (arcStalk N τ)]
    [IsDiscreteValuationRing (arcStalk N τ)] (e : ℕ)
    (hscale : ∀ (U : (curveC N).left.Opens) (hU : (arcPoint N τ).underlying ∈ U)
      (h : Γ((curveC N).left, U)),
      analyticOrderAt (arcEval N U h) (τ : ℂ) =
        (e : ℕ∞) * IsDiscreteValuationRing.addVal (arcStalk N τ)
          ((curveC N).left.presheaf.germ U _ hU h)) :
    let p := arcPoint N τ
    let D := ComplexPoint.localEtaleCoordinates (curveC N) 1 p
    let t := D.coordinateAlgHom (MvPolynomial.X 0)
    analyticOrderAt (fun z => arcEval N D.neighborhood t z -
        Point.evaluate D.neighborhood t p) (τ : ℂ) = e := by
  intro p D t
  have hD : (arcPoint N τ).underlying ∈ D.neighborhood := D.mem
  obtain ⟨c, hc⟩ : ∃ c, c = Point.evaluate D.neighborhood t p := ⟨_, rfl⟩
  rw [← hc]
  obtain ⟨et, het⟩ : ∃ et, et = analyticOrderAt (fun z => arcEval N D.neighborhood t z - c)
    (τ : ℂ) := ⟨_, rfl⟩
  rw [← het]
  -- `e_t = e · v(t - t(x)) ≥ e`
  let σ : Γ((curveC N).left, D.neighborhood) :=
    D.coordinateAlgHom (MvPolynomial.X 0 - MvPolynomial.C c)
  have hσ : arcEval N D.neighborhood σ =ᶠ[𝓝 (τ : ℂ)]
      fun z => arcEval N D.neighborhood t z - c := by
    filter_upwards [eventually_mem_of_mem N D.neighborhood τ hD] with z hz
    simp only [arcEval, σ]
    rw [← ComplexPoint.sectionEvaluationAlgHom_apply _ _ hz,
      ← ComplexPoint.sectionEvaluationAlgHom_apply _ _ hz, ← AlgHom.comp_apply,
      ← AlgHom.comp_apply, map_sub, MvPolynomial.algHom_C, Algebra.algebraMap_self,
      RingHom.id_apply]
  have hσx : Point.evaluate D.neighborhood σ p = 0 := by
    have h := hσ.self_of_nhds
    simp only [arcEval_coe] at h
    change Point.evaluate D.neighborhood σ (arcPoint N τ) = 0
    rw [h, hc, sub_self]
  have hge : (e : ℕ∞) ≤ et := by
    rw [het, ← analyticOrderAt_congr hσ, hscale D.neighborhood hD σ]
    exact le_mul_of_one_le_right' (one_le_addVal_of_evaluate_eq_zero N τ hD σ hσx)
  -- `e ≥ e_t`, through a uniformizer `π` and `dπ = π_t · dt` near `x`
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (arcStalk N τ)
  obtain ⟨U₀, hU₀, π, hπ⟩ := TopCat.Presheaf.exists_germ_eq _ ϖ
  obtain ⟨g, hgle, hxg⟩ := D.isAffine.exists_basicOpen_le (⟨(arcPoint N τ).underlying, hU₀, hD⟩ : ↥(U₀ ⊓ D.neighborhood)) hD
  let Bx := (curveC N).left.basicOpen g
  have hBx : IsAffineOpen Bx := D.isAffine.basicOpen g
  have hBU : Bx ≤ U₀ := hgle.trans inf_le_left
  have hBD : Bx ≤ D.neighborhood := (curveC N).left.basicOpen_le g
  let π' := resO hBU π
  let t' := resO hBD t
  obtain ⟨πt, hπt, -⟩ := existsUnique_smul_coordDiff_basicOpen D g hxg
    ((curveC N).hom.sectionsD Bx π')
  have hexp : (1 : Γ((curveC N).left, Bx)) • (curveC N).hom.sectionsD Bx π' =
      πt • (curveC N).hom.sectionsD Bx t' := by
    rw [one_smul, ← hπt]
    congr 1
    exact ((curveC N).hom.sectionsD_map hBD t).symm
  have hπ0 : Point.evaluate U₀ π p = 0 :=
    evaluate_eq_zero_of_not_isUnit N τ U₀ π hU₀ (by rw [hπ]; exact hϖ.not_isUnit)
  have hπord : analyticOrderAt (arcEval N U₀ π) (τ : ℂ) = e := by
    rw [hscale U₀ hU₀ π, hπ, IsDiscreteValuationRing.addVal_uniformizer hϖ, mul_one]
  have hresπ : arcEval N Bx π' =ᶠ[𝓝 (τ : ℂ)] arcEval N U₀ π := by
    filter_upwards [eventually_mem_of_mem N Bx τ hxg] with z hz
    exact (Point.evaluate_res hBU π _ hz).symm
  have hrest : arcEval N Bx t' =ᶠ[𝓝 (τ : ℂ)] arcEval N D.neighborhood t := by
    filter_upwards [eventually_mem_of_mem N Bx τ hxg] with z hz
    exact (Point.evaluate_res hBD t _ hz).symm
  have hderiv : deriv (arcEval N Bx π') =ᶠ[𝓝 (τ : ℂ)]
      fun z => arcEval N Bx πt z * deriv (arcEval N Bx t') z := by
    filter_upwards [eventually_mem_of_mem N Bx τ hxg,
      isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz hzpos
    have h := arc_expression_eq N hBx 1 π' πt t' hexp (ofComplex z) hz
    have hcz : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hzpos]
    rw [hcz, ← Point.evaluationHom_apply Bx ⟨_, hz⟩, map_one, one_mul] at h
    exact h
  have hanπ := arcEval_analyticAt N U₀ π τ hU₀
  have hant := arcEval_analyticAt N D.neighborhood t τ hD
  have hanπ' := arcEval_analyticAt N Bx π' τ hxg
  have hant' := arcEval_analyticAt N Bx t' τ hxg
  have hanπt := arcEval_analyticAt N Bx πt τ hxg
  -- orders of the derivatives
  have h1 : analyticOrderAt (deriv (arcEval N Bx π')) (τ : ℂ) + 1 = e := by
    rw [hanπ'.analyticOrderAt_deriv_add_one, ← hπord]
    apply analyticOrderAt_congr
    filter_upwards [hresπ] with z hz
    rw [hz, show arcEval N Bx π' τ = 0 by rw [hresπ.self_of_nhds, arcEval_coe, hπ0], sub_zero]
  have h2 : analyticOrderAt (deriv (arcEval N Bx t')) (τ : ℂ) + 1 = et := by
    rw [hant'.analyticOrderAt_deriv_add_one, het]
    apply analyticOrderAt_congr
    filter_upwards [hrest] with z hz
    rw [hz, hrest.self_of_nhds, arcEval_coe, hc]
  have h3 : analyticOrderAt (deriv (arcEval N Bx t')) (τ : ℂ) ≤
      analyticOrderAt (deriv (arcEval N Bx π')) (τ : ℂ) := by
    rw [analyticOrderAt_congr hderiv]
    rw [show (fun z => arcEval N Bx πt z * deriv (arcEval N Bx t') z) =
      arcEval N Bx πt * deriv (arcEval N Bx t') from rfl, analyticOrderAt_mul hanπt hant'.deriv]
    exact le_add_self
  have hle : et ≤ (e : ℕ∞) := by
    rw [← h1, ← h2]
    exact add_le_add_left h3 1
  exact le_antisymm hle hge

/-- A function with a nonzero meromorphic germ does not vanish on a punctured neighbourhood. -/
theorem eventually_ne_zero_of_germ {τ : ℍ} {G : ℂ → ℂ} {g : X0Model.MeromorphicGerm (τ : ℂ)}
    (h : (G : PuncturedGerm (τ : ℂ)) = X0Model.meromorphicIncl (τ : ℂ) g) (hg : g ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), G z ≠ 0 := by
  obtain ⟨f, hf, hfm⟩ := g.property
  have hGf : G =ᶠ[𝓝[≠] (τ : ℂ)] f := Germ.coe_eq.mp (h.trans hf.symm)
  rcases hfm.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    apply hg
    apply Subtype.ext
    exact hf.symm.trans (Germ.coe_eq.mpr h0)
  · exact (hGf.and hne).mono fun z hz => hz.1 ▸ hz.2

/-- The order arithmetic at an arc point. -/
theorem order_arith {e m k : ℕ} (he : 1 ≤ e) {n : ℤ}
    (h : (m : ℤ) * e + n = (k : ℤ) * e + ((e : ℤ) - 1)) :
    (e : ℤ) ∣ n + 1 ∧ ((e : ℤ) - 1 ≤ n → m ≤ k) := by
  refine ⟨⟨(k : ℤ) - m + 1, by linarith⟩, fun hn => ?_⟩
  have h1 : (m : ℤ) * e ≤ (k : ℤ) * e := by linarith
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  exact_mod_cast le_of_mul_le_mul_right h1 he'

/-- **K11 at arc points**, proved. -/
theorem k11Arc_holds : K11Arc N := by
  intro τ
  obtain ⟨hd, hdvr⟩ := arcStalk_isDiscreteValuationRing N τ
  obtain ⟨e, he, hscale⟩ := exists_ramification_index N τ
  refine ⟨e, he, fun A B F hB hF hFgerm => ?_⟩
  have het := chart_order_eq_ramification N τ e hscale
  let D := ComplexPoint.localEtaleCoordinates (curveC N) 1 (arcPoint N τ)
  let t := D.coordinateAlgHom (MvPolynomial.X 0)
  have hD : (arcPoint N τ).underlying ∈ D.neighborhood := D.mem
  -- representatives over the preimage of an affine open of the model
  obtain ⟨V₁, hV₁, h₁⟩ := exists_rep N A
  obtain ⟨V₂, hV₂, h₂⟩ := exists_rep N B
  obtain ⟨V₃, hV₃, h₃⟩ := exists_rep N (jC N)
  have hV₁₂ := nonempty_preirreducible_inter V₁.isOpen V₂.isOpen hV₁ hV₂
  obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (V₁ ⊓ V₂).isOpen V₃.isOpen hV₁₂ hV₃
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (x := y) (U := V₁ ⊓ V₂ ⊓ V₃) hy
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  let W : (curveC N).left.Opens := toModel N ⁻¹ᵁ U
  have hWV (V : (X0Model.curve N).Opens) (hV : (U : Set (X0Model.curve N)) ⊆ V) :
      W ≤ toModel N ⁻¹ᵁ V := fun x hx => hV hx
  obtain ⟨s, hs⟩ := h₁ W (hWV V₁ fun x hx => (hUV hx).1.1)
  obtain ⟨b, hb⟩ := h₂ W (hWV V₂ fun x hx => (hUV hx).1.2)
  obtain ⟨c, hc⟩ := h₃ W (hWV V₃ fun x hx => (hUV hx).2)
  obtain ⟨GA, hGA, hvA⟩ := hs.exists_continuation
  obtain ⟨GB, hGB, hvB⟩ := hb.exists_continuation
  obtain ⟨GJ, hGJ, hvJ⟩ := hc.exists_continuation
  have hWev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (arcPoint N (ofComplex z)).underlying ∈ W := by
    filter_upwards [eventually_complexPoint_mem_affine N U hU τ] with z hz
    show toModel N (arcPoint N (ofComplex z)).underlying ∈ U
    rw [toModel_underlying]
    exact hz trivial
  have hposev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), 0 < z.im :=
    nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  have hGBne : ∀ᶠ z in 𝓝[≠] (τ : ℂ), GB z ≠ 0 := eventually_ne_zero_of_germ (hGB τ) hB
  -- the open `R = W ∩ D(b) ∩ D.neighborhood` and a basic open `B₁ ⊆ R` of `D.neighborhood`
  let R : (curveC N).left.Opens := W ⊓ (curveC N).left.basicOpen b ⊓ D.neighborhood
  have hRev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), (arcPoint N (ofComplex z)).underlying ∈ R := by
    filter_upwards [hWev, hGBne, hposev, nhdsWithin_le_nhds (eventually_mem_of_mem N _ τ hD)]
      with z hzW hzB hzpos hzD
    refine ⟨⟨hzW, ?_⟩, hzD⟩
    apply (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero b _ hzW).mpr
    rw [(hvB _ hzW).2]
    have hcz : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hzpos]
    rw [hcz]
    exact hzB
  obtain ⟨z₁, hz₁⟩ := hRev.exists
  obtain ⟨g₁, hg₁R, hz₁g⟩ := D.isAffine.exists_basicOpen_le
    (⟨_, hz₁⟩ : R) hz₁.2
  let B₁ := (curveC N).left.basicOpen g₁
  have hB₁aff : IsAffineOpen B₁ := D.isAffine.basicOpen g₁
  have hB₁ne : (B₁ : Set (curveC N).left).Nonempty := ⟨_, hz₁g⟩
  have hB₁W : B₁ ≤ W := hg₁R.trans (inf_le_left.trans inf_le_left)
  have hB₁b : B₁ ≤ (curveC N).left.basicOpen b := hg₁R.trans (inf_le_left.trans inf_le_right)
  have hB₁D : B₁ ≤ D.neighborhood := (curveC N).left.basicOpen_le g₁
  have hB₁ev := eventually_arc_mem_open N B₁ hB₁ne τ
  let s₁ := resO hB₁W s
  let b₁ := resO hB₁W b
  let c₁ := resO hB₁W c
  let t₁ := resO hB₁D t
  have hb₁u : IsUnit b₁ := by
    have h := ((curveC N).left.toRingedSpace.isUnit_res_basicOpen b).map
      ((curveC N).left.presheaf.map (homOfLE hB₁b).op).hom
    have e₁ : b₁ = (curveC N).left.presheaf.map (homOfLE hB₁b).op
        ((curveC N).left.presheaf.map (homOfLE ((curveC N).left.basicOpen_le b)).op b) := by
      change resO hB₁W b = resO hB₁b (resO _ b)
      rw [resO_resO]
    rw [e₁]
    exact h
  obtain ⟨ct, hct, -⟩ := existsUnique_smul_coordDiff_basicOpen D g₁ hz₁g
    ((curveC N).hom.sectionsD B₁ c₁)
  have hdt : coordDiff D hB₁D = (curveC N).hom.sectionsD B₁ t₁ :=
    ((curveC N).hom.sectionsD_map hB₁D t).symm
  let u := hb₁u.unit
  let a : Γ((curveC N).left, B₁) := s₁ * ((u⁻¹ : Γ((curveC N).left, B₁)ˣ) : Γ((curveC N).left, B₁)) * ct
  have hba : b₁ * a = s₁ * ct := by
    have h1 : (u : Γ((curveC N).left, B₁)) = b₁ := hb₁u.unit_spec
    rw [← h1]
    simp only [a]
    rw [mul_comm s₁, mul_assoc, ← mul_assoc (u : Γ((curveC N).left, B₁)), Units.mul_inv, one_mul]
  have hB₁rep : b₁ • (a • coordDiff D hB₁D) = s₁ • (curveC N).hom.sectionsD B₁ c₁ := by
    rw [← smul_assoc, smul_eq_mul, hba, mul_smul, hct]
  -- the analytic identity `a(P z) · (t ∘ P)'(z) = F(z)` near `τ`
  have hFrel : ∀ᶠ z in 𝓝[≠] (τ : ℂ), F z * GB z = GA z * jDeriv z := by
    have h := congrArg (fun x => x * X0Model.meromorphicIncl (τ : ℂ) (fieldGermC N τ B)) hFgerm
    rw [← map_mul, mul_comm (ratGerm N τ A B), mul_assoc, ratGerm, div_mul_cancel₀ _ hB,
      map_mul, ← hGB τ, ← hGA τ] at h
    have h' : ((fun z => F z * GB z : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) =
        ((fun z => GA z * jDeriv z : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) := by
      rw [show (fun z => F z * GB z) = F * GB from rfl,
        show (fun z => GA z * jDeriv z) = GA * jDeriv from rfl, Germ.coe_mul, Germ.coe_mul, h]
      rw [mul_comm]
      rfl
    exact Germ.coe_eq.mp h'
  have hcore : ∀ᶠ z in 𝓝[≠] (τ : ℂ),
      arcEval N B₁ a z * deriv (arcEval N D.neighborhood t) z = F z := by
    filter_upwards [hB₁ev, hGBne, hFrel, hposev] with z hz hzB hzF hzpos
    have hcz : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hzpos]
    have hzW := hB₁W hz
    -- `c₁ ∘ P = j` near `z`
    have hcj : arcEval N B₁ c₁ =ᶠ[𝓝 z] jFun := by
      have hev := eventually_mem_of_mem N B₁ (ofComplex z) hz
      rw [hcz] at hev
      filter_upwards [hev, isOpen_upperHalfPlaneSet.mem_nhds hzpos] with w hw hwpos
      have hcw : ((ofComplex w : ℍ) : ℂ) = w := by rw [ofComplex_apply_of_im_pos hwpos]
      simp only [arcEval, c₁]
      rw [← Point.evaluate_res hB₁W c _ hw, (hvJ _ (hB₁W hw)).2]
      have := eq_of_germ_eq (hvJ _ (hB₁W hw)).1 (analyticAt_jFun (ofComplex w))
        ((hGJ (ofComplex w)).trans (fieldGermC_jC N (ofComplex w)))
      rw [hcw] at this ⊢
      exact this
    have htt : arcEval N B₁ t₁ =ᶠ[𝓝 z] arcEval N D.neighborhood t := by
      have hev := eventually_mem_of_mem N B₁ (ofComplex z) hz
      rw [hcz] at hev
      filter_upwards [hev] with w hw
      exact (Point.evaluate_res hB₁D t _ hw).symm
    have hexp := arc_expression_eq N hB₁aff 1 c₁ ct t₁
      (by rw [one_smul, ← hct, hdt]) (ofComplex z) hz
    rw [hcz, ← Point.evaluationHom_apply B₁ ⟨_, hz⟩, map_one, one_mul, hcj.deriv_eq,
      htt.deriv_eq] at hexp
    -- `a(P z) = GA z / GB z · ct(P z)`
    have hs₁ : Point.evaluate B₁ s₁ (arcPoint N (ofComplex z)) = GA z := by
      rw [← Point.evaluate_res hB₁W s _ hz, (hvA _ hzW).2, hcz]
    have hb₁ : Point.evaluate B₁ b₁ (arcPoint N (ofComplex z)) = GB z := by
      rw [← Point.evaluate_res hB₁W b _ hz, (hvB _ hzW).2, hcz]
    have hev : ∀ r r' : Γ((curveC N).left, B₁), Point.evaluate B₁ (r * r') (arcPoint N (ofComplex z)) =
        Point.evaluate B₁ r (arcPoint N (ofComplex z)) * Point.evaluate B₁ r' (arcPoint N (ofComplex z)) := by
      intro r r'
      rw [← Point.evaluationHom_apply B₁ ⟨_, hz⟩, map_mul, Point.evaluationHom_apply,
        Point.evaluationHom_apply]
    have hinv : Point.evaluate B₁ ((u⁻¹ : Γ((curveC N).left, B₁)ˣ) : Γ((curveC N).left, B₁))
        (arcPoint N (ofComplex z)) = (GB z)⁻¹ := by
      have h1 : Point.evaluate B₁ ((u⁻¹ : Γ((curveC N).left, B₁)ˣ) : Γ((curveC N).left, B₁))
          (arcPoint N (ofComplex z)) * Point.evaluate B₁ b₁ (arcPoint N (ofComplex z)) = 1 := by
        rw [← hev, ← hb₁u.unit_spec, Units.inv_mul, ← Point.evaluationHom_apply B₁ ⟨_, hz⟩,
          map_one]
      rw [hb₁] at h1
      exact eq_inv_of_mul_eq_one_left h1
    simp only [arcEval]
    rw [hev, hev, hs₁, hinv, mul_assoc, mul_assoc, ← hexp]
    change GA z * ((GB z)⁻¹ * jDeriv z) = F z
    rw [← mul_assoc, ← div_eq_mul_inv, div_mul_eq_mul_div, ← hzF, mul_div_cancel_right₀ _ hzB]
  -- the generic germ of `a` as a quotient of germs at `x`
  have hgenB₁ : genericPoint (curveC N).left ∈ B₁ := genericPoint_mem hz₁g
  let aK : (curveC N).left.functionField := (curveC N).left.presheaf.germ B₁ _ hgenB₁ a
  obtain ⟨uS, wS, hwS, huw⟩ := IsFractionRing.div_surjective
    (A := (curveC N).left.presheaf.stalk (arcPoint N τ).underlying) aK
  obtain ⟨U₁, hxU₁, ur, hur⟩ := TopCat.Presheaf.exists_germ_eq _ uS
  obtain ⟨U₂, hxU₂, wr, hwr⟩ := TopCat.Presheaf.exists_germ_eq _ wS
  have hkey : ∀ (U' : (curveC N).left.Opens) (hx : (arcPoint N τ).underlying ∈ U')
      (r : Γ((curveC N).left, U')),
      algebraMap ((curveC N).left.presheaf.stalk (arcPoint N τ).underlying)
        (curveC N).left.functionField ((curveC N).left.presheaf.germ U' _ hx r) =
        (curveC N).left.presheaf.germ U' (genericPoint (curveC N).left) (genericPoint_mem hx) r := by
    intro U' hx r
    change ((curveC N).left.presheaf.stalkSpecializes _) ((curveC N).left.presheaf.germ U' _ hx r) = _
    exact TopCat.Presheaf.germ_stalkSpecializes_apply (curveC N).left.presheaf hx _ r
  have hwS0 : wS ≠ 0 := nonZeroDivisors.ne_zero hwS
  have hwK : algebraMap ((curveC N).left.presheaf.stalk (arcPoint N τ).underlying)
      (curveC N).left.functionField wS ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hwS
  have hgerm_eq : (curveC N).left.presheaf.germ (U₂ ⊓ B₁) (genericPoint (curveC N).left)
      ⟨genericPoint_mem hxU₂, hgenB₁⟩ (resO inf_le_left wr * resO inf_le_right a) =
      (curveC N).left.presheaf.germ U₁ (genericPoint (curveC N).left) (genericPoint_mem hxU₁) ur := by
    have g₁ := TopCat.Presheaf.germ_res_apply (curveC N).left.presheaf
      (homOfLE (inf_le_left : U₂ ⊓ B₁ ≤ U₂)) (genericPoint (curveC N).left)
      ⟨genericPoint_mem hxU₂, hgenB₁⟩ wr
    have g₂ := TopCat.Presheaf.germ_res_apply (curveC N).left.presheaf
      (homOfLE (inf_le_right : U₂ ⊓ B₁ ≤ B₁)) (genericPoint (curveC N).left)
      ⟨genericPoint_mem hxU₂, hgenB₁⟩ a
    rw [map_mul, g₁, g₂, ← hkey U₂ hxU₂ wr, ← hkey U₁ hxU₁ ur, hwr, hur]
    change _ * aK = _
    rw [← huw]
    field_simp
  obtain ⟨V, hgenV, iV₁, iV₂, hVeq⟩ := TopCat.Presheaf.germ_eq _ _ _ _ _ _ hgerm_eq
  have hVne : (V : Set (curveC N).left).Nonempty := ⟨_, hgenV⟩
  -- the analytic relation `w(P z) F(z) = u(P z) (t ∘ P)'(z)` near `τ`
  let Wf := arcEval N U₂ wr
  let Uf := arcEval N U₁ ur
  let Tf := arcEval N D.neighborhood t
  have hfinal : (Wf * F) =ᶠ[𝓝[≠] (τ : ℂ)] (Uf * deriv Tf) := by
    filter_upwards [eventually_arc_mem_open N V hVne τ, hcore] with z hz hzc
    have h1 := congrArg (fun r => Point.evaluate V r (arcPoint N (ofComplex z))) hVeq
    have e₁ : iV₁ = homOfLE iV₁.le := Subsingleton.elim _ _
    have e₂ : iV₂ = homOfLE iV₂.le := Subsingleton.elim _ _
    rw [e₁, e₂] at h1
    rw [← Point.evaluate_res iV₁.le _ _ hz, ← Point.evaluate_res iV₂.le _ _ hz] at h1
    have hzUB : (arcPoint N (ofComplex z)).underlying ∈ U₂ ⊓ B₁ := iV₁.le hz
    rw [← Point.evaluationHom_apply _ ⟨_, hzUB⟩, map_mul, Point.evaluationHom_apply,
      Point.evaluationHom_apply, ← Point.evaluate_res inf_le_left wr _ hzUB,
      ← Point.evaluate_res inf_le_right a _ hzUB] at h1
    change arcEval N U₂ wr z * F z = arcEval N U₁ ur z * deriv (arcEval N D.neighborhood t) z
    rw [← hzc, ← mul_assoc]
    exact congrArg (· * deriv (arcEval N D.neighborhood t) z) h1
  -- orders at `τ`
  have hWan : AnalyticAt ℂ Wf (τ : ℂ) := arcEval_analyticAt N U₂ wr τ hxU₂
  have hUan : AnalyticAt ℂ Uf (τ : ℂ) := arcEval_analyticAt N U₁ ur τ hxU₁
  have hTan : AnalyticAt ℂ Tf (τ : ℂ) := arcEval_analyticAt N D.neighborhood t τ hD
  have het' : analyticOrderAt (fun z => Tf z -
      Point.evaluate D.neighborhood t (arcPoint N τ)) (τ : ℂ) = e := het
  have hTd1 : analyticOrderAt (deriv Tf) (τ : ℂ) + 1 = e := by
    rw [hTan.analyticOrderAt_deriv_add_one, ← het']
    congr 1
    funext z
    show Tf z - arcEval N D.neighborhood t τ = _
    rw [arcEval_coe]
  have hTd : analyticOrderAt (deriv Tf) (τ : ℂ) = ((e - 1 : ℕ) : ℕ∞) := by
    have hne : analyticOrderAt (deriv Tf) (τ : ℂ) ≠ ⊤ := by
      intro h; rw [h, top_add] at hTd1; exact ENat.top_ne_natCast e hTd1
    lift analyticOrderAt (deriv Tf) (τ : ℂ) to ℕ using hne with q hq
    have : q + 1 = e := by exact_mod_cast hTd1
    rw [← this, Nat.add_sub_cancel]
  have hwv : IsDiscreteValuationRing.addVal (arcStalk N τ) wS ≠ ⊤ :=
    (IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hwS0
  lift IsDiscreteValuationRing.addVal (arcStalk N τ) wS to ℕ using hwv with m hm
  have hWord : analyticOrderAt Wf (τ : ℂ) = ((e * m : ℕ) : ℕ∞) := by
    change analyticOrderAt (arcEval N U₂ wr) (τ : ℂ) = _
    rw [hscale U₂ hxU₂ wr, hwr, ← hm]
    push_cast; rfl
  have hmer := meromorphicOrderAt_congr hfinal
  rw [meromorphicOrderAt_mul hWan.meromorphicAt hF,
    meromorphicOrderAt_mul hUan.meromorphicAt hTan.deriv.meromorphicAt,
    hWan.meromorphicOrderAt_eq, hUan.meromorphicOrderAt_eq, hTan.deriv.meromorphicOrderAt_eq,
    hWord, hTd] at hmer
  have hUord : analyticOrderAt Uf (τ : ℂ) = (e : ℕ∞) * IsDiscreteValuationRing.addVal
      (arcStalk N τ) uS := by
    change analyticOrderAt (arcEval N U₁ ur) (τ : ℂ) = _
    rw [hscale U₁ hxU₁ ur, hur]
  -- regularity of the coefficient gives a local section representing `(A / B) · dj`
  have hfinish : IsRegularFunctionAt aK (arcPoint N τ).underlying →
      DiffRegularAt N (arcPoint N τ).underlying A B := by
    intro hreg
    let ω : RationalDifferential (curveC N) := ⟨B₁, hB₁ne, a • coordDiff D hB₁D⟩
    have hωreg : ω.RegularAt (arcPoint N τ).underlying :=
      (curveC_regularAt_iff N D ω hB₁D a rfl).mpr hreg
    obtain ⟨U', hxU', sU', V', hV'U', hV'ω, hV'ne, hsV'⟩ := hωreg
    refine ⟨U', hxU', sU', fun W'' hW'' s'' b'' c'' hs'' hb'' hc'' hbu'' => ?_⟩
    by_cases hne : (W'' : Set (curveC N).left).Nonempty
    · have hV''ne : ((W'' ⊓ V' : (curveC N).left.Opens) : Set (curveC N).left).Nonempty :=
        inter_nonempty hne hV'ne
      have h₁ : W'' ⊓ V' ≤ W'' := inf_le_left
      have h₂ : W'' ⊓ V' ≤ V' := inf_le_right
      have hVB : W'' ⊓ V' ≤ B₁ := h₂.trans hV'ω
      apply eq_of_resD_eq h₁ hV''ne
      have es : resO h₁ s'' = resO hVB s₁ :=
        (hs''.res N h₁).unique N ((hs.res N hB₁W).res N hVB)
      have eb : resO h₁ b'' = resO hVB b₁ :=
        (hb''.res N h₁).unique N ((hb.res N hB₁W).res N hVB)
      have ec : resO h₁ c'' = resO hVB c₁ :=
        (hc''.res N h₁).unique N ((hc.res N hB₁W).res N hVB)
      have hsec : resD h₁ (resD hW'' sU') = resD hVB (a • coordDiff D hB₁D) := by
        rw [resD_resD, show h₁.trans hW'' = h₂.trans hV'U' from rfl, ← resD_resD hV'U' h₂, hsV',
          resD_resD]
      have hB := congrArg (resD hVB) hB₁rep
      rw [resD_smul hVB b₁, resD_smul hVB s₁] at hB
      have hd₁ : resD h₁ ((curveC N).hom.sectionsD W'' c'') =
          (curveC N).hom.sectionsD (W'' ⊓ V') (resO h₁ c'') :=
        ((curveC N).hom.sectionsD_map h₁ c'').symm
      have hd₂ : resD hVB ((curveC N).hom.sectionsD B₁ c₁) =
          (curveC N).hom.sectionsD (W'' ⊓ V') (resO hVB c₁) :=
        ((curveC N).hom.sectionsD_map hVB c₁).symm
      rw [hd₂] at hB
      rw [resD_smul, resD_smul, hsec, eb, hd₁, es, ec]
      exact hB
    · exact relativeDifferentials_eq_of_empty N hne _ _
  by_cases hu0 : uS = 0
  · have haK : aK = 0 := by
      rw [← huw, hu0, map_zero, zero_div]
    have hUtop : analyticOrderAt Uf (τ : ℂ) = ⊤ := by
      rw [hUord, hu0, AddValuation.map_zero]
      exact ENat.mul_top (by exact_mod_cast (show e ≠ 0 by omega))
    have hFtop : meromorphicOrderAt F (τ : ℂ) = ⊤ := by
      rw [hUtop, ENat.map_top, top_add, ENat.map_natCast] at hmer
      exact (WithTop.add_eq_top.mp hmer).resolve_left WithTop.coe_ne_top
    refine ⟨fun n hn => ?_, fun _ => hfinish ?_⟩
    · rw [hFtop] at hn
      exact (WithTop.top_ne_coe hn).elim
    · rw [haK]
      exact (isRegularFunctionAt_iff _ _).mpr ⟨0, map_zero _⟩
  · lift IsDiscreteValuationRing.addVal (arcStalk N τ) uS to ℕ using
      (IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hu0 with k hk
    have hU' : analyticOrderAt Uf (τ : ℂ) = ((e * k : ℕ) : ℕ∞) := by
      rw [hUord]
      push_cast
      rfl
    rw [hU', ENat.map_natCast, ENat.map_natCast, ENat.map_natCast] at hmer
    have hFfin : meromorphicOrderAt F (τ : ℂ) ≠ ⊤ := by
      intro h
      rw [h, WithTop.add_top, ← WithTop.coe_add] at hmer
      exact WithTop.top_ne_coe hmer
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hFfin
    rw [← hn, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_inj] at hmer
    have harith := order_arith he (m := m) (k := k) (n := n) (by
      push_cast [Nat.cast_sub he] at hmer
      linarith)
    refine ⟨fun n' hn' => ?_, fun hle => hfinish ?_⟩
    · rw [← hn, WithTop.coe_inj] at hn'
      rw [← hn']
      exact harith.1
    · rw [← hn, WithTop.coe_le_coe] at hle
      have hmk := harith.2 hle
      have hdvd : wS ∣ uS := (IsDiscreteValuationRing.addVal_le_iff_dvd).mp (by
        rw [← hm, ← hk]
        exact_mod_cast hmk)
      obtain ⟨r, hr⟩ := hdvd
      refine (isRegularFunctionAt_iff _ _).mpr ⟨r, ?_⟩
      rw [← huw, hr, map_mul, mul_div_cancel_left₀ _ hwK]

/-- **Route B for `Γ₀(N)`, given only K11 at the cusps.** The native value `ω ↦ f_ω` is a
complex-linear equivalence between global relative differentials of the complexified modular
curve and weight-two cusp forms on `Γ₀(N)`, with inverse `Ψ`. -/
theorem routeB_linearEquiv_of_k11Cusp (h11c : K11Cusp N) :
    letI := differentialsModule N
    ∃ e : Γ((curveC N).hom.relativeDifferentials, ⊤) ≃ₗ[ℂ] CuspFormN N,
      (∀ ω τ, e ω τ = nativeValue N ω τ) ∧
        ∀ f, e.symm f = psi N (psiHypotheses N (k10_holds N) (k11Arc_holds N) h11c (k12_holds N)) f :=
  routeB_linearEquiv_of_points_regularity N (k10_holds N) (k11Arc_holds N) h11c (k12_holds N)

end ZInQ.Manuscript.RC.CuspFormDifferentials
