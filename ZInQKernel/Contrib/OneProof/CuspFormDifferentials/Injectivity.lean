import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.NativeValue
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.PointedCurve
import ZInQKernel.Contrib.OneProof.RC.X0Branch.Model

/-! K9: a global relative differential of the complexified modular curve whose native
value vanishes identically on the upper half-plane is zero.

The argument. The curve is geometrically integral (it has a rational point), so its
complexification is integral, and a differential vanishing on one nonempty open vanishes.
Write `ω = a · dt` near `P i` in local étale coordinates. A nonzero regular function on
such a neighbourhood has finitely many complex zeros (the coordinate ring is quasi-finite
over a polynomial ring in one variable, hence of dimension at most one), while the fibres
of `τ ↦ P τ` are `Γ₀(N)`-orbits, hence countable, so `P` maps no open set of parameters
into a finite set. Near `i` one has `f_ω = (a ∘ P) · (t ∘ P)′`; analyticity forces either
`a ∘ P` or `(t ∘ P)′` to vanish near `i`, and both alternatives put `P` of an open set
into a finite zero set. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane
open scoped Topology Manifold

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open J0Cusps

/-! ### Smooth complex curves -/

section Curve

variable {X : Over (Spec (CommRingCat.of ℂ))} [SmoothOfRelativeDimension 1 X.hom]

omit [SmoothOfRelativeDimension 1 X.hom] in
/-- Constants evaluate to themselves. -/
theorem evaluate_specStructureMap_eq {U : X.left.Opens} (c : ℂ) (q : ComplexPoint X)
    (hq : q.underlying ∈ U) :
    Point.evaluate U (X.hom.specStructureMap U c) q = c := by
  let : Algebra ℂ Γ(X.left, U) := (X.hom.specStructureMap U).hom.toAlgebra
  exact (ComplexPoint.sectionEvaluationAlgHom_apply U q hq _).symm.trans
    ((ComplexPoint.sectionEvaluationAlgHom U q hq).commutes c)

omit [SmoothOfRelativeDimension 1 X.hom] in
theorem evaluate_sub_eq {U : X.left.Opens} (a b : Γ(X.left, U)) (q : ComplexPoint X)
    (hq : q.underlying ∈ U) :
    Point.evaluate U (a - b) q = Point.evaluate U a q - Point.evaluate U b q := by
  rw [← Point.evaluationHom_apply U ⟨q, hq⟩, ← Point.evaluationHom_apply U ⟨q, hq⟩,
    ← Point.evaluationHom_apply U ⟨q, hq⟩, map_sub]

/-- The coordinate ring of an étale coordinate neighbourhood has dimension at most one. -/
theorem ringKrullDim_etaleNeighborhood_le_one {x : X.left} (D : LocalEtaleCoordinates X 1 x) :
    ringKrullDim Γ(X.left, D.neighborhood) ≤ 1 := by
  let := (D.coordinateAlgHom : MvPolynomial (Fin 1) ℂ →+* Γ(X.left, D.neighborhood)).toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin 1) ℂ) Γ(X.left, D.neighborhood) := D.etale
  calc ringKrullDim Γ(X.left, D.neighborhood) ≤ ringKrullDim (MvPolynomial (Fin 1) ℂ) :=
        Algebra.QuasiFinite.ringKrullDim_le
    _ = 1 := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        simp

/-- In a domain of dimension at most one, every prime containing a nonzero element is
minimal over it. -/
theorem mem_minimalPrimes_span_of_dim_le_one {A : Type*} [CommRing A] [IsDomain A]
    (hA : ringKrullDim A ≤ 1) {g : A} (hg : g ≠ 0) (P : Ideal A) [P.IsPrime] (hgP : g ∈ P) :
    P ∈ (Ideal.span {g}).minimalPrimes := by
  refine ⟨⟨‹_›, (Ideal.span_singleton_le_iff_mem _).2 hgP⟩, fun Q ⟨hQ, hgQ⟩ hQP => ?_⟩
  by_contra hne
  have hlt : Q < P := lt_of_le_of_ne hQP (fun h => hne (h ▸ le_rfl))
  have hP1 : P.height ≤ 1 := by
    have := (Ideal.height_le_ringKrullDim_of_isPrime (I := P)).trans hA
    exact_mod_cast this
  have hQfin : Q.FiniteHeight := by
    refine ⟨Or.inr ?_⟩
    exact ne_top_of_le_ne_top (by simp)
      ((Ideal.height_mono hQP).trans hP1)
  have h1 : Q.height < 1 := (Ideal.height_strict_mono_of_isPrime hlt).trans_le hP1
  have h0 : Q.height = 0 := Order.lt_one_iff.1 h1
  rw [Ideal.height_eq_zero_iff_eq_bot] at h0
  apply hg
  have : Ideal.span {g} ≤ ⊥ := h0 ▸ hgQ
  simpa using this

/-- A nonzero regular function on an étale coordinate neighbourhood of an integral smooth
complex curve has finitely many complex zeros. -/
theorem finite_zeros_etaleNeighborhood [IsIntegral X.left] {x : X.left}
    (D : LocalEtaleCoordinates X 1 x) (g : Γ(X.left, D.neighborhood)) (hg : g ≠ 0) :
    {p : ComplexPoint X | p.underlying ∈ D.neighborhood ∧
      Point.evaluate D.neighborhood g p = 0}.Finite := by
  have : Nonempty D.neighborhood := ⟨⟨x, D.mem⟩⟩
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hU := D.isAffine
  have : IsNoetherianRing Γ(X.left, D.neighborhood) :=
    IsLocallyNoetherian.component_noetherian ⟨D.neighborhood, hU⟩
  let M := (Ideal.span {g}).minimalPrimes
  have hM : M.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hM' : {P : PrimeSpectrum Γ(X.left, D.neighborhood) | P.asIdeal ∈ M}.Finite :=
    hM.preimage (fun P _ Q _ h => PrimeSpectrum.ext h)
  let S := (fun P => hU.fromSpec P) '' {P : PrimeSpectrum Γ(X.left, D.neighborhood) |
    P.asIdeal ∈ M}
  have hS : S.Finite := hM'.image _
  have hinj : Function.Injective (fun p : ComplexPoint X => p.underlying) := by
    intro p q h
    apply (ZInQ.Contrib.CloudB3W17bOkaComparison.nativePointClosedEquiv X).injective
    apply Subtype.ext
    rw [ZInQ.Contrib.CloudB3W17bOkaComparison.nativePointClosedEquiv_val,
      ZInQ.Contrib.CloudB3W17bOkaComparison.nativePointClosedEquiv_val]
    exact h
  refine (hS.preimage hinj.injOn).subset ?_
  rintro p ⟨hp, hz⟩
  let y : D.neighborhood := ⟨p.underlying, hp⟩
  refine ⟨hU.primeIdealOf y, ?_, hU.fromSpec_primeIdealOf y⟩
  have hnot : p.underlying ∉ X.left.basicOpen g := fun hb =>
    ((Point.mem_overOpen_basicOpen_iff_isUnit_evaluate g p hp).1 hb).ne_zero hz
  have hgP : g ∈ (hU.primeIdealOf y).asIdeal := by
    by_contra hgn
    apply hnot
    have hmem : hU.primeIdealOf y ∈ hU.fromSpec ⁻¹ᵁ X.left.basicOpen g := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hgn
    have h2 : hU.fromSpec (hU.primeIdealOf y) ∈ X.left.basicOpen g := hmem
    rw [hU.fromSpec_primeIdealOf] at h2
    exact h2
  exact mem_minimalPrimes_span_of_dim_le_one (ringKrullDim_etaleNeighborhood_le_one D) hg _ hgP

/-- The coordinate of an étale chart is not constant. -/
theorem coordinate_sub_const_ne_zero {x : X.left} (D : LocalEtaleCoordinates X 1 x)
    [Nontrivial Γ(X.left, D.neighborhood)] (c : ℂ) :
    D.coordinateAlgHom (MvPolynomial.X 0) - X.hom.specStructureMap D.neighborhood c ≠ 0 := by
  intro h
  have ht := sub_eq_zero.1 h
  have hd : X.hom.sectionsD D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0)) = 0 := by
    rw [ht]
    exact Scheme.Hom.sectionsD_specStructureMap _ _ _
  obtain ⟨a, -, huniq⟩ := D.existsUnique_smul_sectionsD
    (X.hom.sectionsD D.neighborhood (D.coordinateAlgHom (MvPolynomial.X 0)))
  have h1 := huniq 1 (one_smul _ _)
  have h0 := huniq 0 (by
    show (0 : Γ(X.left, D.neighborhood)) • _ = _
    rw [zero_smul, hd])
  exact one_ne_zero (h1.trans h0.symm)

/-- On an integral smooth complex curve, a global differential whose restriction to one
étale coordinate neighbourhood vanishes is zero. -/
theorem eq_zero_of_restrict_etaleNeighborhood_eq_zero [IsIntegral X.left]
    (ω : Γ(X.hom.relativeDifferentials, ⊤)) {x : X.left} (D : LocalEtaleCoordinates X 1 x)
    (h0 : X.hom.relativeDifferentials.presheaf.map
      (homOfLE (le_top : D.neighborhood ≤ ⊤)).op ω = 0) :
    ω = 0 := by
  let T := X.hom.relativeDifferentials
  let E (y : X.left) := AlgebraicGeometry.localEtaleCoordinates X 1 y
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨T.presheaf, T.isSheaf⟩
    (fun y => (E y).neighborhood) ⊤ (fun _ => homOfLE le_top)
    (fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, (E y).mem⟩) ω 0 fun y => ?_
  obtain ⟨a, ha, -⟩ := (E y).existsUnique_smul_sectionsD
    (T.presheaf.map (homOfLE le_top).op ω)
  suffices hz : a = 0 by rw [map_zero, ← ha, hz, zero_smul]
  obtain ⟨z, hzE, hzD⟩ : ((E y).neighborhood ∩ D.neighborhood : Set X.left).Nonempty :=
    nonempty_preirreducible_inter (E y).neighborhood.isOpen D.neighborhood.isOpen
      ⟨y, (E y).mem⟩ ⟨x, D.mem⟩
  obtain ⟨s, hs, hzW⟩ := (E y).isAffine.exists_basicOpen_le
    (⟨z, hzE, hzD⟩ : ↥((E y).neighborhood ⊓ D.neighborhood)) hzE
  let W := X.left.basicOpen s
  let B := (E y).restrictBasicOpen s hzW
  have hE : W ≤ (E y).neighborhood := X.left.basicOpen_le s
  have hD : W ≤ D.neighborhood := hs.trans inf_le_right
  let aW := X.left.presheaf.map (homOfLE hE).op a
  let η := X.hom.sectionsD W (B.coordinateAlgHom (MvPolynomial.X 0))
  have hAW : aW • η = T.presheaf.map (homOfLE le_top).op ω :=
    ComplexPoint.restrict_differential_expression ω hE _ _ ha
  have hω : T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ω = 0 := by
    have : T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ω =
        T.presheaf.map (homOfLE hD).op
          (T.presheaf.map (homOfLE (le_top : D.neighborhood ≤ ⊤)).op ω) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [this, h0, map_zero]
  have hz0 : (0 : Γ(X.left, W)) • η = T.presheaf.map (homOfLE le_top).op ω := by
    rw [zero_smul, hω]
  have haW : aW = 0 := (B.existsUnique_smul_sectionsD _).unique hAW hz0
  have : Nonempty W := ⟨⟨z, hzW⟩⟩
  exact map_injective_of_isIntegral X.left (homOfLE hE) (by rw [map_zero]; exact haW)

end Curve

/-! ### The complexified modular curve -/

variable (N : ℕ) [NeZero N]

/-- The complexified modular curve is integral: the model is geometrically integral,
being smooth, proper and integral with a rational point. -/
instance isIntegral_curveC : IsIntegral (curveC N).left := by
  have : IsIntegral (source N).left := X0Model.integral N
  have : IsProper (source N).hom := X0Model.proper N
  have := model_smooth_one N
  have : GeometricallyConnected (source N).hom :=
    (isCurve_of_point (source N)
      (rationalPoint (X := source N) (X0Model.cusp N) (X0Model.cusp_overQ N))).geomConnected
  have : Smooth (source N).hom := SmoothOfRelativeDimension.smooth 1 _
  have : GeometricallyIntegral (source N).hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral _
  change IsIntegral
    (Limits.pullback (source N).hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
  infer_instance

theorem complexPoint_eq_of_arcPoint_eq {τ σ : ℍ} (h : arcPoint N τ = arcPoint N σ) :
    X0Model.complexPoint N τ = X0Model.complexPoint N σ := by
  have e (υ : ℍ) : (arcPoint N υ).left ≫ Limits.pullback.fst _ _ =
      X0Model.complexPoint N υ :=
    Limits.pullback.lift_fst _ _ _
  rw [← e τ, ← e σ, h]

/-- The fibres of `τ ↦ P τ` are countable: they lie in `Γ₀(N)`-orbits. -/
theorem countable_arcPoint_fiber (p : ComplexPoint (curveC N)) :
    {τ : ℍ | arcPoint N τ = p}.Countable := by
  rcases Set.eq_empty_or_nonempty {τ : ℍ | arcPoint N τ = p} with h | ⟨τ₀, hτ₀⟩
  · rw [h]
    exact Set.countable_empty
  · have : Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
      Function.Injective.countable (β := Fin 2 → Fin 2 → ℤ)
        (f := fun g : Matrix.SpecialLinearGroup (Fin 2) ℤ => g.1) Subtype.val_injective
    refine (Set.countable_range
      (fun g : Matrix.SpecialLinearGroup (Fin 2) ℤ => g • τ₀)).mono ?_
    intro σ hσ
    obtain ⟨γ, -, hγ⟩ := (X0Branch.complexPoint_eq_iff N τ₀ σ).1
      (complexPoint_eq_of_arcPoint_eq N (hτ₀.trans hσ.symm))
    exact ⟨γ, hγ⟩

/-- `τ ↦ P τ` maps no neighbourhood of a parameter into a finite set. -/
theorem not_eventually_arcPoint_mem_finite (τ₀ : ℍ) {S : Set (ComplexPoint (curveC N))}
    (hS : S.Finite) : ¬ ∀ᶠ z in 𝓝 (τ₀ : ℂ), arcPoint N (ofComplex z) ∈ S := by
  intro h
  have h' : ∀ᶠ z in 𝓝 (τ₀ : ℂ), 0 < z.im ∧ arcPoint N (ofComplex z) ∈ S :=
    Filter.Eventually.and (((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      τ₀.im_pos) : ∀ᶠ z in 𝓝 (τ₀ : ℂ), 0 < z.im) h
  obtain ⟨U, hUsub, hUo, hU0⟩ := mem_nhds_iff.1 h'
  have hc : U.Countable := by
    have hsub : U ⊆ (fun τ : ℍ => (τ : ℂ)) '' ⋃ p ∈ S, {τ : ℍ | arcPoint N τ = p} := by
      intro z hz
      obtain ⟨him, hmem⟩ := hUsub hz
      refine ⟨ofComplex z, Set.mem_iUnion₂.2 ⟨_, hmem, rfl⟩, ?_⟩
      rw [ofComplex_apply_of_im_pos him]
    exact ((hS.countable.biUnion fun p _ => countable_arcPoint_fiber N p).image _).mono hsub
  exact (hUo.measure_ne_zero MeasureTheory.volume ⟨_, hU0⟩) (hc.measure_zero _)

/-- K9: if the native value of a global relative differential vanishes at every point of
the upper half-plane, the differential is zero. -/
theorem eq_zero_of_nativeValue_eq_zero (ω : Γ((curveC N).hom.relativeDifferentials, ⊤))
    (h : ∀ τ : ℍ, nativeValue N ω τ = 0) : ω = 0 := by
  let τ₀ : ℍ := UpperHalfPlane.I
  let D := localEtaleCoordinates (curveC N) 1 (arcPoint N τ₀).underlying
  have hp : (arcPoint N τ₀).underlying ∈ D.neighborhood := D.mem
  have : Nonempty D.neighborhood := ⟨⟨_, hp⟩⟩
  obtain ⟨a, ha, -⟩ := D.existsUnique_smul_sectionsD
    ((curveC N).hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω)
  by_cases ha0 : a = 0
  · exact eq_zero_of_restrict_etaleNeighborhood_eq_zero ω D (by rw [← ha, ha0, zero_smul])
  exfalso
  let t := D.coordinateAlgHom (MvPolynomial.X 0)
  obtain ⟨hmem, hA⟩ := arcPoint_evaluate N D.neighborhood a τ₀ hp
  have hT := (arcPoint_evaluate N D.neighborhood t τ₀ hp).2
  let T : ℂ → ℂ := fun z => Point.evaluate D.neighborhood t (arcPoint N (ofComplex z))
  have hmemC : ∀ᶠ z in 𝓝 (τ₀ : ℂ),
      (arcPoint N (ofComplex z)).underlying ∈ D.neighborhood :=
    eventually_ofComplex hmem
  have hprod : ∀ᶠ z in 𝓝 (τ₀ : ℂ),
      Point.evaluate D.neighborhood a (arcPoint N (ofComplex z)) * deriv T z = 0 := by
    filter_upwards [hmemC, eventuallyEq_coe_comp_ofComplex τ₀.im_pos] with z hz hcz
    have hcz' : ((ofComplex z : ℍ) : ℂ) = z := hcz
    have := nativeValue_eq_of_expression N ω a t ha (ofComplex z) hz
    rw [h, hcz'] at this
    exact this.symm
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with hA0 | hAne
  · apply not_eventually_arcPoint_mem_finite N τ₀ (finite_zeros_etaleNeighborhood D a ha0)
    filter_upwards [hmemC, hA0] with z hz hz0
    exact ⟨hz, hz0⟩
  rcases hT.deriv.eventually_eq_zero_or_eventually_ne_zero with hT0 | hTne
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1
      (hT0.and (hT.eventually_analyticAt.and hmemC))
    have hconst : ∀ z ∈ Metric.ball (τ₀ : ℂ) r, T z = T τ₀ := fun z hz =>
      IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball _ _).isPreconnected
        (fun w hw => (hball w hw).2.1.differentiableAt.differentiableWithinAt)
        (fun w hw => (hball w hw).1) hz (Metric.mem_ball_self hr)
    let k := (curveC N).hom.specStructureMap D.neighborhood (T τ₀)
    apply not_eventually_arcPoint_mem_finite N τ₀
      (finite_zeros_etaleNeighborhood D (t - k) (coordinate_sub_const_ne_zero D (T τ₀)))
    filter_upwards [Metric.ball_mem_nhds _ hr] with z hz
    refine ⟨(hball z hz).2.2, ?_⟩
    rw [evaluate_sub_eq _ _ _ (hball z hz).2.2, evaluate_specStructureMap_eq _ _ (hball z hz).2.2]
    exact sub_eq_zero.2 (hconst z hz)
  · obtain ⟨z, ⟨h1, h2⟩, h3⟩ := ((hAne.and hTne).and (hprod.filter_mono nhdsWithin_le_nhds)).exists
    exact mul_ne_zero h1 h2 h3

/-- K9 in function form: `f_ω = 0` on `ℍ` implies `ω = 0`. -/
theorem eq_zero_of_nativeValue_fun_eq_zero (ω : Γ((curveC N).hom.relativeDifferentials, ⊤))
    (h : nativeValue N ω = 0) : ω = 0 :=
  eq_zero_of_nativeValue_eq_zero N ω (fun τ => congrFun h τ)

/-- K9 as injectivity of the `ℂ`-linear native value map. -/
theorem nativeValueLinear_injective :
    letI := differentialsModule N
    Function.Injective (nativeValueLinear N) := by
  intro ω ω' h
  have h0 : nativeValue N (ω - ω') = 0 := by
    rw [← nativeValueLinear_apply, map_sub, h, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_nativeValue_fun_eq_zero N _ h0)

end ZInQ.Manuscript.RC.CuspFormDifferentials
