import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Core
import ZInQKernel.Contrib.OneProof.RC.X0Model.Section
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-! The analytic point map `τ ↦ P τ` of the complexified modular curve is holomorphic.
Near each parameter the point factors through the complex base change of one affine
open of the model, so every regular function evaluated along the map is a quotient of
complex combinations of the meromorphic continuations of regular sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter ModularCurve ShimuraPointDict PkgI3 UpperHalfPlane
open scoped Topology Manifold TensorProduct

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open J0Cusps

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

variable (N : ℕ) [NeZero N]

/-! ### Eventual membership of the analytic points in an affine open -/

private theorem arc_preimage_top_comp {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B]
    (u : Spec (.of A) ⟶ X) (f : Spec (.of B) ⟶ Spec (.of A)) (U : X.Opens)
    (h : ⊤ ≤ u ⁻¹ᵁ U) : ⊤ ≤ (f ≫ u) ⁻¹ᵁ U :=
  fun x _ => by rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply]; exact h trivial

private def arcSectionField (U : (X0Model.curve N).Opens) [Nonempty U] :
    Γ(X0Model.curve N, U) →+* modularFunctionField N :=
  (X0Model.functionField N).toRingHom.comp ((X0Model.curve N).germToFunctionField U).hom

private def arcInteriorSection (U : (X0Model.curve N).Opens) [Nonempty U]
    (τ : UpperHalfPlane) : Γ(X0Model.curve N, U) →+* X0Model.MeromorphicGerm (τ : ℂ) :=
  (X0Model.fieldGerm N τ).comp (arcSectionField N U)

private theorem arc_regular_interiorSection (U : (X0Model.curve N).Opens)
    [Nonempty U] (r : Γ(X0Model.curve N, U)) (τ : UpperHalfPlane) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f (τ : ℂ))
    (he : (f : PuncturedGerm (τ : ℂ)) =
      X0Model.meromorphicIncl (τ : ℂ) (arcInteriorSection N U τ r)) :
    arcInteriorSection N U τ r ∈ X0Model.meromorphicValuation (τ : ℂ) :=
  ⟨f τ, he ▸ hasValue_coe.mpr (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)⟩

private theorem arc_chart_mem_of_regular (U : (X0Model.curve N).Opens)
    [Nonempty U] (hU : IsAffineOpen U) (τ : UpperHalfPlane)
    (h : ∀ r, arcInteriorSection N U τ r ∈ X0Model.meromorphicValuation (τ : ℂ))
    (hg : ⊤ ≤ (X0Model.genericMap N (X0Model.fieldGerm N τ)) ⁻¹ᵁ U) :
    ⊤ ≤ (X0Model.complexPoint N τ) ⁻¹ᵁ U := by
  let R := X0Model.meromorphicValuation (τ : ℂ)
  let F := X0Model.MeromorphicGerm (τ : ℂ)
  let g := (arcInteriorSection N U τ).codRestrict R.toSubring h
  let u := Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec
  have hu : ⊤ ≤ u ⁻¹ᵁ U := by
    intro z _
    rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply]
    change _ ∈ (U : Set (X0Model.curve N))
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self _
  have he : Spec.map (CommRingCat.ofHom (algebraMap R F)) ≫ u =
      X0Model.genericMap N (X0Model.fieldGerm N τ) := by
    calc
      _ = Spec.map (X0Model.sectionMap (X0Model.genericMap N (X0Model.fieldGerm N τ)) U hg) ≫
            hU.fromSpec := by
        change Spec.map _ ≫ Spec.map (CommRingCat.ofHom g) ≫ _ = _
        rw [← Category.assoc, ← Spec.map_comp, X0Model.sectionMap_generic]
        rfl
      _ = _ := sectionMap_factor _ hU hg
  let ι : ℚ →+* R :=
    ((X0Model.constantGerm (τ : ℂ)).comp (Rat.castHom ℂ)).codRestrict R.toSubring
      fun c => ⟨(c : ℂ), hasValue_coe.mpr tendsto_const_nhds⟩
  let : Algebra ℚ R := ι.toAlgebra
  obtain ⟨v, _, huniq⟩ :=
    X0Model.existsUnique_specialization (R := R) N (X0Model.fieldGerm N τ)
  have hu' : u = X0Model.analyticArc N τ :=
    (huniq u ⟨he, maps_to_rat_unique _ _⟩).trans
      (huniq _ ⟨X0Model.analyticArc_generic N τ, maps_to_rat_unique _ _⟩).symm
  rw [X0Model.complexPoint, ← hu']
  exact arc_preimage_top_comp u _ U hu

private theorem arc_eventually_chart_mem (U : (X0Model.curve N).Opens)
    [Nonempty U] (hU : IsAffineOpen U) {I : Type} {F : Filter I}
    (x : I → UpperHalfPlane)
    (h : ∀ r, ∀ᶠ i in F,
      arcInteriorSection N U (x i) r ∈ X0Model.meromorphicValuation (x i : ℂ))
    (hg : ∀ i, ⊤ ≤ (X0Model.genericMap N (X0Model.fieldGerm N (x i))) ⁻¹ᵁ U) :
    ∀ᶠ i in F, ⊤ ≤ (X0Model.complexPoint N (x i)) ⁻¹ᵁ U := by
  classical
  let A := Γ(X0Model.curve N, U)
  let hf : LocallyOfFiniteType (X0Model.overQ N) := (X0Model.proper N).toLocallyOfFiniteType
  let α : ℚ →+* A :=
    ((Scheme.ΓSpecIso (.of ℚ)).inv ≫ (X0Model.overQ N).appLE ⊤ U (by simp)).hom
  let := α.toAlgebra
  have hα : α.FiniteType :=
    ((X0Model.overQ N).finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (RingHom.FiniteType.of_surjective _
        ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of ℚ)).inv).2))
  have hfin : Algebra.FiniteType ℚ A := hα
  obtain ⟨S, hS⟩ := hfin.out
  filter_upwards [(eventually_all_finset S).2 fun r _ => h r] with i hi
  apply arc_chart_mem_of_regular N U hU (x i) _ (hg i)
  let B : Subalgebra ℚ A :=
    { toSubsemiring := ((X0Model.meromorphicValuation (x i : ℂ)).toSubring.comap
        (arcInteriorSection N U (x i))).toSubsemiring
      algebraMap_mem' := fun q => by
        change arcInteriorSection N U (x i) (α q) ∈ X0Model.meromorphicValuation (x i : ℂ)
        have e : (arcInteriorSection N U (x i)).comp α =
            (X0Model.constantGerm (x i : ℂ)).comp (Rat.castHom ℂ) := Subsingleton.elim _ _
        change ((arcInteriorSection N U (x i)).comp α) q ∈ _
        rw [e]
        exact ⟨(q : ℂ), hasValue_coe.mpr tendsto_const_nhds⟩ }
  have hle : Algebra.adjoin ℚ (S : Set A) ≤ B := Algebra.adjoin_le fun r hr => hi r hr
  rw [hS] at hle
  exact fun r => hle (show r ∈ (⊤ : Subalgebra ℚ A) from trivial)

private theorem arc_generic_hits_open (U : (X0Model.curve N).Opens)
    [Nonempty U] {K : Type} [Field K] (e : modularFunctionField N →+* K) :
    ⊤ ≤ (X0Model.genericMap N e) ⁻¹ᵁ U := by
  intro z _
  have hz : X0Model.genericMap N e z = genericPoint (X0Model.curve N) := by
    rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
    dsimp only [X0Model.genericMap]
    erw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  change X0Model.genericMap N e z ∈ U
  rw [hz]
  exact ((genericPoint_spec (X0Model.curve N)).mem_open_set_iff U.isOpen).mpr
    (by rw [Set.univ_inter]; exact Set.nonempty_coe_sort.mp ‹Nonempty U›)

/-- Membership of the analytic point in an affine open of the model is an open
condition on the parameter. -/
theorem eventually_complexPoint_mem (U : (X0Model.curve N).Opens) (hU : IsAffineOpen U)
    (τ₀ : ℍ) (h₀ : ⊤ ≤ (X0Model.complexPoint N τ₀) ⁻¹ᵁ U) :
    ∀ᶠ τ in 𝓝 τ₀, ⊤ ≤ (X0Model.complexPoint N τ) ⁻¹ᵁ U := by
  have hmem : X0Model.complexPoint N τ₀ (default : Spec (.of ℂ)) ∈ U := h₀ trivial
  have : Nonempty U := ⟨⟨_, hmem⟩⟩
  apply arc_eventually_chart_mem N U hU (F := 𝓝 τ₀) id _
    (fun τ => arc_generic_hits_open N U _)
  intro r
  obtain ⟨g, -, hgerm, hval⟩ := X0Model.sectionMeromorphicContinuation N U r
  have han := (hval τ₀ hmem).1
  have hev : ∀ᶠ τ : ℍ in 𝓝 τ₀, AnalyticAt ℂ g (τ : ℂ) :=
    (continuous_coe.tendsto τ₀).eventually han.eventually_analyticAt
  exact hev.mono fun τ hτ => arc_regular_interiorSection N U r τ hτ (hgerm τ)

/-! ### Transferring eventual statements between `ℍ` and `ℂ` -/

theorem eventually_ofComplex {P : ℍ → Prop} {τ₀ : ℍ} (h : ∀ᶠ τ in 𝓝 τ₀, P τ) :
    ∀ᶠ z in 𝓝 (τ₀ : ℂ), P (ofComplex z) := by
  have hc : ContinuousAt ofComplex (τ₀ : ℂ) :=
    (contMDiffAt_ofComplex (n := 1) τ₀.im_pos).continuousAt
  have ht : Tendsto ofComplex (𝓝 (τ₀ : ℂ)) (𝓝 τ₀) := by
    simpa only [ofComplex_apply] using hc.tendsto
  exact ht.eventually h

theorem eventually_coe {P : ℂ → Prop} {τ₀ : ℍ} (h : ∀ᶠ z in 𝓝 (τ₀ : ℂ), P z) :
    ∀ᶠ τ : ℍ in 𝓝 τ₀, P (τ : ℂ) :=
  (continuous_coe.tendsto τ₀).eventually h

/-! ### Factorization through an affine base change -/

section Affine

variable {A : Type} [CommRing A] [Algebra ℚ A]

private def arcSpecPoint (f : A →+* ℂ) :
    AbVar.ptObj (K := ℚ) ℂ ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ A))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f)) (maps_to_rat_unique _ _)

private def arcTensorMap (f : A →+* ℂ) : ℂ ⊗[ℚ] A →ₐ[ℂ] ℂ :=
  AlgHom.liftEquiv ℚ ℂ A ℂ
    { toRingHom := f
      commutes' := fun r => DFunLike.congr_fun
        (Subsingleton.elim (f.comp (algebraMap ℚ A)) (algebraMap ℚ ℂ)) r }

private theorem arcTensorMap_tmul (f : A →+* ℂ) (c : ℂ) (a : A) :
    arcTensorMap f (c ⊗ₜ[ℚ] a) = c * f a := by
  simp [arcTensorMap]

private def arcTensorProjection :
    Over.mk (ComplexPoint.affineSpecStructureMap (ℂ ⊗[ℚ] A)) ⟶
      complexBaseChange.obj (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ A)))) :=
  Over.homMk
    (Limits.pullback.lift
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] ℂ ⊗[ℚ] A).toRingHom))
      (ComplexPoint.affineSpecStructureMap (ℂ ⊗[ℚ] A))
      (maps_to_rat_unique _ _))
    (Limits.pullback.lift_snd _ _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem arcTensorPoint_eq (f : A →+* ℂ) :
    Point.map (arcTensorProjection (A := A))
      ((ComplexPoint.affineSpecEquiv (ℂ ⊗[ℚ] A)).symm (arcTensorMap f)) =
        complexLift (arcSpecPoint f) := by
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · simp only [Point.map, Over.comp_left, arcTensorProjection, Over.homMk_left,
      complexLift, Category.assoc, Limits.pullback.lift_fst, arcSpecPoint]
    change Spec.map (CommRingCat.ofHom (arcTensorMap f).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] ℂ ⊗[ℚ] A).toRingHom) =
      Spec.map (CommRingCat.ofHom f)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    change arcTensorMap f ((1 : ℂ) ⊗ₜ[ℚ] a) = f a
    simp [arcTensorMap]
  · exact Over.w _ |>.trans (Over.w _).symm

end Affine

/-! ### Regular functions along the analytic point map -/

/-- Every regular function on an open of the complexified curve, evaluated along the
analytic point map, is holomorphic near each parameter whose point lies in the open,
and the points of nearby parameters lie in the open too. -/
theorem arcPoint_evaluate (V : (curveC N).left.Opens) (s : Γ((curveC N).left, V)) (τ₀ : ℍ)
    (h : (arcPoint N τ₀).underlying ∈ V) :
    (∀ᶠ τ in 𝓝 τ₀, (arcPoint N τ).underlying ∈ V) ∧
      AnalyticAt ℂ (fun z : ℂ => Point.evaluate V s (arcPoint N (ofComplex z))) (τ₀ : ℂ) := by
  classical
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := X0Model.complexPoint N τ₀ (default : Spec (.of ℂ))) (U := ⊤) trivial
  have h₀ : ⊤ ≤ (X0Model.complexPoint N τ₀) ⁻¹ᵁ U := by
    intro x _
    rwa [Subsingleton.elim x (default : Spec (.of ℂ))]
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have hev := eventually_complexPoint_mem N U hU τ₀ h₀
  let A := Γ(X0Model.curve N, U)
  let := (show ℚ →+* A from
    (Spec.homEquiv (hU.fromSpec ≫ (source N).hom)).hom).toAlgebra
  let k : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ A))) ⟶ source N :=
    Over.homMk hU.fromSpec (Spec.map_preimage _).symm
  let R := ℂ ⊗[ℚ] A
  let Φ : Over.mk (ComplexPoint.affineSpecStructureMap R) ⟶ curveC N :=
    arcTensorProjection ≫ complexBaseChange.map k
  let f : ℍ → A →+* ℂ := fun τ =>
    if hτ : ⊤ ≤ (X0Model.complexPoint N τ) ⁻¹ᵁ U then
      (sectionEval (X0Model.complexPoint N τ) U hτ).hom
    else (sectionEval (X0Model.complexPoint N τ₀) U h₀).hom
  let ψ : ℍ → ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap R)) := fun τ =>
    (ComplexPoint.affineSpecEquiv R).symm (arcTensorMap (f τ))
  have hfac : ∀ τ, ⊤ ≤ (X0Model.complexPoint N τ) ⁻¹ᵁ U → arcPoint N τ = Point.map Φ (ψ τ) := by
    intro τ hτ
    have hfτ : f τ = (sectionEval (X0Model.complexPoint N τ) U hτ).hom := dite_eq_left hτ
    have hint : arcSpecPoint (f τ) ≫ k = interior N τ := by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom (f τ)) ≫ hU.fromSpec = X0Model.complexPoint N τ
      rw [hfτ]
      exact sectionMap_factor _ hU hτ
    change complexLift (interior N τ) = Point.map (complexBaseChange.map k)
      (Point.map arcTensorProjection (ψ τ))
    rw [arcTensorPoint_eq, ← complexLift_comp, hint]
  -- analytic dependence of the tensor evaluations
  have hsec : ∀ a : A, AnalyticAt ℂ (fun z : ℂ => f (ofComplex z) a) (τ₀ : ℂ) := by
    intro a
    obtain ⟨g, -, -, hval⟩ := X0Model.sectionMeromorphicContinuation N U a
    have han := (hval τ₀ (h₀ trivial)).1
    apply han.congr
    filter_upwards [eventually_ofComplex hev,
      eventuallyEq_coe_comp_ofComplex τ₀.im_pos] with z hz hcz
    have hfz : f (ofComplex z) = (sectionEval (X0Model.complexPoint N (ofComplex z)) U hz).hom :=
      dite_eq_left hz
    rw [hfz]
    have hv := (hval (ofComplex z) (hz trivial)).2
    have hcz' : ((ofComplex z : ℍ) : ℂ) = z := hcz
    rw [show g z = g ((ofComplex z : ℍ) : ℂ) by rw [hcz']]
    exact hv.symm
  have htensor : ∀ r : R, AnalyticAt ℂ (fun z : ℂ => arcTensorMap (f (ofComplex z)) r)
      (τ₀ : ℂ) := by
    intro r
    induction r using TensorProduct.inductionOn with
    | tmul c a =>
      simp only [arcTensorMap_tmul]
      exact (analyticAt_const (v := c)).mul (hsec a)
    | add x y hx hy =>
      simp only [map_add]
      exact hx.add hy
  have heval : ∀ (a : Γ(Spec (.of R), ⊤)) (τ : ℍ),
      Point.evaluate ⊤ a (ψ τ) = arcTensorMap (f τ) ((Scheme.ΓSpecIso (.of R)).hom a) :=
    fun a τ => ComplexPoint.evaluate_affineSpecEquiv_symm_top R a _
  -- localize on a basic open of the affine base change
  let W : (Spec (.of R)).Opens := Φ.left ⁻¹ᵁ V
  let t : Γ(Spec (.of R), W) := Φ.left.app V s
  have hψ₀ : (ψ τ₀).underlying ∈ W := by
    have := h
    rw [hfac τ₀ h₀, Point.underlying_map] at this
    exact this
  obtain ⟨g, hgW, hg₀⟩ := (isAffineOpen_top (Spec (.of R))).exists_basicOpen_le
    (⟨(ψ τ₀).underlying, hψ₀⟩ : W) trivial
  let t' := (Spec (.of R)).presheaf.map (homOfLE hgW).op t
  have : IsAffine (Over.mk (ComplexPoint.affineSpecStructureMap R)).left :=
    inferInstanceAs (IsAffine (Spec (.of R)))
  obtain ⟨m, a, hdiv⟩ := ComplexPoint.exists_evaluate_affine_basicOpen_eq_div
    (X := Over.mk (ComplexPoint.affineSpecStructureMap R)) g t'
  let G : ℂ → ℂ := fun z => arcTensorMap (f (ofComplex z)) ((Scheme.ΓSpecIso (.of R)).hom g)
  let Aa : ℂ → ℂ := fun z => arcTensorMap (f (ofComplex z)) ((Scheme.ΓSpecIso (.of R)).hom a)
  have hG := htensor ((Scheme.ΓSpecIso (.of R)).hom g)
  have hA := htensor ((Scheme.ΓSpecIso (.of R)).hom a)
  have hG₀ : G τ₀ ≠ 0 := by
    have hmem := (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := Over.mk (ComplexPoint.affineSpecStructureMap R)) (U := ⊤) g (ψ τ₀) trivial).mp hg₀
    rw [heval] at hmem
    change arcTensorMap (f (ofComplex (τ₀ : ℂ))) _ ≠ 0
    rwa [ofComplex_apply]
  have hGne : ∀ᶠ z in 𝓝 (τ₀ : ℂ), G z ≠ 0 := hG.continuousAt.eventually_ne hG₀
  have hgood : ∀ᶠ z in 𝓝 (τ₀ : ℂ),
      ⊤ ≤ (X0Model.complexPoint N (ofComplex z)) ⁻¹ᵁ U ∧
        (ψ (ofComplex z)).underlying ∈ (Spec (.of R)).basicOpen g := by
    filter_upwards [eventually_ofComplex hev, hGne] with z hz hGz
    refine ⟨hz, ?_⟩
    have := (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := Over.mk (ComplexPoint.affineSpecStructureMap R)) (U := ⊤) g (ψ (ofComplex z))
        trivial).mpr (by rw [heval]; exact hGz)
    exact this
  have hmemV : ∀ᶠ z in 𝓝 (τ₀ : ℂ), (arcPoint N (ofComplex z)).underlying ∈ V := by
    filter_upwards [hgood] with z hz
    rw [hfac _ hz.1, Point.underlying_map]
    exact hgW hz.2
  refine ⟨?_, ?_⟩
  · simpa only [ofComplex_apply] using eventually_coe hmemV
  · have hq : AnalyticAt ℂ (fun z => Aa z / G z ^ m) (τ₀ : ℂ) :=
      hA.div (hG.pow m) (pow_ne_zero m hG₀)
    apply hq.congr
    filter_upwards [hgood] with z hz
    symm
    rw [hfac _ hz.1, Point.evaluate_map]
    change Point.evaluate (X := Over.mk (ComplexPoint.affineSpecStructureMap R)) W t
      (ψ (ofComplex z)) = _
    rw [Point.evaluate_res (X := Over.mk (ComplexPoint.affineSpecStructureMap R)) hgW t _ hz.2,
      ]
    exact (hdiv _ hz.2).trans (by rw [heval, heval])

/-! ### Continuity and holomorphy of the point map -/

/-- The analytic point map is continuous for the analytic topology. -/
theorem continuousAt_arcPoint (τ₀ : ℍ) : ContinuousAt (arcPoint N) τ₀ := by
  have hn := @TopologicalSpace.nhds_generateFrom _
    (Point.analyticSubbasis (R := ℂ) (X := curveC N)) (arcPoint N τ₀)
  rw [← Point.analyticTopology_eq_generateFrom] at hn
  unfold ContinuousAt
  rw [hn]
  simp only [tendsto_iInf, tendsto_principal]
  rintro _ ⟨hpW, U, s, O, hO, rfl⟩
  obtain ⟨hmem, han⟩ := arcPoint_evaluate N U s τ₀ hpW.1
  have hc : ContinuousAt (fun τ : ℍ => Point.evaluate U s (arcPoint N τ)) τ₀ := by
    have := han.continuousAt.comp (continuous_coe.continuousAt (x := τ₀))
    simpa only [Function.comp_def, ofComplex_apply] using this
  filter_upwards [hmem, hc.preimage_mem_nhds (hO.mem_nhds hpW.2)] with τ h1 h2
  exact ⟨h1, h2⟩

/-- K4: the analytic point map `τ ↦ P τ` is holomorphic. -/
theorem mdifferentiable_arcPoint :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N) := by
  intro τ₀
  rw [mdifferentiableAt_iff_target]
  refine ⟨continuousAt_arcPoint N τ₀, ?_⟩
  set p := arcPoint N τ₀
  let L := ComplexPoint.localChart (curveC N) 1 p
  let D := localEtaleCoordinates (curveC N) 1 p.underlying
  have hsrc : ∀ᶠ τ in 𝓝 τ₀, arcPoint N τ ∈ L.source :=
    continuousAt_arcPoint N τ₀ (L.open_source.mem_nhds
      (ComplexPoint.mem_localChart_source (curveC N) 1 p))
  have heq : (extChartAt 𝓘(ℂ, Fin 1 → ℂ) p ∘ arcPoint N) =ᶠ[𝓝 τ₀]
      fun τ i => Point.evaluate D.ambientCoordinateOpen (D.ambientCoordinateSection i)
        (arcPoint N τ) := by
    filter_upwards [hsrc] with τ hτ
    funext i
    exact ComplexPoint.localChart_apply_component_eq_evaluate (curveC N) 1 p _ hτ i
  refine MDifferentiableAt.congr_of_eventuallyEq ?_ heq
  rw [mdifferentiableAt_pi_space]
  intro i
  have hp : p.underlying ∈ D.ambientCoordinateOpen := by
    have e : D.neighborhood = D.ambientCoordinateOpen := D.neighborhood.ι_image_top.symm
    rw [← e]
    exact D.mem
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  exact (arcPoint_evaluate N _ (D.ambientCoordinateSection i) τ₀ hp).2.differentiableAt

end ZInQ.Manuscript.RC.CuspFormDifferentials
