import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Construction

/-! K14: the native value of `Ψ f` is `f`, and with K8 and K9 the native value is a
linear equivalence between global differentials of `curveC N` and weight-two cusp forms
on `Γ₀(N)`, with inverse `Ψ`.

The computation: near a parameter `τ` whose point lies in an open `W'` carrying
representatives `s`, `b`, `c` of `A`, `B`, `1 ⊗ j` (with `b` a unit), `Ψ f = (s / b) · dc`
on `W'`, so the expression rule (K5) gives `f_{Ψ f}(τ) = (A / B)(τ) · j′(τ)`, the values of
the representatives along the analytic point map being the meromorphic continuations of
`A`, `B` and `j`. By P1, `(A / B) · j′ = f` near `τ`, and the identity theorem extends
`f_{Ψ f} = f` to `ℍ`. Such parameters exist: the analytic points lie in any nonempty
affine open of the model for all parameters in a punctured neighbourhood of any point
(the regular functions of the open are finitely generated and their continuations are
holomorphic off a discrete set). The finite-generation argument follows the eventual
chart membership used for K4. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane ModularCurve ShimuraPointDict PkgI3
open scoped Topology TensorProduct MatrixGroups ModularForm Manifold

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open X0Model J0Cusps

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

variable (N : ℕ) [NeZero N]

/-! ### Analytic points in a nonempty affine open of the model -/

private theorem wf_preimage_top_comp {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B]
    (u : Spec (.of A) ⟶ X) (f : Spec (.of B) ⟶ Spec (.of A)) (U : X.Opens)
    (h : ⊤ ≤ u ⁻¹ᵁ U) : ⊤ ≤ (f ≫ u) ⁻¹ᵁ U :=
  fun x _ => by rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply]; exact h trivial

private def wfSectionField (U : (X0Model.curve N).Opens) [Nonempty U] :
    Γ(X0Model.curve N, U) →+* modularFunctionField N :=
  (X0Model.functionField N).toRingHom.comp ((X0Model.curve N).germToFunctionField U).hom

private def wfInteriorSection (U : (X0Model.curve N).Opens) [Nonempty U]
    (τ : UpperHalfPlane) : Γ(X0Model.curve N, U) →+* X0Model.MeromorphicGerm (τ : ℂ) :=
  (X0Model.fieldGerm N τ).comp (wfSectionField N U)

private theorem wf_regular_interiorSection (U : (X0Model.curve N).Opens)
    [Nonempty U] (r : Γ(X0Model.curve N, U)) (τ : UpperHalfPlane) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f (τ : ℂ))
    (he : (f : PuncturedGerm (τ : ℂ)) =
      X0Model.meromorphicIncl (τ : ℂ) (wfInteriorSection N U τ r)) :
    wfInteriorSection N U τ r ∈ X0Model.meromorphicValuation (τ : ℂ) :=
  ⟨f τ, he ▸ hasValue_coe.mpr (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)⟩

private theorem wf_chart_mem_of_regular (U : (X0Model.curve N).Opens)
    [Nonempty U] (hU : IsAffineOpen U) (τ : UpperHalfPlane)
    (h : ∀ r, wfInteriorSection N U τ r ∈ X0Model.meromorphicValuation (τ : ℂ))
    (hg : ⊤ ≤ (X0Model.genericMap N (X0Model.fieldGerm N τ)) ⁻¹ᵁ U) :
    ⊤ ≤ (X0Model.complexPoint N τ) ⁻¹ᵁ U := by
  let R := X0Model.meromorphicValuation (τ : ℂ)
  let F := X0Model.MeromorphicGerm (τ : ℂ)
  let g := (wfInteriorSection N U τ).codRestrict R.toSubring h
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
  exact wf_preimage_top_comp u _ U hu

private theorem wf_eventually_chart_mem (U : (X0Model.curve N).Opens)
    [Nonempty U] (hU : IsAffineOpen U) {I : Type} {F : Filter I}
    (x : I → UpperHalfPlane)
    (h : ∀ r, ∀ᶠ i in F,
      wfInteriorSection N U (x i) r ∈ X0Model.meromorphicValuation (x i : ℂ))
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
  apply wf_chart_mem_of_regular N U hU (x i) _ (hg i)
  let B : Subalgebra ℚ A :=
    { toSubsemiring := ((X0Model.meromorphicValuation (x i : ℂ)).toSubring.comap
        (wfInteriorSection N U (x i))).toSubsemiring
      algebraMap_mem' := fun q => by
        change wfInteriorSection N U (x i) (α q) ∈ X0Model.meromorphicValuation (x i : ℂ)
        have e : (wfInteriorSection N U (x i)).comp α =
            (X0Model.constantGerm (x i : ℂ)).comp (Rat.castHom ℂ) := Subsingleton.elim _ _
        change ((wfInteriorSection N U (x i)).comp α) q ∈ _
        rw [e]
        exact ⟨(q : ℂ), hasValue_coe.mpr tendsto_const_nhds⟩ }
  have hle : Algebra.adjoin ℚ (S : Set A) ≤ B := Algebra.adjoin_le fun r hr => hi r hr
  rw [hS] at hle
  exact fun r => hle (show r ∈ (⊤ : Subalgebra ℚ A) from trivial)

private theorem wf_generic_hits_open (U : (X0Model.curve N).Opens)
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

/-- In a nonempty affine open of the model, the analytic point of every parameter in a
punctured neighbourhood of any point of `ℍ` lies in the open. -/
theorem eventually_complexPoint_mem_affine (U : (X0Model.curve N).Opens) [Nonempty U]
    (hU : IsAffineOpen U) (τ₀ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), ⊤ ≤ (X0Model.complexPoint N (ofComplex z)) ⁻¹ᵁ U := by
  apply wf_eventually_chart_mem N U hU (F := 𝓝[≠] (τ₀ : ℂ)) (fun z => ofComplex z) _
    (fun z => wf_generic_hits_open N U _)
  intro r
  obtain ⟨g, hg, hgerm⟩ := X0Model.exists_meromorphicContinuation N (wfSectionField N U r)
  have hmer : MeromorphicAt g (τ₀ : ℂ) := (hg τ₀.im_pos).meromorphicAt
  have hpos : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), 0 < z.im :=
    nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ₀.im_pos)
  filter_upwards [hmer.eventually_analyticAt, hpos] with z hz hzpos
  have hcz : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hzpos]
  apply wf_regular_interiorSection N U r (ofComplex z) (f := g) (by rw [hcz]; exact hz)
  exact hgerm (ofComplex z)

/-! ### Representatives: restriction, existence, evaluation -/

theorem RepOn.res {W W' : (curveC N).left.Opens} (h : W' ≤ W) {A : FieldC N}
    {s : Γ((curveC N).left, W)} (hA : RepOn N W A s) :
    RepOn N W' A ((curveC N).left.presheaf.map (homOfLE h).op s) := by
  induction hA with
  | zero => rw [map_zero]; exact RepOn.zero
  | tmul c V r hW =>
    have e1 : (curveC N).left.presheaf.map (homOfLE h).op
        ((curveC N).hom.specStructureMap W c) = (curveC N).hom.specStructureMap W' c := by
      rw [← (curveC N).hom.specStructureMap_map h]
      rfl
    have e2 : (curveC N).left.presheaf.map (homOfLE h).op
        ((curveC N).left.presheaf.map (homOfLE hW).op ((toModel N).app V r)) =
        (curveC N).left.presheaf.map (homOfLE (h.trans hW)).op ((toModel N).app V r) := by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [map_mul, e1, e2]
    exact RepOn.tmul c V r (h.trans hW)
  | add _ _ ihA ihB => rw [map_add]; exact ihA.add ihB

/-- Every element of `ℂ ⊗[ℚ] ℚ(X₀(N))` is represented over the preimage of some nonempty
open of the model. -/
theorem exists_rep (A : FieldC N) :
    ∃ V : (X0Model.curve N).Opens, (V : Set (X0Model.curve N)).Nonempty ∧
      ∀ W : (curveC N).left.Opens, W ≤ toModel N ⁻¹ᵁ V → ∃ s, RepOn N W A s := by
  induction A using TensorProduct.inductionOn with
  | tmul c a =>
    obtain ⟨x, rfl⟩ := (X0Model.functionField N).surjective a
    obtain ⟨V, hV, r, hr⟩ := (X0Model.curve N).presheaf.exists_germ_eq x
    have : Nonempty V := ⟨⟨_, hV⟩⟩
    refine ⟨V, ⟨_, hV⟩, fun W hW => ?_⟩
    have h := RepOn.tmul (N := N) (W := W) c V r hW
    have hx : (X0Model.curve N).germToFunctionField V r = x := hr
    rw [hx] at h
    exact ⟨_, h⟩
  | add A B hA hB =>
    obtain ⟨V₁, hV₁, h₁⟩ := hA
    obtain ⟨V₂, hV₂, h₂⟩ := hB
    refine ⟨V₁ ⊓ V₂, nonempty_preirreducible_inter V₁.isOpen V₂.isOpen hV₁ hV₂,
      fun W hW => ?_⟩
    obtain ⟨s, hs⟩ := h₁ W fun x hx => (show _ ∧ _ from hW hx).1
    obtain ⟨t, ht⟩ := h₂ W fun x hx => (show _ ∧ _ from hW hx).2
    exact ⟨s + t, hs.add ht⟩

theorem arcPoint_left_comp (τ : ℍ) :
    (arcPoint N τ).left ≫ toModel N = X0Model.complexPoint N τ :=
  Limits.pullback.lift_fst _ _ _

theorem toModel_underlying (τ : ℍ) :
    toModel N (arcPoint N τ).underlying = X0Model.complexPoint N τ (default : Spec (.of ℂ)) := by
  have key : ∀ x, toModel N ((arcPoint N τ).left x) = X0Model.complexPoint N τ x := by
    intro x
    rw [← arcPoint_left_comp N τ, Scheme.Hom.comp_apply]
  exact (key _).trans (congrArg _ (Subsingleton.elim _ _))

set_option backward.isDefEq.respectTransparency.types false in
private theorem wf_sectionMap_stalk {X : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A]
    (u : Spec (.of A) ⟶ X) (U : X.Opens) (hu : ⊤ ≤ u ⁻¹ᵁ U) :
    X0Model.sectionMap u U hu =
      X.presheaf.germ U _ (hu (show IsLocalRing.closedPoint A ∈ ⊤ from trivial)) ≫
        Scheme.stalkClosedPointTo u := by
  symm
  rw [Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, X0Model.sectionMap,
    Scheme.Hom.appLE, Category.assoc]
  rfl

private theorem wf_sectionMap_congr {X : Scheme.{0}} {A : Type} [CommRing A]
    {u u' : Spec (.of A) ⟶ X} (e : u = u') (U : X.Opens) (hu : ⊤ ≤ u ⁻¹ᵁ U)
    (hu' : ⊤ ≤ u' ⁻¹ᵁ U) : X0Model.sectionMap u U hu = X0Model.sectionMap u' U hu' := by
  subst e; rfl

theorem complexPoint_top_le (τ : ℍ) (V : (X0Model.curve N).Opens)
    (h : toModel N (arcPoint N τ).underlying ∈ V) :
    ⊤ ≤ (X0Model.complexPoint N τ) ⁻¹ᵁ V := by
  intro x _
  rw [Subsingleton.elim x (default : Spec (.of ℂ))]
  rw [toModel_underlying] at h
  exact h

/-- Evaluation of a pulled-back regular function along the analytic point map is the
section value at the model's analytic point. -/
theorem evaluate_toModel (τ : ℍ) (V : (X0Model.curve N).Opens) (r : Γ(X0Model.curve N, V))
    (W : (curveC N).left.Opens) (hW : W ≤ toModel N ⁻¹ᵁ V)
    (hτ : (arcPoint N τ).underlying ∈ W) :
    Point.evaluate W ((curveC N).left.presheaf.map (homOfLE hW).op ((toModel N).app V r))
        (arcPoint N τ) =
      X0Model.sectionMap (X0Model.complexPoint N τ) V
        (complexPoint_top_le N τ V (hW hτ)) r := by
  rw [← Point.evaluate_res hW _ _ hτ, Point.evaluate, dite_eq_left (hW hτ)]
  rw [← (toModel N).germ_stalkMap_apply V (arcPoint N τ).underlying (hW hτ) r]
  have e : (toModel N).stalkMap (arcPoint N τ).underlying ≫ (arcPoint N τ).stalkHom =
      Scheme.stalkClosedPointTo ((arcPoint N τ).left ≫ toModel N) :=
    (Scheme.stalkClosedPointTo_comp _ _).symm
  rw [← CommRingCat.comp_apply, e]
  have hu : ⊤ ≤ ((arcPoint N τ).left ≫ toModel N) ⁻¹ᵁ V := by
    rw [arcPoint_left_comp]; exact complexPoint_top_le N τ V (hW hτ)
  rw [wf_sectionMap_congr (arcPoint_left_comp N τ).symm V _ hu, wf_sectionMap_stalk]
  rfl

theorem evaluate_specStructureMap (W : (curveC N).left.Opens) (c : ℂ)
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ W) :
    Point.evaluate W ((curveC N).hom.specStructureMap W c) q = c := by
  let : Algebra ℂ Γ((curveC N).left, W) := ((curveC N).hom.specStructureMap W).hom.toAlgebra
  exact (ComplexPoint.sectionEvaluationAlgHom_apply W q hq _).symm.trans
    ((ComplexPoint.sectionEvaluationAlgHom W q hq).commutes c)

private theorem wf_evaluate_add {U : (curveC N).left.Opens} (a a' : Γ((curveC N).left, U))
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ U) :
    Point.evaluate U (a + a') q = Point.evaluate U a q + Point.evaluate U a' q := by
  rw [← Point.evaluationHom_apply U ⟨q, hq⟩, ← Point.evaluationHom_apply U ⟨q, hq⟩,
    ← Point.evaluationHom_apply U ⟨q, hq⟩, map_add]

private theorem wf_evaluate_mul {U : (curveC N).left.Opens} (a a' : Γ((curveC N).left, U))
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ U) :
    Point.evaluate U (a * a') q = Point.evaluate U a q * Point.evaluate U a' q := by
  rw [← Point.evaluationHom_apply U ⟨q, hq⟩, ← Point.evaluationHom_apply U ⟨q, hq⟩,
    ← Point.evaluationHom_apply U ⟨q, hq⟩, map_mul]

private theorem wf_evaluate_zero {U : (curveC N).left.Opens}
    (q : ComplexPoint (curveC N)) (hq : q.underlying ∈ U) :
    Point.evaluate U (0 : Γ((curveC N).left, U)) q = 0 := by
  rw [← Point.evaluationHom_apply U ⟨q, hq⟩, map_zero]

/-- A representative of `A`, evaluated along the analytic point map, is one meromorphic
continuation of `A`, holomorphic at every parameter whose point lies in the open. -/
theorem RepOn.exists_continuation {W : (curveC N).left.Opens} {A : FieldC N}
    {s : Γ((curveC N).left, W)} (hA : RepOn N W A s) :
    ∃ G : ℂ → ℂ, (∀ τ : ℍ, (G : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (fieldGermC N τ A)) ∧
      ∀ τ : ℍ, (arcPoint N τ).underlying ∈ W →
        AnalyticAt ℂ G (τ : ℂ) ∧ Point.evaluate W s (arcPoint N τ) = G τ := by
  induction hA with
  | zero =>
    refine ⟨0, fun τ => ?_, fun τ hτ => ⟨analyticAt_const, ?_⟩⟩
    · rw [map_zero, map_zero]; rfl
    · rw [wf_evaluate_zero N _ hτ]; rfl
  | tmul c V r hW =>
    obtain ⟨g, -, hgerm, hval⟩ := X0Model.sectionMeromorphicContinuation N V r
    refine ⟨fun z => c * g z, fun τ => ?_, fun τ hτ => ?_⟩
    · rw [fieldGermC_tmul, map_mul, ← hgerm τ]
      rfl
    · have hmem : X0Model.complexPoint N τ (default : Spec (.of ℂ)) ∈ V := by
        have := hW hτ
        rw [Scheme.Hom.mem_preimage, toModel_underlying] at this
        exact this
      obtain ⟨han, hv⟩ := hval τ hmem
      refine ⟨analyticAt_const.mul han, ?_⟩
      rw [wf_evaluate_mul N _ _ _ hτ, evaluate_specStructureMap N W c _ hτ,
        evaluate_toModel N τ V r W hW hτ]
      exact congrArg (fun t => c * t) hv
  | add _ _ ihA ihB =>
    obtain ⟨G₁, hG₁, hv₁⟩ := ihA
    obtain ⟨G₂, hG₂, hv₂⟩ := ihB
    refine ⟨fun z => G₁ z + G₂ z, fun τ => ?_, fun τ hτ => ?_⟩
    · rw [map_add, map_add, ← hG₁ τ, ← hG₂ τ]; rfl
    · obtain ⟨ha₁, he₁⟩ := hv₁ τ hτ
      obtain ⟨ha₂, he₂⟩ := hv₂ τ hτ
      exact ⟨ha₁.add ha₂, by rw [wf_evaluate_add N _ _ _ hτ, he₁, he₂]⟩

/-- Two functions holomorphic at `z` with the same punctured germ agree at `z`. -/
theorem eq_of_germ_eq {F G : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) (hG : AnalyticAt ℂ G z)
    (h : (F : PuncturedGerm z) = (G : PuncturedGerm z)) : F z = G z :=
  tendsto_nhds_unique
    ((hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (Germ.coe_eq.mp h))
    (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

theorem fieldGermC_jC (τ : ℍ) :
    meromorphicIncl (τ : ℂ) (fieldGermC N τ (jC N)) = (jFun : PuncturedGerm (τ : ℂ)) := by
  rw [fieldGermC_tmul, map_one, one_mul, jField, fieldGerm_j]
  exact Germ.coe_eq.mpr (Eventually.of_forall fun _ => by simp)

/-! ### The native value of `Ψ f` -/

theorem analyticOnNhd_nativeValue (ω : Γ((curveC N).hom.relativeDifferentials, ⊤)) :
    AnalyticOnNhd ℂ (fun z => nativeValue N ω (ofComplex z)) {z : ℂ | 0 < z.im} := by
  have hd : DifferentiableOn ℂ (nativeValue N ω ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_nativeValue N ω)
  exact fun z hz => hd.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hz)

/-- **K14.** The native value of `Ψ f` is `f`. -/
theorem nativeValue_psi (H : PsiHypotheses N) (f : CuspFormN N) :
    nativeValue N (psi N H f) = f := by
  obtain ⟨hAB, -, hω⟩ := psi_spec N H f
  set A := psiNum N H f
  set B := psiDen N H f
  set ω := psi N H f
  -- representatives over a common affine open of the model
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
  -- a parameter whose point lies in `W`
  have hmemW : ∀ τ : ℍ, ⊤ ≤ (X0Model.complexPoint N τ) ⁻¹ᵁ U →
      (arcPoint N τ).underlying ∈ W := by
    intro τ hτ
    show toModel N (arcPoint N τ).underlying ∈ U
    rw [toModel_underlying]
    exact hτ trivial
  obtain ⟨z₁, hz₁⟩ := (eventually_complexPoint_mem_affine N U hU UpperHalfPlane.I).exists
  set τ₁ : ℍ := ofComplex z₁
  have hτ₁ : (arcPoint N τ₁).underlying ∈ W := hmemW τ₁ hz₁
  -- `GB` does not vanish near `τ₁`
  have hGBne : ∀ᶠ z in 𝓝[≠] (τ₁ : ℂ), GB z ≠ 0 := by
    refine (hvB τ₁ hτ₁).1.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 => ?_
    apply (hAB τ₁).1
    apply (meromorphicIncl (τ₁ : ℂ)).injective
    rw [← hGB τ₁, map_zero]
    exact Germ.coe_eq.mpr (h0.filter_mono nhdsWithin_le_nhds)
  have hWev : ∀ᶠ z in 𝓝[≠] (τ₁ : ℂ), (arcPoint N (ofComplex z)).underlying ∈ W :=
    nhdsWithin_le_nhds (eventually_ofComplex (arcPoint_evaluate N W s τ₁ hτ₁).1)
  have hposev : ∀ᶠ z in 𝓝[≠] (τ₁ : ℂ), 0 < z.im :=
    nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ₁.im_pos)
  obtain ⟨z₂, hz₂B, hz₂W, hz₂pos⟩ := (hGBne.and (hWev.and hposev)).exists
  set τ₂ : ℍ := ⟨z₂, hz₂pos⟩
  have hτ₂ : (arcPoint N τ₂).underlying ∈ W := by
    have : ofComplex z₂ = τ₂ := ofComplex_apply_of_im_pos hz₂pos
    rw [← this]; exact hz₂W
  -- the open `W'` where `b` is a unit
  let W' : (curveC N).left.Opens := (curveC N).left.basicOpen b
  have hW'W : W' ≤ W := (curveC N).left.basicOpen_le b
  let s' := (curveC N).left.presheaf.map (homOfLE hW'W).op s
  let b' := (curveC N).left.presheaf.map (homOfLE hW'W).op b
  let c' := (curveC N).left.presheaf.map (homOfLE hW'W).op c
  have hb'u : IsUnit b' := (curveC N).left.toRingedSpace.isUnit_res_basicOpen b
  have hrel := hω W' le_top s' b' c' (hs.res N hW'W) (hb.res N hW'W) (hc.res N hW'W) hb'u
  -- the expression `Ψ f = (s' / b') · dc'` on `W'`
  set u := hb'u.unit
  have hexpr : (s' * (u⁻¹ : Γ((curveC N).left, W')ˣ)) •
      (curveC N).hom.sectionsD W' c' =
      (curveC N).hom.relativeDifferentials.presheaf.map (homOfLE le_top).op ω := by
    have h1 : (u : Γ((curveC N).left, W')) = b' := hb'u.unit_spec
    rw [mul_comm, mul_smul, ← hrel, ← h1, ← mul_smul, Units.inv_mul, one_smul]
  have hbval : ∀ τ : ℍ, (arcPoint N τ).underlying ∈ W' →
      Point.evaluate W' b' (arcPoint N τ) = GB τ := by
    intro τ hτ
    rw [← Point.evaluate_res hW'W b _ hτ]
    exact (hvB τ (hW'W hτ)).2
  -- the native value on `W'`
  have hnv : ∀ τ : ℍ, (arcPoint N τ).underlying ∈ W' →
      nativeValue N ω τ = GA τ / GB τ * jDeriv τ := by
    intro τ hτ
    rw [nativeValue_eq_of_expression N ω _ _ hexpr τ hτ]
    have hτW := hW'W hτ
    have hev1 : Point.evaluate W' (s' * (u⁻¹ : Γ((curveC N).left, W')ˣ)) (arcPoint N τ) =
        GA τ / GB τ := by
      rw [wf_evaluate_mul N _ _ _ hτ, ← Point.evaluate_res hW'W s _ hτ, (hvA τ hτW).2]
      have hinv : Point.evaluate W' ((u⁻¹ : Γ((curveC N).left, W')ˣ) : Γ((curveC N).left, W'))
          (arcPoint N τ) = (GB τ)⁻¹ := by
        have h1 : Point.evaluate W' ((u⁻¹ : Γ((curveC N).left, W')ˣ) :
            Γ((curveC N).left, W')) (arcPoint N τ) * Point.evaluate W' b' (arcPoint N τ) = 1 := by
          rw [← wf_evaluate_mul N _ _ _ hτ, ← hb'u.unit_spec, Units.inv_mul,
            ← Point.evaluationHom_apply W' ⟨_, hτ⟩, map_one]
        rw [hbval τ hτ] at h1
        exact eq_inv_of_mul_eq_one_left h1
      rw [hinv, div_eq_mul_inv]
    have hev2 : (fun z : ℂ => Point.evaluate W' c' (arcPoint N (ofComplex z))) =ᶠ[𝓝 (τ : ℂ)]
        jFun := by
      filter_upwards [eventually_ofComplex (arcPoint_evaluate N W' c' τ hτ).1,
        isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz hzpos
      have hzW := hW'W hz
      obtain ⟨hanJ, hvalJ⟩ := hvJ (ofComplex z) hzW
      rw [← Point.evaluate_res hW'W c _ hz, hvalJ]
      have hcz : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hzpos]
      have := eq_of_germ_eq hanJ (analyticAt_jFun (ofComplex z))
        ((hGJ (ofComplex z)).trans (fieldGermC_jC N (ofComplex z)))
      rw [hcz] at this ⊢
      exact this
    rw [hev1, hev2.deriv_eq]
    rfl
  -- comparison with `f` near `τ₂`
  have hτ₂W' : (arcPoint N τ₂).underlying ∈ W' := by
    have hev := (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero (U := W) b (arcPoint N τ₂) hτ₂)
    apply hev.mpr
    rw [(hvB τ₂ hτ₂).2]
    exact hz₂B
  have hW'ev : ∀ᶠ z in 𝓝 (τ₂ : ℂ), (arcPoint N (ofComplex z)).underlying ∈ W' :=
    eventually_ofComplex (arcPoint_evaluate N W' s' τ₂ hτ₂W').1
  have hGBne₂ : ∀ᶠ z in 𝓝[≠] (τ₂ : ℂ), GB z ≠ 0 := by
    refine (hvB τ₂ hτ₂).1.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 => ?_
    apply (hAB τ₂).1
    apply (meromorphicIncl (τ₂ : ℂ)).injective
    rw [← hGB τ₂, map_zero]
    exact Germ.coe_eq.mpr (h0.filter_mono nhdsWithin_le_nhds)
  have hjne : ∀ᶠ z in 𝓝[≠] (τ₂ : ℂ), jDeriv z ≠ 0 :=
    (analyticAt_jDeriv τ₂).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun h0 =>
      jDeriv_not_eventually_zero τ₂ (h0.filter_mono nhdsWithin_le_nhds)
  have hquot : ∀ᶠ z in 𝓝[≠] (τ₂ : ℂ), quotientByJDeriv N f z * GB z = GA z := by
    have h := congrArg (fun x => x * meromorphicIncl (τ₂ : ℂ) (fieldGermC N τ₂ B)) (hAB τ₂).2
    rw [← map_mul, div_mul_cancel₀ _ (hAB τ₂).1, ← hGA τ₂, ← hGB τ₂] at h
    exact Germ.coe_eq.mp h
  have hfreq : ∃ᶠ z in 𝓝[≠] (τ₂ : ℂ),
      nativeValue N ω (ofComplex z) = f (ofComplex z) := by
    refine Eventually.frequently ?_
    filter_upwards [nhdsWithin_le_nhds hW'ev, hGBne₂, hjne, hquot,
      nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ₂.im_pos)]
      with z hzW hzB hzj hzq hzpos
    have hcz : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hzpos]
    rw [hnv _ hzW, hcz, ← hzq]
    rw [mul_div_cancel_right₀ _ hzB, quotientByJDeriv, div_mul_cancel₀ _ hzj]
  have heq := (analyticOnNhd_nativeValue N ω).eqOn_of_preconnected_of_frequently_eq
    (fun z hz => cuspForm_analyticAt N f ⟨z, hz⟩)
    (convex_halfSpace_im_gt 0).isPreconnected τ₂.im_pos hfreq
  funext τ
  have := heq τ.im_pos
  simpa only [ofComplex_apply] using this

/-! ### The linear equivalence -/

/-- **K14 with K8 and K9.** The native value is a complex-linear equivalence between global
differentials of `curveC N` and weight-two cusp forms on `Γ₀(N)`, with inverse `Ψ`. -/
theorem exists_linearEquiv (H : PsiHypotheses N) (h8 : K8 N) (h9 : K9 N) :
    letI := differentialsModule N
    ∃ e : Γ((curveC N).hom.relativeDifferentials, ⊤) ≃ₗ[ℂ] CuspFormN N,
      (∀ ω τ, e ω τ = nativeValue N ω τ) ∧ ∀ f, e.symm f = psi N H f := by
  let := differentialsModule N
  obtain ⟨Φ, hΦ⟩ := h8
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ω h0
    apply h9
    funext τ
    rw [← hΦ, h0]
    rfl
  have hΦψ : ∀ f, Φ (psi N H f) = f := fun f => by
    ext τ
    rw [hΦ, nativeValue_psi N H f]
  have hsurj : Function.Surjective Φ := fun f => ⟨psi N H f, hΦψ f⟩
  let e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  refine ⟨e, fun ω τ => hΦ ω τ, fun f => ?_⟩
  apply e.injective
  rw [LinearEquiv.apply_symm_apply]
  exact (hΦψ f).symm

end ZInQ.Manuscript.RC.CuspFormDifferentials
