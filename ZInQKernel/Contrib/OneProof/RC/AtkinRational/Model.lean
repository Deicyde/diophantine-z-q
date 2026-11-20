import ZInQKernel.Contrib.OneProof.RC.AtkinRational.FunctionField
import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Generic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Topology.KrullDimension.Curve
import Mathlib.Algebra.AlgebraicCard

/-! The rational involution on the normalization used by the at-scale
join. Extension, comparison on the valuative chart, and density:
tex 2943–2944, on the spot (c). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Filter UpperHalfPlane ShimuraPointDict
open scoped Topology MatrixGroups TauCeti.ExactDivisor
open ZInQ.Contrib.CloudW07JacobiansCurves ZInQ.Contrib.RC53Assist.AbelianCurve
open ZInQ.Manuscript.RC.AtkinPin ZInQ.Manuscript.RC.X0Model
open ZInQ.Manuscript.RC.ModFnClassify
open ModularCurve (modularFunctionField)

namespace ZInQ.Manuscript.RC.AtkinRational

variable {N Q : ℕ} [NeZero N]

omit [NeZero N] in
private theorem hasValue_pull (hQ : Q ∥ N) (τ : ℍ)
    (a : MeromorphicGerm (↑(atkinGL hQ • τ) : ℂ)) {c : ℂ}
    (hc : HasValue (meromorphicIncl _ a) c) :
    HasValue (meromorphicIncl _ (pullGerm hQ τ a)) c := by
  obtain ⟨f, hf, _⟩ := a.property
  change HasValue a.val c at hc
  change HasValue (pullPuncturedGerm hQ τ a.val) c
  rw [← hf] at hc ⊢
  exact hasValue_coe.mpr ((hasValue_coe.mp hc).comp (mobius_tendsto hQ τ))

private def pullValuation (hQ : Q ∥ N) (τ : ℍ) :
    meromorphicValuation (↑(atkinGL hQ • τ) : ℂ) →+* meromorphicValuation (τ : ℂ) where
  toFun a := ⟨pullGerm hQ τ a.val, valueOfGerm _ a,
    hasValue_pull hQ τ a.val (finiteValue_spec (meromorphicIncl _) a)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ a.val b.val)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

omit [NeZero N] in
private theorem pullValuation_residue (hQ : Q ∥ N) (τ : ℍ) :
    (valueOfGerm _).comp (pullValuation hQ τ) = valueOfGerm _ := by
  ext a
  exact hasValue_unique (finiteValue_spec (meromorphicIncl _) (pullValuation hQ τ a))
    (hasValue_pull hQ τ a.val (finiteValue_spec (meromorphicIncl _) a))

private theorem spec_to_rat_eq {R : Type} [CommRing R]
    (u v : Spec (.of R) ⟶ Spec (.of ℚ)) : u = v := by
  apply Spec.homEquiv.injective
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- The function field pullback has an everywhere-defined rational extension. -/
theorem exists_modelMap (hQ : Q ∥ N) :
    ∃ w : X0Model.curve N ⟶ X0Model.curve N, w ≫ overQ N = overQ N ∧
      (X0Model.curve N).fromSpecFunctionField ≫ w =
        genericMap N ((functionField N).symm.toRingHom.comp (pullback hQ)) := by
  let : (X0Model.curve N).Over (Spec (.of ℚ)) := ⟨overQ N⟩
  have : IsProper (X0Model.curve N ↘ Spec (.of ℚ)) := proper N
  have : Smooth (overQ N) := smooth N
  have : (X0Model.curve N).IsSeparated :=
    ⟨by rw [← terminal.comp_from (X0Model.curve N ↘ Spec (.of ℚ))]; infer_instance⟩
  let s : Spec (X0Model.curve N).functionField ⟶ X0Model.curve N :=
    Spec.map (CommRingCat.ofHom ((functionField N).symm.toRingHom.comp
      ((pullback hQ).comp (functionField N).toRingHom))) ≫ (X0Model.curve N).fromSpecFunctionField
  obtain ⟨w, hw, hg⟩ := Scheme.exists_hom_of_valuationRing_stalk
    (base := Spec (.of ℚ)) (smooth_curve_valuation_stalk (overQ N)
      (ParamAtScale.model_dimension (X0Branch.model N))) s (spec_to_rat_eq _ _)
  exact ⟨w, hw.1, hg⟩

set_option backward.isDefEq.respectTransparency false in
/-- The chart compatibility is checked on the full meromorphic branch.
Pulling back the analytic arc over its valuation ring commutes with
residue, so this also covers points where the plane equation has several
branches. -/
theorem modelMap_chart (hQ : Q ∥ N) (w : X0Model.curve N ⟶ X0Model.curve N)
    (hw : (X0Model.curve N).fromSpecFunctionField ≫ w =
      genericMap N ((functionField N).symm.toRingHom.comp (pullback hQ))) (τ : ℍ) :
    complexPoint N τ ≫ w = complexPoint N (atkinGL hQ • τ) := by
  let σ := atkinGL hQ • τ
  let R := meromorphicValuation (τ : ℂ)
  let K := MeromorphicGerm (τ : ℂ)
  let R' := meromorphicValuation (σ : ℂ)
  let K' := MeromorphicGerm (σ : ℂ)
  let : Algebra ℚ R := (((constantGerm (τ : ℂ)).comp (Rat.castHom ℂ)).codRestrict
    R.toSubring (fun c => by
      change ∃ d, HasValue (((fun _ => (c : ℂ)) : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) d
      exact ⟨(c : ℂ), hasValue_coe.mpr tendsto_const_nhds⟩)).toAlgebra
  let pull := pullValuation hQ τ
  let A := analyticArc N τ ≫ w
  let B := Spec.map (CommRingCat.ofHom pull) ≫ analyticArc N σ
  have hv : (pullGerm hQ τ).comp (algebraMap R' K') =
      (algebraMap R K).comp pull := by
    ext a
    rfl
  have hA : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ A =
      genericMap N ((fieldGerm N τ).comp (pullback hQ)) := by
    unfold A
    rw [← Category.assoc, analyticArc_generic]
    unfold genericMap
    rw [Category.assoc, hw]
    simp only [genericMap, ← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change fieldGerm N τ ((functionField N) ((functionField N).symm
      (pullback hQ ((functionField N) a)))) = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  have hB : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ B =
      genericMap N ((fieldGerm N τ).comp (pullback hQ)) := by
    unfold B
    rw [← Category.assoc, ← Spec.map_comp,
      show CommRingCat.ofHom pull ≫ CommRingCat.ofHom (algebraMap R K) =
        CommRingCat.ofHom (algebraMap R' K') ≫ CommRingCat.ofHom (pullGerm hQ τ) from
          CommRingCat.hom_ext hv.symm, Spec.map_comp, Category.assoc, analyticArc_generic]
    unfold genericMap
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    exact RingHom.ext fun a => (fieldGerm_pullback hQ τ ((functionField N) a)).symm
  have heq : A = B := by
    obtain ⟨u, _, hu⟩ := existsUnique_specialization (R := R) N
      ((fieldGerm N τ).comp (pullback hQ))
    exact (hu A ⟨hA, spec_to_rat_eq _ _⟩).trans (hu B ⟨hB, spec_to_rat_eq _ _⟩).symm
  unfold complexPoint
  rw [Category.assoc]
  change Spec.map (CommRingCat.ofHom (valueOfGerm (τ : ℂ))) ≫ A = _
  rw [heq]
  unfold B
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (pullValuation_residue hQ τ)

private theorem exists_transcendental_j : ∃ τ : ℍ, Transcendental ℚ (analyticJ τ) := by
  by_contra h
  let U : Set ℂ := upperDomain
  have ha (τ : ℍ) : IsAlgebraic ℚ (analyticJ τ) := by
    by_contra ht
    exact h ⟨τ, ht⟩
  have hsub : jFunction '' U ⊆ {z : ℂ | IsAlgebraic ℚ z} := by
    rintro _ ⟨z, hz, rfl⟩
    exact ha (ofComplex z)
  have hconn : IsPreconnected (jFunction '' U) :=
    (convex_halfSpace_im_gt 0).isPreconnected.image _ analyticOn_j.continuousOn
  have hs := (Algebraic.countable ℚ ℂ).isTotallyDisconnected
    (jFunction '' U) hsub hconn
  let t : ℍ := ⟨Complex.I, by simp⟩
  have he (τ : ℍ) : jFunction τ = jFunction t :=
    hs ⟨_, τ.im_pos, rfl⟩ ⟨_, t.im_pos, rfl⟩
  obtain ⟨f, hf, hf₀, hval⟩ := j_cusp_unit
  have hq := (qParam_tendsto_atImInfty (h := 1) one_pos)
  have ht₁ := hf.continuousAt.tendsto.comp hq
  have ht₂ := hq.mul_const (jFunction t)
  simp only [zero_mul] at ht₂
  have ht := ht₁.congr (fun τ => (hval τ).trans (by rw [he]))
  exact one_ne_zero (hf₀ ▸ tendsto_nhds_unique ht ht₂)

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

private theorem jLinePoint_generic {c : ℂ} (h : Transcendental ℚ c) :
    X0Model2.jLinePoint (Rat.castHom ℂ) c default = genericPoint NormalModel.P := by
  let e := NormalModel.isAffineOpen_chart 0
  let p := ProjectiveLine.polyEquivChart ℚ 0
  have hi : Function.Injective (Polynomial.eval₂RingHom (Rat.castHom ℂ) c) :=
    transcendental_iff_injective.mp h
  have hj : Function.Injective ((Polynomial.eval₂RingHom (Rat.castHom ℂ) c).comp
      p.symm.toRingHom) :=
    hi.comp p.symm.injective
  unfold X0Model2.jLinePoint
  rw [Scheme.Hom.comp_apply, ← genericPoint_eq_of_isOpenImmersion e.fromSpec]
  congr 1
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  rw [Spec.map_apply]
  rw [show (default : Spec (.of ℂ)) = (⊥ : PrimeSpectrum ℂ)
    from Subsingleton.elim _ _]
  change Ideal.comap ((Polynomial.eval₂RingHom (Rat.castHom ℂ) c).comp p.symm.toRingHom)
    ((⊥ : PrimeSpectrum ℂ).asIdeal) =
      (⊥ : PrimeSpectrum Γ(NormalModel.P, NormalModel.chart 0)).asIdeal
  rw [PrimeSpectrum.asIdeal_bot, PrimeSpectrum.asIdeal_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp hj

/-- The chart includes a point defining a dominant rational morphism
from `Spec ℂ`: choose a transcendental first j-coordinate; finiteness
of the projection excludes a closed point above the generic point. -/
theorem exists_dominant_chart (N : ℕ) [NeZero N] :
    ∃ τ : ℍ, IsDominant (complexPoint N τ) := by
  obtain ⟨τ, ht⟩ := exists_transcendental_j
  refine ⟨τ, ?_⟩
  have hj : X0Model2.jProjection N (complexPoint N τ default) = genericPoint NormalModel.P := by
    rw [← Scheme.Hom.comp_apply, X0Model2.complexPoint_jProjection]
    exact jLinePoint_generic ht
  have hnc : ¬ IsClosed ({genericPoint NormalModel.P} : Set NormalModel.P) := by
    intro hc
    have hu : ({genericPoint NormalModel.P} : Set NormalModel.P) = Set.univ :=
      hc.closure_eq.symm.trans (genericPoint_spec NormalModel.P)
    let hsub : Subsingleton NormalModel.P := ⟨fun x y =>
      (Set.mem_singleton_iff.mp (hu ▸ Set.mem_univ x)).trans
        (Set.mem_singleton_iff.mp (hu ▸ Set.mem_univ y)).symm⟩
    let : DiscreteTopology NormalModel.P :=
      (subsingleton_iff_discrete_and_indiscrete.mp hsub).1
    have h := topologicalKrullDim_zero_of_discreteTopology NormalModel.P
    rw [NormalModel.topologicalKrullDim_P] at h
    exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) h
  let x := complexPoint N τ default
  have hdim : topologicalKrullDim (X0Model.curve N) ≤ 1 :=
    le_of_eq (NormalModel.topologicalKrullDim_Xn (modularFunctionField N))
  have hx : x = genericPoint (X0Model.curve N) := by
    apply (show IsGenericPoint x (Set.univ : Set (X0Model.curve N)) from ?_).eq (genericPoint_spec _)
    by_contra h
    have hclosed : IsClosed ({x} : Set (X0Model.curve N)) :=
      IsOpen.isClosed_singleton_of_mem_compl hdim isClosed_closure.isOpen_compl
        (Set.nonempty_compl.mpr h) (fun hx' => hx' (subset_closure rfl))
    apply hnc
    rw [← hj, ← Set.image_singleton]
    exact (X0Model2.jProjection N).isClosedMap _ hclosed
  rw [isDominant_iff, denseRange_iff_closure_range]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← show closure ({genericPoint (X0Model.curve N)} : Set (X0Model.curve N)) = Set.univ from
    genericPoint_spec (X0Model.curve N)]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨default, hx⟩)

/-- Two rational morphisms from the actual model to a separated target
coincide if their restrictions to the interior chart agree. -/
theorem ext_model_of_chart {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℚ)) [IsSeparated y]
    {f g : X0Model.curve N ⟶ Y} (hq : f ≫ y = g ≫ y)
    (h : ∀ τ : ℍ, complexPoint N τ ≫ f = complexPoint N τ ≫ g) : f = g := by
  obtain ⟨τ, hd⟩ := exists_dominant_chart N
  exact ext_of_isDominant_of_isSeparated y hq (complexPoint N τ) (h τ)

private theorem modelMap_square (hQ : Q ∥ N) {w : X0Model.curve N ⟶ X0Model.curve N}
    (hq : w ≫ overQ N = overQ N)
    (hc : ∀ τ : ℍ, complexPoint N τ ≫ w = complexPoint N (atkinGL hQ • τ)) :
    w ≫ w = 𝟙 _ := by
  have : IsProper (overQ N) := proper N
  apply ext_model_of_chart (overQ N) (by simp only [Category.assoc, hq, Category.id_comp])
  intro τ
  rw [← Category.assoc, hc τ, hc (atkinGL hQ • τ), Category.comp_id]
  have h := atkinInterior_involutive (X0Branch.model N) hQ
    ⟨(X0Branch.model N).complexPoint τ, τ, rfl⟩
  rw [atkinInterior_apply, atkinInterior_apply] at h
  exact congrArg (fun p : Interior (X0Branch.model N) => p.val.val) h

/-- The rational Atkin–Lehner involution on the model of the at-scale join. -/
def rationalAtkin (hQ : Q ∥ N) : RationalAtkin (X0Branch.model N) hQ :=
  let w := (exists_modelMap hQ).choose
  let hq := (exists_modelMap hQ).choose_spec.1
  let hc := modelMap_chart hQ w (exists_modelMap hQ).choose_spec.2
  ⟨w, hq, modelMap_square hQ hq hc, fun τ => Subtype.ext (hc τ)⟩


end ZInQ.Manuscript.RC.AtkinRational
