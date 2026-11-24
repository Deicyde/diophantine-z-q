import Mathlib.Analysis.Analytic.Order
import ZInQKernel.Contrib.OneProof.JDescent5Parameter
import ZInQKernel.Contrib.OneProof.JDescent5Doubling
import ZInQKernel.Contrib.OneProof.JDescent2

/-! Evaluation of the local parameter on the specified period. -/

namespace HDec.CMBranch.CMjBridges

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace Filter Set TauCeti
open scoped Topology UpperHalfPlane _root_.PeriodPair CategoryTheory.MonObj
open _root_.ZInQ.LeafPush2 (CPts cDom cEvalAt IsUniformization)

noncomputable section
attribute [local instance] abVar_isIntegral abVarFunctionFieldAlgebra
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem cpt_one_left {L : Type} [Field L] (A : PkgI3.AbVar L) (σ : L →+* ℂ) :
    (1 : CPts A σ).left = Spec.map (CommRingCat.ofHom σ) ≫ abVarUnit A := rfl

/-- The unit complex point is the only one whose underlying scheme point is the rational
identity. The residue spectrum of the identity is isomorphic to the ground spectrum. -/
theorem cpt_support_eq_identity_iff {L : Type} [Field L] (A : PkgI3.AbVar L)
    {σ : L →+* ℂ} (p : CPts A σ) :
    p.left (IsLocalRing.closedPoint ℂ) = abVarIdentity A ↔ p = 1 := by
  let X := A.X.left
  let O := abVarIdentity A
  let u := abVarUnit A
  let j := X.fromSpecResidueField O
  let g := Scheme.descResidueField (Scheme.stalkClosedPointTo u)
  have hu : Spec.map g ≫ j = u :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L X u
  constructor
  · intro hp
    obtain ⟨r, hr⟩ := Spec.map_surjective (j ≫ A.X.hom)
    have hrg : r ≫ g = 𝟙 (CommRingCat.of L) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_id, hr, ← Category.assoc, hu]
      exact Over.w (η[A.X])
    have hgr : g ≫ r = 𝟙 (X.residueField O) := by
      ext a
      apply g.hom.injective
      have he := congrArg (fun f : CommRingCat.of L ⟶ CommRingCat.of L => f (g a)) hrg
      exact he
    have hd : ∃ d : Spec (CommRingCat.of ℂ) ⟶ Spec (X.residueField
        (p.left (IsLocalRing.closedPoint ℂ))),
        d ≫ X.fromSpecResidueField (p.left (IsLocalRing.closedPoint ℂ)) = p.left :=
      ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField ℂ X p.left⟩
    rw [hp] at hd
    obtain ⟨d, hd⟩ := hd
    have hj : (j ≫ A.X.hom) ≫ Spec.map g = 𝟙 _ := by
      rw [← hr, ← Spec.map_comp, hgr, Spec.map_id]
    have hdj : d ≫ j = p.left := hd
    have hd' : p.left ≫ A.X.hom ≫ Spec.map g = d := calc
      _ = d ≫ ((j ≫ A.X.hom) ≫ Spec.map g) := by rw [← hdj]; simp only [Category.assoc]
      _ = d := by rw [hj, Category.comp_id]
    have hw : p.left ≫ A.X.hom = Spec.map (CommRingCat.ofHom σ) := Over.w p
    apply Over.OverMorphism.ext
    rw [cpt_one_left]
    calc
      p.left = d ≫ j := hdj.symm
      _ = (p.left ≫ A.X.hom ≫ Spec.map g) ≫ j := congrArg (fun f => f ≫ j) hd'.symm
      _ = (p.left ≫ A.X.hom) ≫ (Spec.map g ≫ j) := by simp only [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom σ) ≫ abVarUnit A := by rw [hu, hw]
  · rintro rfl
    rw [cpt_one_left]
    change (Spec.map (CommRingCat.ofHom σ) ≫ u) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) = O
    rw [Scheme.Hom.comp_apply, Spec_closedPoint]

/-- Evaluation on an open agrees with evaluation through the local ring at the point. -/
private theorem cEvalAt_eq_stalkClosedPointTo {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens) (f : Γ(A.X.left, U))
    (h : p.left (IsLocalRing.closedPoint ℂ) ∈ U) :
    cEvalAt p U f = Scheme.stalkClosedPointTo p.left
      (A.X.left.presheaf.germ U (p.left (IsLocalRing.closedPoint ℂ)) h f) := by
  have hpre := (Scheme.preimage_eq_top_of_closedPoint_mem p.left h).ge
  let q : Spec (CommRingCat.of ℂ) ⟶ A.X.left := p.left
  have hq : q (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ U := h
  have hg := Scheme.germ_stalkClosedPointTo q U hq
  have hrest : (⊤ : (Spec (CommRingCat.of ℂ)).Opens) ⟶ p.left ⁻¹ᵁ U :=
    (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem p.left h).symm).hom
  have he : hrest = homOfLE hpre := Subsingleton.elim _ _
  have hg' : A.X.left.presheaf.germ U _ h ≫ Scheme.stalkClosedPointTo p.left =
      p.left.appLE U ⊤ hpre ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := by
    change A.X.left.presheaf.germ U _ hq ≫ Scheme.stalkClosedPointTo q = _
    rw [hg]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom]
    change p.left.app U ≫ (Spec (CommRingCat.of ℂ)).presheaf.map hrest.op ≫ _ = _
    rw [he, Scheme.Hom.appLE, Category.assoc]
    rfl
  rw [cEvalAt, dite_eq_left hpre]
  exact (congrArg (fun g : Γ(A.X.left, U) ⟶ CommRingCat.of ℂ => g f) hg').symm

private theorem cEvalAt_restrict {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) {U V : A.X.left.Opens} (hVU : V ≤ U)
    (h : p.left (IsLocalRing.closedPoint ℂ) ∈ V) (f : Γ(A.X.left, U)) :
    cEvalAt p V (A.X.left.presheaf.map (homOfLE hVU).op f) = cEvalAt p U f := by
  rw [cEvalAt_eq_stalkClosedPointTo p V _ h, cEvalAt_eq_stalkClosedPointTo p U _ (hVU h),
    TopCat.Presheaf.germ_res_apply]

private theorem cEvalAt_via_germ_nonunit {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (hp : p.left (IsLocalRing.closedPoint ℂ) = abVarIdentity A)
    (V : A.X.left.Opens) (hV : abVarIdentity A ∈ V) (s : Γ(A.X.left, V))
    (hs : ¬ IsUnit (A.X.left.presheaf.germ V (abVarIdentity A) hV s)) :
    cEvalAt p V s = 0 := by
  have hh : p.left (IsLocalRing.closedPoint ℂ) ∈ V := hp.symm ▸ hV
  rw [cEvalAt_eq_stalkClosedPointTo p V s hh]
  let M (q : A.X.left) : Prop := ∀ hq : q ∈ V, ¬ IsUnit (A.X.left.presheaf.germ V q hq s)
  have hM : M (abVarIdentity A) := fun _ => hs
  have hs' := (hp.symm ▸ hM : M _) hh
  have : IsLocalHom (Scheme.stalkClosedPointTo p.left).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' p.left
  by_contra h
  exact hs' (IsLocalHom.map_nonunit (f := (Scheme.stalkClosedPointTo p.left).hom) _ (isUnit_iff_ne_zero.mpr h))

private theorem cEvalAt_via_germ_unit {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} (p : CPts A σ) (hp : p.left (IsLocalRing.closedPoint ℂ) = abVarIdentity A)
    (V : A.X.left.Opens) (hV : abVarIdentity A ∈ V) (s : Γ(A.X.left, V))
    (hs : IsUnit (A.X.left.presheaf.germ V (abVarIdentity A) hV s)) :
    cEvalAt p V s ≠ 0 := by
  have hh : p.left (IsLocalRing.closedPoint ℂ) ∈ V := hp.symm ▸ hV
  rw [cEvalAt_eq_stalkClosedPointTo p V s hh]
  let M (q : A.X.left) : Prop := ∀ hq : q ∈ V, IsUnit (A.X.left.presheaf.germ V q hq s)
  have hM : M (abVarIdentity A) := fun _ => hs
  have hs' := (hp.symm ▸ hM : M _) hh
  exact (hs'.map (Scheme.stalkClosedPointTo p.left).hom).ne_zero

private theorem deriv_ne_zero_of_eventual_doubling {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : ContinuousAt g 0) (h0 : f 0 = 0)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0)
    (hdouble : ∀ᶠ z in 𝓝 (0 : ℂ), f (2 * z) = 2 * f z + f z ^ 2 * g z) :
    deriv f 0 ≠ 0 := by
  obtain ⟨n, v, hv, hv0, h⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hfac : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * v z := by
    simpa only [Filter.EventuallyEq, sub_zero, smul_eq_mul] using h
  have hn : n ≠ 0 := by
    intro hn
    have he := hfac.eq_of_nhds
    exact hv0 (by simpa only [hn, pow_zero, _root_.one_mul, h0] using he.symm)
  have h2c : ContinuousAt (fun z : ℂ => 2 * z) 0 := by fun_prop
  have h2 : Tendsto (fun z : ℂ => 2 * z) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using h2c.tendsto
  have hfac2 := hfac.comp_tendsto h2
  let l (z : ℂ) := (2 : ℂ) ^ n * v (2 * z)
  let r (z : ℂ) := 2 * v z + z ^ n * v z ^ 2 * g z
  have he : l =ᶠ[𝓝[≠] (0 : ℂ)] r := by
    have hp : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 := nhdsWithin_le_nhds
    filter_upwards [hdouble.filter_mono hp, hfac2.filter_mono hp, hfac.filter_mono hp,
      self_mem_nhdsWithin] with z hdz hz2 hz hz0
    have heq : f (2 * z) = (2 * z) ^ n * v (2 * z) := hz2
    have heq' : f z = z ^ n * v z := hz
    apply mul_left_cancel₀ (pow_ne_zero n (show z ≠ 0 from hz0))
    rw [heq, heq', mul_pow] at hdz
    dsimp only [l, r]
    linear_combination hdz
  have hvl : ContinuousAt (fun z : ℂ => v (2 * z)) 0 :=
    (show ContinuousAt v ((2 : ℂ) * 0) by simpa only [mul_zero] using hv.continuousAt).comp h2c
  have hl : ContinuousAt l 0 := continuousAt_const.mul hvl
  have hr : ContinuousAt r 0 := (continuousAt_const.mul hv.continuousAt).add
    (((continuousAt_id.pow n).mul (hv.continuousAt.pow 2)).mul hg)
  have he0 := tendsto_nhds_unique_of_eventuallyEq
    (hl.tendsto.mono_left nhdsWithin_le_nhds) (hr.tendsto.mono_left nhdsWithin_le_nhds) he
  have hp : (2 : ℂ) ^ n = 2 := mul_right_cancel₀ hv0 (by
    simpa only [l, r, mul_zero, zero_pow hn, zero_mul, add_zero] using he0)
  have hpn : (2 : ℕ) ^ n = (2 : ℕ) ^ 1 := by
    exact_mod_cast (hp.trans (pow_one (2 : ℂ)).symm)
  have hn1 : n = 1 := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hpn
  rw [hn1] at h
  have ho := (hf.analyticOrderAt_eq_natCast (n := 1)).mpr ⟨v, hv, hv0, h⟩
  have hd := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp ho).2
  simpa only [iteratedDeriv_one] using hd

private theorem cEvalAt_doubling_pullback {L : Type} [Field L] (A : PkgI3.AbVar L)
    {σ : L →+* ℂ} (p : CPts A σ) (V W : A.X.left.Opens)
    (hWV : W ≤ (abVarDoubleOver A).left ⁻¹ᵁ V) (t : Γ(A.X.left, V))
    (hp : ⊤ ≤ p.left ⁻¹ᵁ W) :
    cEvalAt (p ≫ abVarDoubleOver A) V t =
      cEvalAt p W ((abVarDoubleOver A).left.appLE V W hWV t) := by
  have hq : ⊤ ≤ (p ≫ abVarDoubleOver A).left ⁻¹ᵁ V := hp.trans (p.left.preimage_mono hWV)
  simp only [cEvalAt, dite_eq_left hp, dite_eq_left hq]
  have he := Scheme.Hom.appLE_comp_appLE p.left (abVarDoubleOver A).left V W ⊤ hWV hp
  have he' : (abVarDoubleOver A).left.appLE V W hWV ≫ p.left.appLE W ⊤ hp =
      (p ≫ abVarDoubleOver A).left.appLE V ⊤ hq := he
  exact (congrArg (fun h : Γ(A.X.left, V) ⟶ Γ(Spec (CommRingCat.of ℂ), ⊤) =>
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (h t)) he').symm

private theorem abVar_period_parameter_derivative {L : Type} [Field L]
    (A : PkgI3.AbVar L) {σ : L →+* ℂ} {Λ : Submodule ℤ (Fin 1 → ℂ)}
    {Φ : (Fin 1 → ℂ) → CPts A σ} (s : ℂ) (hΦ : IsUniformization σ Λ Φ)
    (P : Place L (AbVarFunctionField A))
    (hp : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring)
    (V : A.X.left.Opens) (hV : abVarIdentity A ∈ V) (t : Γ(A.X.left, V))
    (ht : letI : Nonempty V := ⟨⟨abVarIdentity A, hV⟩⟩
          P.ord (A.X.left.germToFunctionField V t) = 1)
    (htNU : ¬ IsUnit (A.X.left.presheaf.germ V (abVarIdentity A) hV t))
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), cEvalAt (Φ (fun _ => s * z)) V t = 0) :
    deriv (fun z => cEvalAt (Φ (fun _ => s * z)) V t) 0 ≠ 0 := by
  let X := A.X.left
  let O := abVarIdentity A
  let d := (abVarDoubleOver A).left
  let t₀ := X.presheaf.germ V O hV t
  let F := AbVarFunctionField A
  have : Nonempty V := ⟨⟨O, hV⟩⟩
  have ht₀ : P.ord (algebraMap (X.presheaf.stalk O) F t₀) = 1 := by
    change P.ord (algebraMap (X.presheaf.stalk O) F (X.presheaf.germ V O hV t)) = 1
    rw [X.algebraMap_germ_eq_germToFunctionField hV t]
    exact ht
  have ht₀0 : X.residue O t₀ = 0 := by
    change IsLocalRing.residue _ t₀ = 0
    rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨g₀, hg₀⟩ := abVar_double_parameter_mod_square A P hp t₀ ht₀ ht₀0
  obtain ⟨Vg, hVg, g, hg⟩ := X.presheaf.exists_germ_eq g₀
  let W := V ⊓ d ⁻¹ᵁ V ⊓ Vg
  have hW : O ∈ W := ⟨⟨hV, by change d O ∈ V; rw [abVarDouble_fix_identity]; exact hV⟩, hVg⟩
  have hWV : W ≤ V := inf_le_left.trans inf_le_left
  have hWd : W ≤ d ⁻¹ᵁ V := inf_le_left.trans inf_le_right
  have hWg : W ≤ Vg := inf_le_right
  let tw : Γ(X, W) := X.presheaf.map (homOfLE hWV).op t
  let gw : Γ(X, W) := X.presheaf.map (homOfLE hWg).op g
  let td : Γ(X, W) := d.appLE V W hWd t
  have htd : X.presheaf.germ W O hW td = fixedStalkMap d O (abVarDouble_fix_identity A) t₀ := by
    let h := (Inseparable.of_eq (abVarDouble_fix_identity A)).specializes
    let hdV : d O ∈ V := h.mem_open V.isOpen hV
    change X.presheaf.germ W O hW (X.presheaf.map (homOfLE hWd).op (d.app V t)) =
      d.stalkMap O (X.presheaf.stalkSpecializes h t₀)
    have he := congrArg (fun k : Γ(X, V) ⟶ X.presheaf.stalk (d O) => k t)
      (X.presheaf.germ_stalkSpecializes hV h)
    change X.presheaf.stalkSpecializes h t₀ = X.presheaf.germ V (d O) hdV t at he
    rw [X.presheaf.germ_res_apply, he, d.germ_stalkMap_apply]
  have htd' : td = 2 * tw + tw ^ 2 * gw := by
    have : Nonempty W := ⟨⟨O, hW⟩⟩
    apply X.germToFunctionField_injective W
    rw [← X.algebraMap_germ_eq_germToFunctionField hW td,
      ← X.algebraMap_germ_eq_germToFunctionField hW (2 * tw + tw ^ 2 * gw)]
    apply congrArg (algebraMap (X.presheaf.stalk O) F)
    change (X.presheaf.germ W O hW).hom td =
      (X.presheaf.germ W O hW).hom (2 * tw + tw ^ 2 * gw)
    rw [map_add, map_mul, map_mul, map_ofNat, map_pow]
    change X.presheaf.germ W O hW td = 2 * X.presheaf.germ W O hW (X.presheaf.map _ t) +
      (X.presheaf.germ W O hW (X.presheaf.map _ t)) ^ 2 *
        X.presheaf.germ W O hW (X.presheaf.map _ g)
    rw [htd, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, hg]
    exact hg₀
  let v : ℂ → (Fin 1 → ℂ) := fun z _ => s * z
  let ev (z : ℂ) := Φ (v z)
  have hv : Differentiable ℂ v := by
    apply differentiable_pi.mpr
    intro i
    change Differentiable ℂ (fun z : ℂ => s * z)
    fun_prop
  have hv0 : v 0 = 0 := by ext i; simp [v]
  have hzero : ev 0 = 1 := (hΦ.2.1 _).mpr (hv0.symm ▸ Λ.zero_mem)
  have hsupp : (ev 0).left (IsLocalRing.closedPoint ℂ) = O :=
    (cpt_support_eq_identity_iff A _).mpr hzero
  have hopen (T : X.Opens) : IsOpen (v ⁻¹' cDom Φ T) := (hΦ.2.2.2.1 T).preimage hv.continuous
  have hmem (T : X.Opens) (hT : O ∈ T) : 0 ∈ v ⁻¹' cDom Φ T :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (ev 0).left (hsupp.symm ▸ hT)).ge
  have han (T : X.Opens) (hT : O ∈ T) (a : Γ(X, T)) :
      AnalyticAt ℂ (fun z => cEvalAt (ev z) T a) 0 := by
    apply (DifferentiableOn.analyticOnNhd _ (hopen T)) 0 (hmem T hT)
    exact (hΦ.2.2.2.2 T a).comp hv.differentiableOn (mapsTo_preimage _ _)
  refine deriv_ne_zero_of_eventual_doubling (han V hV t) (han W hW gw).continuousAt
    (cEvalAt_via_germ_nonunit (ev 0) hsupp V hV t htNU) hne ?_
  filter_upwards [(hopen W).mem_nhds (hmem W hW)] with z (hz : v z ∈ cDom Φ W)
  have hdoub : ev z ≫ abVarDoubleOver A = ev (2 * z) := by
    have hh : v (2 * z) = v z + v z := by ext i; simp only [v, Pi.add_apply]; ring
    change ev z ≫ abVarDoubleOver A = Φ (v (2 * z))
    rw [hh, hΦ.1, abVarDoubleOver, MonObj.comp_pow, Category.comp_id, pow_two]
  have he := cEvalAt_doubling_pullback A (ev z) V W hWd t hz
  rw [hdoub] at he
  change cEvalAt (ev (2 * z)) V t = cEvalAt (ev z) W td at he
  rw [he, htd']
  let φ := (((ev z).left.appLE W ⊤ hz) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom
  change cEvalAt (ev z) W (2 * tw + tw ^ 2 * gw) =
    2 * cEvalAt (ev z) V t + cEvalAt (ev z) V t ^ 2 * cEvalAt (ev z) W gw
  have hφ (a : Γ(X, W)) : φ a = cEvalAt (ev z) W a := by
    have hpre : ⊤ ≤ (ev z).left ⁻¹ᵁ W := hz
    rw [cEvalAt, dite_eq_left hpre]
    rfl
  rw [← hφ, map_add, map_mul, map_mul, map_ofNat, map_pow, hφ]
  have hm : (ev z).left (IsLocalRing.closedPoint ℂ) ∈ W := hz trivial
  have htw : cEvalAt (ev z) W tw = cEvalAt (ev z) V t :=
    cEvalAt_restrict (ev z) hWV hm t
  rw [htw, hφ gw]

/-- Every point off the period lattice evaluates the sections on the complement of the
identity. -/
theorem abVar_period_mem_punctured {L : Type} [Field L] {A : PkgI3.AbVar L}
    {σ : L →+* ℂ} {τ : ℍ} {Λ : Submodule ℤ (Fin 1 → ℂ)}
    {Φ : (Fin 1 → ℂ) → CPts A σ} {s : ℂ} (hΦ : IsUniformization σ Λ Φ)
    (hs : s ≠ 0) (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ)))
    {z : ℂ} (hz : z ∉ (PeriodPair.ofTau τ).lattice) :
    ⊤ ≤ (Φ (fun _ => s * z)).left ⁻¹ᵁ abVarPunctured A := by
  let p := Φ (fun _ => s * z)
  apply (Scheme.preimage_eq_top_of_closedPoint_mem p.left _).ge
  intro hp
  have h₁ := (cpt_support_eq_identity_iff A p).mp hp
  obtain ⟨m, n, h⟩ := (hΛ _).mp ((hΦ.2.1 _).mp h₁)
  have h' : z = (m : ℂ) + (n : ℂ) * (τ : ℂ) := mul_left_cancel₀ hs h
  apply hz
  refine PeriodPair.mem_lattice.mpr ⟨n, m, ?_⟩
  change (n : ℂ) * (τ : ℂ) + (m : ℂ) * 1 = z
  rw [h']
  ring

/-- The exact order-two pole in the generic stalk gives an analytic double pole on the
given period. Its parameter has a simple zero by comparing leading terms under doubling. -/
theorem abVar_evaluatedPole_of_order
    {L : Type} [Field L] (A : PkgI3.AbVar L) {σ : L →+* ℂ} {τ : ℍ}
    {Λ : Submodule ℤ (Fin 1 → ℂ)} {Φ : (Fin 1 → ℂ) → CPts A σ} {s : ℂ}
    (hΦ : IsUniformization σ Λ Φ) (hs : s ≠ 0)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = s * (m + n * (τ : ℂ)))
    (P : Place L (AbVarFunctionField A))
    (hp : (algebraMap (A.X.left.presheaf.stalk (abVarIdentity A)) (AbVarFunctionField A)).range =
      P.integers.toSubring) (x : Γ(A.X.left, abVarPunctured A))
    (hx : letI := abVarPunctured_nonempty A P hp
          P.ord (A.X.left.germToFunctionField (abVarPunctured A) x) = -2) :
    HasDoublePoleAtZero (fun z => cEvalAt (Φ (fun _ => s * z)) (abVarPunctured A) x) := by
  have := abVarPunctured_nonempty A P hp
  let U := abVarPunctured A
  let X := A.X.left
  obtain ⟨V, hV, t, u, ht, htNU, huU, hrel⟩ := abVar_orderTwo_localParameter A P hp U x hx
  let v : ℂ → (Fin 1 → ℂ) := fun z _ => s * z
  let ev (z : ℂ) := Φ (v z)
  have hv : Differentiable ℂ v := by
    apply differentiable_pi.mpr
    intro i
    change Differentiable ℂ (fun z : ℂ => s * z)
    fun_prop
  have hv0 : v 0 = 0 := by ext i; simp [v]
  have hzero : ev 0 = 1 := (hΦ.2.1 _).mpr (hv0.symm ▸ Λ.zero_mem)
  have hsupport : (ev 0).left (IsLocalRing.closedPoint ℂ) = abVarIdentity A :=
    (cpt_support_eq_identity_iff A (ev 0)).2 hzero
  have hV0 : v 0 ∈ cDom Φ V :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (ev 0).left (hsupport.symm ▸ hV)).ge
  have hopen : IsOpen (v ⁻¹' cDom Φ V) := (hΦ.2.2.2.1 V).preimage hv.continuous
  have hV0' : 0 ∈ v ⁻¹' cDom Φ V := hV0
  have ha (f : Γ(X, V)) : AnalyticAt ℂ (fun z => cEvalAt (ev z) V f) 0 := by
    apply (DifferentiableOn.analyticOnNhd _ hopen) 0 hV0'
    exact (hΦ.2.2.2.2 V f).comp hv.differentiableOn (mapsTo_preimage _ _)
  have ht0 : cEvalAt (ev 0) V t = 0 := cEvalAt_via_germ_nonunit (ev 0) hsupport V hV t htNU
  have hu0 : cEvalAt (ev 0) V u ≠ 0 := cEvalAt_via_germ_unit (ev 0) hsupport V hV u huU
  have hev : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
      cEvalAt (ev z) V t ^ 2 * cEvalAt (ev z) U x = cEvalAt (ev z) V u := by
    let Q := PeriodPair.ofTau τ
    have hl : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ∉ Q.lattice := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Q.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz h0
      exact fun h => hz ⟨h, h0⟩
    have hn0 : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ v ⁻¹' cDom Φ V := hopen.mem_nhds hV0'
    have hn := hn0.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))
    filter_upwards [hl, hn] with z hz hzV
    have hU' : ⊤ ≤ (ev z).left ⁻¹ᵁ U := abVar_period_mem_punctured hΦ hs hΛ hz
    have hS : (ev z).left (IsLocalRing.closedPoint ℂ) ∈ V ⊓ U :=
      ⟨hzV trivial, hU' trivial⟩
    have hT : ⊤ ≤ (ev z).left ⁻¹ᵁ (V ⊓ U) :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (ev z).left hS).ge
    let φ := (((ev z).left.appLE (V ⊓ U) ⊤ hT) ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom
    have hval := congrArg φ hrel
    rw [map_mul, map_pow] at hval
    have hE (f : Γ(X, V ⊓ U)) : φ f = cEvalAt (ev z) (V ⊓ U) f := by
      simp only [cEvalAt, dite_eq_left hT]; rfl
    rw [hE, hE, hE, cEvalAt_restrict _ inf_le_left hS, cEvalAt_restrict _ inf_le_right hS,
      cEvalAt_restrict _ inf_le_left hS] at hval
    exact hval
  have ht_ne : ¬ ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), cEvalAt (ev z) V t = 0 := by
    intro hh
    have hne := (ha u).continuousAt.eventually_ne hu0
    have hp' : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 := nhdsWithin_le_nhds
    have he : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), False := by
      filter_upwards [hev, hh.filter_mono hp', hne.filter_mono hp'] with z hz hz0 hzu
      exact hzu (by simpa only [hz0, zero_pow (by decide : 2 ≠ 0), zero_mul] using hz.symm)
    exact he.exists.choose_spec
  have hd := abVar_period_parameter_derivative A s hΦ P hp V hV t ht htNU ht_ne
  exact hasDoublePoleAtZero_of_localParameter (ha t) ht0 hd (ha u) hu0 hev

#print axioms cpt_one_left
#print axioms cpt_support_eq_identity_iff
#print axioms cEvalAt_eq_stalkClosedPointTo
#print axioms cEvalAt_restrict
#print axioms cEvalAt_via_germ_nonunit
#print axioms cEvalAt_via_germ_unit
#print axioms abVar_period_mem_punctured
#print axioms deriv_ne_zero_of_eventual_doubling
#print axioms cEvalAt_doubling_pullback
#print axioms abVar_period_parameter_derivative
#print axioms abVar_evaluatedPole_of_order

end

end HDec.CMBranch.CMjBridges
