import ZInQKernel.Contrib.OneProof.AfTateLambda
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Dimension
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! Valuative centers and evaluation of rational functions on a smooth proper curve. -/

noncomputable section

namespace ShimuraPointDict

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open LeafModCurves PkgI3.AbVar AfTateLam

variable {X : Over SpecQ} [IsIntegral X.left]

/-- The underlying scheme map of a complex point. -/
abbrev complexMap (x : CPt X) : Spec (CommRingCat.of ℂ) ⟶ X.left := x.left

/-- Both directions of the comparison between the section and stalk descriptions of regularity. -/
theorem regAt_iff_stalk {x : CPt X} {g : X.left.functionField} {c : ℂ} :
    RegAt x g c ↔
      ∃ r : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ)),
        algebraMap _ X.left.functionField r = g ∧ Scheme.stalkClosedPointTo (complexMap x) r = c := by
  let v := complexMap x
  have eval_section (U : X.left.Opens) (hU : ⊤ ≤ v ⁻¹ᵁ U) (hv) :
      X.left.presheaf.germ U (v (IsLocalRing.closedPoint (CommRingCat.of ℂ))) hv ≫
        Scheme.stalkClosedPointTo v = v.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of ℂ)).hom := by
    rw [Scheme.germ_stalkClosedPointTo v U hv]
    simp only [Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      Category.assoc]
    congr 3
  constructor
  · rintro ⟨U, hU, s, hx, hs, hc⟩
    let : Nonempty U := hU
    have hm : v (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ U := hx (show _ ∈ ⊤ from trivial)
    exact ⟨X.left.presheaf.germ U _ hm s,
      (Scheme.algebraMap_germ_eq_germToFunctionField X.left hm s).trans hs,
      (congrArg (fun k : Γ(X.left, U) ⟶ CommRingCat.of ℂ => k s) (eval_section U hx hm)).trans hc⟩
  · rintro ⟨r, hr, hc⟩
    obtain ⟨U, hm, s, hs⟩ := X.left.presheaf.exists_germ_eq r
    let : Nonempty U := ⟨⟨_, hm⟩⟩
    have hx : ⊤ ≤ v ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem v hm).ge
    refine ⟨U, inferInstance, s, hx, ?_, ?_⟩
    · rw [← hr, ← hs, Scheme.algebraMap_germ_eq_germToFunctionField]
    · rw [← hc, ← hs]
      exact (congrArg (fun k : Γ(X.left, U) ⟶ CommRingCat.of ℂ => k s) (eval_section U hx hm)).symm

private theorem spec_to_rat_eq {S : CommRingCat} (f g : Spec S ⟶ SpecQ) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_rat _ _)

/-- The square with the generic point at the top and the base map of the valuation ring
at the bottom. -/
abbrev valuationSquare (A : ValuationSubring X.left.functionField) (a : ℚ →+* A) :
    ValuativeCommSq X.hom where
  R := A
  K := X.left.functionField
  i₁ := X.left.fromSpecStalk (genericPoint X.left)
  i₂ := Spec.map (CommRingCat.ofHom a)
  commSq := ⟨spec_to_rat_eq _ _⟩

variable (A : ValuationSubring X.left.functionField) (a : ℚ →+* A)

private theorem specMap_to_generic (y : X.left) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.left.presheaf.stalk y) X.left.functionField)) ≫
      X.left.fromSpecStalk y = X.left.fromSpecStalk (genericPoint X.left) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec X.left).specializes trivial)

private theorem centerMap_comp
    (l : (valuationSquare A a).commSq.LiftStruct) :
    A.subtype.comp (Scheme.stalkClosedPointTo l.l).hom =
      algebraMap _ X.left.functionField := by
  let y := l.l (IsLocalRing.closedPoint (CommRingCat.of A))
  have h :
      Spec.map (Scheme.stalkClosedPointTo l.l ≫ CommRingCat.ofHom A.subtype) ≫
          X.left.fromSpecStalk y =
        Spec.map (CommRingCat.ofHom (algebraMap (X.left.presheaf.stalk y) X.left.functionField)) ≫
          X.left.fromSpecStalk y := by
    rw [specMap_to_generic, Spec.map_comp, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact l.fac_left
  have hh := (cancel_mono (X.left.fromSpecStalk y)).mp h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hh)

private theorem centerMap_surjective (hC : IsCurve X)
    (l : (valuationSquare A a).commSq.LiftStruct) :
    Function.Surjective (Scheme.stalkClosedPointTo l.l).hom := by
  let y := l.l (IsLocalRing.closedPoint (CommRingCat.of A))
  let := hC.smooth
  let : ValuationRing (X.left.presheaf.stalk (l.l (IsLocalRing.closedPoint (CommRingCat.of A)))) :=
    Scheme.valuationRing_stalk X.hom y
  have hb := bijective_rangeRestrict_comp_of_valuationRing (Scheme.stalkClosedPointTo l.l).hom
    A.subtype (centerMap_comp A a l)
  intro b
  obtain ⟨r, hr⟩ := hb.2 (A.subtype.rangeRestrict b)
  exact ⟨r, A.subtype_injective (congrArg (fun w : A.subtype.range => w.val) hr)⟩

/-- Properness produces a complex point realizing the prescribed value of every element
of the valuation subring. -/
theorem exists_regAt_of_valuation (a : ℚ →+* A) (hC : IsCurve X) (e : A →+* ℂ) :
    ∃ x : CPt X, ∀ b : A, RegAt x (b : X.left.functionField) (e b) := by
  let := hC.proper
  have hp : ValuativeCriterion X.hom := by
    have h : ((@IsProper : MorphismProperty Scheme)) X.hom := hC.proper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨⟨l⟩⟩ := hp.existence (valuationSquare A a)
  let L : Spec (CommRingCat.of A) ⟶ X.left := l.l
  let f : Spec (CommRingCat.of ℂ) ⟶ X.left := Spec.map (CommRingCat.ofHom e) ≫ L
  let x : CPt X := Over.homMk f (spec_to_rat_eq _ _)
  use x
  intro b
  obtain ⟨r, hr⟩ := centerMap_surjective A a hC l b
  obtain ⟨U, hm, s, hs⟩ := X.left.presheaf.exists_germ_eq r
  let : Nonempty U := ⟨⟨_, hm⟩⟩
  have hU : ⊤ ≤ L ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem L hm).ge
  have hh : ⊤ ≤ (Spec.map (CommRingCat.ofHom e)) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens) := by simp
  have hx : ⊤ ≤ f ⁻¹ᵁ U := by
    dsimp only [f]
    rw [Scheme.Hom.comp_preimage]
    exact hh.trans ((Spec.map (CommRingCat.ofHom e)).preimage_mono hU)
  refine ⟨U, inferInstance, s, hx, ?_, ?_⟩
  · rw [← Scheme.algebraMap_germ_eq_germToFunctionField X.left hm s, hs, ← centerMap_comp A a l]
    exact congrArg Subtype.val hr
  · have hv := Scheme.germ_stalkClosedPointTo L U hm
    have hv' : X.left.presheaf.germ U _ hm ≫ Scheme.stalkClosedPointTo L =
        L.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (.of A)).hom := by
      rw [hv]
      simp only [Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
        Category.assoc]
      congr 3
    have hs' : (Scheme.ΓSpecIso (.of A)).hom (L.appLE U ⊤ hU s) = b := by
      have h := congrArg (fun k : Γ(X.left, U) ⟶ CommRingCat.of A => k s) hv'
      change (Scheme.stalkClosedPointTo L) (X.left.presheaf.germ U _ hm s) =
        (Scheme.ΓSpecIso (.of A)).hom (L.appLE U ⊤ hU s) at h
      rw [hs] at h
      exact h.symm.trans hr
    change ((Spec.map (CommRingCat.ofHom e) ≫ L).appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (.of ℂ)).hom) s = e b
    rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ hU hh, Category.assoc]
    have htop : (Spec.map (CommRingCat.ofHom e)).appLE ⊤ ⊤ hh =
        (Spec.map (CommRingCat.ofHom e)).appTop :=
      Scheme.Hom.appLE_eq_app _
    rw [htop, Scheme.ΓSpecIso_naturality]
    exact congrArg e hs'

private def lift_of_stalk {x : CPt X}
    (v : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ)) →+* A)
    (hv : A.subtype.comp v = algebraMap _ X.left.functionField) :
    (valuationSquare A a).commSq.LiftStruct where
  l := Spec.map (CommRingCat.ofHom v) ≫ X.left.fromSpecStalk _
  fac_left := by
    change Spec.map (CommRingCat.ofHom A.subtype) ≫ _ = _
    rw [← Spec.map_comp_assoc]
    change Spec.map (CommRingCat.ofHom (A.subtype.comp v)) ≫ _ = _
    rw [hv, specMap_to_generic]
  fac_right := spec_to_rat_eq _ _

/-- Two complex points that induce the same evaluation from the same valuation ring coincide.
Each point's stalk must map to this ring compatibly with its function field embedding. -/
theorem point_eq_of_stalk_to_valuation (a : ℚ →+* A) (hC : IsCurve X) (e : A →+* ℂ) {x y : CPt X}
    (vx : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ)) →+* A)
    (vy : X.left.presheaf.stalk (complexMap y (IsLocalRing.closedPoint ℂ)) →+* A)
    (hvx : A.subtype.comp vx = algebraMap _ X.left.functionField)
    (hvy : A.subtype.comp vy = algebraMap _ X.left.functionField)
    (hex : e.comp vx = (Scheme.stalkClosedPointTo (complexMap x)).hom)
    (hey : e.comp vy = (Scheme.stalkClosedPointTo (complexMap y)).hom) : x = y := by
  let := hC.proper
  let := IsSeparated.valuativeCriterion X.hom (valuationSquare A a)
  have hx : Spec.map (CommRingCat.ofHom e) ≫ (lift_of_stalk A a vx hvx).l = complexMap x := by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom vx) ≫ _ = _
    rw [← Spec.map_comp_assoc]
    change Spec.map (CommRingCat.ofHom (e.comp vx)) ≫ _ = _
    rw [hex]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  have hy : Spec.map (CommRingCat.ofHom e) ≫ (lift_of_stalk A a vy hvy).l = complexMap y := by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom vy) ≫ _ = _
    rw [← Spec.map_comp_assoc]
    change Spec.map (CommRingCat.ofHom (e.comp vy)) ≫ _ = _
    rw [hey]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  rw [Subsingleton.elim (lift_of_stalk A a vx hvx) (lift_of_stalk A a vy hvy), hy] at hx
  exact Over.OverMorphism.ext hx.symm

#print axioms regAt_iff_stalk
#print axioms spec_to_rat_eq
#print axioms specMap_to_generic
#print axioms centerMap_comp
#print axioms centerMap_surjective
#print axioms exists_regAt_of_valuation
#print axioms point_eq_of_stalk_to_valuation

end ShimuraPointDict
