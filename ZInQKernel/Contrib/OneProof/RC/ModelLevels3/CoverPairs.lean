import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ShortLevelAction
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.PairIsomorphisms
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.ShortRepresentatives

/-! # Cyclic pairs read from the whole short cover -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : ShortBase R))
  [Algebra R (ExactOrderAlgebra (shortFamily R) hn)]
  [IsScalarTower R (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)]
  {k : Type*} [Field k] [Algebra R k] [DecidableEq k]

private theorem short_specialized (c : ShortBase R →ₐ[R] k) :
    ((shortFamily R).map c.toRingHom).IsShortNF :=
  ⟨by simp [shortFamily, shortEquation], by simp [shortFamily, shortEquation],
    by simp [shortFamily, shortEquation]⟩

/-- The elliptic equation and cyclic subgroup of a point of the cover. -/
noncomputable def shortCoverPair (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k) :
    EnhancedCurve k (n + 2) :=
  let data := shortExactOrderPoints hn f
  ⟨(shortFamily R).map data.1.toRingHom, inferInstance, subgroupOfGenerator data.2⟩

private theorem markedPair_cast {W V : WeierstrassCurve k} (h : W = V) (he : V.IsElliptic)
    (P : Generators V.toAffine.Point (n + 2)) :
    (⟨W, h.symm ▸ he, subgroupOfGenerator (h.symm ▸ P)⟩ : EnhancedCurve k (n + 2)) =
      ⟨V, he, subgroupOfGenerator P⟩ := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem shortCoverPair_marked (W : WeierstrassCurve k) [W.IsElliptic] [W.IsShortNF]
    (P : Generators W.toAffine.Point (n + 2)) :
    shortCoverPair hn (exactOrderPointOfGenerator hn W P) =
      ⟨W, inferInstance, subgroupOfGenerator P⟩ := by
  let read (data : Σ c : ShortBase R →ₐ[R] k,
      Generators ((shortFamily R).map c.toRingHom).toAffine.Point (n + 2)) :
      EnhancedCurve k (n + 2) :=
    ⟨(shortFamily R).map data.1.toRingHom, inferInstance, subgroupOfGenerator data.2⟩
  change read (shortExactOrderPoints hn (exactOrderPointOfGenerator hn W P)) = _
  rw [exactOrderPointOfGenerator_read]
  exact markedPair_cast (shortFamily_map_coefficientPoint (R := R) W) inferInstance P

private theorem coefficientPoint_specialized (c : ShortBase R →ₐ[R] k) :
    let W := (shortFamily R).map c.toRingHom
    letI := short_specialized c
    shortCoefficientPoint (R := R) W = c := by
  intro W
  letI := short_specialized c
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (shortEquation R).Δ)
  change ((shortCoefficientPoint (R := R) W).comp (IsScalarTower.toAlgHom R
    (MvPolynomial (Fin 2) R) (ShortBase R))).toRingHom =
    (c.comp (IsScalarTower.toAlgHom R (MvPolynomial (Fin 2) R) (ShortBase R))).toRingHom
  congr 1
  ext i
  have h := shortFamily_map_coefficientPoint (R := R) W
  fin_cases i
  · exact congrArg WeierstrassCurve.a₄ h
  · exact congrArg WeierstrassCurve.a₆ h

private theorem markedSigma_eq {b c : ShortBase R →ₐ[R] k} (hc : b = c)
    (hw : (shortFamily R).map b.toRingHom = (shortFamily R).map c.toRingHom)
    (P : Generators ((shortFamily R).map c.toRingHom).toAffine.Point (n + 2)) :
    (⟨b, hw.symm ▸ P⟩ : Σ a : ShortBase R →ₐ[R] k,
      Generators ((shortFamily R).map a.toRingHom).toAffine.Point (n + 2)) = ⟨c, P⟩ := by
  cases hc
  rfl

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem exactOrderPointOfGenerator_specialized (c : ShortBase R →ₐ[R] k)
    (P : Generators ((shortFamily R).map c.toRingHom).toAffine.Point (n + 2)) :
    let W := (shortFamily R).map c.toRingHom
    letI := short_specialized c
    exactOrderPointOfGenerator hn W P = (shortExactOrderPoints hn).symm ⟨c, P⟩ := by
  intro W
  letI := short_specialized c
  apply (shortExactOrderPoints hn).injective
  rw [exactOrderPointOfGenerator_read, Equiv.apply_symm_apply]
  exact markedSigma_eq (coefficientPoint_specialized c)
    (shortFamily_map_coefficientPoint (R := R) W) P

set_option backward.isDefEq.respectTransparency false in
/-- Every cyclic pair can be read on a point of the exact-order cover. -/
theorem shortCoverPairClass_surjective (h₂ : (2 : k) ≠ 0) (h₃ : (3 : k) ≠ 0) :
    Function.Surjective
      (fun f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k =>
        (Quot.mk _ (shortCoverPair hn f) : PairClasses k (n + 2))) := by
  intro x
  obtain ⟨B, hB, ⟨P, hP⟩, hx⟩ := pairClasses_has_short_generator h₂ h₃ x
  letI := B.elliptic
  letI := hB
  refine ⟨exactOrderPointOfGenerator hn B.equation P, ?_⟩
  change (Quot.mk _ (shortCoverPair hn (exactOrderPointOfGenerator hn B.equation P)) :
    PairClasses k (n + 2)) = x
  rw [shortCoverPair_marked, hP]
  exact hx

private theorem map_subgroupOfGenerator {W V : WeierstrassCurve k}
    (e : W.toAffine.Point ≃+ V.toAffine.Point) (P : Generators W.toAffine.Point (n + 2)) :
    AddSubgroup.zmultiples (e P.val) = e.mapAddSubgroup (subgroupOfGenerator P).val :=
  (AddMonoidHom.map_zmultiples e.toAddMonoidHom P.val).symm

private theorem generator_transport (W V : WeierstrassCurve k) (v : VariableChange k)
    (h : v • W = V) (T : Generators W.toAffine.Point (n + 2))
    (T' : Generators (v • W).toAffine.Point (n + 2))
    (ht : T'.val = (Point.addEquivVariableChange W v).symm T.val) :
    ((h ▸ T') : Generators V.toAffine.Point (n + 2)).val = (changePoints W V v h) T.val := by
  cases h
  exact ht

private theorem exactOrderPointOfGenerator_cast {U V : WeierstrassCurve k} (h : U = V)
    [U.IsElliptic] [U.IsShortNF] [V.IsElliptic] [V.IsShortNF]
    (P : Generators U.toAffine.Point (n + 2)) :
    exactOrderPointOfGenerator hn V (h ▸ P) = exactOrderPointOfGenerator hn U P := by
  cases h
  rfl

variable [IsDomain (ShortBase R)]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Two marked points give the same pair class exactly when one is
obtained by unit multiplication of its generator and short scaling. -/
theorem shortCoverPairClass_eq_iff (h₂ : (2 : k) ≠ 0) (h₃ : (3 : k) ≠ 0)
    (f g : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k) :
    (Quot.mk _ (shortCoverPair hn f) : PairClasses k (n + 2)) = Quot.mk _ (shortCoverPair hn g) ↔
      ∃ (a : (ZMod (n + 2))ˣ) (u : kˣ),
        g = scaleShortExactOrderPoint hn u (f.comp (shortLevelUnitAut hn a).toAlgHom) := by
  letI : NeZero (n + 2) := ⟨by omega⟩
  obtain ⟨⟨c, P⟩, rfl⟩ := (shortExactOrderPoints hn).symm.surjective f
  obtain ⟨⟨b, Q⟩, rfl⟩ := (shortExactOrderPoints hn).symm.surjective g
  let W := (shortFamily R).map c.toRingHom
  let V := (shortFamily R).map b.toRingHom
  letI : W.IsShortNF := short_specialized c
  letI : V.IsShortNF := short_specialized b
  rw [← exactOrderPointOfGenerator_specialized hn c P, ← exactOrderPointOfGenerator_specialized hn b Q,
    shortCoverPair_marked, shortCoverPair_marked]
  let X : EnhancedCurve k (n + 2) := ⟨W, inferInstance, subgroupOfGenerator P⟩
  let Y : EnhancedCurve k (n + 2) := ⟨V, inferInstance, subgroupOfGenerator Q⟩
  have scale_marked (u : kˣ) (T : Generators W.toAffine.Point (n + 2)) :
      let V' := shortScaling u • W
      letI := (shortScaling_coefficients W u).1
      scaleShortExactOrderPoint hn u (exactOrderPointOfGenerator hn W T) =
        exactOrderPointOfGenerator hn V'
          ⟨(Point.addEquivVariableChange W (shortScaling u)).symm T.val,
            (shortScaling_order_mul W u T.val 0).1.trans T.property⟩ := by
    rw [exactOrderPointOfGenerator_specialized hn c T]
    exact scale_inverse_shortExactOrderPoints hn u c T
  constructor
  · intro h
    obtain ⟨v, hv, he⟩ := (pairClasses_eq_iff X Y).mp h
    change v • W = V at hv
    haveI : (v • W).IsShortNF := hv.symm ▸ (inferInstance : V.IsShortNF)
    obtain ⟨hr, hs, ht⟩ := short_change_parameters W v h₂ h₃
    let u := v.u⁻¹
    have hu : shortScaling u = v := by
      cases v
      simp_all [shortScaling, u]
    have hV : shortScaling u • W = V := hu.symm ▸ hv
    let e := changePoints W V (shortScaling u) hV
    have he' : e.mapAddSubgroup (subgroupOfGenerator P).val = (subgroupOfGenerator Q).val := by
      change (changePoints W V (shortScaling u) hV).mapAddSubgroup _ = _
      revert hV
      rw [hu]
      intro _
      exact he
    let P' : Generators V.toAffine.Point (n + 2) :=
      ⟨e P.val, (addOrderOf_injective e.toAddMonoidHom e.injective P.val).trans P.property⟩
    obtain ⟨a, ha⟩ := (generatorOrbit_iff P' Q).2 ((map_subgroupOfGenerator e P).trans he')
    refine ⟨a, u, ?_⟩
    obtain ⟨T, hT, hf⟩ := shortLevelUnitAut_on_generator hn a W P
    rw [hf, scale_marked]
    have hQ : Q.val = e T.val := by
      calc
        Q.val = (a : ZMod (n + 2)).val • e P.val := (congrArg Subtype.val ha).symm
        _ = e T.val := by rw [hT, map_nsmul]
    let V' := shortScaling u • W
    letI : V'.IsShortNF := (shortScaling_coefficients W u).1
    let T' : Generators V'.toAffine.Point (n + 2) :=
      ⟨(Point.addEquivVariableChange W (shortScaling u)).symm T.val,
        (shortScaling_order_mul W u T.val 0).1.trans T.property⟩
    have hQ' : Q = ((hV ▸ T') : Generators V.toAffine.Point (n + 2)) := Subtype.ext
      (hQ.trans (generator_transport W V (shortScaling u) hV T T' rfl).symm)
    change exactOrderPointOfGenerator hn V Q = exactOrderPointOfGenerator hn V' T'
    rw [hQ']
    exact exactOrderPointOfGenerator_cast hn hV T'
  · rintro ⟨a, u, h⟩
    obtain ⟨T, hT, hf⟩ := shortLevelUnitAut_on_generator hn a W P
    rw [hf, scale_marked] at h
    have hpair := congrArg (shortCoverPair hn) h
    rw [shortCoverPair_marked, shortCoverPair_marked] at hpair
    rw [hpair]
    apply (pairClasses_eq_iff _ _).2
    refine ⟨shortScaling u, rfl, ?_⟩
    let e := (Point.addEquivVariableChange W (shortScaling u)).symm
    change e.mapAddSubgroup (subgroupOfGenerator P).val = AddSubgroup.zmultiples (e T.val)
    have hPT := (generatorOrbit_iff P T).1 ⟨a, Subtype.ext hT.symm⟩
    exact (congrArg e.mapAddSubgroup hPT).trans (map_subgroupOfGenerator e T).symm

#print axioms short_specialized
#print axioms shortCoverPair
#print axioms markedPair_cast
#print axioms shortCoverPair_marked
#print axioms coefficientPoint_specialized
#print axioms markedSigma_eq
#print axioms exactOrderPointOfGenerator_specialized
#print axioms shortCoverPairClass_surjective
#print axioms map_subgroupOfGenerator
#print axioms generator_transport
#print axioms exactOrderPointOfGenerator_cast
#print axioms shortCoverPairClass_eq_iff

end WeierstrassCurve.ModelLevels
