import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.CoverPairs
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.RationalPoints
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-! **Enhanced curves along ring maps of fields** (rc-model-generic7, item 2, T1 and T2).

* `pointMapAlong σ W`: TauCeti's `Point.mapAlong` along a ring map `σ : k₁ →+* k₂` of fields, as
  an additive map `W(k₁) → (W.map σ)(k₂)` (additivity is TauCeti's `mapAlong_add`).
  `ptMap_eq_pointMapAlong`: it is the vendored `ptMap` (both send `(x, y)` to `(σ x, σ y)`).
* `pairClassesMap σ : PairClasses k₁ N → PairClasses k₂ N` (T1): map the curve along `σ` and
  the cyclic subgroup along `pointMapAlong σ`. It is well defined because a variable change `v`
  goes to `v.map σ` (Mathlib's `map_variableChange`) and the variable-change point maps commute
  with `pointMapAlong` (coordinate formula). `pairClassesMap_id`, `pairClassesMap_comp`, and for a
  ring isomorphism `pairClassesMap_symm_apply`. No characteristic hypothesis.
* `cyclicQuotientCurve_map` (T2): the vendored Vélu composite commutes with ring maps of fields
  with algebraically closed source, in every characteristic. This re-derives the `hc` step of
  the vendored `cyclicQuotientJ_map` from the public `iterate_cqjStep_stMap`,
  `cyclicQuotientCurve_def` and `cqjIterate_def`.
* `shortCoverPair_comp`: the pair read on a cover point is natural along algebra maps of fields.
* `rationalPoints_comp`: `rationalPoints h₂ (σ ∘ x) = pairClassesMap σ (rationalPoints h₂ x)`
  for every `ℚ`-algebra map `σ` of algebraically closed fields of characteristic 0, and
  `rationalPoints_ringEquiv` for a ring isomorphism.

Provenance: on the spot (c); transport of structure along a field map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric7

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.ModelLevels
  WeierstrassCurve.ModelTorsion

section Fields

variable {k₁ k₂ k₃ : Type*} [Field k₁] [Field k₂] [Field k₃]
  [DecidableEq k₁] [DecidableEq k₂] [DecidableEq k₃]

/-- TauCeti's point map `Point.mapAlong σ` along a ring map of fields, as an additive map. -/
def pointMapAlong (σ : k₁ →+* k₂) (W : WeierstrassCurve k₁) :
    W.toAffine.Point →+ (W.map σ).toAffine.Point :=
  AddMonoidHom.mk' (Point.mapAlong σ σ.injective) (Point.mapAlong_add σ σ.injective)

theorem pointMapAlong_apply (σ : k₁ →+* k₂) (W : WeierstrassCurve k₁) (P : W.toAffine.Point) :
    pointMapAlong σ W P = Point.mapAlong σ σ.injective P :=
  rfl

theorem pointMapAlong_injective (σ : k₁ →+* k₂) (W : WeierstrassCurve k₁) :
    Function.Injective (pointMapAlong σ W) :=
  Point.mapAlong_injective σ σ.injective

/-- The vendored `ptMap` is TauCeti's `Point.mapAlong`, pointwise. -/
theorem ptMap_eq_pointMapAlong (σ : k₁ →+* k₂) (W : WeierstrassCurve k₁) :
    P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.P2MKcCQJbc.ptMap
      σ W = pointMapAlong σ W := by
  ext P
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

/-- A cyclic subgroup of order `N` mapped along `pointMapAlong σ` (injective). -/
def cyclicMap (σ : k₁ →+* k₂) (W : WeierstrassCurve k₁) {N : ℕ}
    (C : CyclicSubgroups W.toAffine.Point N) : CyclicSubgroups (W.map σ).toAffine.Point N :=
  ⟨C.1.map (pointMapAlong σ W), by
    have e := AddSubgroup.equivMapOfInjective C.1 (pointMapAlong σ W) (pointMapAlong_injective σ W)
    exact ⟨e.isAddCyclic.mp C.2.1, (Nat.card_congr e.toEquiv).symm.trans C.2.2⟩⟩

/-- An enhanced curve mapped along a ring map of fields: the curve `A.equation.map σ` and the
image of the subgroup under `pointMapAlong σ`. -/
def enhancedMap (σ : k₁ →+* k₂) {N : ℕ} (A : EnhancedCurve k₁ N) : EnhancedCurve k₂ N :=
  haveI := A.elliptic
  ⟨A.equation.map σ, inferInstance, cyclicMap σ A.equation A.subgroup⟩

/-- Two enhanced curves with equal equations and corresponding subgroups are equal. -/
theorem enhancedCurve_eq {N : ℕ} {A B : EnhancedCurve k₁ N} (h : A.equation = B.equation)
    (hs : ∀ P, P ∈ A.subgroup.1 ↔
      cast (congrArg (fun V : WeierstrassCurve k₁ => V.toAffine.Point) h) P ∈ B.subgroup.1) :
    A = B := by
  obtain ⟨Ae, Aell, AC⟩ := A
  obtain ⟨Be, Bell, BC⟩ := B
  dsimp only at h hs
  subst h
  have : AC = BC := Subtype.ext (AddSubgroup.ext hs)
  subst this
  rfl

/-- Two enhanced curves related by a variable change `v` define the same class, with the
subgroup condition read through the forward variable-change point map. -/
theorem quot_mk_eq_of_variableChange {N : ℕ} (A B : EnhancedCurve k₁ N) (v : VariableChange k₁)
    (h : v • A.equation = B.equation)
    (hs : ∀ P : (v • A.equation).toAffine.Point,
      Point.addEquivVariableChange A.equation v P ∈ A.subgroup.1 ↔
        cast (congrArg (fun V : WeierstrassCurve k₁ => V.toAffine.Point) h) P ∈ B.subgroup.1) :
    (Quot.mk _ A : PairClasses k₁ N) = Quot.mk _ B := by
  obtain ⟨Be, Bell, BC⟩ := B
  dsimp only at h hs
  subst h
  apply Quot.sound
  refine ⟨v, rfl, ?_⟩
  ext P
  change P ∈ A.subgroup.1.map (Point.addEquivVariableChange A.equation v).symm.toAddMonoidHom ↔
    P ∈ BC.1
  rw [AddSubgroup.mem_map_equiv, AddEquiv.symm_symm]
  exact hs P

/-- The variable-change point maps commute with `pointMapAlong`. -/
theorem addEquivVariableChange_pointMapAlong (σ : k₁ →+* k₂) (W : WeierstrassCurve k₁)
    (v : VariableChange k₁) (Q : (v • W).toAffine.Point) :
    Point.addEquivVariableChange (W.map σ) (v.map σ)
        (cast (congrArg (fun V : WeierstrassCurve k₂ => V.toAffine.Point)
          (WeierstrassCurve.map_variableChange W v σ).symm) (pointMapAlong σ (v • W) Q)) =
      pointMapAlong σ W (Point.addEquivVariableChange W v Q) := by
  rcases Q with _ | ⟨x, y, h⟩
  · have h0 : (Point.zero : (v • W).toAffine.Point) = 0 := rfl
    rw [h0, map_zero, Point.cast_zero, map_zero, map_zero, map_zero]
    exact (WeierstrassCurve.map_variableChange W v σ).symm
  · rw [pointMapAlong_apply, Point.mapAlong_some, Point.cast_some,
      Point.coe_addEquivVariableChange, Point.coe_addEquivVariableChange,
      Point.equivVariableChange_some, Point.equivVariableChange_some, pointMapAlong_apply,
      Point.mapAlong_some]
    simp only [VariableChange.map, Units.coe_map, MonoidHom.coe_ofClass, map_add, map_mul, map_pow]
    all_goals exact (WeierstrassCurve.map_variableChange W v σ).symm

/-- **`PairClasses.map` along a ring map of fields** (T1). The class of `(E, C)` goes to the
class of `(E.map σ, C.map (pointMapAlong σ E))`. -/
def pairClassesMap (σ : k₁ →+* k₂) (N : ℕ) : PairClasses k₁ N → PairClasses k₂ N :=
  Quot.lift (fun A => Quot.mk _ (enhancedMap σ A)) (by
    rintro A ⟨Be, Bell, BC⟩ ⟨v, h, hsub⟩
    dsimp only at h hsub
    subst h
    have hBC : ∀ Q, Q ∈ BC.1 ↔ Point.addEquivVariableChange A.equation v Q ∈ A.subgroup.1 := by
      intro Q
      have hsub' : (Point.addEquivVariableChange A.equation v).symm.mapAddSubgroup A.subgroup.1 =
          BC.1 := hsub
      rw [← hsub']
      change Q ∈ A.subgroup.1.map (Point.addEquivVariableChange A.equation v).symm.toAddMonoidHom ↔ _
      rw [AddSubgroup.mem_map_equiv, AddEquiv.symm_symm]
    have h' := (WeierstrassCurve.map_variableChange A.equation v σ)
    refine quot_mk_eq_of_variableChange _ _ (v.map σ) h' fun P => ?_
    change _ ∈ A.subgroup.1.map (pointMapAlong σ A.equation) ↔
      _ ∈ BC.1.map (pointMapAlong σ (v • A.equation))
    constructor
    · rintro ⟨R, hR, hRP⟩
      let Q := (Point.addEquivVariableChange A.equation v).symm R
      have hQ : Q ∈ BC.1 := (hBC Q).2 (by simpa [Q] using hR)
      refine ⟨Q, hQ, ?_⟩
      have key := addEquivVariableChange_pointMapAlong σ A.equation v Q
      simp only [Q, AddEquiv.apply_symm_apply] at key
      rw [hRP] at key
      have hP := (Point.addEquivVariableChange (A.equation.map σ) (v.map σ)).injective key
      rw [← hP]
      exact ((cast_cast _ _ _).trans (cast_eq _ _)).symm
    · rintro ⟨Q, hQ, hQP⟩
      refine ⟨Point.addEquivVariableChange A.equation v Q, (hBC Q).1 hQ, ?_⟩
      rw [← addEquivVariableChange_pointMapAlong σ A.equation v Q]
      congr 1
      rw [hQP]
      exact (cast_cast _ _ _).trans (cast_eq _ _))

theorem pairClassesMap_mk (σ : k₁ →+* k₂) {N : ℕ} (A : EnhancedCurve k₁ N) :
    pairClassesMap σ N (Quot.mk _ A) = Quot.mk _ (enhancedMap σ A) :=
  rfl

theorem pointMapAlong_id (W : WeierstrassCurve k₁) :
    pointMapAlong (RingHom.id k₁) W = AddMonoidHom.id _ := by
  ext P
  exact Point.mapAlong_id P

theorem pairClassesMap_id (N : ℕ) (x : PairClasses k₁ N) :
    pairClassesMap (RingHom.id k₁) N x = x := by
  induction x using Quot.ind with
  | mk A =>
    rw [pairClassesMap_mk]
    congr 1
    refine enhancedCurve_eq rfl fun P => ?_
    change P ∈ A.subgroup.1.map (pointMapAlong (RingHom.id k₁) A.equation) ↔ P ∈ A.subgroup.1
    rw [pointMapAlong_id, AddSubgroup.map_id]

theorem pointMapAlong_comp (σ : k₁ →+* k₂) (τ : k₂ →+* k₃) (W : WeierstrassCurve k₁)
    (P : W.toAffine.Point) :
    pointMapAlong τ (W.map σ) (pointMapAlong σ W P) = pointMapAlong (τ.comp σ) W P :=
  Point.mapAlong_mapAlong σ σ.injective τ τ.injective P

theorem pairClassesMap_comp (σ : k₁ →+* k₂) (τ : k₂ →+* k₃) (N : ℕ) (x : PairClasses k₁ N) :
    pairClassesMap τ N (pairClassesMap σ N x) = pairClassesMap (τ.comp σ) N x := by
  induction x using Quot.ind with
  | mk A =>
    rw [pairClassesMap_mk, pairClassesMap_mk, pairClassesMap_mk]
    congr 1
    refine enhancedCurve_eq rfl fun P => ?_
    change P ∈ (A.subgroup.1.map (pointMapAlong σ A.equation)).map
        (pointMapAlong τ (A.equation.map σ)) ↔
      P ∈ A.subgroup.1.map (pointMapAlong (τ.comp σ) A.equation)
    rw [AddSubgroup.map_map]
    have : (pointMapAlong τ (A.equation.map σ)).comp (pointMapAlong σ A.equation) =
        pointMapAlong (τ.comp σ) A.equation := AddMonoidHom.ext (pointMapAlong_comp σ τ _)
    rw [this]

/-- Along a ring isomorphism, `pairClassesMap σ.symm` inverts `pairClassesMap σ`. -/
theorem pairClassesMap_symm_apply (σ : k₁ ≃+* k₂) (N : ℕ) (x : PairClasses k₁ N) :
    pairClassesMap (σ.symm : k₂ →+* k₁) N (pairClassesMap (σ : k₁ →+* k₂) N x) = x := by
  rw [pairClassesMap_comp]
  have : (σ.symm : k₂ →+* k₁).comp (σ : k₁ →+* k₂) = RingHom.id k₁ := by
    ext a
    simp
  rw [this, pairClassesMap_id]

theorem pairClassesMap_apply_symm (σ : k₁ ≃+* k₂) (N : ℕ) (x : PairClasses k₂ N) :
    pairClassesMap (σ : k₁ →+* k₂) N (pairClassesMap (σ.symm : k₂ →+* k₁) N x) = x := by
  simpa using pairClassesMap_symm_apply σ.symm N x

/-- Along a ring isomorphism, `pairClassesMap` is injective. -/
theorem pairClassesMap_injective (σ : k₁ ≃+* k₂) (N : ℕ) :
    Function.Injective (pairClassesMap (σ : k₁ →+* k₂) N) :=
  Function.LeftInverse.injective (pairClassesMap_symm_apply σ N)

end Fields

section T2

open P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.P2MKcCQJbc

variable {A B : Type*} [Field A] [Field B] [DecidableEq A] [DecidableEq B] [IsAlgClosed A]

/-- **The vendored Vélu composite commutes with ring maps of fields** (T2), for algebraically
closed source, in every characteristic. Re-derivation of the `hc` step of the vendored
`cyclicQuotientJ_map` from the public `iterate_cqjStep_stMap`. -/
theorem cyclicQuotientCurve_map (σ : A →+* B) (V : WeierstrassCurve A)
    (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    (V.map σ).cyclicQuotientCurve (H.map (pointMapAlong σ V)) N =
      (V.cyclicQuotientCurve H N).map σ := by
  rw [← ptMap_eq_pointMapAlong]
  have h := iterate_cqjStep_stMap σ N.primeFactorsList.length ⟨⟨V, H⟩, N⟩
  rw [cyclicQuotientCurve_def, cyclicQuotientCurve_def, cqjIterate_def, cqjIterate_def]
  exact congrArg (fun s : CQJState B => s.1.1) h

end T2

section Cover

variable {R : Type*} [CommRing R] {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : ShortBase R))
  [Algebra R (ExactOrderAlgebra (shortFamily R) hn)]
  [IsScalarTower R (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)]
  {k₁ k₂ : Type*} [Field k₁] [Field k₂] [Algebra R k₁] [Algebra R k₂]
  [DecidableEq k₁] [DecidableEq k₂]

/-- **The pair read on a cover point is natural along algebra maps of fields.** -/
theorem shortCoverPair_comp (σ : k₁ →ₐ[R] k₂)
    (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k₁) :
    shortCoverPair hn (σ.comp f) = enhancedMap (σ : k₁ →+* k₂) (shortCoverPair hn f) := by
  refine enhancedCurve_eq rfl fun P => ?_
  obtain ⟨h₁, e₁⟩ := shortExactOrderPoints_affine hn (σ.comp f)
  obtain ⟨h₂, e₂⟩ := shortExactOrderPoints_affine hn f
  change P ∈ AddSubgroup.zmultiples (shortExactOrderPoints hn (σ.comp f)).2.1 ↔
    P ∈ (AddSubgroup.zmultiples (shortExactOrderPoints hn f).2.1).map
      (pointMapAlong (σ : k₁ →+* k₂) _)
  rw [AddMonoidHom.map_zmultiples, e₁, e₂, pointMapAlong_apply, Point.mapAlong_some]
  rfl

theorem shortCoverPair_class_comp (σ : k₁ →ₐ[R] k₂)
    (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k₁) :
    (Quot.mk _ (shortCoverPair hn (σ.comp f)) : PairClasses k₂ (n + 2)) =
      pairClassesMap (σ : k₁ →+* k₂) (n + 2) (Quot.mk _ (shortCoverPair hn f)) := by
  rw [pairClassesMap_mk, shortCoverPair_comp]

end Cover

section Rational

open ModelGeneric ModelGeneric2 RC.ModelInvariants

open private rationalLevel_isUnit from ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational

variable {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra ℚ K₁] [Algebra ℚ K₂]
  [DecidableEq K₁] [DecidableEq K₂] [IsAlgClosed K₁] [IsAlgClosed K₂]

set_option maxHeartbeats 1000000 in
/-- **Naturality of the rational point reading** (T1): for every `ℚ`-algebra map `σ` of
algebraically closed fields of characteristic 0,
`rationalPoints h₂ (σ ∘ x) = pairClassesMap σ (rationalPoints h₂ x)`. Through a lift of `x` to
the cover (`degreeZeroInvariants_restrict_surjective`), the computation property of
`rationalPointReading` and `shortCoverPair_class_comp`. -/
theorem rationalPoints_comp {N : ℕ} [NeZero N] (h₂ : 2 ≤ N) (σ : K₁ →ₐ[ℚ] K₂)
    (x : Y0RationalAlgebra h₂ →ₐ[ℚ] K₁) :
    rationalPoints h₂ (σ.comp x) = pairClassesMap (σ : K₁ →+* K₂) N (rationalPoints h₂ x) := by
  obtain _ | _ | n := N
  · omega
  · omega
  let hn := rationalLevel_isUnit (N := n + 2)
  let gr := rationalGrading h₂
  letI := rationalAction h₂
  letI := rationalAction_comm h₂
  letI := rationalGradedAlgebra h₂
  letI := rationalAction_preserves h₂
  have hδ : (↑(shortExactOrderDiscriminantUnit (R := ℚ) hn) : rationalCover (n + 2)) ∈
      gr 12 := shortExactOrderDiscriminantUnit_mem (R := ℚ) hn
  obtain ⟨f, rfl⟩ := degreeZeroInvariants_restrict_surjective (G := (ZMod (n + 2))ˣ)
    (k := K₁) gr (by decide) hδ x
  change (rationalPointReading h₂).val (σ.comp (f.comp (Y0RationalInclusion h₂))) =
    pairClassesMap (σ : K₁ →+* K₂) (n + 2)
      ((rationalPointReading h₂).val (f.comp (Y0RationalInclusion h₂)))
  rw [← AlgHom.comp_assoc, (rationalPointReading h₂).property, (rationalPointReading h₂).property]
  exact shortCoverPair_class_comp _ σ f

/-- `rationalPoints_comp` along a ring isomorphism of algebraically closed fields of
characteristic 0 (a ring isomorphism of `ℚ`-algebras is `ℚ`-linear). -/
theorem rationalPoints_ringEquiv {N : ℕ} [NeZero N] (h₂ : 2 ≤ N) (σ : K₁ ≃+* K₂)
    (x : Y0RationalAlgebra h₂ →ₐ[ℚ] K₁) :
    rationalPoints h₂ ((σ : K₁ →+* K₂).toRatAlgHom.comp x) =
      pairClassesMap (σ : K₁ →+* K₂) N (rationalPoints h₂ x) :=
  rationalPoints_comp h₂ _ x

end Rational

end ZInQ.Manuscript.RC.ModelGeneric7

#print axioms ZInQ.Manuscript.RC.ModelGeneric7.ptMap_eq_pointMapAlong
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.pairClassesMap
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.pairClassesMap_id
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.pairClassesMap_comp
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.pairClassesMap_symm_apply
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.pairClassesMap_injective
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.cyclicQuotientCurve_map
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.shortCoverPair_comp
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.rationalPoints_comp
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.rationalPoints_ringEquiv
