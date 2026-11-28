import ZInQKernel.Contrib.OneProof.RC.SamePlace.Supersingular
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong

/-! # The Frobenius twist on the coarse special fibre (rc-same-place1, item 5)

For a bijective ring endomorphism `σ` of a field `K` (in use: the `ell`-power Frobenius
`frobenius K ell` of a perfect field of characteristic `ell`, bijective by Mathlib's
`bijective_frobenius`), the twist `E ↦ E.map σ` of Weierstrass curves comes with the group
isomorphism `twistPoints σ hσ E : E(K) ≃+ (E.map σ)(K)`, the tree's point map
`Point.mapAlong σ` (additive over fields by `mapAlong_add`, surjective along a surjective map by
`mapAlong_surjective`). It commutes with variable changes (`mapAlong_changePoints`, with
Mathlib's `map_variableChange`), so it descends to the pair classes (`pairTwist σ hσ`), and it
preserves supersingularity since it maps `E[ell]` bijectively (`isSupersingular_map`).

`frobTwist ell` is the twist along `frobenius K ell` on `PairClasses K N`, and
`frobTwistSS ell` its restriction to the supersingular classes `ssPoint K ell N`: the moduli-side
`X.frobenius` of the same-place lane (never `J ∘ uniformizer ∘ J⁻¹`).

Provenance: on the spot (c). The manuscript asserts that Frobenius acts on the supersingular set
(tex 8489–8490); the descent of the twist to pair classes and the supersingularity argument are
not printed there. Sketch: a variable change `v` from `A` to `B` maps to the variable change
`v.map σ` from `A.map σ` to `B.map σ`, with coordinates transformed by `σ`; and `E[ell] ≅
(E.map σ)[ell]` along the additive bijection `mapAlong σ`. -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Manuscript.RC.SamePlace

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.ModelLevels

section General

variable {F L : Type} [Field F] [Field L] [DecidableEq F] [DecidableEq L] (φ : F →+* L)

/-- **The point map along a ring map commutes with variable changes.** -/
theorem mapAlong_changePoints (W V : WeierstrassCurve F) (v : VariableChange F) (h : v • W = V)
    (h' : v.map φ • W.map φ = V.map φ) (P : W.toAffine.Point) :
    Point.mapAlong φ φ.injective (changePoints W V v h P) =
      changePoints (W.map φ) (V.map φ) (v.map φ) h' (Point.mapAlong φ φ.injective P) := by
  subst h
  have hinv : (v.map φ)⁻¹ = (v⁻¹).map φ := ((VariableChange.mapHom φ).map_inv v).symm
  change Point.mapAlong φ φ.injective ((Point.addEquivVariableChange W v).symm P) =
    cast (congrArg (fun V : WeierstrassCurve L => V.toAffine.Point) h')
      ((Point.addEquivVariableChange (W.map φ) (v.map φ)).symm (Point.mapAlong φ φ.injective P))
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← Point.zero_def, map_zero, Point.mapAlong_zero, Point.mapAlong_zero, map_zero,
      Point.cast_zero h']
  · rw [Point.mapAlong_some, Point.coe_addEquivVariableChange_symm,
      Point.coe_addEquivVariableChange_symm, Point.equivVariableChange_symm_some,
      Point.equivVariableChange_symm_some, Point.mapAlong_some, Point.cast_some h']
    simp only [hinv, VariableChange.map_u, VariableChange.map_r, VariableChange.map_s,
      VariableChange.map_t, Units.coe_map, MonoidHom.coe_coe, map_add, map_mul, map_pow]

end General

variable {K : Type} [Field K] [DecidableEq K] (σ : K →+* K) (hσ : Function.Bijective σ)

/-- **The twist on points**: `Point.mapAlong σ` as a group isomorphism `E(K) ≃+ (E.map σ)(K)`. -/
def twistPoints (E : WeierstrassCurve K) : E.toAffine.Point ≃+ (E.map σ).toAffine.Point :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (Point.mapAlong σ σ.injective) (Point.mapAlong_add σ σ.injective))
    ⟨Point.mapAlong_injective σ σ.injective, Point.mapAlong_surjective σ σ.injective hσ.2⟩

@[simp] theorem twistPoints_apply (E : WeierstrassCurve K) (P : E.toAffine.Point) :
    twistPoints σ hσ E P = Point.mapAlong σ σ.injective P :=
  rfl

/-- The twist of a cyclic subgroup of order `N` is a cyclic subgroup of order `N`. -/
def twistSubgroup {N : ℕ} (E : WeierstrassCurve K) (C : CyclicSubgroups E.toAffine.Point N) :
    CyclicSubgroups (E.map σ).toAffine.Point N :=
  ⟨C.1.map (twistPoints σ hσ E).toAddMonoidHom, by
    let e := C.1.equivMapOfInjective (twistPoints σ hσ E).toAddMonoidHom
      (twistPoints σ hσ E).injective
    haveI := C.2.1
    exact ⟨isAddCyclic_of_surjective e.toAddMonoidHom e.surjective,
      (Nat.card_congr e.toEquiv).symm.trans C.2.2⟩⟩

/-- The twist of an enhanced curve. -/
def twistEnhanced {N : ℕ} (A : EnhancedCurve K N) : EnhancedCurve K N :=
  letI := A.elliptic
  ⟨A.equation.map σ, inferInstance, twistSubgroup σ hσ A.equation A.subgroup⟩

/-- **The twist on pair classes**, well defined through variable changes. -/
def pairTwist {N : ℕ} : PairClasses K N → PairClasses K N :=
  Quot.lift (fun A => Quot.mk _ (twistEnhanced σ hσ A)) (by
    intro A B hAB
    obtain ⟨v, h, hs⟩ := (pairClasses_eq_iff A B).mp (Quot.sound hAB)
    have h' : v.map σ • A.equation.map σ = B.equation.map σ := by
      rw [map_variableChange, h]
    refine (pairClasses_eq_iff _ _).mpr ⟨v.map σ, h', ?_⟩
    change AddSubgroup.map _ (A.subgroup.1.map (twistPoints σ hσ A.equation).toAddMonoidHom) =
      B.subgroup.1.map (twistPoints σ hσ B.equation).toAddMonoidHom
    rw [← hs]
    change AddSubgroup.map _ (A.subgroup.1.map _) = AddSubgroup.map _ (A.subgroup.1.map _)
    simp only [AddSubgroup.map_map]
    refine (AddSubgroup.map_map _ _ _).trans ?_
    refine congrArg (fun g : A.equation.toAffine.Point →+ (B.equation.map σ).toAffine.Point =>
      AddSubgroup.map g A.subgroup.1) (AddMonoidHom.ext fun P => ?_)
    exact (mapAlong_changePoints σ A.equation B.equation v h h' P).symm)

@[simp] theorem pairTwist_mk {N : ℕ} (A : EnhancedCurve K N) :
    pairTwist σ hσ (Quot.mk _ A : PairClasses K N) = Quot.mk _ (twistEnhanced σ hσ A) :=
  rfl

include hσ in
/-- **The twist preserves supersingularity**: it maps `E[ell]` bijectively. -/
theorem isSupersingular_map (ell : ℕ) (E : WeierstrassCurve K) [E.IsElliptic] :
    IsSupersingular ell (E.map σ) ↔ IsSupersingular ell E :=
  (torsionBy_eq_bot_congr (twistPoints σ hσ E) _).symm

theorem pairTwist_isSupersingular {N : ℕ} (ell : ℕ) (x : PairClasses K N) :
    PairClasses.IsSupersingular ell (pairTwist σ hσ x) ↔ PairClasses.IsSupersingular ell x := by
  induction x using Quot.ind with
  | _ A =>
    letI := A.elliptic
    exact isSupersingular_map σ hσ ell A.equation

section Frobenius

variable (ell : ℕ) [Fact ell.Prime] [CharP K ell] [PerfectRing K ell]

/-- **The `ell`-power Frobenius twist on pair classes**: `E ↦ E.map (frobenius K ell)`, with the
cyclic subgroup moved by the point map `Point.mapAlong (frobenius K ell)`. -/
def frobTwist {N : ℕ} : PairClasses K N → PairClasses K N :=
  pairTwist (frobenius K ell) (bijective_frobenius K ell)

/-- **The moduli-side `X.frobenius`**: the Frobenius twist on the supersingular pair classes. -/
def frobTwistSS {N : ℕ} (x : ssPoint K ell N) : ssPoint K ell N :=
  ⟨frobTwist ell x.1,
    (pairTwist_isSupersingular (frobenius K ell) (bijective_frobenius K ell) ell x.1).mpr x.2⟩

@[simp] theorem frobTwistSS_val {N : ℕ} (x : ssPoint K ell N) :
    (frobTwistSS ell x).1 = frobTwist ell x.1 :=
  rfl

end Frobenius

end ZInQ.Manuscript.RC.SamePlace

#print axioms ZInQ.Manuscript.RC.SamePlace.mapAlong_changePoints
#print axioms ZInQ.Manuscript.RC.SamePlace.twistPoints
#print axioms ZInQ.Manuscript.RC.SamePlace.pairTwist
#print axioms ZInQ.Manuscript.RC.SamePlace.isSupersingular_map
#print axioms ZInQ.Manuscript.RC.SamePlace.pairTwist_isSupersingular
#print axioms ZInQ.Manuscript.RC.SamePlace.frobTwist
#print axioms ZInQ.Manuscript.RC.SamePlace.frobTwistSS
