import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
import ZInQKernel.Contrib.BrauerT14T15.LocalT15
import ZInQKernel.Contrib.RC53Assist.DerivedKummerActual.Actual
import ZInQKernel.Contrib.RC53Assist.CentralKummer.RationalKummer

/-!
# The sign-line trace at the first coefficient level

Adapted from Chey Loveday's CochainsHomology, LocalInvariantTwo and LocalTraceTwo
in CheyLoveday/diophantine-z-q at 6f33aa2f664db18a6c1e428d15a148a0ae81cf7a.
The Kummer comparison uses the coefficient inclusion into the Brauer group.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.PlaceAboveTwo.SignLine

open CategoryTheory HomologicalComplex
open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Contrib.BrauerT14T15
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open ZInQ.Contrib.CloudB3RC53.Duality
open ZInQ.Manuscript.RC53Assist.CentralKummer

section Cochains

universe u

variable {R G : Type u} [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The homogeneous complex after forgetting the topology and extending by zero. -/
def cochains (X : TopRep.{u} R G) : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((forget₂ (TopModuleCat R) (ModuleCat R)).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat R)).obj (TopRep.homogeneousCochains X)

/-- The homology of the integer-indexed cochain model is Mathlib's
continuous cohomology with the topology on its carrier forgotten. -/
noncomputable def cochainsHomologyIso (X : TopRep.{u} R G) (n : ℕ) :
    (cochains X).homology (n : ℤ) ≅
      (forget₂ (TopModuleCat R) (ModuleCat R)).obj (continuousCohomology n X) := by
  let F := forget₂ (TopModuleCat R) (ModuleCat R)
  let A := TopRep.homogeneousCochains X
  let B := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj A
  have inherited : F.PreservesHomology := by infer_instance
  exact (B.extendHomologyIso ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl) ≪≫
    (A.sc n).mapHomologyIso F

end Cochains

/-- At precision two, `μ₂` is the sign line written additively. -/
abbrev signLine (G : Type) [Group G] : TopRep (ZMod 2) G :=
  TopRep.of (ContRepresentation.trivial (ZMod 2) G (ZMod 2))

local instance trivialAction (G : Type) [Group G] : DistribMulAction G (ZMod 2) :=
  (signLine G).distribMulAction

local instance continuousTrivialAction (G : Type) [Group G] [TopologicalSpace G] :
    ContinuousSMul G (ZMod 2) := ⟨continuous_snd⟩

private theorem trivial_smul {G : Type} [Group G] (g : G) (x : ZMod 2) : g • x = x := rfl

variable (F : Type) [Field F]

/-- The mod-two sign-line complex over the algebraic-closure Galois group. -/
abbrev signComplex := cochains (signLine (Field.absoluteGaloisGroup F))

private def sepClasses : H2 (Field.absoluteGaloisGroup F) (ZMod 2) ≃+
    H2 (AbsoluteGaloisGroup F) (ZMod 2) :=
  explicitMap2Equiv _ _ _ _ (absoluteGaloisGroupRestrictEquiv F).symm
    (AddEquiv.refl _) continuous_id continuous_id (by
      intro g a
      rfl)

private def signCoeff : ZMod 2 →+[AbsoluteGaloisGroup F] UnitsCoeff F where
  __ := sgn F
  map_smul' g a := (smul_sgn g a).symm

private def signClasses : H2 (AbsoluteGaloisGroup F) (ZMod 2) →+
    H2 (AbsoluteGaloisGroup F) (UnitsCoeff F) :=
  explicitCoeff2 _ _ (signCoeff F) continuous_of_discreteTopology

private theorem asCocycle (c : Z2 (AbsoluteGaloisGroup F) (ZMod 2)) :
    PkgI6.IsCocycle2 (fun g h => c.1 (g, h)) := by
  refine ⟨(mem_Z2_iff.mp c.2).1, fun g h k => ?_⟩
  have he := (mem_Z2_iff.mp c.2).2 g h k
  rw [trivial_smul] at he
  linear_combination -he

private theorem signClasses_mk (c : Z2 (AbsoluteGaloisGroup F) (ZMod 2)) :
    signClasses F (H2pi _ _ c) =
      H2pi (AbsoluteGaloisGroup F) (UnitsCoeff F)
        ⟨fun q => sgn F (c.1 q), sgn_mem_Z2 (asCocycle F c)⟩ := rfl

private theorem signClasses_injective [CharZero F] : Function.Injective (signClasses F) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
  change signClasses F (H2pi _ _ c) = 0 at hx
  rw [signClasses_mk F c] at hx
  obtain ⟨f, hf, he⟩ := isCoboundary2_of_sgn_mem_B2 (K := F) two_ne_zero (asCocycle F c)
    (H2pi_eq_zero_iff.mp hx)
  apply H2pi_eq_zero_iff.mpr
  exact mem_B2_iff'.mpr ⟨f, hf, fun g h => (he g h).symm⟩

private theorem exists_signClasses [CharZero F]
    (x : H2 (AbsoluteGaloisGroup F) (UnitsCoeff F)) (hx : 2 • x = 0) :
    ∃ a, signClasses F a = x := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨ε, hε, h⟩ := exists_sgn_eq_of_two_nsmul (K := F) two_ne_zero z hx
  let c : Z2 (AbsoluteGaloisGroup F) (ZMod 2) := ⟨fun q => ε q.1 q.2, mem_Z2_iff.mpr
    ⟨hε.1, fun g h k => by
      rw [trivial_smul]
      have hc := hε.2 g h k
      linear_combination -hc⟩⟩
  exact ⟨H2pi _ _ c, (signClasses_mk F c).trans h⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem two_nsmul_modTwo (x : ZMod 2) : 2 • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
  change (0 : ZMod 2) • x = 0
  exact zero_smul _ _

/-- The sign cocycle, viewed in the Brauer group before taking its local invariant. -/
def signBrauer : (signComplex F).homology 2 →+ Br F := by
  letI : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  let X := signLine (Field.absoluteGaloisGroup F)
  exact (unitsRepH2Equiv F).toAddMonoidHom.comp ((signClasses F).comp
    ((sepClasses F).toAddMonoidHom.comp
      (X.explicitH2AddEquivContinuousCohomologyOfDiscrete.symm.toAddMonoidHom.comp
        (cochainsHomologyIso X 2).hom.hom.toAddMonoidHom)))

/-- The value of the sign cocycle under the local Brauer invariant. -/
def circleInvariant : (signComplex F).homology 2 →+
    AddCircle (1 : ℚ) :=
  (invMap F).toAddMonoidHom.comp (signBrauer F)

theorem circleInvariant_injective [CharZero F] : Function.Injective (circleInvariant F) := by
  letI : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  let X := signLine (Field.absoluteGaloisGroup F)
  exact (explicitInv F).injective.comp ((signClasses_injective F).comp
    ((sepClasses F).injective.comp
      (X.explicitH2AddEquivContinuousCohomologyOfDiscrete.symm.injective.comp
        ((ModuleCat.mono_iff_injective _).mp inferInstance))))

private theorem exists_circleInvariant [CharZero F] {y : AddCircle (1 : ℚ)} (hy : 2 • y = 0) :
    ∃ x, circleInvariant F x = y := by
  letI : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F))
  have h : 2 • (explicitInv F).symm y = 0 := by rw [← map_nsmul, hy, map_zero]
  obtain ⟨x, hx⟩ := exists_signClasses F _ h
  let e := (cochainsHomologyIso (signLine (Field.absoluteGaloisGroup F)) 2).toLinearEquiv
  let b := (signLine (Field.absoluteGaloisGroup F)).explicitH2AddEquivContinuousCohomologyOfDiscrete
  refine ⟨e.symm (b ((sepClasses F).symm x)), ?_⟩
  change explicitInv F (signClasses F ((sepClasses F) (b.symm (e (e.symm _))))) = y
  rw [e.apply_symm_apply, b.symm_apply_apply, AddEquiv.apply_symm_apply, hx,
    AddEquiv.apply_symm_apply]

private theorem circleInvariant_two_nsmul (x : (signComplex F).homology 2) :
    2 • circleInvariant F x = 0 := by
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
  change circleInvariant F ((0 : ZMod 2) • x) = 0
  rw [zero_smul, map_zero]

private def residueValue (x : (signComplex F).homology 2) : ZMod 2 :=
  (ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero 2 (circleInvariant_two_nsmul F x)).choose

private theorem residueValue_spec (x : (signComplex F).homology 2) :
    ZMod.toRatAddCircle 2 (residueValue F x) = circleInvariant F x :=
  (ZMod.exists_toRatAddCircle_eq_of_nsmul_eq_zero 2 (circleInvariant_two_nsmul F x)).choose_spec

private def residueInvariant : (signComplex F).homology 2 →+ ZMod 2 where
  toFun := residueValue F
  map_zero' := ZMod.toRatAddCircle_injective 2 <| by rw [residueValue_spec, map_zero, map_zero]
  map_add' x y := ZMod.toRatAddCircle_injective 2 <| by
    rw [map_add (ZMod.toRatAddCircle 2), residueValue_spec, residueValue_spec,
      residueValue_spec, map_add]

/-- The invariant on `H²(F, μ₂)` sends the normalized Brauer value `1/2` to `1`. -/
def invariant [CharZero F] : (signComplex F).homology 2 ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.ofBijective (AddMonoidHom.toZModLinearMap 2 (residueInvariant F)) (by
    constructor
    · intro x y he
      apply circleInvariant_injective F
      rw [← residueValue_spec F x, ← residueValue_spec F y]
      exact congrArg (ZMod.toRatAddCircle 2) he
    · intro a
      obtain ⟨x, hx⟩ := exists_circleInvariant F
        (show 2 • (ZMod.toRatAddCircle 2 a) = 0 by rw [← map_nsmul, two_nsmul_modTwo, map_zero])
      refine ⟨x, ZMod.toRatAddCircle_injective 2 ?_⟩
      exact (residueValue_spec F x).trans hx)

theorem invariant_normalization [CharZero F] (x : (signComplex F).homology 2) :
    ZMod.toRatAddCircle 2 (invariant F x) = circleInvariant F x := residueValue_spec F x

variable [CharZero F]

/-- The Kummer class whose coefficient inclusion is the Brauer class of the sign cocycle. -/
def kummerClass (x : (signComplex F).homology 2) :
    H2 (AbsoluteGaloisGroup F) (KummerCoeff F 2) :=
  (FiniteTrace.kummerBrauerEquiv F 2 (isUnit_iff_ne_zero.mpr two_ne_zero)).symm
    ⟨signBrauer F x, AddSubgroup.torsionBy.nsmul_iff.mpr (by
      rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
      change signBrauer F ((0 : ZMod 2) • x) = 0
      rw [zero_smul, map_zero])⟩

/-- The two normalizations agree for the same Brauer class at level two. -/
theorem finiteInvariant_kummerClass
    (x : (signComplex F).homology 2) :
    FiniteTrace.finiteInvariant F 2 (isUnit_iff_ne_zero.mpr two_ne_zero) (kummerClass F x) =
      invariant F x := by
  apply ZMod.toRatAddCircle_injective 2
  rw [FiniteTrace.finiteInvariant_toRat, invariant_normalization]
  apply congrArg (invMap F)
  let e := FiniteTrace.kummerBrauerEquiv F 2 (isUnit_iff_ne_zero.mpr two_ne_zero)
  exact congrArg Subtype.val (e.apply_symm_apply _)

/-- Extend the invariant to degree-two cochains and specify its value on
cycles. The extension automatically vanishes on degree-two boundaries. -/
theorem exists_local_trace : ∃ tr : (signComplex F).X 2 →ₗ[ZMod 2] ZMod 2,
    (∀ z : (signComplex F).cycles 2, tr ((signComplex F).iCycles 2 z) =
      invariant F ((signComplex F).homologyπ 2 z)) ∧
    (∀ b : (signComplex F).X 1, tr ((signComplex F).d 1 2 b) = 0) := by
  let C := signComplex F
  let tr := (invariant F).toLinearMap.comp
    ((C.homologyπ 2).hom.comp (cyclesRetraction C 2))
  have htr (z : C.cycles 2) : tr (C.iCycles 2 z) = invariant F (C.homologyπ 2 z) := by
    change invariant F (C.homologyπ 2 (cyclesRetraction C 2 (C.iCycles 2 z))) = _
    rw [cyclesRetraction_iCycles]
  refine ⟨tr, htr, fun b => ?_⟩
  have hb := congrArg (fun f : C.X 1 ⟶ C.X 2 => f b) (C.toCycles_i 1 2)
  have hp := congrArg (fun f : C.X 1 ⟶ C.homology 2 => f b)
    (C.toCycles_comp_homologyπ 1 2)
  change C.iCycles 2 (C.toCycles 1 2 b) = C.d 1 2 b at hb
  change C.homologyπ 2 (C.toCycles 1 2 b) = 0 at hp
  rw [← hb, htr]
  change invariant F (C.homologyπ 2 (C.toCycles 1 2 b)) = 0
  rw [hp, map_zero]

private def signInvariantsEquiv :
    (signLine (Field.absoluteGaloisGroup F)).ρ.invariants ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.ofBijective (signLine (Field.absoluteGaloisGroup F)).ρ.invariants.subtype
    ⟨Subtype.val_injective, fun a => ⟨⟨a, (ContRepresentation.mem_invariants _).mpr
      (fun _ => rfl)⟩, rfl⟩⟩

/-- The constant value of a degree-zero cocycle. -/
def degreeZero : (signComplex F).homology 0 ≃ₗ[ZMod 2] ZMod 2 :=
  ((cochainsHomologyIso (signLine (Field.absoluteGaloisGroup F)) 0).toLinearEquiv.trans
    (((forget₂ (TopModuleCat (ZMod 2)) (ModuleCat (ZMod 2))).mapIso
      (ContinuousCohomology.zeroIso (signLine (Field.absoluteGaloisGroup F)))).toLinearEquiv)).trans
        (signInvariantsEquiv F)

/-- The adjoint of the degree-(0,2) pairing given by scalar multiplication
followed by the local invariant. -/
def duality02 : (signComplex F).homology 2 ≃ₗ[ZMod 2]
    Module.Dual (ZMod 2) ((signComplex F).homology 0) :=
  ((invariant F).trans (LinearMap.ringLmapEquivSelf (ZMod 2) (ZMod 2) (ZMod 2)).symm).trans
    (LinearEquiv.arrowCongr (degreeZero F).symm (LinearEquiv.refl (ZMod 2) (ZMod 2)))

theorem duality02_apply (a : (signComplex F).homology 0) (x : (signComplex F).homology 2) :
    duality02 F x a = degreeZero F a * invariant F x := rfl

/-- Evaluating the cup with a constant degree-zero cocycle by any normalized
local chain trace gives the degree-(0,2) pairing. -/
theorem trace_duality02 (tr : (signComplex F).X 2 →ₗ[ZMod 2] ZMod 2)
    (normalization : ∀ z : (signComplex F).cycles 2, tr ((signComplex F).iCycles 2 z) =
      invariant F ((signComplex F).homologyπ 2 z))
    (a : (signComplex F).homology 0) (z : (signComplex F).cycles 2) :
    tr (degreeZero F a • (signComplex F).iCycles 2 z) =
      duality02 F ((signComplex F).homologyπ 2 z) a := by
  rw [map_smul, normalization, duality02_apply]
  rfl

end ZInQ.Contrib.RC53Assist.PlaceAboveTwo.SignLine

end
