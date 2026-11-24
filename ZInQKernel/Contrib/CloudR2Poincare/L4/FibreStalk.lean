import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom

/-!
# The local ring of an actual scheme-theoretic fibre

H-72 round 2, lane L4.

SOURCE / CHANGE NOTICE: adapted from AxiomMath/Stacks
`c496df0d9beea9deaeabcea8492605f9a0a2313b`,
`StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FibreStalk.lean`,
lines 93–192 and 341–358, and the flat-stalk specialization in
`FibreDimensionBaseChange/LocalRing.lean:149–167`. Apache-2.0; the upstream
license is retained as `LICENSE.Stacks`.

Only the canonical quotient-stalk bridge is retained: no Cohen–Macaulay
predicate, perfect-complex tree, or fibre-dimension leaf is assumed. The
shared base-change-stalk and flat-local-ring dimension proofs are imported
from the one L3-owned copy. Every new declaration is in the L4 namespace.
-/

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option linter.style.haveILetI false

universe u

private def localizationEquivOfSurjective {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing R] [IsLocalRing S] (M : Submonoid R) [IsLocalization M S]
    (h : Function.Surjective (algebraMap R S)) : R ≃ₐ[R] S := by
  haveI : IsLocalHom (algebraMap R S) := IsLocalHom.of_surjective _ h
  have hM : M ≤ IsUnit.submonoid R := fun s hs =>
    (isUnit_map_iff (algebraMap R S) s).mp (IsLocalization.map_units S ⟨s, hs⟩)
  letI : IsLocalization M R := IsLocalization.self hM
  exact IsLocalization.algEquiv M R S

/-- The canonical fibre-stalk quotient bridge at the point named by the fibre inclusion. -/
theorem quotientStalk_bridge {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ∃ e :
      ((X.presheaf.stalk (f.fiberι (f x) (f.asFiber x))) ⧸
        Ideal.map (f.stalkMap (f.fiberι (f x) (f.asFiber x))).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (f.fiberι (f x) (f.asFiber x)))))) ≃+*
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)),
      ∀ b : X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)),
        e (Ideal.Quotient.mk
          (Ideal.map (f.stalkMap (f.fiberι (f x) (f.asFiber x))).hom
            (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (f.fiberι (f x) (f.asFiber x)))))) b) =
          ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom b := by
  classical
  let g := Y.fromSpecResidueField (f x)
  let z : (pullback f g).carrier := f.asFiber x
  let pX : pullback f g ⟶ X := pullback.fst f g
  let pY : pullback f g ⟶ Spec (Y.residueField (f x)) := pullback.snd f g
  let h : (pX ≫ f).base z = (pY ≫ g).base z :=
    congrArg (fun k : pullback f g ⟶ Y => k.base z) pullback.condition
  let R := Y.presheaf.stalk ((pX ≫ f).base z)
  let A := X.presheaf.stalk (pX.base z)
  let B := (Spec (Y.residueField (f x))).presheaf.stalk (pY.base z)
  let C := (pullback f g).presheaf.stalk z
  let eEq : R ≃+* Y.presheaf.stalk (g (pY.base z)) :=
    (eqToIso (congrArg Y.presheaf.stalk h)).commRingCatIsoToRingEquiv
  letI : Algebra R A := (f.stalkMap (pX.base z)).hom.toAlgebra
  let ρ : R →+* B :=
    (((eqToHom (congrArg Y.presheaf.stalk h)) ≫ g.stalkMap (pY.base z)).hom)
  letI : Algebra R B := ρ.toAlgebra
  have hρ : Function.Surjective ρ := by
    intro b
    obtain ⟨c, hc⟩ := g.stalkMap_surjective (pY.base z) b
    refine ⟨eEq.symm c, ?_⟩
    change (g.stalkMap (pY.base z)).hom (eEq (eEq.symm c)) = b
    rw [eEq.apply_symm_apply, hc]
  let hb : pY.base z = IsLocalRing.closedPoint (Y.residueField (f x)) := Subsingleton.elim _ _
  let eB : B ≃+* Y.residueField (f x) :=
    (((Spec (Y.residueField (f x))).presheaf.stalkCongr (.of_eq hb)) ≪≫
      stalkClosedPointIso (Y.residueField (f x))).commRingCatIsoToRingEquiv
  letI : Field B := (eB.isField (Field.toIsField _)).toField
  let ρAlg : R →ₐ[R] B := Algebra.ofId R B
  let eR : (R ⧸ IsLocalRing.maximalIdeal R) ≃ₐ[R] B :=
    (Ideal.quotientEquivAlgOfEq R (IsLocalRing.ker_eq_maximalIdeal ρ hρ).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := ρAlg) hρ)
  haveI : IsLocalHom (algebraMap R A) := f.toLRSHom.prop (pX.base z)
  let I : Ideal A := Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R)
  have hIlt : I < ⊤ := (IsLocalRing.map_maximalIdeal_le (algebraMap R A)).trans_lt
    (IsLocalRing.maximalIdeal.isMaximal A).lt_top
  let Q := A ⧸ I
  let e₁ := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R) A
    (IsLocalRing.maximalIdeal R)
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := A)) eR
  let eQT := e₁.trans e₂
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hIlt.ne
  letI : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI := eQT.toRingEquiv.isLocalRing
  obtain ⟨φ, hleft, _, hLoc⟩ :=
    ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization
      f g z
  let T := TensorProduct R A B
  letI : Algebra T C := φ.toAlgebra
  obtain ⟨M, hM⟩ := hLoc
  letI : IsLocalization M C := hM
  have hφsurj : Function.Surjective φ := by
    intro c
    obtain ⟨a, ha⟩ := pX.stalkMap_surjective z c
    exact ⟨Algebra.TensorProduct.includeLeft (R := R) (S := A) (A := A) (B := B) a,
      (DFunLike.congr_fun hleft a).trans ha⟩
  let eLoc : T ≃ₐ[T] C := localizationEquivOfSurjective M hφsurj
  refine ⟨eQT.toRingEquiv.trans eLoc.toRingEquiv, fun b => ?_⟩
  change A at b
  have hmk : eQT (Ideal.Quotient.mk I b) =
      Algebra.TensorProduct.includeLeft (R := R) (S := A) (A := A) (B := B) b := by
    simp [eQT, e₁, e₂, I, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  have heLoc (t : T) : eLoc t = φ t := by
    calc
      eLoc t = algebraMap T C t := by
        simpa [eLoc, localizationEquivOfSurjective] using eLoc.commutes t
      _ = φ t := rfl
  change eLoc (eQT (Ideal.Quotient.mk I b)) = _
  rw [hmk, heLoc]
  exact DFunLike.congr_fun hleft b

/-- The actual fibre local ring is the canonical quotient of the source local ring. -/
def quotientStalkEquivFiberStalk {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) ≃+*
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  classical
  let F := (f.fiber (f x)).presheaf.stalk (f.asFiber x)
  let Q : X → Type _ := fun a =>
    (X.presheaf.stalk a) ⧸ Ideal.map (f.stalkMap a).hom
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f a)))
  let P : X → Type _ := fun a => Q a ≃+* F
  have h : f.fiberι (f x) (f.asFiber x) = x := f.fiberι_asFiber x
  have e : P (f.fiberι (f x) (f.asFiber x)) := Classical.choose (quotientStalk_bridge f x)
  change P x
  exact h ▸ e

/-- The flat local-ring dimension formula for an actual scheme morphism. -/
theorem flat_stalk_dimension {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) +
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have hflat : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have hF : ringKrullDim
      (ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.ClosedFibre
        (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) =
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    ringKrullDim_eq_of_ringEquiv (quotientStalkEquivFiberStalk f x)
  rw [ZInQ.Contrib.CloudR2Poincare.L3.StacksPort.ringKrullDim_eq_add_ringKrullDim_closedFibre
    _ _ hflat, hF]

end ZInQ.Contrib.CloudR2Poincare.L4
