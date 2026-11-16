import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.MulEtale.Direct.AllBase
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Algebraize

/-!
# Native bridges for prime-to-characteristic torsion

These bridges use the original `PkgI2.Pts` and multiplicative group law.
They do not assume a torsion cardinality or a degree formula. In particular,
finiteness below is not a proof that the cardinality equals `n ^ (2 * g)`.

Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
-/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudB3W16Torsion

variable {k : Type} [Field k] (A : Grp (Over (Spec (.of k))))
  [PkgI2.IsAbelianVariety A]

/-- The original torsion set is exactly the additive torsion subgroup of the original points. -/
def torsionEquivAddSubgroup (n : ℕ) :
    PkgI2.torsion A k n ≃ AddSubgroup.torsionBy (Additive (PkgI2.Pts A k)) n where
  toFun x := ⟨Additive.ofMul x.1, by
    change n • Additive.ofMul x.1 = 0
    exact congrArg Additive.ofMul x.2⟩
  invFun x := ⟨Additive.toMul x.1, by
    change (Additive.toMul x.1) ^ n = 1
    exact congrArg Additive.toMul x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The point comparison respects the *original* multiplication, regardless of the supplied
membership proof. -/
theorem torsionEquivAddSubgroup_mul (n : ℕ) (x y : PkgI2.torsion A k n)
    (h : x.1 * y.1 ∈ PkgI2.torsion A k n) :
    torsionEquivAddSubgroup A n ⟨x.1 * y.1, h⟩ =
      torsionEquivAddSubgroup A n x + torsionEquivAddSubgroup A n y := rfl

/-- Native H101, applied over a field, gives étaleness of multiplication by `n`
without a characteristic-zero restriction. -/
theorem multiplication_etale (n : ℕ) (hnk : (n : k) ≠ 0) :
    Etale ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := by
  haveI := PkgI2.IsAbelianVariety.geomIntegral (A := A)
  haveI : GeometricallyConnected A.X.hom := by
    refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr (fun K _ s => ?_)⟩
    haveI : IsIntegral (pullback A.X.hom s) :=
      GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)
    infer_instance
  haveI : PkgI2.IsAbelianScheme A :=
    ⟨PkgI2.IsAbelianVariety.proper, PkgI2.IsAbelianVariety.smooth, inferInstance⟩
  exact H101DirectFieldRoute.multiplication_etale k A n
    (isUnit_iff_ne_zero.mpr hnk)

/-- Multiplication prime to the characteristic is finite: properness and étaleness imply
properness and local quasi-finiteness, hence finiteness. No degree value is asserted. -/
theorem multiplication_finite (n : ℕ) (hnk : (n : k) ≠ 0) :
    IsFinite ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := by
  haveI := PkgI2.IsAbelianVariety.proper (A := A)
  haveI := multiplication_etale A n hnk
  haveI : IsProper ((𝟙 A.X ^ n : A.X ⟶ A.X).left ≫ A.X.hom) := by
    rw [Over.w]
    infer_instance
  haveI : IsProper ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := IsProper.of_comp _ A.X.hom
  haveI : LocallyQuasiFinite ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := by
    constructor
    intro U hU V hV e
    have h := ((𝟙 A.X ^ n : A.X ⟶ A.X).left).etale_appLE hU hV e
    algebraize [(((𝟙 A.X ^ n : A.X ⟶ A.X).left).appLE U V e).hom]
    haveI : Algebra.Etale Γ(A.X.left, U) Γ(A.X.left, V) := h
    change Algebra.QuasiFinite Γ(A.X.left, U) Γ(A.X.left, V)
    infer_instance
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Over an algebraically closed field, the original `n`-torsion set is finite.
Its points inject into the finite set-theoretic fibre of multiplication by `n` over the unit. -/
theorem finite_torsion [IsAlgClosed k] (n : ℕ) (hnk : (n : k) ≠ 0) :
    Finite (PkgI2.torsion A k n) := by
  haveI := PkgI2.IsAbelianVariety.proper (A := A)
  haveI := PkgI2.IsAbelianVariety.smooth (A := A)
  haveI := multiplication_finite A n hnk
  let s := IsLocalRing.closedPoint k
  let e := (η[A.X]).left s
  haveI := (Scheme.Hom.finite_preimage_singleton
    ((𝟙 A.X ^ n : A.X ⟶ A.X).left) e).to_subtype
  let F : PkgI2.torsion A k n → ((𝟙 A.X ^ n : A.X ⟶ A.X).left) ⁻¹' {e} := fun p =>
    ⟨p.1.left s, by
      change ((𝟙 A.X ^ n : A.X ⟶ A.X).left) (p.1.left s) = e
      have hp : p.1 ≫ (𝟙 A.X ^ n : A.X ⟶ A.X) = 1 := by
        rw [MonObj.comp_pow, Category.comp_id]
        exact p.2
      have hp' := congrArg (fun f : PkgI2.Pts A k => f.left) hp
      change p.1.left ≫ (𝟙 A.X ^ n : A.X ⟶ A.X).left = (1 : PkgI2.Pts A k).left at hp'
      have hpoint := congrArg (fun f : Spec (.of k) ⟶ A.X.left => f s) hp'
      change (𝟙 A.X ^ n : A.X ⟶ A.X).left (p.1.left s) =
        (1 : PkgI2.Pts A k).left s at hpoint
      have hone : (1 : PkgI2.Pts A k).left s = e := by
        simp [Hom.one_def, PkgI2.specOver, e]
        rfl
      exact hpoint.trans hone⟩
  exact Finite.of_injective F (fun p q hpq =>
    Subtype.ext (Over.OverMorphism.ext
      (ext_of_apply_closedPoint_eq A.X.hom
        (by simpa [PkgI2.specOver] using Over.w p.1)
        (by simpa [PkgI2.specOver] using Over.w q.1)
        (congrArg Subtype.val hpq))))

end ZInQ.Contrib.CloudB3W16Torsion
