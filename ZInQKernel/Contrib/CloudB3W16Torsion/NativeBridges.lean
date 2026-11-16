import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.Contrib.OneProof.MulEtale

/-!
# Native bridges for prime-to-characteristic torsion

These bridges use the original `PkgI2.Pts` and multiplicative group law.
They do not assume a torsion cardinality or a degree formula. In particular,
finiteness below is not a proof that the cardinality equals `n ^ (2 * g)`.

Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
-/

noncomputable section

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
  haveI : PkgI2.IsAbelianScheme A :=
    ⟨PkgI2.IsAbelianVariety.proper, PkgI2.IsAbelianVariety.smooth, inferInstance⟩
  exact ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof k A n
    (isUnit_iff_ne_zero.mpr hnk)

/-- Multiplication prime to the characteristic is finite: properness and étaleness imply
properness and local quasi-finiteness, hence finiteness. No degree value is asserted. -/
theorem multiplication_finite (n : ℕ) (hnk : (n : k) ≠ 0) :
    IsFinite ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := by
  haveI := PkgI2.IsAbelianVariety.proper (A := A)
  haveI := multiplication_etale A n hnk
  haveI : IsProper ((𝟙 A.X ^ n : A.X ⟶ A.X).left) := by
    apply IsProper.of_comp _ A.X.hom
    rw [Over.w]
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
  apply Finite.of_injective (β := ((𝟙 A.X ^ n : A.X ⟶ A.X).left) ⁻¹' {e})
    (fun p => ⟨p.1.left s, ?_⟩)
  · change ((𝟙 A.X ^ n : A.X ⟶ A.X).left) (p.1.left s) = e
    have hp : p.1 ≫ (𝟙 A.X ^ n : A.X ⟶ A.X) = 1 := by
      rw [MonObj.comp_pow, Category.comp_id]
      exact p.2
    have hp' := congrArg (fun f : PkgI2.Pts A k => f.left s) hp
    simpa [Hom.one_def, PkgI2.specOver, e] using hp'
  · intro p q hpq
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact ext_of_apply_closedPoint_eq A.X.hom (Over.w p.1) (Over.w q.1)
      (congrArg Subtype.val hpq)

end ZInQ.Contrib.CloudB3W16Torsion
