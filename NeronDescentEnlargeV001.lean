import NeronInvariantTorsionV001

/-!
# Enlarging the coordinate field of an unramified descent

If `x ∈ A(Ω)` comes from `y ∈ A(M)` and `M ⊆ M'` with `M'` finite separable over `K` and its integral
closure over `O` unramified at the centre of `w`, then `x` has an unramified descent (through `M'`).
So the unramifiedness input may be supplied for any convenient finite field containing a coordinate
field, for instance an inertia-invariant subfield of a finite Galois extension.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits

namespace NeronInvariantTorsion

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]
variable (O : ValuationSubring K) [IsDiscreteValuationRing O]
variable (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)

omit [IsDiscreteValuationRing O] in
theorem hasUnramifiedDescent_of_le {A : PkgI3.AbVar K} (x : A.Pt Ω)
    (M M' : IntermediateField K Ω) (hMM' : M ≤ M') [FiniteDimensional K M']
    [Algebra.IsSeparable K M'] [Algebra O M'] [IsScalarTower O K M']
    [Algebra.IsUnramifiedAt O (center O w hw M')]
    (y : A.Pt M) (hxy : Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ y.left = x.left) :
    HasUnramifiedDescent O w hw x := by
  let incl : M →+* M' := (IntermediateField.inclusion hMM').toRingHom
  have hy : y.left ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap K M)) := Over.w y
  have h1 : CommRingCat.ofHom (algebraMap K M) ≫ CommRingCat.ofHom incl =
      CommRingCat.ofHom (algebraMap K M') := by
    ext a; rfl
  have h2 : CommRingCat.ofHom incl ≫ CommRingCat.ofHom M'.val.toRingHom =
      CommRingCat.ofHom M.val.toRingHom := by
    ext a; rfl
  let y' : A.Pt M' := Over.homMk (Spec.map (CommRingCat.ofHom incl) ≫ y.left)
    ((Category.assoc _ _ _).trans ((congrArg (Spec.map (CommRingCat.ofHom incl) ≫ ·) hy).trans
      ((Spec.map_comp _ _).symm.trans (congrArg Spec.map h1))))
  refine ⟨M', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, y', ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ y.left) ((Spec.map_comp _ _).symm.trans (congrArg Spec.map h2))).trans hxy)

end NeronInvariantTorsion
