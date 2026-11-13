/-! ## lt-goodred §3: `QMEndRank` (copied verbatim) with base change on endomorphisms

Copied verbatim from `scratch/linked-tate/parts/95_linked.lean`: §1 `BaseChangeEnd` (L36-89:
`endBC`, `specMap_flat`, `specMap_surjective`, `endBC_injective`) and `QMEndRank` (L311-326). -/

section LTQMEndRankSec

noncomputable section

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-! ### §1 Base change on endomorphisms (copied from `scratch/bp-qmmoduli/QMAbVar.lean` L533-575:
`endBC` as unram-tate copied it, `specMap_flat`, `specMap_surjective`, `endBC_injective`) -/

section BaseChangeEnd

variable {K : Type} [Field K]

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (copied verbatim from bp-qmmoduli's `endBC`):
`End_K(A) → End_L(A_L)`, `f ↦ (Over.pullback (Spec L → Spec K)).map f`, a ring homomorphism
(functoriality, and `Functor.map_mul` for the monoidal functor `Over.pullback`). -/
noncomputable def endBC (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    PkgI3.AbVar.End A →+* PkgI3.AbVar.End (A.baseChange L) where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl

/-- `Spec L → Spec K` is flat, surjective and quasi-compact, so `Over.pullback` along it is
faithful (Mathlib, `Morphisms/FlatDescent.lean`). -/
instance specMap_flat (L : Type) [Field L] [Algebra K L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance specMap_surjective (L : Type) [Field L] [Algebra K L] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

/-- Base change on endomorphisms is injective. -/
theorem endBC_injective (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    Function.Injective (endBC A L) := by
  intro f g h
  apply PkgI3.AbVar.Hom.ext'
  exact (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map_injective
    (congrArg PkgI3.AbVar.Hom.hom h)

end BaseChangeEnd

/-- **Glue: the endomorphism ring of the QM model has rank 4** (linked-tate; G5-G6 + A9, N5
L564-577). For a `QML3` object `PK` over `K ⊆ ℚ̄` and a tower `K ≤ L ≤ L'` (`L'/ℚ` finite), if every
nonzero endomorphism of `A' = (PK.A)_{L,L'}` is an isogeny (`EndDivision`, which `FibreSimple`
supplies for the fibre), then `End_{L'}(A')` is a free `ℤ`-module of rank 4. Route (STANDARD,
UNVERIFIED numbering): `End(A')` is finitely generated and torsion-free (Mumford §19 Thm 3:
`End ⊗ ℤ_ℓ ↪ End T_ℓ`), so free; `End⁰(A')` is a division algebra containing `ι(B)`, `B = (2,−3)`
of dimension 4, and by Albert's classification for simple abelian surfaces in characteristic 0
(Mumford §21) it is `ℚ`, real quadratic, CM quartic or an indefinite quaternion algebra over `ℚ`;
only the last contains `B`, so `End⁰(A') = B`. GLUE (literature-backed). -/
def QMEndRank : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (PK : LeafQM.AV.QML3 K),
    PkgI3.EndDivision (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) = 4


end HSyn.LinkedTate

end

end LTQMEndRankSec
