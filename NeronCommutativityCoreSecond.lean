import ZInQKernel.HDecomp.Objects
import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# Commutativity from the actual Néron mapping property

The data are the given group scheme over the valuation ring and its actual
generic-fibre group isomorphism to the original abelian variety. The Néron
mapping property on the smooth product test scheme forces commutativity;
base change then transports the same group law to every special fibre.
No commutativity or Tate-filtration input is added to the model data.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace SemistableGeometry.NeronCommutativityCore

variable {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}

abbrev j : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O K))

/-- The original generic abelian group law and the genuine Néron mapping property make the model commutative. -/
theorem model_commutative
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (e : (Over.pullback (j (O := O))).obj N ≅ A.X)
    (he : letI : GrpObj ((Over.pullback (j (O := O))).obj N) := Functor.grpObjObj
      IsMonHom e.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N ↦ (Over.pullback (j (O := O))).map f ≫ e.hom)) :
    IsCommMonObj N := by
  let F := Over.pullback (j (O := O))
  let : GrpObj (F.obj N) := Functor.grpObjObj
  let : IsMonHom e.hom := he
  let : Smooth (N ⊗ N).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hxy : fst N N * snd N N = snd N N * fst N N := by
    apply (hN (N ⊗ N)).1
    simp only [Functor.map_mul, MonObj.mul_comp]
    exact mul_comm _ _
  constructor
  calc
    (β_ N N).hom ≫ μ[N] = snd N N * fst N N := by
      simp only [Hom.mul_def]
      congr 1
    _ = fst N N * snd N N := hxy.symm
    _ = μ[N] := by simp [Hom.mul_def]

/-- Every actual base change, in particular a geometric special fibre, inherits this proved commutative group law. -/
theorem baseChange_commutative
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [Smooth N.hom]
    (e : (Over.pullback (j (O := O))).obj N ≅ A.X)
    (he : letI : GrpObj ((Over.pullback (j (O := O))).obj N) := Functor.grpObjObj
      IsMonHom e.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N ↦ (Over.pullback (j (O := O))).map f ≫ e.hom))
    (S : Scheme) (f : S ⟶ Spec (CommRingCat.of O)) :
    IsCommMonObj ((Over.pullback f).obj N) := by
  let : IsCommMonObj N := model_commutative N e he hN
  infer_instance

end SemistableGeometry.NeronCommutativityCore
