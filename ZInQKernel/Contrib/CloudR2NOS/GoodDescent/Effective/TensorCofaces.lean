/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Actual canonical tensor-square/triple Čech base maps for the level-FREE
source effective Proj descent theorem. All morphisms and scalar triangles
are constructed at arbitrary Type u. No cocycle or unknown quotient input
is assumed. This is not an arbitrary ramified good-reduction theorem.
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces

variable (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R']

abbrev Base : Scheme.{u} := Spec (CommRingCat.of R)
abbrev Cover : Scheme.{u} := Spec (CommRingCat.of R')
abbrev Square : Scheme.{u} := Spec (CommRingCat.of (R' ⊗[R] R'))
abbrev Triple : Scheme.{u} := Spec (CommRingCat.of (R' ⊗[R] (R' ⊗[R] R')))

def baseMap : Cover R' ⟶ Base R := Spec.map (CommRingCat.ofHom (algebraMap R R'))
def left : Square R R' ⟶ Cover R' :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').toRingHom)
def right : Square R R' ⟶ Cover R' :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').toRingHom)

def face12 : Triple R R' ⟶ Square R R' :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R R')
    (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R')).toRingHom)
def face13 : Triple R R' ⟶ Square R R' :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R R')
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R')).toRingHom)
def face23 : Triple R R' ⟶ Square R R' :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : R' ⊗[R] R' →ₐ[R] R' ⊗[R] (R' ⊗[R] R')).toRingHom)

@[reassoc]
theorem left_base : left R R' ≫ baseMap R R' = right R R' ≫ baseMap R R' := by
  unfold left right baseMap
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').commutes r |>.trans
    ((Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').commutes r).symm

@[reassoc]
theorem face12_left : face12 R R' ≫ left R R' = face13 R R' ≫ left R R' := by
  unfold face12 face13 left
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

@[reassoc]
theorem face12_right : face12 R R' ≫ right R R' = face23 R R' ≫ left R R' := by
  unfold face12 face23 right left
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

@[reassoc]
theorem face13_right : face13 R R' ≫ right R R' = face23 R R' ≫ right R R' := by
  unfold face13 face23 right
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- The square ring is the ACTUAL fibre product of the affine cover base.
    This is the primitive used for scheme-nerve comparisons, not assumed
    equality of two arbitrary schemes bearing similar names. -/
theorem isPullback_square : IsPullback (left R R') (right R R') (baseMap R R') (baseMap R R') := by
  refine IsPullback.of_iso_pullback ⟨left_base R R'⟩ (pullbackSpecIso R R' R').symm ?_ ?_
  · change (pullbackSpecIso R R' R').inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : R' →ₐ[R] R' ⊗[R] R').toRingHom)
    exact pullbackSpecIso_inv_fst R R' R'
  · change (pullbackSpecIso R R' R').inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : R' →ₐ[R] R' ⊗[R] R').toRingHom)
    exact pullbackSpecIso_inv_snd R R' R'

#print axioms left_base
#print axioms face12_left
#print axioms face12_right
#print axioms face13_right
#print axioms isPullback_square

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces
