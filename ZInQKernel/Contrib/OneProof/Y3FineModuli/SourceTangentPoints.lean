import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Trace
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

/-!
# The actual dual-number tangent-point definitions used by the QM source

Source: `anthropics/fermats-last-theorem`, revision
`6e837e75355538c7f80bab5b956861e86c4eacc2`,
`Definitions/Def_CerednikDrinfeld_QMModuli.lean`, sections Points and Tangent.

Apache-2.0; see `Vendor/AnthropicFLT/LICENSE` and the source/change notice.
Mechanical changes: import the existing kernel's namespaced copy of the source
relative group law; place these source definitions in this port namespace.
These are morphisms of schemes and actual dual-number tangent points, not a
replacement moduli object, a Tate-module model, or an assumed trace condition.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace ZInQ.Contrib.OneProof.Y3FineModuli.Source

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian

namespace CerednikDrinfeld.QM

section Points

variable {R : Type u} [CommRing R]

def mapPt {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : SchemeHomOver t f' :=
  ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩

@[simp] theorem mapPt_coe {A A' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    {f' : A' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    (mapPt φ hφ P).1 = P.1 ≫ φ := rfl

abbrev pushPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (φ : A ⟶ A) (hφ : φ ≫ f = f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : SchemeHomOver t f :=
  mapPt φ hφ P

def FactorsThrough {A C : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (lev : C ⟶ A) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (P : SchemeHomOver t f) : Prop :=
  ∃ P₀ : T ⟶ C, P₀ ≫ lev = P.1

def nsmulPt {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : ℕ → SchemeHomOver t f → SchemeHomOver t f
  | 0, _ => L.one t
  | n + 1, P => L.mul t (nsmulPt L t n P) P

end Points

section Tangent

variable {S : Type u} [CommRing S]

def geomPoint (k : Type u) [Field k] (sk : S →+* k) :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom sk)

def tangentBase (k : Type u) [Field k] (sk : S →+* k) :
    Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp sk))

def tangentZero (k : Type u) [Field k] :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)

def tangentScale (k : Type u) [Field k] (c : k) :
    Spec (CommRingCat.of (DualNumber k)) ⟶ Spec (CommRingCat.of (DualNumber k)) :=
  Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom)

def IsTangentVector {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (k : Type u) [Field k] (sk : S →+* k)
    (P : SchemeHomOver (tangentBase k sk) f) : Prop :=
  tangentZero k ≫ P.1 = (L.one (geomPoint k sk)).1

end Tangent

end CerednikDrinfeld.QM

end ZInQ.Contrib.OneProof.Y3FineModuli.Source
