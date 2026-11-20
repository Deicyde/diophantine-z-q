/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_JacJ1Iface.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * 2 internal `import`s retargeted to `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil`.
  * 1 scope(s) the source leaves open at EOF closed explicitly (end) so the port namespace can be closed; Lean closes these implicitly at EOF in the original, so this is a no-op.
  * one `w03_open "AlgebraicGeometry"` inserted after the port namespace: this file `open`s `AlgebraicGeometry`, which the port also declares as nested namespace(s), so a
    plain `open` would resolve to the nested one and hide Mathlib's. The dual root+prefix
    shim keeps the Mathlib root namespace(s) visible, exactly as in the original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

w03_open "AlgebraicGeometry"

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

open NeronModelInfra

namespace GoodReductionJacobian

section AbstractCarriers

variable (R : Type u) [CommRing R]

structure AbelianSchemePropertyBundle {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) :
    Prop where

  smooth : Smooth f

  proper : IsProper f

  connectedFibres : ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s})

  hasGroupLaw : Nonempty (RelativeGroupLaw R f)

structure RelativePic0Designation {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) where

  P : Scheme.{u}

  toBase : P ⟶ Spec (CommRingCat.of R)

  zeroSection : Spec (CommRingCat.of R) ⟶ P

  zeroSection_toBase : zeroSection ≫ toBase = 𝟙 (Spec (CommRingCat.of R))

def trivialPic0Designation {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) :
    RelativePic0Designation R c where
  P := Spec (CommRingCat.of R)
  toBase := 𝟙 _
  zeroSection := 𝟙 _
  zeroSection_toBase := Category.comp_id _

end AbstractCarriers

section AvatarBridge

variable {R : Type u} [CommRing R]
variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

structure AvatarSchemeBridge (A : Type*) [AddCommGroup A]
    (D : RelativePic0Designation R c) (L : RelativeGroupLaw R D.toBase)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of R)) where

  pts : A ≃ SchemeHomOver σ D.toBase

  pts_add : ∀ x y : A, pts (x + y) = L.mul σ (pts x) (pts y)

  pts_zero : (pts 0).1 = σ ≫ D.zeroSection

namespace AvatarSchemeBridge

variable {A : Type*} [AddCommGroup A]
variable {D : RelativePic0Designation R c} {L : RelativeGroupLaw R D.toBase}
variable {T : Scheme.{u}} {σ : T ⟶ Spec (CommRingCat.of R)}

theorem law_one_eq_pts_zero (B : AvatarSchemeBridge A D L σ) :
    L.one σ = B.pts 0 := by
  have hidem : L.mul σ (B.pts 0) (B.pts 0) = B.pts 0 := by
    rw [← B.pts_add, add_zero]
  calc L.one σ
      = L.mul σ (L.inv σ (B.pts 0)) (B.pts 0) := (L.inv_mul_cancel σ (B.pts 0)).symm
    _ = L.mul σ (L.inv σ (B.pts 0)) (L.mul σ (B.pts 0) (B.pts 0)) := by rw [hidem]
    _ = L.mul σ (L.mul σ (L.inv σ (B.pts 0)) (B.pts 0)) (B.pts 0) :=
        (L.mul_assoc σ _ _ _).symm
    _ = L.mul σ (L.one σ) (B.pts 0) := by rw [L.inv_mul_cancel]
    _ = B.pts 0 := L.one_mul σ _

end AvatarSchemeBridge

end AvatarBridge

end GoodReductionJacobian

namespace MilneJVScheme

open GoodReductionJacobian

variable {k : Type u} [Field k]

structure JacobianSchemeData (A : Type*) [AddCommGroup A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (g : ℕ)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of k)) where

  D : RelativePic0Designation k c

  L : RelativeGroupLaw k D.toBase

  bridge : AvatarSchemeBridge A D L σ

  hAbel : AbelianSchemePropertyBundle k D.toBase

  hDim : Prop

def JacobianSchemeData.ofCore (A : Type*) [AddCommGroup A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (g : ℕ)
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    (pts : A ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (pts_add : ∀ x y : A, pts (x + y) = L.mul (𝟙 (Spec (CommRingCat.of k))) (pts x) (pts y))
    (hsmooth : Smooth f) (hproper : IsProper f)
    (hconn : ∀ s : Spec (CommRingCat.of k), _root_.IsConnected (f.base ⁻¹' {s})) :
    JacobianSchemeData A c g (𝟙 (Spec (CommRingCat.of k))) where
  D :=
    { P := J
      toBase := f
      zeroSection := (pts 0).1
      zeroSection_toBase := (pts 0).2 }
  L := L
  bridge :=
    { pts := pts
      pts_add := pts_add
      pts_zero := (Category.id_comp _).symm }
  hAbel :=
    { smooth := hsmooth
      proper := hproper
      connectedFibres := hconn
      hasGroupLaw := ⟨L⟩ }
  hDim := True

end MilneJVScheme

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
