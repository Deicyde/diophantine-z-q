/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean
  Source sha256  : 44da970a1cb409fc1a1c3b1555542101fb523627b527f858cd70b4a30389c2c6
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"
open CategoryTheory CategoryTheory.Limits NeronModelInfra
r2nos_open_dual "CategoryTheory CategoryTheory.Limits NeronModelInfra"

namespace AlgebraicGeometry.SmoothProperCurve
r2nos_namespace_dual

structure FiniteMapData {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) where

  U : C.Opens

  V : C.Opens

  f : Γ(C, U)

  g : Γ(C, V)

  m : ℕ
  isAffineOpen_U : IsAffineOpen U
  isAffineOpen_V : IsAffineOpen V
  sup_eq_top : U ⊔ V = ⊤

  mem_U_iff : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base

  inf_eq_basicOpen : U ⊓ V = C.basicOpen f

  inf_eq_basicOpen_g : U ⊓ V = C.basicOpen g

  res_f_mul_res_g : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1

  finite_f : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite

  finite_g : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite

  levelSet_free : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Finite S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.Free S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.finrank S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) = m

namespace FiniteMapData
r2nos_namespace_dual

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : FiniteMapData c ε)

theorem range_subset_V : Set.range ε.1.base ⊆ (𝔉.V : Set C) := by
  rintro x ⟨y, rfl⟩
  have hx : ε.1.base y ∈ (⊤ : C.Opens) := trivial
  rw [← 𝔉.sup_eq_top, TopologicalSpace.Opens.mem_sup] at hx
  rcases hx with h | h
  · exact absurd ⟨y, rfl⟩ ((𝔉.mem_U_iff _).mp h)
  · exact h

theorem coe_U_eq_compl : (𝔉.U : Set C) = (Set.range ε.1.base)ᶜ :=
  Set.ext fun x => 𝔉.mem_U_iff x

theorem isAffineOpen_inf : IsAffineOpen (𝔉.U ⊓ 𝔉.V) := by
  rw [𝔉.inf_eq_basicOpen]; exact 𝔉.isAffineOpen_U.basicOpen _

theorem basicOpen_f_eq_basicOpen_g : C.basicOpen 𝔉.f = C.basicOpen 𝔉.g := by
  rw [← 𝔉.inf_eq_basicOpen, 𝔉.inf_eq_basicOpen_g]

def twoAffineOpenCover : C.TwoAffineOpenCover where
  U0 := 𝔉.V
  U1 := 𝔉.U
  isAffineOpen_U0 := 𝔉.isAffineOpen_V
  isAffineOpen_U1 := 𝔉.isAffineOpen_U
  sup_eq_top := by rw [sup_comm, 𝔉.sup_eq_top]
  isAffineOpen_inf := by rw [inf_comm]; exact 𝔉.isAffineOpen_inf

@[simp] theorem twoAffineOpenCover_U0 : 𝔉.twoAffineOpenCover.U0 = 𝔉.V := rfl
@[simp] theorem twoAffineOpenCover_U1 : 𝔉.twoAffineOpenCover.U1 = 𝔉.U := rfl

theorem range_subset_twoAffineOpenCover_U0 : Set.range ε.1.base ⊆ (𝔉.twoAffineOpenCover.U0 : Set C) :=
  𝔉.range_subset_V

theorem twoAffineOpenCover_U1_eq_compl : (𝔉.twoAffineOpenCover.U1 : Set C) = (Set.range ε.1.base)ᶜ :=
  𝔉.coe_U_eq_compl

theorem moduleFinite_U :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    letI : Algebra (Polynomial R) Γ(C, 𝔉.U) := (Polynomial.aeval 𝔉.f : Polynomial R →ₐ[R] Γ(C, 𝔉.U)).toRingHom.toAlgebra
    Module.Finite (Polynomial R) Γ(C, 𝔉.U) :=
  𝔉.finite_f

theorem moduleFinite_V :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.V
    letI : Algebra (Polynomial R) Γ(C, 𝔉.V) := (Polynomial.aeval 𝔉.g : Polynomial R →ₐ[R] Γ(C, 𝔉.V)).toRingHom.toAlgebra
    Module.Finite (Polynomial R) Γ(C, 𝔉.V) :=
  𝔉.finite_g

theorem levelSet_finite (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    Module.Finite S (S ⊗[R] Γ(C, 𝔉.U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))}) :=
  (𝔉.levelSet_free S s).1

theorem levelSet_finrank_eq (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    Module.finrank S (S ⊗[R] Γ(C, 𝔉.U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))}) = 𝔉.m :=
  (𝔉.levelSet_free S s).2.2

def LevelSetsGenericallyEtale : Prop :=
  ∃ D : Polynomial R, (∃ i, IsUnit (D.coeff i)) ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (s : S),
      IsUnit (Polynomial.aeval s D) →
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
      Algebra.Etale S (S ⊗[R] Γ(C, 𝔉.U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))})

end FiniteMapData

end AlgebraicGeometry.SmoothProperCurve

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
