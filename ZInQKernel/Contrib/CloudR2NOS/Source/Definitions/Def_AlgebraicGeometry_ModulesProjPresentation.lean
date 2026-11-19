/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_ModulesProjPresentation.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import(s) of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (re-provides, under the port prefix, db584 API this file's source relies on and Mathlib 56a removed or moved).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / port utilities.
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpace
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

open CategoryTheory CategoryTheory.Limits Opposite MvPolynomial HomogeneousLocalization
r2nos_open_dual "CategoryTheory CategoryTheory.Limits Opposite MvPolynomial HomogeneousLocalization"

namespace AlgebraicGeometry
r2nos_namespace_dual

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Scheme.Modules
r2nos_namespace_dual

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

structure ProjPresentation (M : X.Modules) (f : X ⟶ Spec (.of R)) (N : ℕ) where

  σ : Fin (N + 1) → Γ(M, ⊤)

  toProj : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

  toProj_π : toProj ≫ ProjSpace.π R N = f

  frame : ∀ (i : Fin (N + 1)) (V : X.Opens),
    V ≤ toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) →
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ i) : Γ(M, V))

  app_ratio_smul : ∀ i j : Fin (N + 1),
    (toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
        (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) •
        M.presheaf.map (homOfLE (le_top : toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) ≤ ⊤)).op (σ i)
      = M.presheaf.map (homOfLE (le_top : toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) ≤ ⊤)).op (σ j)

def FiniteBySections (M : X.Modules) (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (N : ℕ) (𝔓 : M.ProjPresentation f N), IsFinite 𝔓.toProj

def ClosedImmersionBySections (M : X.Modules) (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (N : ℕ) (𝔓 : M.ProjPresentation f N), IsClosedImmersion 𝔓.toProj

end Scheme.Modules

namespace ProjSpace
r2nos_namespace_dual

variable (R : Type u) [CommRing R]

def awayZeroEval :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0 : MvPolynomial (Fin 1) R) →+* R :=
  (IsLocalization.Away.lift (S := Localization.Away (X 0 : MvPolynomial (Fin 1) R))
      (X 0 : MvPolynomial (Fin 1) R)
      (g := (MvPolynomial.aeval (R := R) (fun _ : Fin 1 => (1 : R))).toRingHom)
      (by simp)).comp
    (algebraMap (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0 : MvPolynomial (Fin 1) R))
      (Localization.Away (X 0 : MvPolynomial (Fin 1) R)))

def pointOfProjZero : Spec (.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 1) R) :=
  Spec.map (CommRingCat.ofHom (awayZeroEval R)) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0) one_pos

theorem pointOfProjZero_π : pointOfProjZero R ≫ π R 0 = 𝟙 _ := by
  rw [pointOfProjZero, Category.assoc, awayι_comp_π, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext r : 2
  change awayZeroEval R (algebraMap R _ r) = r
  simp only [awayZeroEval, RingHom.coe_comp, Function.comp_apply]
  rw [HomogeneousLocalization.algebraMap_apply, val_algebraMap, IsLocalization.Away.lift_eq]
  simp

theorem pointOfProjZero_preimage_basicOpen :
    pointOfProjZero R ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) = ⊤ := by
  rw [pointOfProjZero, Scheme.Hom.comp_preimage]
  have : Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0) one_pos ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) = ⊤ := by
    rw [← Proj.opensRange_awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0) one_pos]
    exact Scheme.Hom.preimage_opensRange _
  rw [this]
  rfl

end ProjSpace

variable (R : Type u) [CommRing R]

def Scheme.Modules.unitOne (X : Scheme.{u}) :
    Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), (⊤ : X.Opens)) :=
  (show Γ(X, ⊤) from 1)

def Scheme.Modules.ProjPresentation.unitSpec :
    Scheme.Modules.ProjPresentation (SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules)
      (𝟙 (Spec (.of R))) 0 where
  σ := fun _ => Scheme.Modules.unitOne (Spec (.of R))
  toProj := ProjSpace.pointOfProjZero R
  toProj_π := ProjSpace.pointOfProjZero_π R
  frame := fun i V _ => by
    have h : (Scheme.Modules.presheaf (SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules)).map
        (homOfLE (le_top : V ≤ ⊤)).op (Scheme.Modules.unitOne (Spec (.of R)))
        = (show Γ(Spec (.of R), V) from 1) := by
      change ((Spec (.of R)).ringCatSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom 1 = 1
      exact map_one _
    rw [h]
    change Function.Bijective fun g : Γ(Spec (.of R), V) => g * 1
    simp only [mul_one]
    exact Function.bijective_id
  app_ratio_smul := fun i j => by
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst hi hj
    rw [ProjSpace.ratio_self, map_one, map_one, one_smul]

end AlgebraicGeometry

end


end ZInQ.Contrib.CloudW03NeronSurj.FLT
