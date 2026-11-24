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
  Source file    : Definitions/Def_AlgebraicGeometry_AffineLimit.lean
  Source sha256  : c6fb4cd6a6982ac4dc9a36c1c18ff0ce8482e8d41ae40c06e253c1b468e515e7
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe w u

open CategoryTheory Opposite
r2nos_open_dual "CategoryTheory Opposite"

namespace AlgebraicGeometry.AffineLimit
r2nos_namespace_dual

variable (R : Type u) [CommRing R]

noncomputable abbrev specOver (A : Type u) [CommRing A] [Algebra R A] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

noncomputable abbrev specOverOfSubalgebra {A : Type u} [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) :
    specOver R A ⟶ specOver R A₀ :=
  Over.homMk (Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl)

noncomputable abbrev specOverOfLE {A : Type u} [CommRing A] [Algebra R A] (A₀ A₁ : Subalgebra R A) (h : A₀ ≤ A₁) :
    specOver R A₁ ⟶ specOver R A₀ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl)

variable {R}

def IsLFPSurj (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A] (x : G.obj (op (specOver R A))),
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (x₀ : G.obj (op (specOver R A₀))),
      G.map (specOverOfSubalgebra R A₀).op x₀ = x

def IsLFPInj (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (_ : A₀.FG)
    (x₀ x₀' : G.obj (op (specOver R A₀))),
    G.map (specOverOfSubalgebra R A₀).op x₀ = G.map (specOverOfSubalgebra R A₀).op x₀' →
    ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (h : A₀ ≤ A₁),
      G.map (specOverOfLE R A₀ A₁ h).op x₀ = G.map (specOverOfLE R A₀ A₁ h).op x₀'

def HomIsLFP {X : Scheme.{u}} (ξ : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  (∀ (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X),
      φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of A₀) ⟶ X),
        φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) ∧
        Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ) ∧
  (∀ (A : Type u) [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (_ : A₀.FG)
      (φ₀ φ₀' : Spec (CommRingCat.of A₀) ⟶ X),
      φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) →
      φ₀' ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) →
      Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀' →
      ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (h : A₀ ≤ A₁),
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) ≫ φ₀ =
          Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) ≫ φ₀')

end AlgebraicGeometry.AffineLimit

end ZInQ.Contrib.CloudW03NeronSurj.FLT
