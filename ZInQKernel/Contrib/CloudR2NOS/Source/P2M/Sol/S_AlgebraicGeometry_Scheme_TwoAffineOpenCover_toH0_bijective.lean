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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective.lean
  Source sha256  : 114ec02deb639075c9042c7ab0d63b8c7ff04654f474968b210386c87389235f
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory
r2nos_open_dual "CategoryTheory"

noncomputable section

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec Scheme Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Γ Opens Cover TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom"
namespace TwoAffineOpenCover
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "algebraOfHom cover structureSheafSections toH0 toH0_apply_coe U1 U0 sup_eq_top"
w03_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
r2nos_open_dual "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace"

namespace SheafCondition
r2nos_namespace_dual

variable (X : Scheme.{u}) (U V : X.Opens)

private abbrev _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.TwoAffineOpenCover.SheafCondition.eqLocus : Subring (Γ(X, U) × Γ(X, V)) :=
  RingHom.eqLocus
    ((X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom.comp (RingHom.fst Γ(X, U) Γ(X, V)))
    ((X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom.comp (RingHom.snd Γ(X, U) Γ(X, V)))

w03_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover.SheafCondition" "eqLocus"
theorem mem_eqLocus_iff (s : Γ(X, U) × Γ(X, V)) :
    s ∈ eqLocus X U V ↔
      (X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op).hom s.1
        = (X.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op).hom s.2 :=
  Iff.rfl

def gammaEquiv (h : U ⊔ V = ⊤) : Γ(X, ⊤) ≃+* eqLocus X U V :=
  ((X.presheaf.mapIso (eqToIso h).op).trans (X.sheaf.objSupIsoProdEqLocus U V)).commRingCatIsoToRingEquiv

private theorem map_comp_apply {W₁ W₂ W₃ : X.Opens} (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃) (a : Γ(X, W₃)) :
    (X.presheaf.map f.op).hom ((X.presheaf.map g.op).hom a) = (X.presheaf.map (f ≫ g).op).hom a := by
  rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]

theorem gammaEquiv_apply_fst (h : U ⊔ V = ⊤) (a : Γ(X, ⊤)) :
    (gammaEquiv X U V h a).1.1 = (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a := by
  have h0 : (gammaEquiv X U V h a).1.1
      = ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.1 := rfl
  have h1 : ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.1
      = (X.presheaf.map (homOfLE le_sup_left).op).hom ((X.presheaf.map (eqToHom h).op).hom a) :=
    X.sheaf.objSupIsoProdEqLocus_hom_fst U V _
  rw [h0, h1, map_comp_apply X (homOfLE le_sup_left) (eqToHom h) a,
    Subsingleton.elim ((homOfLE le_sup_left : U ⟶ U ⊔ V) ≫ eqToHom h) (homOfLE (le_top : U ≤ ⊤))]

theorem gammaEquiv_apply_snd (h : U ⊔ V = ⊤) (a : Γ(X, ⊤)) :
    (gammaEquiv X U V h a).1.2 = (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a := by
  have h0 : (gammaEquiv X U V h a).1.2
      = ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.2 := rfl
  have h1 : ((X.sheaf.objSupIsoProdEqLocus U V).hom ((X.presheaf.map (eqToHom h).op).hom a)).1.2
      = (X.presheaf.map (homOfLE le_sup_right).op).hom ((X.presheaf.map (eqToHom h).op).hom a) :=
    X.sheaf.objSupIsoProdEqLocus_hom_snd U V _
  rw [h0, h1, map_comp_apply X (homOfLE le_sup_right) (eqToHom h) a,
    Subsingleton.elim ((homOfLE le_sup_right : V ⟶ U ⊔ V) ≫ eqToHom h) (homOfLE (le_top : V ≤ ⊤))]

end SheafCondition

open SheafCondition
r2nos_open_dual "SheafCondition"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

theorem toH0_bijective' : letI := algebraOfHom c ⊤; Function.Bijective (𝒱.toH0 c) := by
  letI := algebraOfHom c ⊤
  have hpair : ∀ s : Γ(X, ⊤),
      ((𝒱.toH0 c s : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1))
        = (gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top s).1 := fun s => by
    rw [toH0_apply_coe]
    exact Prod.ext (gammaEquiv_apply_fst X _ _ _ s).symm (gammaEquiv_apply_snd X _ _ _ s).symm
  constructor
  · intro s s' hss'
    apply (gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top).injective
    apply Subtype.ext
    rw [← hpair, ← hpair, hss']
  · rintro ⟨p, hp⟩
    have hp' : p ∈ eqLocus X 𝒱.U0 𝒱.U1 :=
      (mem_eqLocus_iff X 𝒱.U0 𝒱.U1 p).mpr ((TwoChartCech.Cover.mem_H0_structureSheaf_iff _ p).mp hp)
    refine ⟨(gammaEquiv X 𝒱.U0 𝒱.U1 𝒱.sup_eq_top).symm ⟨p, hp'⟩, Subtype.ext ?_⟩
    rw [hpair, RingEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem solution {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}}
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ AlgebraicGeometry.Spec (.of R)) :
    letI := AlgebraicGeometry.Scheme.TwoAffineOpenCover.algebraOfHom c ⊤
    Function.Bijective (𝒱.toH0 c) :=
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.toH0_bijective' 𝒱 c

end
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
