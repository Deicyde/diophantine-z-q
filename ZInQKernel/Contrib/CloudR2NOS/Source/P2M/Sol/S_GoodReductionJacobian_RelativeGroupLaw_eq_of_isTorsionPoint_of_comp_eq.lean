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
  Source file    : P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_eq_of_isTorsionPoint_of_comp_eq.lean
  Source sha256  : 1d2fc720547d9a6818403c52ba89500cf22786073ea6a05beadc7260944879ac
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_isTorsionPoint_of_comp_eq
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

namespace P2mTorsionRigidity
r2nos_namespace_dual

theorem preconnectedSpace_of_forall_specializes {α : Type*} [TopologicalSpace α] (c : α)
    (hc : ∀ x : α, x ⤳ c) : PreconnectedSpace α := by
  refine ⟨fun U V hU hV hUV hxU' hyV' => ?_⟩
  obtain ⟨x, -, hxU⟩ := hxU'
  obtain ⟨y, -, hyV⟩ := hyV'
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hxV : x ∉ V := fun hxV => by
    have : x ∈ Set.univ ∩ (U ∩ V) := ⟨Set.mem_univ x, hxU, hxV⟩
    rw [h] at this; exact this
  have hyU : y ∉ U := fun hyU => by
    have : y ∈ Set.univ ∩ (U ∩ V) := ⟨Set.mem_univ y, hyU, hyV⟩
    rw [h] at this; exact this
  have hcV : c ∈ Vᶜ := (hc x).mem_closed hV.isClosed_compl hxV
  have hcU : c ∈ Uᶜ := (hc y).mem_closed hU.isClosed_compl hyU
  rcases hUV (Set.mem_univ c) with hcU' | hcV'
  · exact hcU hcU'
  · exact hcV hcV'

scoped instance preconnectedSpace_spec_of_isLocalRing (O : Type u) [CommRing O] [IsLocalRing O] :
    PreconnectedSpace (Spec (CommRingCat.of O)) :=
  preconnectedSpace_of_forall_specializes (IsLocalRing.closedPoint O)
    (fun x => IsLocalRing.specializes_closedPoint x)

scoped instance connectedSpace_spec_of_isLocalRing (O : Type u) [CommRing O] [IsLocalRing O] :
    ConnectedSpace (Spec (CommRingCat.of O)) where
  toNonempty := ⟨IsLocalRing.closedPoint O⟩

section Torsion

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem coe_nsmul_eq_comp_schemeNsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id x.1)
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

theorem coe_comp_schemeNsmul_of_isTorsionPoint (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) {x : SchemeHomOver t f}
    (hx : G.IsTorsionPoint t n x) :
    x.1 ≫ G.schemeNsmul n = (G.one t).1 := by
  rw [← coe_nsmul_eq_comp_schemeNsmul, hx]

variable [IsLocalRing R]

theorem eq_of_isTorsionPoint_of_comp_eq [IsSeparated f] [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    {T : Scheme.{u}} [PreconnectedSpace T] (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) (hx : G.IsTorsionPoint t n x) (hy : G.IsTorsionPoint t n y)
    {Z : Scheme.{u}} [Nonempty Z] (p : Z ⟶ T) (hp : p ≫ x.1 = p ≫ y.1) :
    x = y := by
  haveI : FormallyUnramified (G.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
      G hcomm n hn
  haveI : LocallyOfFiniteType (G.schemeNsmul n ≫ f) := by
    rw [G.schemeNsmul_over n]; infer_instance
  haveI : LocallyOfFiniteType (G.schemeNsmul n) := locallyOfFiniteType_of_comp _ f
  haveI : IsSeparated (G.schemeNsmul n ≫ f) := by
    rw [G.schemeNsmul_over n]; infer_instance
  haveI : IsSeparated (G.schemeNsmul n) := IsSeparated.of_comp _ f
  apply Subtype.ext
  refine AlgebraicGeometry.eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace
    (G.schemeNsmul n) x.1 y.1 ?_ p hp
  rw [coe_comp_schemeNsmul_of_isTorsionPoint G t n hx,
    coe_comp_schemeNsmul_of_isTorsionPoint G t n hy]

theorem eq_of_isTorsionPoint_of_residue_comp_eq [IsSeparated f] [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    (O : Type u) [CommRing O] [IsLocalRing O]
    (t : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) (hx : G.IsTorsionPoint t n x) (hy : G.IsTorsionPoint t n y)
    (hres : Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ x.1 =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ y.1) :
    x = y :=
  eq_of_isTorsionPoint_of_comp_eq G hcomm n hn t x y hx hy
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) hres

end Torsion

end P2mTorsionRigidity
w03_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_isTorsionPoint_of_comp_eq.P2mTorsionRigidity"

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] [LocallyOfFiniteType f]
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R))
    {T : Scheme.{u}} [PreconnectedSpace T] (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) (hx : G.IsTorsionPoint t n x) (hy : G.IsTorsionPoint t n y)
    {Z : Scheme.{u}} [Nonempty Z] (p : Z ⟶ T) (hp : p ≫ x.1 = p ≫ y.1) :
    x = y :=
  P2mTorsionRigidity.eq_of_isTorsionPoint_of_comp_eq G hcomm n hn t x y hx hy p hp
end S_GoodReductionJacobian_RelativeGroupLaw_eq_of_isTorsionPoint_of_comp_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
