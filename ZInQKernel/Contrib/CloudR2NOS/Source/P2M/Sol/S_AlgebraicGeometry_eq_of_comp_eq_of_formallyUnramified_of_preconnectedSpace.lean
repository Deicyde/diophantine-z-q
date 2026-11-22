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
  Source file    : P2M/Sol/S_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace.lean
  Source sha256  : 5655cbc23916b0e9b82628ff8665aa374f4734f9c21703f0ac0d771c2bcd385d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

universe u

namespace P2mUnramifiedRigidity
r2nos_namespace_dual

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

theorem isOpen_range_diagonal [FormallyUnramified g] [LocallyOfFiniteType g] :
    IsOpen (Set.range (pullback.diagonal g).base) :=
  (pullback.diagonal g).isOpenEmbedding.isOpen_range

theorem isClosed_range_diagonal [IsSeparated g] :
    IsClosed (Set.range (pullback.diagonal g).base) := by
  haveI : IsClosedImmersion (pullback.diagonal g) := IsSeparated.isClosedImmersion_diagonal
  exact (pullback.diagonal g).isClosedEmbedding.isClosed_range

variable {g}

theorem comp_lift_eq_comp_diagonal {T Z : Scheme.{u}} (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (p : Z ⟶ T) (hp : p ≫ u₁ = p ≫ u₂) :
    p ≫ pullback.lift u₁ u₂ hg = (p ≫ u₁) ≫ pullback.diagonal g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
      Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
      Category.comp_id, hp]

theorem eq_of_comp_eq {T Z : Scheme.{u}} [FormallyUnramified g] [LocallyOfFiniteType g]
    [IsSeparated g] [PreconnectedSpace T]
    (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (p : Z ⟶ T) [Nonempty Z] (hp : p ≫ u₁ = p ≫ u₂) : u₁ = u₂ := by
  set v : T ⟶ pullback g g := pullback.lift u₁ u₂ hg with hv
  set W : Set T := v.base ⁻¹' Set.range (pullback.diagonal g).base with hW
  have hWclopen : IsClopen W :=
    ⟨(isClosed_range_diagonal g).preimage v.base.hom.continuous,
      (isOpen_range_diagonal g).preimage v.base.hom.continuous⟩
  have hWne : W.Nonempty := by
    obtain ⟨z⟩ := ‹Nonempty Z›
    refine ⟨p.base z, ?_⟩
    show v.base (p.base z) ∈ Set.range (pullback.diagonal g).base
    refine ⟨u₁.base (p.base z), ?_⟩
    have h := comp_lift_eq_comp_diagonal u₁ u₂ hg p hp
    have h' := congrArg (fun φ : Z ⟶ pullback g g => φ.base z) h
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at h'
    exact h'.symm
  have hWuniv : W = Set.univ := by
    rcases isClopen_iff.mp hWclopen with h | h
    · exact absurd h hWne.ne_empty
    · exact h
  have hrange : Set.range v.base ⊆ Set.range (pullback.diagonal g).base := by
    rintro _ ⟨t, rfl⟩
    have ht : t ∈ W := by rw [hWuniv]; exact Set.mem_univ t
    exact ht
  set l : T ⟶ X := IsOpenImmersion.lift (pullback.diagonal g) v hrange with hl
  have hlv : l ≫ pullback.diagonal g = v := IsOpenImmersion.lift_fac _ _ hrange
  have h1 : u₁ = l := by
    calc u₁ = v ≫ pullback.fst g g := by rw [hv, pullback.lift_fst]
      _ = (l ≫ pullback.diagonal g) ≫ pullback.fst g g := by rw [hlv]
      _ = l := by simp
  have h2 : u₂ = l := by
    calc u₂ = v ≫ pullback.snd g g := by rw [hv, pullback.lift_snd]
      _ = (l ≫ pullback.diagonal g) ≫ pullback.snd g g := by rw [hlv]
      _ = l := by simp
  rw [h1, h2]

end P2mUnramifiedRigidity

theorem solution
    {X Y T Z : Scheme.{u}} (g : X ⟶ Y) [FormallyUnramified g] [LocallyOfFiniteType g]
    [IsSeparated g] [PreconnectedSpace T]
    (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (p : Z ⟶ T) [Nonempty Z] (hp : p ≫ u₁ = p ≫ u₂) :
    u₁ = u₂ :=
  P2mUnramifiedRigidity.eq_of_comp_eq u₁ u₂ hg p hp
end S_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
