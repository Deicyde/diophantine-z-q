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
  Source file    : P2M/Sol/S_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral.lean
  Source sha256  : 6d601e871be3659bf42e2c6c1744e58e3e4910d7b7b6e4edbed5b508af147fe3
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 2 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
r2nos_namespace_dual

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
r2nos_open_dual "CategoryTheory CategoryTheory.Limits TopologicalSpace Topology"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "LocallyOfFiniteType Spec IsIntegral Scheme Scheme.basicOpen_zero exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen Scheme.ΓSpecIso"
namespace DimAffineOpen
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

theorem height_eq_ringKrullDim_of_isMaximal (k : Type u) [Field k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim A := by
  have h := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k m
  have h0 : ringKrullDim (A ⧸ m) = 0 := by
    letI : Field (A ⧸ m) := Ideal.Quotient.field m
    exact ringKrullDim_eq_zero_of_field (A ⧸ m)
  rwa [h0, add_zero] at h

theorem ringKrullDim_le_ringKrullDim_localization (k : Type u) [Field k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {g : A} (hg : g ≠ 0)
    (L : Type v) [CommRing L] [Algebra A L] [IsLocalization.Away g L] :
    ringKrullDim A ≤ ringKrullDim L := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := by
    rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_noZeroDivisors]
  have hg' : g ∉ (⊥ : Ideal A).jacobson := by rw [hjac]; simpa using hg
  rw [Ideal.jacobson, Ideal.mem_sInf] at hg'
  simp only [Set.mem_setOf_eq, not_forall, exists_prop] at hg'
  obtain ⟨M, ⟨-, hM⟩, hgM⟩ := hg'
  haveI : M.IsMaximal := hM
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid A) : Set A) (M : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hgM (hM.isPrime.mem_of_pow_mem n hn)
  have hMap : (M.map (algebraMap A L)).height = M.height :=
    IsLocalization.height_map_of_disjoint (Submonoid.powers g) M hdisj
  haveI : (M.map (algebraMap A L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) L M hM.isPrime hdisj
  calc ringKrullDim A = M.height := (height_eq_ringKrullDim_of_isMaximal k M).symm
    _ = (M.map (algebraMap A L)).height := by rw [hMap]
    _ ≤ ringKrullDim L := Ideal.height_le_ringKrullDim_of_isPrime

section TopologyB

attribute [local instance] specializationOrder

theorem topologicalKrullDim_le_of_forall_exists_isOpenEmbedding {X : Type u} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] (n : WithBot ℕ∞)
    (h : ∀ x : X, ∃ (U : Type u) (_ : TopologicalSpace U) (g : U → X),
      IsOpenEmbedding g ∧ x ∈ Set.range g ∧ topologicalKrullDim U ≤ n) :
    topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨U, _, g, hg, ⟨y, rfl⟩, hU⟩ := h x
  haveI : QuasiSober U := hg.quasiSober
  haveI : T0Space U := hg.isEmbedding.t0Space
  rw [hg.coheight_eq (x := y)]
  calc (↑(Order.coheight y) : WithBot ℕ∞) ≤ Order.krullDim U := Order.coheight_le_krullDim _
    _ = topologicalKrullDim U :=
        (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := U))).symm
    _ ≤ n := hU

end TopologyB

theorem topologicalKrullDim_affineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim ↥U = ringKrullDim Γ(X, U) := by
  have h : topologicalKrullDim (Spec Γ(X, U)) = ringKrullDim Γ(X, U) :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph] at h
  exact h

section Charts

variable {k : Type u} [Field k]

noncomputable abbrev chartAlgebra {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) : Algebra k Γ(X, U) :=
  ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra

theorem chart_finiteType {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := chartAlgebra f U
    Algebra.FiniteType k Γ(X, U) := by
  have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

theorem ringKrullDim_sections_le {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsIntegral X] {U U' : X.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hUne : (U : Set X).Nonempty) (hU'ne : (U' : Set X).Nonempty) :
    ringKrullDim Γ(X, U') ≤ ringKrullDim Γ(X, U) := by

  obtain ⟨z, hzU, hzU'⟩ := nonempty_preirreducible_inter U.2 U'.2 hUne hU'ne
  obtain ⟨g, hgU, hzg⟩ := hU'.exists_basicOpen_le ⟨z, hzU⟩ hzU'
  have hg : g ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hzg
    exact hzg
  haveI : Nonempty U' := ⟨⟨z, hzU'⟩⟩
  letI := chartAlgebra f U'
  haveI := chart_finiteType f hU'
  haveI := hU'.isLocalization_basicOpen g
  have h1 : ringKrullDim Γ(X, U') ≤ ringKrullDim Γ(X, X.basicOpen g) :=
    ringKrullDim_le_ringKrullDim_localization k hg _
  have h2 : ringKrullDim Γ(X, X.basicOpen g) = topologicalKrullDim ↥(X.basicOpen g) :=
    (topologicalKrullDim_affineOpen (hU'.basicOpen g)).symm
  have h3 : topologicalKrullDim ↥(X.basicOpen g) ≤ topologicalKrullDim ↥U :=
    Topology.IsInducing.topologicalKrullDim_le (IsEmbedding.inclusion hgU).isInducing
  rw [← topologicalKrullDim_affineOpen hU]
  exact h1.trans (h2.le.trans h3)

theorem topologicalKrullDim_le_ringKrullDim {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim X ≤ ringKrullDim Γ(X, U) := by
  refine topologicalKrullDim_le_of_forall_exists_isOpenEmbedding (X := X) _ fun ξ => ?_
  obtain ⟨U', hU', hξU', -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := ξ) (U := ⊤) trivial
  refine ⟨↥U', inferInstance, Subtype.val, U'.2.isOpenEmbedding_subtypeVal, ⟨⟨ξ, hξU'⟩, rfl⟩, ?_⟩
  rw [topologicalKrullDim_affineOpen hU']
  exact ringKrullDim_sections_le f hU hU' hUne ⟨ξ, hξU'⟩

theorem main {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim X = ringKrullDim Γ(X, U) := by
  refine le_antisymm (topologicalKrullDim_le_ringKrullDim f hU hUne) ?_
  rw [← topologicalKrullDim_affineOpen hU]
  exact topologicalKrullDim_subspace_le X (U : Set X)

end Charts

end AlgebraicGeometry.DimAffineOpen

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral.AlgebraicGeometry in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral.AlgebraicGeometry" in

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim X = ringKrullDim Γ(X, U) :=
  AlgebraicGeometry.DimAffineOpen.main f hU hUne
end S_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
