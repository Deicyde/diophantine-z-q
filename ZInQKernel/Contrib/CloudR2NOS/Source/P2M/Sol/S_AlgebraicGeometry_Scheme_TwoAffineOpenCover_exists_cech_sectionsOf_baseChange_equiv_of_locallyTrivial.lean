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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial.lean
  Source sha256  : 39425d57e9999e25cdb8bee74c99c1c865cc91e6b1a49655c4c1345230cd294c
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
r2nos_namespace_dual
r2nos_erase_attr "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct"

namespace TwoChartCech
r2nos_namespace_dual
w03_export "TwoChartCech" "Cover Sections Sections.cechDiff_apply"
namespace Sections
r2nos_namespace_dual
w03_export "TwoChartCech.Sections" "cechDiff cechDiff_apply H0 H1 mk.injEq r1 r0 M1 mk M01 M0"
namespace BC
r2nos_namespace_dual
w03_open "TwoChartCech.Sections TwoChartCech"

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
variable {𝒰 : TwoChartCech.Cover.{u, u} R} {𝒰A : TwoChartCech.Cover.{u, u} A}
variable (S : TwoChartCech.Sections.{u, u, u} 𝒰) (T : TwoChartCech.Sections.{u, u, u} 𝒰A)
variable (e0 : A ⊗[R] S.M0 ≃ₗ[A] T.M0) (e1 : A ⊗[R] S.M1 ≃ₗ[A] T.M1)

def pairMap : A ⊗[R] (S.M0 × S.M1) →ₗ[A] T.M0 × T.M1 :=
  (e0.toLinearMap.prodMap e1.toLinearMap) ∘ₗ (TensorProduct.prodRight R A A S.M0 S.M1).toLinearMap

theorem pairMap_apply (x : A ⊗[R] (S.M0 × S.M1)) :
    pairMap S T e0 e1 x = (e0 (TensorProduct.prodRight R A A _ _ x).1, e1 (TensorProduct.prodRight R A A _ _ x).2) :=
  rfl

theorem pairMap_bijective : Function.Bijective (pairMap S T e0 e1) := by
  constructor
  · intro x y h
    apply (TensorProduct.prodRight R A A _ _).injective
    rw [pairMap_apply, pairMap_apply, Prod.mk.injEq] at h
    exact Prod.ext (e0.injective h.1) (e1.injective h.2)
  · rintro ⟨p0, p1⟩
    obtain ⟨x0, rfl⟩ := e0.surjective p0
    obtain ⟨x1, rfl⟩ := e1.surjective p1
    refine ⟨(TensorProduct.prodRight R A A _ _).symm (x0, x1), ?_⟩
    rw [pairMap_apply, LinearEquiv.apply_symm_apply]

variable (e01 : A ⊗[R] S.M01 ≃ₗ[A] T.M01)
  (h0 : ∀ x, e01 ((S.r0.baseChange A) x) = T.r0 (e0 x)) (h1 : ∀ x, e01 ((S.r1.baseChange A) x) = T.r1 (e1 x))

include h0 h1 in

theorem e01_cechDiff_baseChange (x : A ⊗[R] (S.M0 × S.M1)) :
    e01 ((S.cechDiff.baseChange A) x) = T.cechDiff (pairMap S T e0 e1 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    rw [pairMap_apply, TensorProduct.prodRight_tmul, LinearMap.baseChange_tmul,
      TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply, TensorProduct.tmul_sub, map_sub]
    have h1' := h1 (a ⊗ₜ[R] s.2)
    have h0' := h0 (a ⊗ₜ[R] s.1)
    rw [LinearMap.baseChange_tmul] at h1' h0'
    exact congrArg₂ (· - ·) h1' h0'

include h0 h1 in
theorem mem_ker_baseChange_iff (x : A ⊗[R] (S.M0 × S.M1)) :
    x ∈ LinearMap.ker (S.cechDiff.baseChange A) ↔ pairMap S T e0 e1 x ∈ T.H0 := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← e01_cechDiff_baseChange S T e0 e1 e01 h0 h1,
    ← map_zero e01, e01.injective.eq_iff]

include h0 h1 in

theorem nonempty_kerEquivH0 : Nonempty (T.H0 ≃ₗ[A] LinearMap.ker (S.cechDiff.baseChange A)) := by
  let f : LinearMap.ker (S.cechDiff.baseChange A) →ₗ[A] T.H0 :=
    (pairMap S T e0 e1).restrict fun x hx => (mem_ker_baseChange_iff S T e0 e1 e01 h0 h1 x).mp hx
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext ((pairMap_bijective S T e0 e1).1 (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := (pairMap_bijective S T e0 e1).2 y
      exact ⟨⟨x, (mem_ker_baseChange_iff S T e0 e1 e01 h0 h1 x).mpr hy⟩, rfl⟩
  exact ⟨(LinearEquiv.ofBijective f hf).symm⟩

include h0 h1 in

theorem nonempty_cokerEquivH1 :
    Nonempty (((A ⊗[R] S.M01) ⧸ LinearMap.range (S.cechDiff.baseChange A)) ≃ₗ[A] T.H1) :=
  Nonempty.intro <| Submodule.Quotient.equiv _ _ e01 (by
    apply le_antisymm
    · rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
      refine ⟨pairMap S T e0 e1 x, ?_⟩
      exact (e01_cechDiff_baseChange S T e0 e1 e01 h0 h1 x).symm
    · rintro y ⟨p, rfl⟩
      obtain ⟨x, rfl⟩ := (pairMap_bijective S T e0 e1).2 p
      exact ⟨(S.cechDiff.baseChange A) x, LinearMap.mem_range_self _ _, e01_cechDiff_baseChange S T e0 e1 e01 h0 h1 x⟩)

theorem nonempty_coker_baseChange_equiv {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) :
    Nonempty (((A ⊗[R] C1) ⧸ LinearMap.range (d.baseChange A)) ≃ₗ[A] A ⊗[R] (C1 ⧸ LinearMap.range d)) := by
  have hexact : Function.Exact d (LinearMap.range d).mkQ := LinearMap.exact_map_mkQ_range d
  have hsurj : Function.Surjective (LinearMap.range d).mkQ := Submodule.mkQ_surjective _
  have hexA : Function.Exact (d.baseChange A) ((LinearMap.range d).mkQ.baseChange A) := by
    have := lTensor_exact A hexact hsurj
    intro y
    exact this y
  have hsurjA : Function.Surjective ((LinearMap.range d).mkQ.baseChange A) := by
    have := LinearMap.lTensor_surjective A hsurj
    intro y; exact this y
  exact ⟨hexA.linearEquivOfSurjective hsurjA⟩

theorem nonempty_ker_baseChange_equiv_of_flat {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1]
    [Module R C1] (d : C0 →ₗ[R] C1) [Module.Flat R A] :
    Nonempty (LinearMap.ker (d.baseChange A) ≃ₗ[A] A ⊗[R] LinearMap.ker d) := by

  let ι : A ⊗[R] LinearMap.ker d →ₗ[A] A ⊗[R] C0 := (LinearMap.ker d).subtype.baseChange A
  have hinj : Function.Injective ι :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := A) (LinearMap.ker d).subtype
      (LinearMap.ker d).injective_subtype
  have hexact : Function.Exact (LinearMap.ker d).subtype d := LinearMap.exact_subtype_ker_map d
  have hexA : Function.Exact ι (d.baseChange A) := by
    have := Module.Flat.lTensor_exact A hexact
    intro y; exact this y
  have hker : LinearMap.ker (d.baseChange A) = LinearMap.range ι := hexA.linearMap_ker_eq
  exact ⟨(LinearEquiv.ofEq _ _ hker) ≪≫ₗ (LinearEquiv.ofInjective ι hinj).symm⟩

end TwoChartCech.Sections.BC

open AlgebraicGeometry.Scheme.TwoAffineOpenCover in
r2nos_open_dual "AlgebraicGeometry.Scheme.TwoAffineOpenCover" in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H1
      ≃ₗ[A] A ⊗[R] (𝒱.sectionsOf c M).H1) ∧
    Nonempty (((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0
      ≃ₗ[A] LinearMap.ker ((𝒱.sectionsOf c M).cechDiff.baseChange A)) ∧
    (Module.Flat R A →
      Nonempty (((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0
      ≃ₗ[A] A ⊗[R] (𝒱.sectionsOf c M).H0)) := by
  obtain ⟨e0, e1, e01, h0, h1, -, -, -⟩ :=
    AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c M htriv A
  refine ⟨?_, TwoChartCech.Sections.BC.nonempty_kerEquivH0 _ _ e0 e1 e01 h0 h1, fun hflat => ?_⟩
  · obtain ⟨f⟩ := TwoChartCech.Sections.BC.nonempty_coker_baseChange_equiv (A := A) (𝒱.sectionsOf c M).cechDiff
    obtain ⟨g⟩ := TwoChartCech.Sections.BC.nonempty_cokerEquivH1 _ _ e0 e1 e01 h0 h1
    exact ⟨g.symm ≪≫ₗ f⟩
  · haveI := hflat
    obtain ⟨g⟩ := TwoChartCech.Sections.BC.nonempty_kerEquivH0 _ _ e0 e1 e01 h0 h1
    obtain ⟨f⟩ := TwoChartCech.Sections.BC.nonempty_ker_baseChange_equiv_of_flat (A := A) (𝒱.sectionsOf c M).cechDiff
    exact ⟨g ≪≫ₗ f⟩
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
