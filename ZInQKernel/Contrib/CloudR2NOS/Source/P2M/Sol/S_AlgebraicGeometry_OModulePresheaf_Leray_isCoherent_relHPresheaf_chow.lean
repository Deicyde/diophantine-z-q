/-
NOS-CORE PROBE STAGING COPY (nos-core-probe-001, lane4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow.lean
  Source sha256  : 5dcaecb72638f3b654287b77e510a32ea005e61c15f62bfec41140c320792ac1
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000`; `set_option synthInstance.maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSimpArgs false`; `set_option linter.unusedVariables false`; `set_option maxHeartbeats 12800000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * H4 lane 1 default-limit edition (2026-11-17, for H5 C4): the cohomology tail of
    `finite_relHPresheaf_obj_chow` (Φker, its surjectivity and the two finiteness cases) is moved into
    the new generic helper `finite_of_cochain_equiv` (original steps, on abstract cochain modules);
    the theorem keeps its statement and instantiates it; v2 also moves `hopen`, `hact` and the whole
    chart part into the new helpers `chow_hopen`, `chow_hact`, `finite_of_chart` (v4: no `set` inside
    the helpers; they name `D.p ⁻¹ᵁ W` and the cover directly; v5 splits the cochain isomorphism
    into `chart_cochain_equiv`; v6 moves its `hstep` into `appLE_mul_res` and the per-`τ` step of
    `hcomm` into `chow_hcomm_tau`; v7 states the final instantiation eta-reduced, with the
    boundary fact as `relAltHB_mkQ_zero`; v8 passes the `Γ(Z, W)`-linear differential `relAltdΓ`
    and the quotient map `relAltπ`). No option, import or
    budget added.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow
r2nos_namespace_dual
r2nos_erase_attr "instance" "ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
r2nos_erase_attr "simp" "ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

noncomputable section

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow.AlgebraicGeometry TopologicalSpace Opposite CategoryTheory.Limits"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.map_appLE IsLocallyNoetherian Scheme.Opens.ι_image_le Scheme.Opens.topIso_inv Surjective IsProper morphismRestrict_ι IsClosedImmersion.of_comp LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom IsAffineOpen.fromSpec_top Scheme.Hom.image_preimage_eq_opensRange_inf QuasiCompact isPullback_morphismRestrict IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec Spec.map Scheme.toSpecΓ_naturality Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.isoSpec_Spec_inv Scheme.Hom.comp_appLE IsAffineOpen.isoSpec_hom_appTop Proj IsClosedImmersion.iff_isProper_and_mono IsClosedImmersion IsSeparated IsLocallyNoetherian.component_noetherian isAffineOpen_top toSpecΓ_SpecMap_ΓSpecIso_inv IsProper.of_comp Proj.basicOpen morphismRestrict IsAffineOpen IsNoetherian Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.comp_preimage Proj.map Scheme.Opens.opensRange_ι morphismRestrict_appLE Scheme.ΓSpecIso ProjSpace.stdCover ProjSpace.stdCoverPullback ProjSpace.π ChowDatumProj OModulePresheaf OModulePresheaf.d_apply OModulePresheaf.unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom OModulePresheaf.Leray.relHPresheaf OModulePresheaf.cechFinite_unit_of_isClosedImmersion_proj ProjSpace.isPullback_map ProjSpace.map_preimage_basicOpen_X"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "res_res cochain d d_apply HSucc IsCoherent unit mk module obj Leray.relHPresheaf Hom cechFinite_unit_of_isClosedImmersion_proj"
namespace Leray
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf.Leray" "map_iInf_fin relAltC relAltd relAltd_apply' relAltHB relAltH relHPresheaf"
w03_open "AlgebraicGeometry.OModulePresheaf.Leray AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

section Local

variable {R : Type u} [CommRing R]

theorem res_res' {V : Scheme.{u}} {O₁ O₂ O₃ : V.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃) (x : Γ(V, O₃)) :
    (V.presheaf.map (homOfLE h12).op).hom ((V.presheaf.map (homOfLE h23).op).hom x)
      = (V.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem res_refl' {V : Scheme.{u}} {O : V.Opens} (h : O ≤ O) (x : Γ(V, O)) :
    (V.presheaf.map (homOfLE h).op).hom x = x := by
  have : (homOfLE h : O ⟶ O) = 𝟙 O := rfl
  rw [this, op_id, V.presheaf.map_id]; rfl

theorem algebraOfHom_compat {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) (W : V.Opens) :
    ∀ c, letI := Scheme.TwoAffineOpenCover.algebraOfHom π W
      algebraMap R Γ(V, W) c = (V.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
        (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
  fun _ => rfl

theorem specMap_algebraMap_eq_fromSpec_comp {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) = hU.fromSpec ≫ f := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
  have halg : CommRingCat.ofHom (algebraMap R Γ(X, U))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U (le_top : U ≤ f ⁻¹ᵁ ⊤) := rfl
  rw [halg, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of R))) hU
      (le_top : U ≤ f ⁻¹ᵁ ⊤)]

theorem isNoeth_of_proper [IsNoetherianRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (CommRingCat.of R)) [IsProper π] : IsNoetherian V := by
  haveI : LocallyOfFiniteType π := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact {}

end Local

section RelHPresheafChow

variable {R : Type u} [CommRing R] {Z : Scheme.{u}}
variable (πZ : Z ⟶ Spec (CommRingCat.of R)) (D : ChowDatumProj πZ)

theorem lift_isClosedImm [IsSeparated πZ] :
    IsClosedImmersion (Limits.pullback.lift D.ιN D.p D.hoverN) := by
  haveI : IsSeparated (Limits.pullback.fst (ProjSpace.π R D.Nd) πZ) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  haveI : IsClosedImmersion (Limits.pullback.lift D.ιN D.p D.hoverN
      ≫ Limits.pullback.fst (ProjSpace.π R D.Nd) πZ) := by
    rw [Limits.pullback.lift_fst]; exact D.hιN_closed
  exact IsClosedImmersion.of_comp _ (Limits.pullback.fst (ProjSpace.π R D.Nd) πZ)


/-- (H4 L1 edition) the algebraic tail of `finite_relHPresheaf_obj_chow`, done once on abstract
cochain modules (original steps): an isomorphism of cochain complexes `φ` and a surjection `π` of
the target cocycles onto `Q` killing coboundaries transport finiteness of the source cohomology. -/
theorem finite_of_cochain_equiv {A : Type*} [CommRing A]
    {C E : ℕ → Type*} [∀ q, AddCommGroup (C q)] [∀ q, Module A (C q)]
    [∀ q, AddCommGroup (E q)] [∀ q, Module A (E q)]
    (dC : ∀ q, C q →ₗ[A] C (q + 1)) (dE : ∀ q, E q →ₗ[A] E (q + 1))
    (φ : ∀ q, C q ≃ₗ[A] E q) (hcomm : ∀ q f, φ (q + 1) (dC q f) = dE q (φ q f))
    (Q : ℕ → Type*) [∀ q, AddCommGroup (Q q)] [∀ q, Module A (Q q)]
    (π : ∀ q, ↥(LinearMap.ker (dE q)) →ₗ[A] Q q) (hπ : ∀ q, Function.Surjective (π q))
    (hπ0 : ∀ q (y : E q) (hy : dE (q + 1) (dE q y) = 0), π (q + 1) ⟨dE q y, hy⟩ = 0)
    (h0 : Module.Finite A ↥(LinearMap.ker (dC 0)))
    (hS : ∀ b, Module.Finite A (↥(LinearMap.ker (dC (b + 1))) ⧸
      (LinearMap.range (dC b)).comap (LinearMap.ker (dC (b + 1))).subtype))
    (b : ℕ) : Module.Finite A (Q b) := by
  let Φker : ∀ q, ↥(LinearMap.ker (dC q)) →ₗ[A] Q q := fun q =>
    { toFun := fun x => π q ⟨φ q x.1, LinearMap.mem_ker.mpr
        ((hcomm q x.1).symm.trans ((congrArg _ (LinearMap.mem_ker.mp x.2)).trans (map_zero _)))⟩
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        exact Subtype.ext (map_add (φ q) x.1 y.1)
      map_smul' := fun a x => by
        rw [RingHom.id_apply, ← map_smul]
        congr 1
        exact Subtype.ext ((φ q).map_smul a x.1) }
  have hΦsurj : ∀ q, Function.Surjective (Φker q) := fun q z => by
    obtain ⟨y, rfl⟩ := hπ q z
    refine ⟨⟨(φ q).symm y.1, LinearMap.mem_ker.mpr ((φ (q + 1)).injective
        ((hcomm q _).trans ((congrArg _ ((φ q).apply_symm_apply y.1)).trans
          ((LinearMap.mem_ker.mp y.2).trans (map_zero _).symm))))⟩, ?_⟩
    show π q ⟨φ q ((φ q).symm y.1), _⟩ = π q y
    congr 1
    exact Subtype.ext ((φ q).apply_symm_apply y.1)
  rcases b with _ | b'
  · haveI := h0; exact Module.Finite.of_surjective (Φker 0) (hΦsurj 0)
  · haveI := hS b'
    refine Module.Finite.of_surjective
      (((LinearMap.range (dC b')).comap (LinearMap.ker (dC (b' + 1))).subtype).liftQ
        (Φker (b' + 1)) ?_)
      (fun z => (hΦsurj (b' + 1) z).elim fun x hx =>
        ⟨Submodule.Quotient.mk x, (Submodule.liftQ_apply _ _ _).trans hx⟩)
    rintro ⟨x, hx⟩ hxS
    obtain ⟨y, rfl⟩ : x ∈ LinearMap.range (dC b') := Submodule.mem_comap.mp hxS
    have hy : dE (b' + 1) (dE b' (φ b' y)) = 0 := by
      rw [← hcomm b' y, ← hcomm (b' + 1) (dC b' y), LinearMap.mem_ker.mp hx, map_zero]
    rw [LinearMap.mem_ker]
    show π (b' + 1) ⟨φ (b' + 1) (dC b' y), _⟩ = 0
    have he : (⟨φ (b' + 1) (dC b' y), LinearMap.mem_ker.mpr ((hcomm (b' + 1) (dC b' y)).symm.trans
          ((congrArg _ (LinearMap.mem_ker.mp hx)).trans (map_zero _)))⟩ :
          ↥(LinearMap.ker (dE (b' + 1)))) = ⟨dE b' (φ b' y), hy⟩ := Subtype.ext (hcomm b' y)
    rw [he]
    exact hπ0 b' (φ b' y) hy

theorem chow_hopen {W : Z.Opens}
    (ιW : (D.p ⁻¹ᵁ W : Scheme.{u}) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (D.Nd + 1)) Γ(Z, W))) [IsAffineHom ιW]
    (hιW_fst : letI := Scheme.TwoAffineOpenCover.algebraOfHom πZ W
      ιW ≫ ProjSpace.map R Γ(Z, W) D.Nd = (D.p ⁻¹ᵁ W).ι ≫ D.ιN)
    {q : ℕ} (τ : (ProjSpace.stdCoverPullback D.ιN).Idx q) :
    (D.p ⁻¹ᵁ W).ι ''ᵁ (ProjSpace.stdCoverPullback ιW).inter τ =
      (ProjSpace.stdCoverPullback D.ιN).inter τ ⊓ D.p ⁻¹ᵁ W := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom πZ W
  have hchart : ∀ j, (ProjSpace.stdCoverPullback ιW).U j = (D.p ⁻¹ᵁ W).ι ⁻¹ᵁ (ProjSpace.stdCoverPullback D.ιN).U j := fun j => by
    show ιW ⁻¹ᵁ (ProjSpace.stdCover Γ(Z, W) D.Nd).U j
      = (D.p ⁻¹ᵁ W).ι ⁻¹ᵁ (D.ιN ⁻¹ᵁ (ProjSpace.stdCover R D.Nd).U j)
    rw [← Scheme.Hom.comp_preimage, ← hιW_fst, Scheme.Hom.comp_preimage,
      show (ProjSpace.stdCover R D.Nd).U j
        = AlgebraicGeometry.Proj.basicOpen _ (MvPolynomial.X j.down) from rfl,
      ProjSpace.map_preimage_basicOpen_X R Γ(Z, W) D.Nd j.down]
    rfl
  rw [show (ProjSpace.stdCoverPullback ιW).inter τ
        = (D.p ⁻¹ᵁ W).ι ⁻¹ᵁ (ProjSpace.stdCoverPullback D.ιN).inter τ from
      (iInf_congr fun j => hchart (τ.1 j)).trans (map_iInf_fin (D.p ⁻¹ᵁ W).ι _).symm,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]

theorem chow_hact {W : Z.Opens} (hW : IsAffineOpen W)
    (ιW : (D.p ⁻¹ᵁ W : Scheme.{u}) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (D.Nd + 1)) Γ(Z, W)))
    (hιW_snd : ιW ≫ ProjSpace.π Γ(Z, W) D.Nd = (D.p ∣_ W) ≫ hW.isoSpec.hom)
    (O : (D.p ⁻¹ᵁ W : Scheme.{u}).Opens) :
    (Scheme.ΓSpecIso (CommRingCat.of Γ(Z, W))).inv
        ≫ (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd).app ⊤
        ≫ (D.p ⁻¹ᵁ W : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op
      = D.p.appLE W ((D.p ⁻¹ᵁ W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _) := by

  rw [show (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd).app ⊤
        ≫ ((D.p ⁻¹ᵁ W) : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op
      = hW.isoSpec.hom.appTop ≫ (D.p ∣_ W).appLE ⊤ O le_top from
      hιW_snd ▸ Scheme.Hom.comp_appLE _ _ ⊤ O le_top,
    IsAffineOpen.isoSpec_hom_appTop,
    show (Scheme.ΓSpecIso (CommRingCat.of Γ(Z, W))).inv = (Scheme.ΓSpecIso Γ(Z, W)).inv
      from rfl,

    Category.assoc (obj := CommRingCat), Iso.inv_hom_id_assoc,
    morphismRestrict_appLE, Scheme.Opens.topIso_inv]
  erw [Scheme.Hom.map_appLE]

theorem appLE_mul_res {X Y : Scheme.{u}} (g : X ⟶ Y) {W : Y.Opens} {U V : X.Opens}
    (hUV : V ≤ U) (hU : U ≤ g ⁻¹ᵁ W) (hV : V ≤ g ⁻¹ᵁ W) (r : Γ(Y, W)) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE hUV).op).hom ((g.appLE W U hU).hom r * x) =
      (g.appLE W V hV).hom r * (X.presheaf.map (homOfLE hUV).op).hom x := by
  rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem chow_hcomm_tau {W : Z.Opens}
    (ιW : (D.p ⁻¹ᵁ W : Scheme.{u}) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (D.Nd + 1)) Γ(Z, W))) [IsClosedImmersion ιW]
    (hopen : ∀ {q} (τ : (ProjSpace.stdCoverPullback D.ιN).Idx q),
      (D.p ⁻¹ᵁ W).ι ''ᵁ (ProjSpace.stdCoverPullback ιW).inter τ
        = (ProjSpace.stdCoverPullback D.ιN).inter τ ⊓ (Opens.map D.p.base).obj W)
    (q : ℕ) (f : (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).cochain
      (ProjSpace.stdCoverPullback ιW) q)
    (τ : (ProjSpace.stdCoverPullback D.ιN).Idx (q + 1)) :
    (D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom
        ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d (ProjSpace.stdCoverPullback ιW) q f τ)
      = relAltd D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q
        (fun τ' => (D.V'.presheaf.map (homOfLE (hopen τ').ge).op).hom (f τ')) τ := by
  show (D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom
      ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d (ProjSpace.stdCoverPullback ιW) q f τ)
    = relAltd D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q
      (fun τ' => (D.V'.presheaf.map (homOfLE (hopen τ').ge).op).hom (f τ')) τ
  rw [OModulePresheaf.d_apply, relAltd_apply']
  refine (map_sum ((D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom : _ →+* _) _ _).trans
    (Finset.sum_congr rfl fun j _ => (map_zsmul
        ((D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom : _ →+* _) _ _).trans
      (congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) ?_))

  exact (res_res' (V := D.V') (hopen τ).ge _
      (f ((ProjSpace.stdCoverPullback D.ιN).face τ j))).trans
    (res_res' (V := D.V') (inf_le_inf_right _ ((ProjSpace.stdCoverPullback D.ιN).inter_le_inter_face τ j))
      (hopen ((ProjSpace.stdCoverPullback D.ιN).face τ j)).ge (f ((ProjSpace.stdCoverPullback D.ιN).face τ j))).symm

/-- (H4 L1 edition v5) the cochain isomorphism and its compatibility with the differentials,
packaged as an existential (original `hopen`/`hact`/`φC`/`hcomm` steps). -/
theorem chart_cochain_equiv {W : Z.Opens} (hW : IsAffineOpen W)
    (ιW : (D.p ⁻¹ᵁ W : Scheme.{u}) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (D.Nd + 1)) Γ(Z, W))) [IsClosedImmersion ιW]
    (hιW_fst : letI := Scheme.TwoAffineOpenCover.algebraOfHom πZ W
      ιW ≫ ProjSpace.map R Γ(Z, W) D.Nd = (D.p ⁻¹ᵁ W).ι ≫ D.ιN)
    (hιW_snd : ιW ≫ ProjSpace.π Γ(Z, W) D.Nd = (D.p ∣_ W) ≫ hW.isoSpec.hom) :
    letI instMR : ∀ O : ((D.p ⁻¹ᵁ W) : Scheme.{u}).Opens, Module Γ(Z, W) Γ(((D.p ⁻¹ᵁ W) : Scheme.{u}), O) :=
      fun O => (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).module O
    ∃ φ : ∀ q, (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).cochain
        (ProjSpace.stdCoverPullback ιW) q ≃ₗ[Γ(Z, W)]
          relAltC D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q,
      ∀ q f, φ (q + 1) ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d
          (ProjSpace.stdCoverPullback ιW) q f) =
        relAltd D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q (φ q f) := by
  have hopen : ∀ {q} (τ : (ProjSpace.stdCoverPullback D.ιN).Idx q),
      (D.p ⁻¹ᵁ W).ι ''ᵁ (ProjSpace.stdCoverPullback ιW).inter τ
        = (ProjSpace.stdCoverPullback D.ιN).inter τ ⊓ (Opens.map D.p.base).obj W := fun τ => chow_hopen πZ D ιW hιW_fst τ
  letI instMR : ∀ O : ((D.p ⁻¹ᵁ W) : Scheme.{u}).Opens, Module Γ(Z, W) Γ(((D.p ⁻¹ᵁ W) : Scheme.{u}), O) :=
    fun O => (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).module O

  have hact : ∀ (O : ((D.p ⁻¹ᵁ W) : Scheme.{u}).Opens),
      (Scheme.ΓSpecIso (CommRingCat.of Γ(Z, W))).inv
          ≫ (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd).app ⊤
          ≫ ((D.p ⁻¹ᵁ W) : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op
        = D.p.appLE W ((D.p ⁻¹ᵁ W).ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _) := fun O =>
    chow_hact πZ D hW ιW hιW_snd O

  let φC : ∀ q, (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).cochain
        (ProjSpace.stdCoverPullback ιW) q
      ≃ₗ[Γ(Z, W)] relAltC D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q := fun q =>
    { toFun := fun f τ => (D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom (f τ)
      invFun := fun g τ => (D.V'.presheaf.map (homOfLE (hopen τ).le).op).hom (g τ)
      left_inv := fun f => funext fun τ =>
        (res_res' _ _ _).trans (res_refl' _ _)
      right_inv := fun g => funext fun τ =>
        (res_res' _ _ _).trans (res_refl' _ _)
      map_add' := fun _ _ => funext fun τ => map_add _ _ _
      map_smul' := fun r f => funext fun τ => by

        have hstep : ∀ (x : Γ(D.V', (D.p ⁻¹ᵁ W).ι ''ᵁ
            (ProjSpace.stdCoverPullback ιW).inter τ)),
            (D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom
                ((D.p.appLE W _ (Scheme.Opens.ι_image_le _ _)).hom r * x)
              = (D.p.appLE W ((ProjSpace.stdCoverPullback D.ιN).inter τ ⊓ (Opens.map D.p.base).obj W)
                  inf_le_right).hom r
                * (D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom x := fun x =>
          appLE_mul_res D.p (hopen τ).ge (Scheme.Opens.ι_image_le _ _) inf_le_right r x
        refine (congrArg _ (?_ : (r • f) τ = _)).trans (hstep (f τ))
        exact congrArg₂ (α := Γ(D.V', _)) (· * ·)
          (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hact _)) r) rfl }

  have hcomm : ∀ q f, φC (q + 1)
        ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d
          (ProjSpace.stdCoverPullback ιW) q f)
      = relAltd D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q (φC q f) := fun q f => funext fun τ =>
    chow_hcomm_tau πZ D ιW hopen q f τ

  exact ⟨φC, hcomm⟩

theorem relAltHB_mkQ_zero (W : Z.Opens) (q : ℕ)
    (y : relAltC D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q)
    (hy : relAltd D.p πZ (ProjSpace.stdCoverPullback D.ιN) W (q + 1)
      (relAltd D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q y) = 0) :
    (relAltHB D.p πZ (ProjSpace.stdCoverPullback D.ιN) W (q + 1)).mkQ
      ⟨relAltd D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q y, hy⟩ = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩

/-- `relAltd` as a `Γ(Z, W)`-linear map (its `Γ(Z, W)`-linearity is `relAltd_Γsmul`). -/
noncomputable def relAltdΓ (W : Z.Opens) (q : ℕ) :
    relAltC D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q →ₗ[Γ(Z, W)] relAltC D.p πZ (ProjSpace.stdCoverPullback D.ιN) W (q + 1) where
  toFun x := relAltd D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q x
  map_add' x y := map_add (relAltd D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q) x y
  map_smul' a x := relAltd_Γsmul D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q a x

theorem relAltdΓ_apply (W : Z.Opens) (q : ℕ) (x : relAltC D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q) :
    relAltdΓ πZ D W q x = relAltd D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q x := rfl

/-- The quotient map from the `Γ(Z, W)`-cycles of `relAltdΓ` onto `relAltH`. -/
noncomputable def relAltπ (W : Z.Opens) (q : ℕ) :
    ↥(LinearMap.ker (relAltdΓ πZ D W q)) →ₗ[Γ(Z, W)] relAltH D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q where
  toFun x := Submodule.Quotient.mk ⟨x.1, LinearMap.mem_ker.mpr
    ((relAltdΓ_apply πZ D W q x.1).symm.trans (LinearMap.mem_ker.mp x.2))⟩
  map_add' x y := congrArg Submodule.Quotient.mk (Subtype.ext rfl)
  map_smul' a x := congrArg Submodule.Quotient.mk (Subtype.ext rfl)

theorem relAltπ_surjective (W : Z.Opens) (q : ℕ) : Function.Surjective (relAltπ πZ D W q) := by
  intro z
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨⟨y, LinearMap.mem_ker.mpr ((relAltdΓ_apply πZ D W q y).trans (LinearMap.mem_ker.mp hy))⟩,
    rfl⟩

theorem relAltπ_coboundary (W : Z.Opens) (q : ℕ) (y : relAltC D.p πZ (ProjSpace.stdCoverPullback D.ιN) W q)
    (hy : relAltdΓ πZ D W (q + 1) (relAltdΓ πZ D W q y) = 0) :
    relAltπ πZ D W (q + 1) ⟨relAltdΓ πZ D W q y, hy⟩ = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr
    (show (⟨_, _⟩ : ↥(LinearMap.ker _)) ∈ relAltHB D.p πZ (ProjSpace.stdCoverPullback D.ιN) W (q + 1) from ⟨y, rfl⟩)

theorem finite_of_chart {W : Z.Opens} (hW : IsAffineOpen W) (b : ℕ)
    (ιW : (D.p ⁻¹ᵁ W : Scheme.{u}) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (D.Nd + 1)) Γ(Z, W))) [IsClosedImmersion ιW]
    (hιW_fst : letI := Scheme.TwoAffineOpenCover.algebraOfHom πZ W
      ιW ≫ ProjSpace.map R Γ(Z, W) D.Nd = (D.p ⁻¹ᵁ W).ι ≫ D.ιN)
    (hιW_snd : ιW ≫ ProjSpace.π Γ(Z, W) D.Nd = (D.p ∣_ W) ≫ hW.isoSpec.hom)
    (hiva : (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).CechFinite
      (ProjSpace.stdCoverPullback ιW)) :
    Module.Finite Γ(Z, W) (relAltH D.p πZ (ProjSpace.stdCoverPullback D.ιN) W b) := by
  letI instMR : ∀ O : ((D.p ⁻¹ᵁ W) : Scheme.{u}).Opens, Module Γ(Z, W) Γ(((D.p ⁻¹ᵁ W) : Scheme.{u}), O) :=
    fun O => (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).module O
  obtain ⟨φC, hcomm⟩ := chart_cochain_equiv πZ D hW ιW hιW_fst hιW_snd
  have h0 := hiva.1
  have hS := hiva.2
  exact finite_of_cochain_equiv
    ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d (ProjSpace.stdCoverPullback ιW))
    (relAltdΓ πZ D W) φC
    (fun q f => (hcomm q f).trans (relAltdΓ_apply πZ D W q (φC q f)).symm)
    (relAltH D.p πZ (ProjSpace.stdCoverPullback D.ιN) W) (relAltπ πZ D W) (relAltπ_surjective πZ D W)
    (relAltπ_coboundary πZ D W) h0 hS b

theorem finite_relHPresheaf_obj_chow [IsNoetherianRing R] [IsProper πZ]
    {W : Z.Opens} (hW : IsAffineOpen W) (b : ℕ) :
    Module.Finite Γ(Z, W) ((relHPresheaf D.p πZ
      (ProjSpace.stdCoverPullback D.ιN) b).obj W) := by
  haveI : IsSeparated (D.p ≫ πZ) := inferInstance
  haveI := lift_isClosedImm πZ D

  letI : Algebra R Γ(Z, W) := Scheme.TwoAffineOpenCover.algebraOfHom πZ W
  haveI : IsNoetherian Z := isNoeth_of_proper πZ
  haveI hNoeth : IsNoetherianRing Γ(Z, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  set K' := ProjSpace.stdCoverPullback D.ιN
  set pW : D.V'.Opens := (Opens.map D.p.base).obj W

  suffices key : Module.Finite Γ(Z, W) (relAltH D.p πZ K' W b) by exact key

  have hsq : (pW.ι ≫ D.ιN) ≫ ProjSpace.π R D.Nd
      = ((D.p ∣_ W) ≫ hW.isoSpec.hom)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, W))) := by
    rw [Category.assoc, D.hoverN, Category.assoc,

      show hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, W))) = W.ι ≫ πZ from by

        rw [specMap_algebraMap_eq_fromSpec_comp πZ hW,
            ← hW.isoSpec_inv_ι, ← Category.assoc, hW.isoSpec.hom_inv_id_assoc],
      ← Category.assoc, ← morphismRestrict_ι D.p W, Category.assoc]

  let ιW := (ProjSpace.isPullback_map R Γ(Z, W) D.Nd).lift _ _ hsq
  have hιW_fst := (ProjSpace.isPullback_map R Γ(Z, W) D.Nd).lift_fst _ _ hsq
  have hιW_snd := (ProjSpace.isPullback_map R Γ(Z, W) D.Nd).lift_snd _ _ hsq

  haveI hιW_cl : IsClosedImmersion ιW := by

    haveI : IsProper (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd) := hιW_snd ▸ inferInstance
    haveI hprop : IsProper ιW := IsProper.of_comp ιW (ProjSpace.π Γ(Z, W) D.Nd)

    haveI : Mono (pW.ι ≫ D.ιN) := mono_comp _ _
    haveI hmono : Mono ιW := mono_of_mono_fac hιW_fst

    exact (IsClosedImmersion.iff_isProper_and_mono ιW).mpr ⟨hprop, hmono⟩

  have hiva := @OModulePresheaf.cechFinite_unit_of_isClosedImmersion_proj Γ(Z, W) _ hNoeth D.Nd _ ιW hιW_cl

  exact finite_of_chart πZ D hW b ιW hιW_fst hιW_snd hiva

theorem isCoherent_relHPresheaf_chow' [IsNoetherianRing R] [IsProper πZ] (b : ℕ) :
    (relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).IsCoherent :=
  fun W => finite_relHPresheaf_obj_chow πZ D W.2 b

end RelHPresheafChow

end AlgebraicGeometry.OModulePresheaf.Leray

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsProper πZ] (D : ChowDatumProj πZ) (b : ℕ) :
    (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.Leray.isCoherent_relHPresheaf_chow' πZ D b

end
end S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
