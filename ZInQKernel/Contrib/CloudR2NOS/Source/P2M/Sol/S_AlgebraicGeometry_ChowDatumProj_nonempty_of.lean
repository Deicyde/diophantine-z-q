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
  Source file    : P2M/Sol/S_AlgebraicGeometry_ChowDatumProj_nonempty_of.lean
  Source sha256  : b3d0062e8e3a3b4a2593f9db725a42669171e8380a7c3c60a05c84cfa7054783
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 13 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 6 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000`; `set_option synthInstance.maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSimpArgs false`; `set_option linter.unusedVariables false`; `set_option maxHeartbeats 16000000 in`; `set_option maxHeartbeats 25600000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

/-
DEFAULT-LIMIT EDITION, 2026-11-17. The attributed base above is preserved.
The Segre coordinate transition is proved separately over its actual
commutative target ring; the scheme gluing theorem supplies all five
compatibility equations from its unchanged actual pullbacks. The two
one-factor inverse-image computations and the one-chart computation are
also separate proved lemmas. Every existing declaration statement and
import is unchanged. No numeric limit option is added. The inherited
nonnumeric transparency switches are disclosed with the source binding.
SOURCE only; parent owns default compilation and C4 owns binding.
-/

/-
DEFAULT-LIMIT CONTINUATION v2, 2026-11-17. The failed v1 SOURCE, its
recorded diff and parent log are preserved separately. The SAME Segre
compatibility is now proved with the source scheme W and the two actual
affine arrows as parameters; the cover consumer supplies its already-proved
left/right pullback equations. No new final hypothesis is introduced.
The actual left/right inverse images use a typed commuting-triangle lemma
and short calculations instead of an underconstrained congrArg.
All existing declarations/imports/attribution/options are unchanged.
No numeric budget change, no admission; parent probes and C4 binds.
-/

/-
DEFAULT-LIMIT CONTINUATION v3, 2026-11-17. Failed v2 SOURCE and all earlier
editions/diffs/logs are preserved separately. The chart overlap, prime-range
argument, ring adjunction and second Segre projection now have separate
proved declarations, so the SAME chart_maps_compat endpoint no longer
elaborates their entire diagram in one budget. The cover consumer exposes
the Fin chart indices before normalizing its original equalities. Typed
inverse-image congruence replaces the prior failed calc chains. No existing
name/statement/import/nonnumeric option is changed, no numeric limit or
final compatibility Fact is added. SOURCE only; parent probes and C4 binds.
-/

/-
DEFAULT-LIMIT CONTINUATION v4, 2026-11-17. The failed 99639ca0 edition
and every earlier SOURCE/diff/log remain unchanged. The four tensor
inclusion mismatches are normalized by their literal tmul value formulas.
The homogeneous transition's open-immersion proof and common composite
are proved at a separate single-factor telescope; assembly uses a genuine
abstract categorical common-factor lemma. Basic-open pullback is proved
at an abstract source and transported through typed actual cover triangles.
The original cover conversions now close their residual reflexive HEq goals.
Every existing name/statement/import/attribution/nonnumeric option remains;
no numeric limit or final Fact is added. Parent probes; C4 binds.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.RationalMap
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.TensorProduct.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of
r2nos_namespace_dual

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
r2nos_open_dual "CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial"
open HomogeneousLocalization TensorProduct
r2nos_open_dual "HomogeneousLocalization TensorProduct"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift Surjective Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right Proj.opensRange_awayι IsClosedImmersion.of_comp Scheme.Hom Scheme.Pullback.range_map Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left IsZariskiLocalAtTarget Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Proj.awayι Scheme.Pullback.openCoverOfLeftRight pullbackSpecIso Proj.fromOfGlobalSections_toSpecZero IsOpenImmersion Proj Scheme.Cover.pullbackHom IsClosedImmersion.spec_of_surjective Proj.pullbackAwayιIso IsClosedImmersion IsSeparated Proj.awayι_preimage_basicOpen ext_to_Spec IsOpenImmersion.isoOfRangeEq toSpecΓ_SpecMap_ΓSpecIso_inv Proj.basicOpen Proj.pullbackAwayιIso_inv_fst IsZariskiLocalAtTarget.of_openCover pullbackSpecIso_hom_fst Scheme.Pullback.openCoverOfLeftRight_f Scheme.Hom.opensRange_pullbackFst Scheme.Cover.ι_glueMorphisms Proj.SpecMap_awayMap_awayι Scheme.Hom.comp_preimage Proj.fromOfGlobalSections pullbackSpecIso_hom_snd IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.Cover IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.ΓSpecIso pullbackSpecIso_hom_fst_assoc ProjSpace.grad0Equiv ProjSpace.π ProjSpace.isProper_π ProjSpace.X_mem_one ProjSpace.awayι_comp_π ProjSpace.ratio ProjSpace.ratio_self ProjSpace.val_algebraMap ProjSpace.affineOpenCover ProjSpace.affineOpenCover_f ProjSpace.adjoin_range_ratio ProjSpace.prodOver ProjSpace.prodOverπ ChowDatum ChowDatumProj"
w03_open "AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace
r2nos_namespace_dual
w03_export "AlgebraicGeometry.ProjSpace" "grad0Equiv π isProper_π X_mem_one awayι_comp_π ratio ratio_self val_algebraMap affineOpenCover affineOpenCover_f adjoin_range_ratio prodOver prodOverπ map"
namespace Segre
r2nos_namespace_dual
w03_open "AlgebraicGeometry.ProjSpace"

section ChartHom

variable (R : Type u) [CommRing R] (n p : ℕ)

abbrev bigN : ℕ := (n + 1) * (p + 1) - 1

theorem bigN_succ :
    (n + 1) * (p + 1) = bigN n p + 1 := by
  have h : 0 < (n + 1) * (p + 1) := Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos p)
  unfold bigN; omega

def idx : Fin (n + 1) × Fin (p + 1) ≃ Fin (bigN n p + 1) :=
  finProdFinEquiv.trans (finCongr (bigN_succ n p))

variable (i : Fin (n + 1)) (j : Fin (p + 1))

local notation "N" => bigN n p
local notation "𝒜ˣ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜ʸ" => MvPolynomial.homogeneousSubmodule (Fin (p + 1)) R
local notation "𝒜ᶻ" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

abbrev Tij : Type u :=
  (Away 𝒜ˣ (MvPolynomial.X i)) ⊗[R] (Away 𝒜ʸ (MvPolynomial.X j))

local notation "Aˣ" => Away 𝒜ˣ (MvPolynomial.X i)
local notation "Aʸ" => Away 𝒜ʸ (MvPolynomial.X j)

def preSegre : MvPolynomial (Fin (N + 1)) R →ₐ[R] (Aˣ ⊗[R] Aʸ) :=
  MvPolynomial.aeval
    (fun α => ((ProjSpace.ratio R n i ((idx n p).symm α).1)
      ⊗ₜ[R] (ProjSpace.ratio R p j ((idx n p).symm α).2) : Aˣ ⊗[R] Aʸ))

theorem preSegre_apply (k : Fin (n + 1)) (l : Fin (p + 1)) :
    preSegre R n p i j (MvPolynomial.X (idx n p (k, l)))
      = ((ProjSpace.ratio R n i k) ⊗ₜ[R] (ProjSpace.ratio R p j l) :
          Aˣ ⊗[R] Aʸ) := by
  unfold preSegre
  rw [MvPolynomial.aeval_X, Equiv.symm_apply_apply]

theorem preSegre_unit :
    (preSegre R n p i j).toRingHom
        (MvPolynomial.X (idx n p (i, j))) = 1 := by
  show preSegre R n p i j (MvPolynomial.X (idx n p (i, j))) = 1
  rw [preSegre_apply, ProjSpace.ratio_self, ProjSpace.ratio_self,
    Algebra.TensorProduct.one_def]

theorem preSegre_mulone :
    (preSegre R n p i j).toRingHom
        (X (idx n p (i, j))) * 1 = 1 := by
  rw [preSegre_unit, mul_one]

def segreLift :
    Localization.Away (X (idx n p (i, j)) :
      MvPolynomial (Fin (N + 1)) R) →+* Tij R n p i j :=
  Localization.awayLift (preSegre R n p i j).toRingHom
    (MvPolynomial.X (idx n p (i, j)))
    ⟨⟨(preSegre R n p i j).toRingHom (X (idx n p (i, j))),
      1, preSegre_mulone R n p i j,
      (one_mul _).trans (preSegre_unit R n p i j)⟩, rfl⟩

def segreChart :
    Away 𝒜ᶻ (MvPolynomial.X (idx n p (i, j)))
      →+* Tij R n p i j :=
  (segreLift R n p i j).comp
    (algebraMap (Away 𝒜ᶻ (MvPolynomial.X (idx n p (i, j))))
      (Localization.Away (MvPolynomial.X (idx n p (i, j)))))

theorem segreChart_ratio (k : Fin (n + 1)) (l : Fin (p + 1)) :
    segreChart R n p i j
        (ProjSpace.ratio R N (idx n p (i, j))
          (idx n p (k, l)))
      = ((ProjSpace.ratio R n i k) ⊗ₜ[R] (ProjSpace.ratio R p j l) :
          Tij R n p i j) := by
  unfold segreChart segreLift Localization.awayLift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk', IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec, map_pow, pow_one, preSegre_unit, one_mul]
  exact preSegre_apply R n p i j k l

theorem segreChart_algebraMap (r : R) :
    segreChart R n p i j
        (algebraMap R (Away 𝒜ᶻ (X (idx n p (i, j)))) r)
      = ((1 : Aˣ) ⊗ₜ[R] algebraMap R Aʸ r : Aˣ ⊗[R] Aʸ) := by
  unfold segreChart segreLift
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    ProjSpace.val_algebraMap]
  erw [IsLocalization.lift_eq]
  have := (preSegre R n p i j).commutes r
  rw [Algebra.TensorProduct.algebraMap_apply'] at this
  exact this

theorem segreChart_surjective :
    Function.Surjective (segreChart R n p i j) := by
  intro z
  suffices h : z ∈ (segreChart R n p i j).range from h
  have hswap : ∀ r, ((1:Aˣ) ⊗ₜ[R] algebraMap R Aʸ r : Aˣ ⊗[R] Aʸ)
      = (algebraMap R Aˣ r) ⊗ₜ[R] (1:Aʸ) := fun r => by
    rw [Algebra.algebraMap_eq_smul_one (A := Aʸ), Algebra.algebraMap_eq_smul_one (A := Aˣ)]
    exact (TensorProduct.smul_tmul r (1:Aˣ) (1:Aʸ)).symm
  have hR : ∀ r, ((algebraMap R Aˣ r) ⊗ₜ[R] (1 : Aʸ) : Aˣ ⊗[R] Aʸ)
      ∈ (segreChart R n p i j).range :=
    fun r => ⟨algebraMap R _ r,
      (segreChart_algebraMap R n p i j r).trans (hswap r)⟩
  have hx : ∀ k, (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Aʸ) : Aˣ ⊗[R] Aʸ)
      ∈ (segreChart R n p i j).range := fun k => by
    rw [show (1 : Aʸ) = ProjSpace.ratio R p j j from (ProjSpace.ratio_self R p j).symm]
    exact ⟨_, segreChart_ratio R n p i j k j⟩
  have hy : ∀ l, ((1 : Aˣ) ⊗ₜ[R] ProjSpace.ratio R p j l : Aˣ ⊗[R] Aʸ)
      ∈ (segreChart R n p i j).range := fun l => by
    rw [show (1 : Aˣ) = ProjSpace.ratio R n i i from (ProjSpace.ratio_self R n i).symm]
    exact ⟨_, segreChart_ratio R n p i j i l⟩
  induction z using TensorProduct.induction_on with
  | zero => exact Subring.zero_mem _
  | add a b ha hb => exact Subring.add_mem _ ha hb
  | tmul a b =>
    rw [show (a ⊗ₜ[R] b : Aˣ ⊗[R] Aʸ) = (a ⊗ₜ[R] (1:Aʸ)) * ((1:Aˣ) ⊗ₜ[R] b) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    refine Subring.mul_mem _ ?_ ?_
    · have ha : a ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R n i)) := by
        rw [ProjSpace.adjoin_range_ratio]; exact Algebra.mem_top
      refine Algebra.adjoin_induction
        (fun c ⟨k, hk⟩ => hk ▸ hx k)
        (fun r => ?_)
        (fun a b _ _ ha hb => by rw [TensorProduct.add_tmul]; exact Subring.add_mem _ ha hb)
        (fun a b _ _ ha hb => by
          rw [show ((a * b) ⊗ₜ[R] (1:Aʸ) : Aˣ ⊗[R] Aʸ) = (a ⊗ₜ 1) * (b ⊗ₜ 1) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
          exact Subring.mul_mem _ ha hb)
        ha
      exact hR r
    · have hb : b ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R p j)) := by
        rw [ProjSpace.adjoin_range_ratio]; exact Algebra.mem_top
      refine Algebra.adjoin_induction
        (fun c ⟨l, hl⟩ => hl ▸ hy l)
        (fun r => ?_)
        (fun a b _ _ ha hb => by rw [TensorProduct.tmul_add]; exact Subring.add_mem _ ha hb)
        (fun a b _ _ ha hb => by
          rw [show ((1:Aˣ) ⊗ₜ[R] (a * b) : Aˣ ⊗[R] Aʸ) = (1 ⊗ₜ a) * (1 ⊗ₜ b) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
          exact Subring.mul_mem _ ha hb)
        hb
      rw [hswap r]; exact hR r

end ChartHom

section ProductCover

variable (R : Type u) [CommRing R] (n p : ℕ)

local notation "N" => bigN n p
local notation "𝒜ˣ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜ʸ" => MvPolynomial.homogeneousSubmodule (Fin (p + 1)) R
local notation "𝒜ᶻ" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

def prodCover :
    (pullback (ProjSpace.π R n) (ProjSpace.π R p)).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (ProjSpace.affineOpenCover R n).openCover (ProjSpace.affineOpenCover R p).openCover _ _

def chartIso (i : Fin (n + 1)) (j : Fin (p + 1)) :
    (prodCover R n p).X (i, j)
      ≅ Spec (.of <| (Away 𝒜ˣ (X i)) ⊗[R] (Away 𝒜ʸ (X j))) :=
  pullback.congrHom (ProjSpace.awayι_comp_π R n i) (ProjSpace.awayι_comp_π R p j)
    ≪≫ pullbackSpecIso R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))

def chartMap (i : Fin (n + 1)) (j : Fin (p + 1)) :
    (prodCover R n p).X (i, j) ⟶ Proj 𝒜ᶻ :=
  (chartIso R n p i j).hom
    ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))
    ≫ Proj.awayι 𝒜ᶻ (MvPolynomial.X (idx n p (i, j)))
        (ProjSpace.X_mem_one R N (idx n p (i, j))) one_pos

theorem chartMap_over (ij : Fin (n + 1) × Fin (p + 1)) :
    chartMap R n p ij.1 ij.2 ≫ ProjSpace.π R N
      = (prodCover R n p).f ij
          ≫ pullback.fst _ _ ≫ ProjSpace.π R n := by
  obtain ⟨i, j⟩ := ij
  change Fin (n + 1) at i; change Fin (p + 1) at j

  show chartMap R n p i j ≫ ProjSpace.π R N
    = (prodCover R n p).f (i, j) ≫ pullback.fst _ _ ≫ ProjSpace.π R n

  rw [chartMap, Category.assoc, Category.assoc, ProjSpace.awayι_comp_π,
    chartIso, Iso.trans_hom, Category.assoc]
  conv_rhs =>
    dsimp only [prodCover, Scheme.Pullback.openCoverOfLeftRight_f]
    rw [← Category.assoc]
    erw [pullback.lift_fst]
    erw [Category.assoc]

    enter [2]
    rw [show (ProjSpace.affineOpenCover R n).openCover.f i ≫ ProjSpace.π R n
        = Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i))))
      from ProjSpace.awayι_comp_π R n i]

  have hcong : (pullback.fst _ _
          : pullback ((ProjSpace.affineOpenCover R n).openCover.f i ≫ ProjSpace.π R n)
              ((ProjSpace.affineOpenCover R p).openCover.f j ≫ ProjSpace.π R p) ⟶ _)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i))))
      = (pullback.congrHom (ProjSpace.awayι_comp_π R n i)
          (ProjSpace.awayι_comp_π R p j)).hom
        ≫ pullback.fst _ _
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i)))) := by
    rw [pullback.congrHom_hom, ← Category.assoc, pullback.lift_fst, Category.comp_id]; rfl
  erw [hcong]

  suffices h : (pullbackSpecIso R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))).hom
        ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))
        ≫ Spec.map (CommRingCat.ofHom
            (algebraMap R (Away 𝒜ᶻ (X (idx n p (i, j))))))
      = pullback.fst _ _
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜ˣ (X i)))) by rw [h]; rfl
  erw [← pullbackSpecIso_hom_fst_assoc R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  show segreChart R n p i j (algebraMap R _ r)
    = Algebra.TensorProduct.includeLeftRingHom (algebraMap R (Away 𝒜ˣ (X i)) r)
  rw [segreChart_algebraMap, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.algebraMap_eq_smul_one (R := R) (A := Away 𝒜ʸ (X j)),
    Algebra.algebraMap_eq_smul_one (R := R) (A := Away 𝒜ˣ (X i))]
  exact (TensorProduct.smul_tmul r (1 : Away 𝒜ˣ (X i)) (1 : Away 𝒜ʸ (X j))).symm

@[reassoc]
theorem prodCover_fst (ij : Fin (n + 1) × Fin (p + 1)) :
    (prodCover R n p).f ij ≫ pullback.fst _ _
      = (pullback.fst _ _ : (prodCover R n p).X ij ⟶ _)
        ≫ Proj.awayι 𝒜ˣ (X ij.1) (ProjSpace.X_mem_one R n ij.1) one_pos := by
  dsimp only [prodCover, Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_fst]; rfl

@[reassoc]
theorem prodCover_snd (ij : Fin (n + 1) × Fin (p + 1)) :
    (prodCover R n p).f ij ≫ pullback.snd _ _
      = (pullback.snd _ _ : (prodCover R n p).X ij ⟶ _)
        ≫ Proj.awayι 𝒜ʸ (X ij.2) (ProjSpace.X_mem_one R p ij.2) one_pos := by
  dsimp only [prodCover, Scheme.Pullback.openCoverOfLeftRight_f]
  erw [pullback.lift_snd]; rfl

@[reassoc]
theorem chartIso_incL (i : Fin (n + 1)) (j : Fin (p + 1)) :
    (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))))
      = pullback.fst _ _ := by
  rw [chartIso, Iso.trans_hom, Category.assoc]
  erw [pullbackSpecIso_hom_fst R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))]
  rw [pullback.congrHom_hom]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem chartIso_incR (i : Fin (n + 1)) (j : Fin (p + 1)) :
    (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
            (R := R) (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))).toRingHom)
      = pullback.snd _ _ := by
  rw [chartIso, Iso.trans_hom, Category.assoc]
  erw [pullbackSpecIso_hom_snd R (Away 𝒜ˣ (X i)) (Away 𝒜ʸ (X j))]
  rw [pullback.congrHom_hom]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem isLocElem_ratio (i k : Fin (n + 1)) :
    HomogeneousLocalization.Away.isLocalizationElem
        (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n k)
      = ProjSpace.ratio R n i k := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, ProjSpace.ratio, pow_one]

theorem range_SpecMap_awayMap (i k : Fin (n + 1)) :
    Set.range (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k)))).base
      = (PrimeSpectrum.basicOpen (ProjSpace.ratio R n i k)
          : Set (PrimeSpectrum (Away 𝒜ˣ (X i)))) := by
  letI := (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k)
    (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k)).toAlgebra
  letI := HomogeneousLocalization.Away.isLocalization_mul
    (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n k) rfl one_ne_zero
  rw [← isLocElem_ratio R n i k]
  exact PrimeSpectrum.localization_away_comap_range _ _

theorem opensRange_prodCover_f (α : Fin (n + 1) × Fin (p + 1)) :
    ((prodCover R n p).f α).opensRange
      = pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)
          ⁻¹ᵁ (Proj.awayι 𝒜ˣ (X α.1) (ProjSpace.X_mem_one R n α.1) one_pos).opensRange
        ⊓ pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)
          ⁻¹ᵁ (Proj.awayι 𝒜ʸ (X α.2) (ProjSpace.X_mem_one R p α.2) one_pos).opensRange := by
  have key : Set.range ((prodCover R n p).f α).base
      = (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)).base ⁻¹' Set.range
          ((ProjSpace.affineOpenCover R n).openCover.f α.1).base
        ∩ (pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)).base ⁻¹' Set.range
          ((ProjSpace.affineOpenCover R p).openCover.f α.2).base := by
    dsimp only [prodCover, Scheme.Pullback.openCoverOfLeftRight_f]
    exact Scheme.Pullback.range_map _ _ (ProjSpace.π R n) (ProjSpace.π R p)
      ((ProjSpace.affineOpenCover R n).openCover.f α.1)
      ((ProjSpace.affineOpenCover R p).openCover.f α.2) (𝟙 _)
      (Category.comp_id _) (Category.comp_id _)
  exact TopologicalSpace.Opens.ext key

theorem awayMap_ratio_transition (i k a : Fin (n + 1)) :
    (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n i)
        (mul_comm (X i) (X k) : (X i * X k : MvPolynomial (Fin (n+1)) R) = X k * X i))
      (ProjSpace.ratio R n k a)
    * (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k))
      (ProjSpace.ratio R n i k)
    = (HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n+1)) R) = X i * X k))
      (ProjSpace.ratio R n i a) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, ProjSpace.ratio,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    pow_one, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

theorem overlap_fst_condition (ij kl : Fin (n + 1) × Fin (p + 1)) :
    (pullback.fst ((prodCover R n p).f ij)
          ((prodCover R n p).f kl)
        ≫ (chartIso R n p ij.1 ij.2).hom
        ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
      ≫ Proj.awayι 𝒜ˣ (X ij.1) (ProjSpace.X_mem_one R n ij.1) one_pos
    = (pullback.snd _ _
        ≫ (chartIso R n p kl.1 kl.2).hom
        ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
      ≫ Proj.awayι 𝒜ˣ (X kl.1) (ProjSpace.X_mem_one R n kl.1) one_pos := by
  simp only [Category.assoc]
  erw [chartIso_incL_assoc R n p ij.1 ij.2,
    chartIso_incL_assoc R n p kl.1 kl.2]
  erw [← prodCover_fst R n p ij, ← prodCover_fst R n p kl]
  rw [← Category.assoc, pullback.condition, Category.assoc]; rfl

theorem overlap_snd_condition (ij kl : Fin (n + 1) × Fin (p + 1)) :
    (pullback.fst ((prodCover R n p).f ij)
          ((prodCover R n p).f kl)
        ≫ (chartIso R n p ij.1 ij.2).hom
        ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
      ≫ Proj.awayι 𝒜ʸ (X ij.2) (ProjSpace.X_mem_one R p ij.2) one_pos
    = (pullback.snd _ _
        ≫ (chartIso R n p kl.1 kl.2).hom
        ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
      ≫ Proj.awayι 𝒜ʸ (X kl.2) (ProjSpace.X_mem_one R p kl.2) one_pos := by
  simp only [Category.assoc]
  erw [chartIso_incR_assoc R n p ij.1 ij.2,
    chartIso_incR_assoc R n p kl.1 kl.2]
  erw [← prodCover_snd R n p ij, ← prodCover_snd R n p kl]
  rw [← Category.assoc, pullback.condition, Category.assoc]; rfl

/-- Tensor coordinate multiplication, separated from the scheme gluing
proof. This is the actual product in the given tensor-product algebra. -/
theorem chart_tmul_factors {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] (φ : A ⊗[R] B →+* C) (a : A) (b : B) :
    φ (a ⊗ₜ[R] b) = φ (a ⊗ₜ[R] (1 : B)) * φ ((1 : A) ⊗ₜ[R] b) := by
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The two actual transition maps agree on the SAME base-ring coefficient. -/
theorem awayMap_algebraMap_eq (i k : Fin (n + 1)) (r : R) :
    HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n i)
        (mul_comm (X i) (X k)) (algebraMap R (Away 𝒜ˣ (X k)) r)
      = HomogeneousLocalization.awayMap 𝒜ˣ (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n + 1)) R) = X i * X k)
        (algebraMap R (Away 𝒜ˣ (X i)) r) := by
  show HomogeneousLocalization.awayMap 𝒜ˣ _ _
      (HomogeneousLocalization.fromZeroRingHom _ _ (ProjSpace.grad0Equiv R n r)) = _
  rw [HomogeneousLocalization.awayMap_fromZeroRingHom,
    ← HomogeneousLocalization.awayMap_fromZeroRingHom _
      (ProjSpace.X_mem_one R n k) rfl]
  rfl

/-- The actual Segre coordinate transition, over an arbitrary commutative
target ring. The five compatibility equations are proved by the scheme
pullback construction when this lemma is used; none is a new final Fact. -/
theorem segreChart_transition {C : Type u} [CommRing C]
    (i k : Fin (n + 1)) (j l : Fin (p + 1))
    (sx : Away 𝒜ˣ (X i * X k) →+* C)
    (sy : Away 𝒜ʸ (X j * X l) →+* C)
    (sz : Away 𝒜ᶻ (X (idx n p (i, j)) * X (idx n p (k, l))) →+* C)
    (τ : Tij R n p i j →+* C) (ρ : Tij R n p k l →+* C)
    (hx1 : ∀ a, sx (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n k) rfl a) = τ (a ⊗ₜ[R] 1))
    (hx2 : ∀ a, sx (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n i) (mul_comm _ _) a) = ρ (a ⊗ₜ[R] 1))
    (hy1 : ∀ b, sy (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p l) rfl b) = τ (1 ⊗ₜ[R] b))
    (hy2 : ∀ b, sy (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p j) (mul_comm _ _) b) = ρ (1 ⊗ₜ[R] b))
    (hz1 : ∀ z, sz (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl z)
      = τ (segreChart R n p i j z))
    (z : Away 𝒜ᶻ (X (idx n p (k, l)))) :
    sz (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (i, j))) (mul_comm _ _) z)
      = ρ (segreChart R n p k l z) := by
  have hX : ∀ a, ρ (ProjSpace.ratio R n k a ⊗ₜ[R] (1 : Away 𝒜ʸ (X l)))
      * τ (ProjSpace.ratio R n i k ⊗ₜ[R] (1 : Away 𝒜ʸ (X j)))
      = τ (ProjSpace.ratio R n i a ⊗ₜ[R] (1 : Away 𝒜ʸ (X j))) := fun a => by
    have h := congrArg sx (awayMap_ratio_transition R n i k a)
    rw [map_mul, hx2, hx1, hx1] at h
    exact h
  have hY : ∀ b, ρ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] ProjSpace.ratio R p l b)
      * τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j l)
      = τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] ProjSpace.ratio R p j b) := fun b => by
    have h := congrArg sy (awayMap_ratio_transition R p j l b)
    rw [map_mul, hy2, hy1, hy1] at h
    exact h
  have hprod : ∀ a b, ρ (ProjSpace.ratio R n k a ⊗ₜ[R] ProjSpace.ratio R p l b)
      * τ (ProjSpace.ratio R n i k ⊗ₜ[R] ProjSpace.ratio R p j l)
      = τ (ProjSpace.ratio R n i a ⊗ₜ[R] ProjSpace.ratio R p j b) := fun a b => by
    rw [chart_tmul_factors R ρ (ProjSpace.ratio R n k a) (ProjSpace.ratio R p l b),
      chart_tmul_factors R τ (ProjSpace.ratio R n i k) (ProjSpace.ratio R p j l),
      chart_tmul_factors R τ (ProjSpace.ratio R n i a) (ProjSpace.ratio R p j b),
      mul_mul_mul_comm, hX a, hY b]
  have hux := hX i
  rw [ProjSpace.ratio_self, ← Algebra.TensorProduct.one_def, map_one] at hux
  have huy := hY j
  rw [ProjSpace.ratio_self, ← Algebra.TensorProduct.one_def, map_one] at huy
  have hunit : IsUnit (τ (ProjSpace.ratio R n i k ⊗ₜ[R] ProjSpace.ratio R p j l)) := by
    rw [chart_tmul_factors R τ]
    exact (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hux)).mul
      (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans huy))
  have hz : z ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R N (idx n p (k, l)))) := by
    rw [ProjSpace.adjoin_range_ratio]
    exact Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | mul a b _ _ ha hb => simp only [map_mul, ha, hb]
  | algebraMap r =>
    calc
      sz (HomogeneousLocalization.awayMap 𝒜ᶻ
          (ProjSpace.X_mem_one R N (idx n p (i, j))) (mul_comm _ _)
          (algebraMap R (Away 𝒜ᶻ (X (idx n p (k, l)))) r))
          = sz (HomogeneousLocalization.awayMap 𝒜ᶻ
            (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl
            (algebraMap R (Away 𝒜ᶻ (X (idx n p (i, j)))) r)) :=
        congrArg sz (awayMap_algebraMap_eq R N (idx n p (i, j)) (idx n p (k, l)) r)
      _ = τ (segreChart R n p i j (algebraMap R _ r)) := hz1 _
      _ = τ ((1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] algebraMap R (Away 𝒜ʸ (X j)) r) :=
        congrArg τ (segreChart_algebraMap R n p i j r)
      _ = sy (HomogeneousLocalization.awayMap 𝒜ʸ (ProjSpace.X_mem_one R p l) rfl
          (algebraMap R (Away 𝒜ʸ (X j)) r)) := (hy1 _).symm
      _ = sy (HomogeneousLocalization.awayMap 𝒜ʸ (ProjSpace.X_mem_one R p j)
          (mul_comm _ _) (algebraMap R (Away 𝒜ʸ (X l)) r)) :=
        (congrArg sy (awayMap_algebraMap_eq R p j l r)).symm
      _ = ρ ((1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] algebraMap R (Away 𝒜ʸ (X l)) r) := hy2 _
      _ = ρ (segreChart R n p k l (algebraMap R _ r)) :=
        (congrArg ρ (segreChart_algebraMap R n p k l r)).symm
  | mem z hzm =>
    obtain ⟨β, rfl⟩ := hzm
    obtain ⟨⟨a, b⟩, rfl⟩ := (idx n p).surjective β
    have hT := congrArg sz (awayMap_ratio_transition R N
      (idx n p (i, j)) (idx n p (k, l)) (idx n p (a, b)))
    rw [map_mul, hz1, hz1, segreChart_ratio, segreChart_ratio] at hT
    rw [segreChart_ratio]
    exact hunit.mul_right_cancel (hT.trans (hprod a b).symm)

/-- A compatible pair of actual projective affine charts has an actual
map to their common homogeneous localization. -/
theorem exists_overlap_map {W : Scheme.{u}} (i k : Fin (n + 1))
    (qi : W ⟶ Spec (.of (Away 𝒜ˣ (X i))))
    (qk : W ⟶ Spec (.of (Away 𝒜ˣ (X k))))
    (h : qi ≫ Proj.awayι 𝒜ˣ (X i) (ProjSpace.X_mem_one R n i) one_pos =
      qk ≫ Proj.awayι 𝒜ˣ (X k) (ProjSpace.X_mem_one R n k) one_pos) :
    ∃ q : W ⟶ Spec (.of (Away 𝒜ˣ (X i * X k))),
      q ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n k) rfl)) = qi ∧
      q ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n i) (mul_comm _ _))) = qk := by
  let q := pullback.lift qi qk h ≫
    (Proj.pullbackAwayιIso 𝒜ˣ (ProjSpace.X_mem_one R n i) one_pos
      (ProjSpace.X_mem_one R n k) one_pos
      (rfl : (X i * X k : MvPolynomial (Fin (n + 1)) R) = X i * X k)).hom
  refine ⟨q, ?_, ?_⟩
  · rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left, pullback.lift_fst]
  · rw [show (mul_comm (X i) (X k) : (X i * X k : MvPolynomial (Fin (n + 1)) R) = X k * X i)
      = (rfl : (_ : MvPolynomial (Fin (n + 1)) R) = X i * X k).trans (mul_comm _ _) from rfl]
    rw [Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right, pullback.lift_snd]

/-- The actual ring map associated to an actual affine-target scheme map. -/
def schemeAdj {W : Scheme.{u}} {A : Type u} [CommRing A] (q : W ⟶ Spec (.of A)) :
    A →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ q.appTop).hom

/-- This actual ring-map construction reverses actual composition. -/
theorem schemeAdj_comp {W : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (q : W ⟶ Spec (.of B)) :
    schemeAdj (q ≫ Spec.map (CommRingCat.ofHom f)) = (schemeAdj q).comp f := by
  change ((Scheme.ΓSpecIso (.of A)).inv ≫
    (Spec.map (CommRingCat.ofHom f)).appTop ≫ q.appTop).hom = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The actual Segre map lands in the common target chart, because both
actual factor-chart denominators avoid the same prime. -/
theorem segre_map_range {W : Scheme.{u}}
    (i k : Fin (n + 1)) (j l : Fin (p + 1))
    (q : W ⟶ Spec (.of (Tij R n p i j)))
    (qx : W ⟶ Spec (.of (Away 𝒜ˣ (X i * X k))))
    (qy : W ⟶ Spec (.of (Away 𝒜ʸ (X j * X l))))
    (hx : qx ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n k) rfl)) =
      q ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (hy : qy ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p l) rfl)) =
      q ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)).toRingHom)) :
    Set.range (q ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))).base ⊆
      Set.range (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
        (ProjSpace.X_mem_one R N (idx n p (k, l)))
        (rfl : (X (idx n p (i, j)) * X (idx n p (k, l)) : MvPolynomial (Fin (N + 1)) R) = _)))).base := by
  rw [range_SpecMap_awayMap R N (idx n p (i, j)) (idx n p (k, l))]
  rintro _ ⟨w, rfl⟩
  show ProjSpace.ratio R N (idx n p (i, j)) (idx n p (k, l)) ∉
    ((q ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))).base w).asIdeal
  intro h
  have hψ : segreChart R n p i j (ProjSpace.ratio R N
      (idx n p (i, j)) (idx n p (k, l))) ∈ (q.base w).asIdeal := h
  rw [segreChart_ratio,
    show (ProjSpace.ratio R n i k ⊗ₜ[R] ProjSpace.ratio R p j l : Tij R n p i j)
      = (ProjSpace.ratio R n i k ⊗ₜ[R] 1) * (1 ⊗ₜ[R] ProjSpace.ratio R p j l) from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]] at hψ
  rcases (q.base w).isPrime.mem_or_mem hψ with hψ' | hψ'
  · have hnot : ProjSpace.ratio R n i k ∉
        ((q ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)).base w).asIdeal := by
      rw [← hx, Scheme.Hom.comp_apply]
      exact (range_SpecMap_awayMap R n i k).le ⟨_, rfl⟩
    exact hnot hψ'
  · have hnot : ProjSpace.ratio R p j l ∉
        ((q ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R)).toRingHom)).base w).asIdeal := by
      rw [← hy, Scheme.Hom.comp_apply]
      exact (range_SpecMap_awayMap R p j l).le ⟨_, rfl⟩
    exact hnot hψ'

/-- The actual common-chart lift has the second actual Segre projection.
The proof applies the already proved ring-coordinate transition to the
same scheme maps; no affine-test/Yoneda assumption is introduced. -/
theorem segre_lift_second {W : Scheme.{u}}
    (i k : Fin (n + 1)) (j l : Fin (p + 1))
    (qij : W ⟶ Spec (.of (Tij R n p i j)))
    (qkl : W ⟶ Spec (.of (Tij R n p k l)))
    (qx : W ⟶ Spec (.of (Away 𝒜ˣ (X i * X k))))
    (qy : W ⟶ Spec (.of (Away 𝒜ʸ (X j * X l))))
    (qz : W ⟶ Spec (.of (Away 𝒜ᶻ (X (idx n p (i, j)) * X (idx n p (k, l))))))
    (hx1 : qx ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n k) rfl)) = qij ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (hx2 : qx ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n i) (mul_comm _ _))) = qkl ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (hy1 : qy ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p l) rfl)) = qij ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
    (hy2 : qy ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ʸ
      (ProjSpace.X_mem_one R p j) (mul_comm _ _))) = qkl ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
    (hz1 : qz ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (k, l))) rfl)) = qij ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))) :
    qz ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (i, j))) (mul_comm _ _))) =
      qkl ≫ Spec.map (CommRingCat.ofHom (segreChart R n p k l)) := by
  refine ext_to_Spec ?_
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  change schemeAdj (qz ≫ Spec.map _) z = schemeAdj (qkl ≫ Spec.map _) z
  rw [schemeAdj_comp, schemeAdj_comp]
  refine segreChart_transition R n p i k j l (schemeAdj qx) (schemeAdj qy) (schemeAdj qz)
    (schemeAdj qij) (schemeAdj qkl) ?_ ?_ ?_ ?_ ?_ z
  · intro a
    simpa only [schemeAdj_comp, RingHom.comp_apply,
      Algebra.TensorProduct.includeLeftRingHom_apply] using
      RingHom.congr_fun (congrArg schemeAdj hx1) a
  · intro a
    simpa only [schemeAdj_comp, RingHom.comp_apply,
      Algebra.TensorProduct.includeLeftRingHom_apply] using
      RingHom.congr_fun (congrArg schemeAdj hx2) a
  · intro b
    have hb := RingHom.congr_fun (congrArg schemeAdj hy1) b
    simp only [schemeAdj_comp, RingHom.comp_apply] at hb
    exact hb.trans (congrArg (schemeAdj qij)
      (show (Algebra.TensorProduct.includeRight (R := R)
        (A := Away 𝒜ˣ (X i)) (B := Away 𝒜ʸ (X j))).toRingHom b =
        (1 : Away 𝒜ˣ (X i)) ⊗ₜ[R] b from rfl))
  · intro b
    have hb := RingHom.congr_fun (congrArg schemeAdj hy2) b
    simp only [schemeAdj_comp, RingHom.comp_apply] at hb
    exact hb.trans (congrArg (schemeAdj qkl)
      (show (Algebra.TensorProduct.includeRight (R := R)
        (A := Away 𝒜ˣ (X k)) (B := Away 𝒜ʸ (X l))).toRingHom b =
        (1 : Away 𝒜ˣ (X k)) ⊗ₜ[R] b from rfl))
  · intro a
    simpa only [schemeAdj_comp, RingHom.comp_apply] using RingHom.congr_fun (congrArg schemeAdj hz1) a

/-- Each actual transition between the homogeneous affine charts is an
open immersion. Proved once at the single-factor coordinate telescope. -/
theorem transition_isOpenImmersion (i k : Fin (n + 1)) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
      (ProjSpace.X_mem_one R n k)
      (rfl : (X i * X k : MvPolynomial (Fin (n + 1)) R) = X i * X k)))) := by
  rw [← Proj.pullbackAwayιIso_inv_fst 𝒜ˣ (ProjSpace.X_mem_one R n i) one_pos
    (ProjSpace.X_mem_one R n k) one_pos rfl]
  infer_instance

/-- The two transition projections have the SAME actual composite into
Proj. This is proved at the fixed single-factor chart, not in the large
Segre assembly. -/
theorem transition_comp_away (i k : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n k)
        (rfl : (X i * X k : MvPolynomial (Fin (n + 1)) R) = X i * X k)))
        ≫ Proj.awayι 𝒜ˣ (X i) (ProjSpace.X_mem_one R n i) one_pos =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ˣ
        (ProjSpace.X_mem_one R n i) (mul_comm _ _)))
        ≫ Proj.awayι 𝒜ˣ (X k) (ProjSpace.X_mem_one R n k) one_pos := by
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

/-- A genuine common factorization identifies the two given composites.
This categorical proof never unfolds scheme/Proj structure. -/
theorem comp_eq_of_common_factor {C : Type*} [Category C] {W D A B Z : C}
    (f : W ⟶ A) (g : W ⟶ B) (q : W ⟶ D) (s : D ⟶ A) (t : D ⟶ B)
    (i : A ⟶ Z) (j : B ⟶ Z) (hf : q ≫ s = f) (hg : q ≫ t = g)
    (hc : s ≫ i = t ≫ j) : f ≫ i = g ≫ j := by
  rw [← hf, ← hg, Category.assoc, Category.assoc, hc]

/-- Actual Segre chart compatibility for two compatible maps from an
arbitrary scheme W. The hypotheses are the ORIGINAL left/right chart
compatibilities, proved by pullback.condition in the cover consumer.
Keeping W and its two affine arrows as parameters avoids unfolding the
large product-cover pullback repeatedly in this proof. -/
theorem chart_maps_compat {W : Scheme.{u}}
    (i k : Fin (n + 1)) (j l : Fin (p + 1))
    (qij : W ⟶ Spec (.of (Tij R n p i j)))
    (qkl : W ⟶ Spec (.of (Tij R n p k l)))
    (hL : (qij ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
        ≫ Proj.awayι 𝒜ˣ (X i) (ProjSpace.X_mem_one R n i) one_pos
      = (qkl ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
        ≫ Proj.awayι 𝒜ˣ (X k) (ProjSpace.X_mem_one R n k) one_pos)
    (hR : (qij ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
        ≫ Proj.awayι 𝒜ʸ (X j) (ProjSpace.X_mem_one R p j) one_pos
      = (qkl ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
        ≫ Proj.awayι 𝒜ʸ (X l) (ProjSpace.X_mem_one R p l) one_pos) :
    (qij ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)))
        ≫ Proj.awayι 𝒜ᶻ (X (idx n p (i, j))) (ProjSpace.X_mem_one R N _) one_pos
      = (qkl ≫ Spec.map (CommRingCat.ofHom (segreChart R n p k l)))
        ≫ Proj.awayι 𝒜ᶻ (X (idx n p (k, l))) (ProjSpace.X_mem_one R N _) one_pos := by
  obtain ⟨qx, hx1, hx2⟩ := exists_overlap_map R n i k
    (qij ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (qkl ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)) hL
  obtain ⟨qy, hy1, hy2⟩ := exists_overlap_map R p j l
    (qij ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
    (qkl ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)).toRingHom)) hR
  let zmap := Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
    (ProjSpace.X_mem_one R N (idx n p (k, l)))
    (rfl : (X (idx n p (i, j)) * X (idx n p (k, l)) : MvPolynomial (Fin (N + 1)) R) = _)))
  haveI : IsOpenImmersion zmap := transition_isOpenImmersion R N
    (idx n p (i, j)) (idx n p (k, l))
  have hrange := segre_map_range R n p i k j l qij qx qy hx1 hy1
  let qz := IsOpenImmersion.lift zmap
    (qij ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))) hrange
  have hz1 : qz ≫ zmap = qij ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)) :=
    IsOpenImmersion.lift_fac _ _ hrange
  have hz2 := segre_lift_second R n p i k j l qij qkl qx qy qz hx1 hx2 hy1 hy2 hz1
  exact comp_eq_of_common_factor
    (qij ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)))
    (qkl ≫ Spec.map (CommRingCat.ofHom (segreChart R n p k l))) qz zmap
    (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜ᶻ
      (ProjSpace.X_mem_one R N (idx n p (i, j))) (mul_comm _ _))))
    (Proj.awayι 𝒜ᶻ (X (idx n p (i, j))) (ProjSpace.X_mem_one R N _) one_pos)
    (Proj.awayι 𝒜ᶻ (X (idx n p (k, l))) (ProjSpace.X_mem_one R N _) one_pos)
    hz1 hz2 (transition_comp_away R N (idx n p (i, j)) (idx n p (k, l)))

theorem chartMap_compat (ij kl : Fin (n + 1) × Fin (p + 1)) :
    pullback.fst ((prodCover R n p).f ij)
        ((prodCover R n p).f kl)
      ≫ chartMap R n p ij.1 ij.2
    = pullback.snd _ _ ≫ chartMap R n p kl.1 kl.2 := by
  obtain ⟨i, j⟩ := ij
  obtain ⟨k, l⟩ := kl
  change Fin (n + 1) at i
  change Fin (n + 1) at k
  change Fin (p + 1) at j
  change Fin (p + 1) at l
  have h := chart_maps_compat R n p i k j l
    (pullback.fst ((prodCover R n p).f (i, j)) ((prodCover R n p).f (k, l))
      ≫ (chartIso R n p i j).hom)
    (pullback.snd ((prodCover R n p).f (i, j)) ((prodCover R n p).f (k, l))
      ≫ (chartIso R n p k l).hom)
    (by convert overlap_fst_condition R n p (i, j) (k, l) using 1 <;>
        (try simp only [Category.assoc]) <;> rfl)
    (by convert overlap_snd_condition R n p (i, j) (k, l) using 1 <;>
        (try simp only [Category.assoc]) <;> rfl)
  convert h using 1 <;> (try simp only [chartMap, Category.assoc]) <;> rfl

def segre2 :
    pullback (ProjSpace.π R n) (ProjSpace.π R p) ⟶ Proj 𝒜ᶻ :=
  (prodCover R n p).glueMorphisms
    (fun ij => chartMap R n p ij.1 ij.2)
    (chartMap_compat R n p)

theorem segre2_over :
    segre2 R n p ≫ ProjSpace.π R N
      = pullback.fst _ _ ≫ ProjSpace.π R n := by
  refine (prodCover R n p).hom_ext _ _ (fun ij => ?_)
  rw [segre2, ← Category.assoc, Scheme.Cover.ι_glueMorphisms]
  exact chartMap_over R n p ij


/-- A typed commuting triangle transports inverse images without inferring
an unknown open set or elaborating a polymorphic congrArg in its consumer. -/
theorem comp_preimage_eq_of_comp_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (he : f ≫ g = h) (U : Z.Opens) :
    f ⁻¹ᵁ (g ⁻¹ᵁ U) = h ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, he]

/-- The inverse image of a basic homogeneous open under an actual affine
chart map, at an abstract source scheme. -/
theorem preimage_away_basic {W : Scheme.{u}} (k i : Fin (n + 1))
    (q : W ⟶ Spec (.of (Away 𝒜ˣ (X k)))) :
    (q ≫ Proj.awayι 𝒜ˣ (X k) (ProjSpace.X_mem_one R n k) one_pos)
        ⁻¹ᵁ Proj.basicOpen 𝒜ˣ (X i) =
      q ⁻¹ᵁ PrimeSpectrum.basicOpen (ProjSpace.ratio R n k i) := by
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜ˣ (ProjSpace.X_mem_one R n k) one_pos
      (ProjSpace.X_mem_one R n i) one_pos, isLocElem_ratio]

/-- Actual left chart pullback, isolated from the double-chart computation. -/
theorem prodCover_preimage_left_basicOpen (k : Fin (n + 1)) (l : Fin (p + 1))
    (i : Fin (n + 1)) :
    (prodCover R n p).f (k, l)
        ⁻¹ᵁ (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)
          ⁻¹ᵁ Proj.basicOpen 𝒜ˣ (X i))
      = ((chartIso R n p k l).hom
          ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
        ⁻¹ᵁ PrimeSpectrum.basicOpen (ProjSpace.ratio R n k i) := by
  let q : (prodCover R n p).X (k, l) ⟶ Spec (.of (Away 𝒜ˣ (X k))) :=
    (chartIso R n p k l).hom ≫
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
  have hq : q = (pullback.fst _ _ : (prodCover R n p).X (k, l) ⟶ _) :=
    chartIso_incL R n p k l
  have htriangle : (prodCover R n p).f (k, l) ≫
        pullback.fst (ProjSpace.π R n) (ProjSpace.π R p) =
      q ≫ Proj.awayι 𝒜ˣ (X k) (ProjSpace.X_mem_one R n k) one_pos :=
    (prodCover_fst R n p (k, l)).trans
      (congrArg (fun h : (prodCover R n p).X (k, l) ⟶ Spec (.of (Away 𝒜ˣ (X k))) =>
        h ≫ Proj.awayι 𝒜ˣ (X k) (ProjSpace.X_mem_one R n k) one_pos) hq).symm
  exact (comp_preimage_eq_of_comp_eq ((prodCover R n p).f (k, l))
      (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)) _ htriangle
      (Proj.basicOpen 𝒜ˣ (X i))).trans (preimage_away_basic R n k i q)

/-- Actual right chart pullback, isolated from the double-chart computation. -/
theorem prodCover_preimage_right_basicOpen (k : Fin (n + 1)) (l : Fin (p + 1))
    (j : Fin (p + 1)) :
    (prodCover R n p).f (k, l)
        ⁻¹ᵁ (pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)
          ⁻¹ᵁ Proj.basicOpen 𝒜ʸ (X j))
      = ((chartIso R n p k l).hom
          ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight (R := R)).toRingHom))
        ⁻¹ᵁ PrimeSpectrum.basicOpen (ProjSpace.ratio R p l j) := by
  let q : (prodCover R n p).X (k, l) ⟶ Spec (.of (Away 𝒜ʸ (X l))) :=
    (chartIso R n p k l).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R)).toRingHom)
  have hq : q = (pullback.snd _ _ : (prodCover R n p).X (k, l) ⟶ _) :=
    chartIso_incR R n p k l
  have htriangle : (prodCover R n p).f (k, l) ≫
        pullback.snd (ProjSpace.π R n) (ProjSpace.π R p) =
      q ≫ Proj.awayι 𝒜ʸ (X l) (ProjSpace.X_mem_one R p l) one_pos :=
    (prodCover_snd R n p (k, l)).trans
      (congrArg (fun h : (prodCover R n p).X (k, l) ⟶ Spec (.of (Away 𝒜ʸ (X l))) =>
        h ≫ Proj.awayι 𝒜ʸ (X l) (ProjSpace.X_mem_one R p l) one_pos) hq).symm
  exact (comp_preimage_eq_of_comp_eq ((prodCover R n p).f (k, l))
      (pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)) _ htriangle
      (Proj.basicOpen 𝒜ʸ (X j))).trans (preimage_away_basic R p l j q)

/-- The actual Segre inverse image on ONE product chart, at default limits. -/
theorem segre2_preimage_chart (i : Fin (n + 1)) (j : Fin (p + 1))
    (k : Fin (n + 1)) (l : Fin (p + 1)) :
    (prodCover R n p).f (k, l)
        ⁻¹ᵁ (segre2 R n p ⁻¹ᵁ Proj.basicOpen 𝒜ᶻ (X (idx n p (i, j))))
      = (prodCover R n p).f (k, l)
        ⁻¹ᵁ (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)
            ⁻¹ᵁ Proj.basicOpen 𝒜ˣ (X i)
          ⊓ pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)
            ⁻¹ᵁ Proj.basicOpen 𝒜ʸ (X j)) := by
  rw [segre2,
    ← Scheme.Hom.comp_preimage ((prodCover R n p).f (k, l))
      ((prodCover R n p).glueMorphisms _ _),
    (prodCover R n p).ι_glueMorphisms _ _ (k, l)]
  change chartMap R n p k l ⁻¹ᵁ _ = _
  rw [chartMap, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜ᶻ (ProjSpace.X_mem_one R N _) one_pos
      (ProjSpace.X_mem_one R N (idx n p (i, j))) one_pos, isLocElem_ratio]
  rw [show (prodCover R n p).f (k, l) ⁻¹ᵁ (_ ⊓ _)
      = (prodCover R n p).f (k, l) ⁻¹ᵁ _
        ⊓ (prodCover R n p).f (k, l) ⁻¹ᵁ _ from rfl,
    prodCover_preimage_left_basicOpen R n p k l i,
    prodCover_preimage_right_basicOpen R n p k l j,
    Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  rw [show (_ ⁻¹ᵁ _ ⊓ _ ⁻¹ᵁ _ : ((prodCover R n p).X (k, l)).Opens)
      = (chartIso R n p k l).hom ⁻¹ᵁ (_ ⊓ _) from rfl]
  congr 1
  erw [← PrimeSpectrum.basicOpen_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul, ← segreChart_ratio R n p k l i j]
  rfl

theorem segre2_preimage (i : Fin (n + 1)) (j : Fin (p + 1)) :
    segre2 R n p
        ⁻¹ᵁ (Proj.awayι 𝒜ᶻ (X (idx n p (i, j)))
          (ProjSpace.X_mem_one R N _) one_pos).opensRange
      = ((prodCover R n p).f (i, j)).opensRange := by

  rw [Proj.opensRange_awayι, opensRange_prodCover_f,
    Proj.opensRange_awayι, Proj.opensRange_awayι]

  have hchart : ∀ (k : Fin (n + 1)) (l : Fin (p + 1)),
      (prodCover R n p).f (k, l)
        ⁻¹ᵁ (segre2 R n p
          ⁻¹ᵁ Proj.basicOpen 𝒜ᶻ (X (idx n p (i, j))))
      = (prodCover R n p).f (k, l)
        ⁻¹ᵁ (pullback.fst (ProjSpace.π R n) (ProjSpace.π R p)
            ⁻¹ᵁ Proj.basicOpen 𝒜ˣ (X i)
          ⊓ pullback.snd (ProjSpace.π R n) (ProjSpace.π R p)
            ⁻¹ᵁ Proj.basicOpen 𝒜ʸ (X j)) :=
    fun k l => segre2_preimage_chart R n p i j k l

  have hcov := (prodCover R n p).iSup_opensRange
  refine le_antisymm (fun q hq => ?_) (fun q hq => ?_)
  all_goals
    obtain ⟨⟨k, l⟩, q', rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show q ∈ ⨆ α, ((prodCover R n p).f α).opensRange from hcov.ge trivial)
  · exact (hchart k l).le hq
  · exact (hchart k l).ge hq


theorem segre2_closedImm :
    IsClosedImmersion (segre2 R n p) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (𝒰 := (ProjSpace.affineOpenCover R N).openCover) (fun β => ?_)
  dsimp only [Scheme.Cover.pullbackHom]

  obtain ⟨⟨i, j⟩, hβ⟩ := (idx n p).surjective β
  subst hβ

  have hrange : Set.range ((prodCover R n p).f (i, j)).base
      = Set.range (pullback.fst (segre2 R n p)
        ((ProjSpace.affineOpenCover R N).openCover.f (idx n p (i, j)))).base := by
    have := segre2_preimage R n p i j
    rw [← Scheme.Hom.opensRange_pullbackFst] at this
    exact congrArg SetLike.coe this.symm

  let e := IsOpenImmersion.isoOfRangeEq ((prodCover R n p).f (i, j))
    (pullback.fst _ _) hrange
  have hθcond : (prodCover R n p).f (i, j) ≫ segre2 R n p
      = ((chartIso R n p i j).hom
          ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)))
        ≫ (ProjSpace.affineOpenCover R N).openCover.f (idx n p (i, j)) := by
    rw [segre2, (prodCover R n p).ι_glueMorphisms _ _ (i, j),
      Category.assoc, ProjSpace.affineOpenCover_f]
    rfl
  let θ := pullback.lift ((prodCover R n p).f (i, j))
    ((chartIso R n p i j).hom
      ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j))) hθcond
  have hsnd : e.hom ≫ pullback.snd (segre2 R n p)
        ((ProjSpace.affineOpenCover R N).openCover.f (idx n p (i, j)))
      = (chartIso R n p i j).hom
        ≫ Spec.map (CommRingCat.ofHom (segreChart R n p i j)) := by
    rw [show e.hom = θ from (cancel_mono (pullback.fst _ _)).mp
      ((IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).trans (pullback.lift_fst _ _ _).symm)]
    exact pullback.lift_snd _ _ _

  have hci : IsClosedImmersion (e.hom ≫ pullback.snd (segre2 R n p)
      ((ProjSpace.affineOpenCover R N).openCover.f (idx n p (i, j)))) := by
    rw [hsnd]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
      (chartIso R n p i j).hom _).mpr
      (IsClosedImmersion.spec_of_surjective _ (segreChart_surjective R n p i j))
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e.hom _).mp hci

end ProductCover

section Recursive

variable (R : Type u) [CommRing R]

structure SegreDatum {m : ℕ} (e : Fin m → ℕ) where

  Nd : ℕ

  segσ : ProjSpace.prodOver R e
    ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Nd + 1)) R)

  hσ_closed : IsClosedImmersion segσ

  hσ_over : segσ ≫ ProjSpace.π R Nd = ProjSpace.prodOverπ R e

attribute [scoped instance] SegreDatum.hσ_closed

def eval0 : MvPolynomial (Fin (0 + 1)) R →+* Γ(Spec (.of R), ⊤) :=
  (Scheme.ΓSpecIso (.of R)).inv.hom.comp
    ((MvPolynomial.aeval (R := R) (fun _ => (1 : R))).toRingHom)

theorem eval0_irrelevant :
    (HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin (0 + 1)) R)).toIdeal.map (eval0 R) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hX0 : eval0 R (X 0) = 1 := by
    unfold eval0
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X]
    exact map_one _
  rw [← hX0]
  refine Ideal.mem_map_of_mem _ ?_
  exact (HomogeneousIdeal.mem_irrelevant_iff _ _).mpr
    (DirectSum.decompose_of_mem_ne _ (ProjSpace.X_mem_one R 0 0) one_ne_zero)

theorem eval0_grad0 :
    ((eval0 R).comp
        (algebraMap ((homogeneousSubmodule (Fin (0 + 1)) R) 0)
          (MvPolynomial (Fin (0 + 1)) R))).comp
      (ProjSpace.grad0Equiv R 0).toRingHom
      = (Scheme.ΓSpecIso (.of R)).inv.hom := by
  ext r
  show (eval0 R) (algebraMap _ _ ((ProjSpace.grad0Equiv R 0) r)) = _
  have hval : (algebraMap ((homogeneousSubmodule (Fin (0 + 1)) R) 0)
      (MvPolynomial (Fin (0 + 1)) R)) ((ProjSpace.grad0Equiv R 0) r) = MvPolynomial.C r := rfl
  rw [hval, eval0, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, MvPolynomial.aeval_C]
  rfl

theorem segreAux0_section :
    Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (0 + 1)) R)
        (eval0 R) (eval0_irrelevant R)
      ≫ ProjSpace.π R 0 = 𝟙 (Spec (.of R)) := by
  rw [ProjSpace.π, ← Category.assoc, Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    eval0_grad0, CommRingCat.ofHom_hom]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv (.of R)

def segreAux0 : SegreDatum R (Fin.elim0 : Fin 0 → ℕ) where
  Nd := 0
  segσ := Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (0 + 1)) R)
    (eval0 R) (eval0_irrelevant R)
  hσ_closed := by

    haveI hsep : IsSeparated (ProjSpace.π R 0) :=
      (ProjSpace.isProper_π R 0).toIsSeparated
    haveI hcomp : IsClosedImmersion (Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (0 + 1)) R)
        (eval0 R) (eval0_irrelevant R)
        ≫ ProjSpace.π R 0) := by
      rw [segreAux0_section R]; infer_instance
    exact @IsClosedImmersion.of_comp _ _ _ _ (ProjSpace.π R 0) hcomp hsep
  hσ_over := by
    show _ = 𝟙 (Spec (.of R))
    exact segreAux0_section R

def segreAuxSucc {m : ℕ} (e : Fin (m + 1) → ℕ)
    (ih : SegreDatum R (e ∘ Fin.succ)) : SegreDatum R e where
  Nd := bigN (e 0) ih.Nd
  segσ :=

    pullback.map _ _ _ _ (𝟙 _) ih.segσ (𝟙 _) (by simp) (by simp [ih.hσ_over])

    ≫ segre2 R (e 0) ih.Nd
  hσ_closed := by
    haveI : IsClosedImmersion (pullback.map (ProjSpace.π R (e 0))
        (ProjSpace.prodOverπ R (e ∘ Fin.succ)) (ProjSpace.π R (e 0))
        (ProjSpace.π R ih.Nd) (𝟙 _) ih.segσ (𝟙 _) (by simp)
        (by simp [ih.hσ_over])) := by

      refine MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsClosedImmersion)
        (f := pullback.snd (ProjSpace.π R (e 0)) (ProjSpace.π R ih.Nd))
        (f' := pullback.snd _ _) ?_ ih.hσ_closed

      refine (IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback (ProjSpace.π R (e 0)) (ProjSpace.π R ih.Nd))).flip
      rw [pullback.lift_fst, Category.comp_id, ih.hσ_over]
      exact IsPullback.of_hasPullback _ _
    exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ this
      (segre2_closedImm R (e 0) ih.Nd)
  hσ_over := by
    rw [Category.assoc, segre2_over]
    show pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ _
      = pullback.fst _ _ ≫ ProjSpace.π R (e 0)
    rw [← Category.assoc, pullback.lift_fst, Category.comp_id]

def segreAux : ∀ {m : ℕ} (e : Fin m → ℕ), SegreDatum R e
  | 0, e => (funext (fun k => k.elim0) : e = Fin.elim0) ▸ segreAux0 R
  | m + 1, e => segreAuxSucc R e (segreAux (e ∘ Fin.succ))

end Recursive

end ProjSpace.Segre
w03_reactivate "P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry.ProjSpace.Segre"
w03_reactivate "P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry.ProjSpace"

section Converter

open ProjSpace.Segre
r2nos_open_dual "ProjSpace.Segre"

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

namespace ChowDatum
r2nos_namespace_dual
w03_export "AlgebraicGeometry.ChowDatum" "hU_dense hι_closed hp_isoU p m U hp_proper hover V' e ι"
end ChowDatum
namespace ChowDatum
r2nos_namespace_dual
r2nos_open_scoped "AlgebraicGeometry.ChowDatum" in

private def _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ChowDatum.toChowDatumProj (D : ChowDatum π) : ChowDatumProj π where
  Nd := (segreAux R D.e).Nd
  V' := D.V'
  p := D.p
  ιN := D.ι ≫ (segreAux R D.e).segσ
  hp_proper := D.hp_proper
  hιN_closed := by
    haveI := D.hι_closed
    haveI := (segreAux R D.e).hσ_closed
    exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ inferInstance inferInstance
  hoverN := by
    rw [Category.assoc, (segreAux R D.e).hσ_over, D.hover]
  U := D.U
  hU_dense := D.hU_dense
  hp_isoU := D.hp_isoU

end ChowDatum
w03_export "AlgebraicGeometry" "ChowDatum.toChowDatumProj"
r2nos_open_scoped "AlgebraicGeometry.ChowDatum" in

theorem ChowDatum.nonempty_chowDatumProj_of :
    Nonempty (ChowDatum π) → Nonempty (ChowDatumProj π) :=
  fun ⟨D⟩ => ⟨D.toChowDatumProj π⟩

end Converter
w03_reactivate "P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry.ProjSpace.Segre"

end AlgebraicGeometry
w03_reactivate "P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry.ProjSpace.Segre P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry"

theorem solution {R : Type u} [CommRing R] {V : AlgebraicGeometry.Scheme.{u}}
    (π : V ⟶ AlgebraicGeometry.Spec (.of R)) :
    Nonempty (AlgebraicGeometry.ChowDatum π) → Nonempty (AlgebraicGeometry.ChowDatumProj π) :=
  AlgebraicGeometry.ChowDatum.nonempty_chowDatumProj_of π

end
w03_reactivate "P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry.ProjSpace P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry.ProjSpace.Segre P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.AlgebraicGeometry"
end S_AlgebraicGeometry_ChowDatumProj_nonempty_of
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
