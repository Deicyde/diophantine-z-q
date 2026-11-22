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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.lean
  Source sha256  : 4af4f5641ceb73d9afc1069b3d5485195593ea32d290765eff7f1eae23b5ef05
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option linter.unusedSectionVars false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T7×2; rule citations in the batch ledger.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom
r2nos_namespace_dual

set_option autoImplicit false

w03_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.AlgebraicGeometry CategoryTheory"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Surjective Spec Scheme IsSeparated OModulePresheaf.AffSES OModulePresheaf"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "AffHom AffSES AffHom.cochainMap AffHom.cochainMap_comp_d AffHom.HSuccMap_mk cochain d H0 HSucc mk d_comp_d"
namespace LES
r2nos_namespace_dual
w03_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
variable (K : V.OrderedAffineCover) {F₁ F₂ F₃ : OModulePresheaf π} (S : AffSES F₁ F₂ F₃)

local notation "ιC" => AffHom.cochainMap (π := π) K S.inc
local notation "πC" => AffHom.cochainMap (π := π) K S.proj

theorem mem_comap_range_iff {F : OModulePresheaf π} {i : ℕ} (x : LinearMap.ker (F.d K (i + 1))) :
    x ∈ (LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype
      ↔ ∃ c, F.d K i c = x.1 := by
  simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]

theorem d_d_apply (F : OModulePresheaf π) (i : ℕ) (c : F.cochain K i) : F.d K (i + 1) (F.d K i c) = 0 := by
  have h := LinearMap.congr_fun (F.d_comp_d K i) c
  rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h

theorem cochain_ses (i : ℕ) :
    Function.Injective (ιC i) ∧ Function.Surjective (πC i) ∧ LinearMap.range (ιC i) = LinearMap.ker (πC i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f g hfg
    exact funext fun s => S.injective (K.affineInter π s) (congrFun hfg s)
  · intro g
    choose lift hlift using fun s => S.surjective (K.affineInter π s) (g s)
    exact ⟨lift, funext hlift⟩
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨f, rfl⟩
      refine LinearMap.mem_ker.mpr (funext fun s => ?_)
      show S.proj.app (K.affineInter π s) (S.inc.app (K.affineInter π s) (f s)) = 0
      have hzero : S.inc.app (K.affineInter π s) (f s) ∈ LinearMap.ker (S.proj.app (K.affineInter π s)) :=
        (S.exact (K.affineInter π s)) ▸ LinearMap.mem_range_self _ (f s)
      exact hzero
    · intro g hg
      have hgs : ∀ s, g s ∈ LinearMap.range (S.inc.app (K.affineInter π s)) := fun s =>
        (S.exact (K.affineInter π s)).symm ▸ LinearMap.mem_ker.mpr (congrFun (LinearMap.mem_ker.mp hg) s)
      choose lift hlift using hgs
      exact ⟨lift, funext hlift⟩

theorem snake_data (i : ℕ) (z : LinearMap.ker (F₃.d K i)) :
    ∃ (k₀ : LinearMap.ker (F₁.d K (i + 1))) (f₀ : F₂.cochain K i),
      πC i f₀ = z.1 ∧ ιC (i + 1) k₀.1 = F₂.d K i f₀ ∧
        ∀ f, πC i f = z.1 → ∃ h, ιC (i + 1) k₀.1 = F₂.d K i f + ιC (i + 1) (F₁.d K i h) := by
  obtain ⟨f₀, hf₀⟩ := (cochain_ses K S i).2.1 z.1
  have hdF : F₂.d K i f₀ ∈ LinearMap.range (ιC (i + 1)) := by
    rw [(cochain_ses K S (i + 1)).2.2]
    refine LinearMap.mem_ker.mpr ?_
    rw [← LinearMap.comp_apply, AffHom.cochainMap_comp_d, LinearMap.comp_apply, hf₀]
    exact LinearMap.mem_ker.mp z.2
  obtain ⟨k₀, hk₀⟩ := hdF
  have hk₀c : k₀ ∈ LinearMap.ker (F₁.d K (i + 1)) := by
    refine LinearMap.mem_ker.mpr ((cochain_ses K S (i + 2)).1 ?_)
    rw [← LinearMap.comp_apply, AffHom.cochainMap_comp_d, LinearMap.comp_apply, hk₀, map_zero]
    exact d_d_apply K F₂ i f₀
  refine ⟨⟨k₀, hk₀c⟩, f₀, hf₀, hk₀, fun f hf => ?_⟩
  have hdiff : f₀ - f ∈ LinearMap.range (ιC i) := by
    rw [(cochain_ses K S i).2.2]
    exact LinearMap.mem_ker.mpr (by rw [map_sub, hf₀, hf, sub_self])
  obtain ⟨h, hh⟩ := hdiff
  refine ⟨h, ?_⟩
  rw [← LinearMap.comp_apply, AffHom.cochainMap_comp_d, LinearMap.comp_apply, hh, map_sub, hk₀]
  abel

noncomputable def delta0 (i : ℕ) : LinearMap.ker (F₃.d K i) →ₗ[R] F₁.HSucc K i := by
  classical
  choose k₀ f₀ hf₀ hk₀ hany using snake_data K S i
  refine
    { toFun := fun z => Submodule.Quotient.mk (k₀ z)
      map_add' := fun z₁ z₂ => (Submodule.Quotient.eq _).mpr ?_
      map_smul' := fun r z => (Submodule.Quotient.eq _).mpr ?_ }
  · obtain ⟨h, hh⟩ := hany (z₁ + z₂) (f₀ z₁ + f₀ z₂) (by rw [map_add, hf₀, hf₀]; rfl)
    refine (mem_comap_range_iff K _).mpr ⟨h, (cochain_ses K S (i + 1)).1 ?_⟩
    show ιC (i + 1) (F₁.d K i h) = ιC (i + 1) (k₀ (z₁ + z₂) - (k₀ z₁ + k₀ z₂)).1
    rw [show ((k₀ (z₁ + z₂) - (k₀ z₁ + k₀ z₂) : LinearMap.ker (F₁.d K (i + 1))).1 : _)
        = (k₀ (z₁ + z₂)).1 - ((k₀ z₁).1 + (k₀ z₂).1) from rfl,
      map_sub, map_add, hh, hk₀, hk₀, map_add]
    abel
  · obtain ⟨h, hh⟩ := hany (r • z) (r • f₀ z) (by rw [map_smul, hf₀]; rfl)
    refine (mem_comap_range_iff K _).mpr ⟨h, (cochain_ses K S (i + 1)).1 ?_⟩
    show ιC (i + 1) (F₁.d K i h) = ιC (i + 1) (k₀ (r • z) - r • k₀ z).1
    rw [show ((k₀ (r • z) - r • k₀ z : LinearMap.ker (F₁.d K (i + 1))).1 : _)
        = (k₀ (r • z)).1 - r • (k₀ z).1 from rfl,
      map_sub, map_smul, hh, hk₀, map_smul]
    abel

theorem delta0_spec (i : ℕ) (z : LinearMap.ker (F₃.d K i)) :
    ∃ (k₀ : LinearMap.ker (F₁.d K (i + 1))) (f₀ : F₂.cochain K i),
      delta0 K S i z = Submodule.Quotient.mk k₀ ∧ πC i f₀ = z.1 ∧ ιC (i + 1) k₀.1 = F₂.d K i f₀ ∧
        ∀ f, πC i f = z.1 → ∃ h, ιC (i + 1) k₀.1 = F₂.d K i f + ιC (i + 1) (F₁.d K i h) := by
  classical
  obtain ⟨f₀, hf₀, hk₀, hany⟩ := Classical.choose_spec (snake_data K S i z)
  exact ⟨_, f₀, rfl, hf₀, hk₀, hany⟩

theorem delta0_eq_zero_of_mem_range (j : ℕ) (z : LinearMap.ker (F₃.d K (j + 1)))
    (hz : ∃ w, F₃.d K j w = z.1) : delta0 K S (j + 1) z = 0 := by
  obtain ⟨w, hw⟩ := hz
  obtain ⟨w', hw'⟩ := (cochain_ses K S j).2.1 w
  have hπf : πC (j + 1) (F₂.d K j w') = z.1 := by
    rw [← LinearMap.comp_apply, AffHom.cochainMap_comp_d, LinearMap.comp_apply, hw', hw]
  obtain ⟨k₀, f₀, hδ, -, -, hany⟩ := delta0_spec K S (j + 1) z
  obtain ⟨h, hh⟩ := hany _ hπf
  rw [hδ]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ((mem_comap_range_iff K _).mpr ⟨h, (cochain_ses K S (j + 2)).1 ?_⟩)
  rw [hh, d_d_apply, zero_add]

noncomputable def delta (i : ℕ) : F₃.HSucc K i →ₗ[R] F₁.HSucc K (i + 1) :=
  Submodule.liftQ _ (delta0 K S (i + 1)) fun z hz =>
    delta0_eq_zero_of_mem_range K S i z ((mem_comap_range_iff K _).mp hz)

theorem ker_delta0_le_range (i : ℕ) :
    LinearMap.ker (delta0 K S i) ≤ LinearMap.range (S.proj.kerMap K i) := by
  intro z hz
  obtain ⟨k₀, f₀, hδ, hf₀, hk₀, -⟩ := delta0_spec K S i z
  rw [LinearMap.mem_ker, hδ] at hz
  obtain ⟨h', hh'⟩ := (mem_comap_range_iff K _).mp ((Submodule.Quotient.mk_eq_zero _).mp hz)
  have hdF : F₂.d K i (f₀ - ιC i h') = 0 := by
    have hchain := LinearMap.congr_fun (AffHom.cochainMap_comp_d K S.inc i) h'
    simp only [LinearMap.comp_apply] at hchain
    rw [map_sub, ← hchain, hh', hk₀, sub_self]
  refine ⟨⟨f₀ - ιC i h', LinearMap.mem_ker.mpr hdF⟩, Subtype.ext ?_⟩
  show πC i (f₀ - ιC i h') = z.1
  have hιker : πC i (ιC i h') = 0 := LinearMap.mem_ker.mp ((cochain_ses K S i).2.2 ▸ ⟨h', rfl⟩)
  rw [map_sub, hf₀, hιker, sub_zero]

theorem ker_delta_le_range (i : ℕ) :
    LinearMap.ker (delta K S i) ≤ LinearMap.range (S.proj.HSuccMap K i) := by
  intro z hz
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hw0 : delta0 K S (i + 1) w = 0 := by simpa [delta, Submodule.liftQ_apply] using hz
  obtain ⟨f', hf'⟩ := ker_delta0_le_range K S (i + 1) (LinearMap.mem_ker.mpr hw0)
  exact ⟨Submodule.Quotient.mk f', by rw [AffHom.HSuccMap_mk, hf']⟩

theorem ker_HSuccMap_zero_le_range_delta0 :
    LinearMap.ker (S.inc.HSuccMap K 0) ≤ LinearMap.range (delta0 K S 0) := by
  intro z hz
  obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hιk : ∃ f, F₂.d K 0 f = (S.inc.kerMap K 1 k).1 := by
    rw [LinearMap.mem_ker, AffHom.HSuccMap_mk] at hz
    exact (mem_comap_range_iff K _).mp ((Submodule.Quotient.mk_eq_zero _).mp hz)
  obtain ⟨f, hf⟩ := hιk
  have hz₀ : πC 0 f ∈ LinearMap.ker (F₃.d K 0) :=
    LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, ← AffHom.cochainMap_comp_d, LinearMap.comp_apply, hf]
      exact LinearMap.mem_ker.mp ((cochain_ses K S 1).2.2 ▸ ⟨k.1, rfl⟩)
  refine ⟨⟨πC 0 f, hz₀⟩, ?_⟩
  obtain ⟨k₀, f₀, hδ, -, hk₀, hany⟩ := delta0_spec K S 0 ⟨πC 0 f, hz₀⟩
  obtain ⟨h, hh⟩ := hany f rfl
  rw [hδ]
  refine (Submodule.Quotient.eq _).mpr ((mem_comap_range_iff K _).mpr ⟨h, (cochain_ses K S 1).1 ?_⟩)
  rw [show ((k₀ - k : LinearMap.ker (F₁.d K 1)).1 : _) = k₀.1 - k.1 from rfl, map_sub, hh,
    show ιC 1 k.1 = (S.inc.kerMap K 1 k).1 from rfl, ← hf]
  abel

theorem ker_HSuccMap_succ_le_range_delta (i : ℕ) :
    LinearMap.ker (S.inc.HSuccMap K (i + 1)) ≤ LinearMap.range (delta K S i) := by
  intro z hz
  obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hιk : ∃ f, F₂.d K (i + 1) f = (S.inc.kerMap K (i + 2) k).1 := by
    rw [LinearMap.mem_ker, AffHom.HSuccMap_mk] at hz
    exact (mem_comap_range_iff K _).mp ((Submodule.Quotient.mk_eq_zero _).mp hz)
  obtain ⟨f, hf⟩ := hιk
  have hz₀ : πC (i + 1) f ∈ LinearMap.ker (F₃.d K (i + 1)) :=
    LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, ← AffHom.cochainMap_comp_d, LinearMap.comp_apply, hf]
      exact LinearMap.mem_ker.mp ((cochain_ses K S (i + 2)).2.2 ▸ ⟨k.1, rfl⟩)
  refine ⟨Submodule.Quotient.mk ⟨πC (i + 1) f, hz₀⟩, ?_⟩
  rw [delta, Submodule.liftQ_apply]
  obtain ⟨k₀, f₀, hδ, -, hk₀, hany⟩ := delta0_spec K S (i + 1) ⟨πC (i + 1) f, hz₀⟩
  obtain ⟨h, hh⟩ := hany f rfl
  rw [hδ]
  refine (Submodule.Quotient.eq _).mpr ((mem_comap_range_iff K _).mpr ⟨h, (cochain_ses K S (i + 2)).1 ?_⟩)
  rw [show ((k₀ - k : LinearMap.ker (F₁.d K (i + 2))).1 : _) = k₀.1 - k.1 from rfl, map_sub, hh,
    show ιC (i + 2) k.1 = (S.inc.kerMap K (i + 2) k).1 from rfl, ← hf]
  abel

end AlgebraicGeometry.OModulePresheaf.LES

universe u
open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.AlgebraicGeometry.OModulePresheaf in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom.AlgebraicGeometry.OModulePresheaf" in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover) :
    ∃ (δ₀ : F₃.H0 K →ₗ[R] F₁.HSucc K 0) (δ : ∀ i : ℕ, F₃.HSucc K i →ₗ[R] F₁.HSucc K (i + 1)), LinearMap.ker δ₀ ≤ LinearMap.range (S.proj.H0Map K) ∧ (∀ i, LinearMap.ker (δ i) ≤ LinearMap.range (S.proj.HSuccMap K i)) ∧ LinearMap.ker (S.inc.HSuccMap K 0) ≤ LinearMap.range δ₀ ∧ (∀ i, LinearMap.ker (S.inc.HSuccMap K (i + 1)) ≤ LinearMap.range (δ i)) :=
  ⟨LES.delta0 K S 0, fun i => LES.delta K S i, LES.ker_delta0_le_range K S 0, fun i => LES.ker_delta_le_range K S i,
    LES.ker_HSuccMap_zero_le_range_delta0 K S, fun i => LES.ker_HSuccMap_succ_le_range_delta K S i⟩
end S_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
