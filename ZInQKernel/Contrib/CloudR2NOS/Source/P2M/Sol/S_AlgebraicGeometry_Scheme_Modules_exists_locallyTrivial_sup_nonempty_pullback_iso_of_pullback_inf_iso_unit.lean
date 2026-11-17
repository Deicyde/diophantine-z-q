/-
NEW EDITION CANDIDATE 002 (H5 lane4 , 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_locallyTrivial_sup_nonempty_pullback_iso_of_pullback_inf_iso_unit.lean
  Source sha256  : e6cc1ae0c23900d032444256420498ee3867aa7cde6911bfa8ab7ca859f39e9c
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 3200000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 10 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_locallyTrivial_sup_nonempty_pullback_iso_of_pullback_inf_iso_unit
r2nos_namespace_dual
r2nos_erase_attr "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom"
r2nos_erase_attr "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle
r2nos_open_dual "CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle"

noncomputable section

namespace GlueChart
r2nos_namespace_dual

variable {X : Scheme.{u}}

def Idx (W : X.Opens) (𝓛 : X.Modules) : Type u :=
  {U : X.Opens // U ≤ W ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)}

def T (W V : X.Opens) (𝓛 : X.Modules) : Idx W 𝓛 ⊕ PUnit.{u+1} → X.Opens := Sum.elim (fun a => a.1) (fun _ => W ⊓ V)

def T' (W V : X.Opens) (𝓛 : X.Modules) : Idx W 𝓛 ⊕ PUnit.{u+1} → X.Opens := Sum.elim (fun a => a.1) (fun _ => V)

variable {W V : X.Opens} {𝓛 : X.Modules}

theorem hle (a : Idx W 𝓛) (p : PUnit.{u+1}) :
    T' W V 𝓛 (.inl a) ⊓ T' W V 𝓛 (.inr p) ≤ T W V 𝓛 (.inl a) ⊓ T W V 𝓛 (.inr p) :=
  le_inf inf_le_left (le_inf (inf_le_left.trans a.2.1) inf_le_right)

theorem hle' (p : PUnit.{u+1}) (a : Idx W 𝓛) :
    T' W V 𝓛 (.inr p) ⊓ T' W V 𝓛 (.inl a) ≤ T W V 𝓛 (.inr p) ⊓ T W V 𝓛 (.inl a) :=
  le_inf (le_inf (inf_le_right.trans a.2.1) inf_le_left) inf_le_right

theorem T'_inf_le (k : Idx W 𝓛 ⊕ PUnit.{u+1}) : T' W V 𝓛 k ⊓ W ≤ T W V 𝓛 k := by
  rcases k with a | p
  · exact inf_le_left
  · exact le_inf inf_le_right inf_le_left

theorem T'_le_sup (k : Idx W 𝓛 ⊕ PUnit.{u+1}) : T' W V 𝓛 k ≤ W ⊔ V := by
  rcases k with a | p
  · exact a.2.1.trans le_sup_left
  · exact le_sup_right

def reU (c : UnitCocycle (T W V 𝓛)) : ∀ k l : Idx W 𝓛 ⊕ PUnit.{u+1}, Γ(X, T' W V 𝓛 k ⊓ T' W V 𝓛 l)
  | .inl a, .inl b => c.u (.inl a) (.inl b)
  | .inl a, .inr p => rO (hle a p) (c.u (.inl a) (.inr p))
  | .inr p, .inl b => rO (hle' p b) (c.u (.inr p) (.inl b))
  | .inr _, .inr _ => 1

theorem reU_ll (c : UnitCocycle (T W V 𝓛)) (a b : Idx W 𝓛) : reU (V := V) c (.inl a) (.inl b) = c.u (.inl a) (.inl b) := rfl
theorem reU_lr (c : UnitCocycle (T W V 𝓛)) (a : Idx W 𝓛) (p : PUnit.{u+1}) :
    reU c (.inl a) (.inr p) = rO (hle a p) (c.u (.inl a) (.inr p)) := rfl
theorem reU_rl (c : UnitCocycle (T W V 𝓛)) (p : PUnit.{u+1}) (b : Idx W 𝓛) :
    reU c (.inr p) (.inl b) = rO (hle' p b) (c.u (.inr p) (.inl b)) := rfl
theorem reU_rr (c : UnitCocycle (T W V 𝓛)) (p q : PUnit.{u+1}) : reU (W := W) (V := V) (𝓛 := 𝓛) c (.inr p) (.inr q) = 1 := rfl


def reseat (c : UnitCocycle (T W V 𝓛)) : UnitCocycle (T' W V 𝓛) where
  u := reU c
  refl k := by
    rcases k with a | p
    · exact c.refl (.inl a)
    · rfl
  cocycle i j k := by
    rcases i with a | p
    · rcases j with b | q
      · rcases k with d | r
        · rw [reU_ll, reU_ll, reU_ll]; exact c.cocycle (.inl a) (.inl b) (.inl d)
        · rw [reU_ll, reU_lr, reU_lr, rO_rO, rO_rO]; exact c.cocycle_le (.inl a) (.inl b) (.inr r) _ _ _
      · rcases k with d | r
        · rw [reU_lr, reU_rl, reU_ll, rO_rO, rO_rO]; exact c.cocycle_le (.inl a) (.inr q) (.inl d) _ _ _
        · simp only [reU_lr, reU_rr, rO_rO, map_one, mul_one]
    · rcases j with b | q
      · rcases k with d | r
        · rw [reU_rl, reU_ll, reU_rl, rO_rO, rO_rO]; exact c.cocycle_le (.inr p) (.inl b) (.inl d) _ _ _
        · rw [reU_rl, reU_lr, reU_rr, rO_rO, rO_rO, map_one]
          have h := c.cocycle_le (.inr p) (.inl b) (.inr r)
            (W := T' W V 𝓛 (.inr p) ⊓ T' W V 𝓛 (.inl b) ⊓ T' W V 𝓛 (.inr r))
            (le_inf (le_inf ((inf_le_left.trans inf_le_right).trans b.2.1) (inf_le_left.trans inf_le_left))
              (inf_le_left.trans inf_le_right))
            (le_inf (inf_le_left.trans inf_le_right)
              (le_inf ((inf_le_left.trans inf_le_right).trans b.2.1) inf_le_right))
            (le_inf (le_inf ((inf_le_left.trans inf_le_right).trans b.2.1) (inf_le_left.trans inf_le_left))
              (le_inf ((inf_le_left.trans inf_le_right).trans b.2.1) inf_le_right))
          rcases p; rcases r
          rw [c.refl, map_one] at h
          exact h
      · rcases k with d | r
        · simp only [reU_rr, reU_rl, rO_rO, map_one, one_mul]
        · simp only [reU_rr, map_one, mul_one]

theorem map_map {Y : Scheme.{u}} (M : Y.Modules) {A B C : Y.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (s : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op s) = M.presheaf.map (homOfLE (hCB.trans hBA)).op s := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

theorem map_smul' {Y : Scheme.{u}} (M : Y.Modules) {A B : Y.Opens} (h : B ≤ A) (g : Γ(Y, A)) (s : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op (g • s) = rO h g • M.presheaf.map (homOfLE h).op s :=
  M.val.map_smul (homOfLE h).op g s

theorem map_irrel {Y : Scheme.{u}} (M : Y.Modules) {A B : Y.Opens} (h h' : B ≤ A) (s : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op s = M.presheaf.map (homOfLE h').op s := rfl

theorem rO_app (W : X.Opens) {A B : X.Opens} (hBA : B ≤ A) (g : Γ(X, A)) :
    rO (X := (W : Scheme.{u})) (show W.ι ⁻¹ᵁ B ≤ W.ι ⁻¹ᵁ A from fun _ hx => hBA hx) ((W.ι.app A).hom g) =
      (W.ι.app B).hom (rO hBA g) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (W.ι.naturality (homOfLE hBA).op) g
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
  exact h.symm

theorem main (W V : X.Opens) (𝓛 : X.Modules)
    (hW : ∀ x ∈ W, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf))
    (hV : Nonempty ((Scheme.Modules.pullback (W ⊓ V).ι).obj 𝓛 ≅ SheafOfModules.unit (↑(W ⊓ V) : Scheme.{u}).ringCatSheaf)) :
    ∃ 𝓛' : X.Modules,
      (∀ x ∈ W ⊔ V, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ⊔ V ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛' ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)) ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj 𝓛' ≅ (Scheme.Modules.pullback W.ι).obj 𝓛) := by
  classical

  have hex : ∀ k : Idx W 𝓛 ⊕ PUnit.{u+1}, ∃ s : Γ(𝓛, T W V 𝓛 k), IsFrameOn s (T W V 𝓛 k) := by
    rintro (a | p)
    · exact exists_isFrameOn_of_pullback_iso_unit a.1 a.2.2.some
    · exact exists_isFrameOn_of_pullback_iso_unit (W ⊓ V) hV.some
  choose e he using hex
  obtain ⟨c, hc⟩ := exists_unitCocycle_map_eq_smul_of_isFrameOn e he
  let c' : UnitCocycle (T' W V 𝓛) := reseat c
  let 𝓛' : X.Modules := glueOfCocycle c'
  refine ⟨𝓛', ?_, ?_⟩
  ·
    intro x hx
    rcases (TopologicalSpace.Opens.mem_sup.mp hx) with hxW | hxV
    · obtain ⟨U, hxU, hUW, hU⟩ := hW x hxW
      let a : Idx W 𝓛 := ⟨U, hUW, hU⟩
      exact ⟨U, hxU, hUW.trans le_sup_left,
        (isFrameOn_glueFrame c' (.inl a)).nonempty_pullback_iso_unit U le_rfl le_rfl⟩
    · exact ⟨V, hxV, le_sup_right,
        (isFrameOn_glueFrame c' (.inr PUnit.unit)).nonempty_pullback_iso_unit V le_rfl le_rfl⟩
  ·
    let Y : Scheme.{u} := W
    let S : Idx W 𝓛 ⊕ PUnit.{u+1} → Y.Opens := fun k => W.ι ⁻¹ᵁ (T' W V 𝓛 k)
    have hS : ⨆ k, S k = ⊤ := by
      refine top_le_iff.mp fun w _ => ?_
      obtain ⟨U, hwU, hUW, hU⟩ := hW w.1 w.2
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨.inl ⟨U, hUW, hU⟩, hwU⟩
    let cc : UnitCocycle S := c'.comap W.ι
    let P : Y.Modules := (Scheme.Modules.pullback W.ι).obj 𝓛'
    let Q : Y.Modules := (Scheme.Modules.pullback W.ι).obj 𝓛

    let fP : ∀ k, Γ(P, S k) := fun k => pullbackLocalSection W.ι (glueFrame c' k)
    have hfP : ∀ k, IsFrameOn (fP k) (S k) := fun k => (isFrameOn_glueFrame c' k).pullbackLocalSection W.ι
    have htP : ∀ k l, P.presheaf.map (homOfLE (inf_le_right : S k ⊓ S l ≤ S l)).op (fP l) =
        cc.u k l • P.presheaf.map (homOfLE (inf_le_left : S k ⊓ S l ≤ S k)).op (fP k) := by
      intro k l
      have h0 := congrArg (pullbackLocalSection W.ι) (map_glueFrame_eq_smul c' k l)
      rw [pullbackLocalSection_smul, ← map_homOfLE_pullbackLocalSection, ← map_homOfLE_pullbackLocalSection] at h0
      exact h0

    have hST : ∀ k, S k ≤ W.ι ⁻¹ᵁ (T W V 𝓛 k) := by
      intro k w hw
      show W.ι.base w ∈ T W V 𝓛 k
      refine T'_inf_le k ⟨hw, ?_⟩
      rw [Scheme.Opens.ι_apply]; exact w.2
    let fQ : ∀ k, Γ(Q, S k) := fun k => Q.presheaf.map (homOfLE (hST k)).op (pullbackLocalSection W.ι (e k))
    have hfQ : ∀ k, IsFrameOn (fQ k) (S k) := fun k =>
      (((he k).pullbackLocalSection W.ι).map (homOfLE (hST k))).mono (hST k)

    have hcc : ∀ k l, cc.u k l = rO (le_inf (inf_le_left.trans (hST k)) (inf_le_right.trans (hST l)))
        ((W.ι.app (T W V 𝓛 k ⊓ T W V 𝓛 l)).hom (c.u k l)) := by
      intro k l
      show (W.ι.app (T' W V 𝓛 k ⊓ T' W V 𝓛 l)).hom (c'.u k l) = _
      rcases k with a | p <;> rcases l with b | q
      · exact (rO_refl _).symm
      · show (W.ι.app _).hom (rO (hle a q) (c.u (.inl a) (.inr q))) = _
        rw [← rO_app]; rfl
      · show (W.ι.app _).hom (rO (hle' p b) (c.u (.inr p) (.inl b))) = _
        rw [← rO_app]; rfl
      · rcases p; rcases q
        show (W.ι.app _).hom 1 = _
        rw [c.refl, map_one, map_one]
        exact (RingHom.map_one _).symm
    have htQ : ∀ k l, Q.presheaf.map (homOfLE (inf_le_right : S k ⊓ S l ≤ S l)).op (fQ l) =
        cc.u k l • Q.presheaf.map (homOfLE (inf_le_left : S k ⊓ S l ≤ S k)).op (fQ k) := by
      intro k l
      have h0 := congrArg (pullbackLocalSection W.ι) (hc k l)
      rw [pullbackLocalSection_smul, ← map_homOfLE_pullbackLocalSection, ← map_homOfLE_pullbackLocalSection] at h0

      have hle2 : S k ⊓ S l ≤ W.ι ⁻¹ᵁ (T W V 𝓛 k ⊓ T W V 𝓛 l) :=
        le_inf (inf_le_left.trans (hST k)) (inf_le_right.trans (hST l))
      have h1 := congrArg (Q.presheaf.map (homOfLE hle2).op) h0
      rw [map_smul', map_map, map_map] at h1
      show Q.presheaf.map (homOfLE _).op (Q.presheaf.map (homOfLE _).op _) =
        cc.u k l • Q.presheaf.map (homOfLE _).op (Q.presheaf.map (homOfLE _).op _)
      rw [map_map, map_map, hcc]
      exact h1
    obtain ⟨φP, -⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame hS cc fP hfP htP
    obtain ⟨φQ, -⟩ := exists_iso_glueOfCocycle_app_eq_glueFrame hS cc fQ hfQ htQ
    exact ⟨φP ≪≫ φQ.symm⟩

end GlueChart

end

theorem solution
    {X : Scheme.{u}} (W V : X.Opens) {𝓛 : X.Modules}
    (hW : ∀ x ∈ W, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf))
    (hV : Nonempty ((Scheme.Modules.pullback (W ⊓ V).ι).obj 𝓛 ≅ SheafOfModules.unit (↑(W ⊓ V) : Scheme.{u}).ringCatSheaf)) :
    ∃ 𝓛' : X.Modules,
      (∀ x ∈ W ⊔ V, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ⊔ V ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛' ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)) ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj 𝓛' ≅ (Scheme.Modules.pullback W.ι).obj 𝓛) :=
  GlueChart.main W V 𝓛 hW hV
end S_AlgebraicGeometry_Scheme_Modules_exists_locallyTrivial_sup_nonempty_pullback_iso_of_pullback_inf_iso_unit
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
