import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_existsUnique_forall_map_eq_of_forall_affineOpens.lean
Original Git blob: 93b41e2f351f4ace22edec17ae3c8d2e3cda2961
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory TopologicalSpace"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_forall_map_eq_of_forall_affineOpens
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry

universe u

open TopologicalSpace

namespace BenchOG1
h77_bridge_namespace

theorem map_map {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens} (f : V ⟶ U) (g : W ⟶ V) (k : W ⟶ U)
    (x : Γ(M, U)) : M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  congr 2

theorem sec_ext {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (Wi : ι → X.Opens) (V : X.Opens)
    (hle : ∀ i, Wi i ≤ V) (hcover : ∀ x ∈ V, ∃ i, x ∈ Wi i) (s t : Γ(M, V))
    (h : ∀ i, M.presheaf.map (homOfLE (hle i)).op s = M.presheaf.map (homOfLE (hle i)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, Scheme.Modules.isSheaf M⟩ Wi V (fun i => homOfLE (hle i))
    (fun x hx => by obtain ⟨i, hi⟩ := hcover x hx; exact Opens.mem_iSup.mpr ⟨i, hi⟩) s t h

theorem sec_ext_affine {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) (s t : Γ(M, V))
    (h : ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ V),
      M.presheaf.map (homOfLE hU).op s = M.presheaf.map (homOfLE hU).op t) : s = t := by
  refine sec_ext M (fun i : {U : X.affineOpens // (U : X.Opens) ≤ V} => (i.1 : X.Opens)) V
    (fun i => i.2) ?_ s t (fun i => h i.1 i.2)
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩

end BenchOG1

theorem solution
    {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (s : ∀ U : X.affineOpens, (U : X.Opens) ≤ W → Γ(M, U))
    (hs : ∀ (U V : X.affineOpens) (hU : (U : X.Opens) ≤ W) (hVU : (V : X.Opens) ≤ U),
      M.presheaf.map (homOfLE hVU).op (s U hU) = s V (hVU.trans hU)) :
    ∃! t : Γ(M, W), ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W),
      M.presheaf.map (homOfLE hU).op t = s U hU := by
  let ι : Type u := {U : X.affineOpens // (U : X.Opens) ≤ W}
  let Ui : ι → X.Opens := fun i => (i.1 : X.Opens)
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
  have hcover : W ≤ iSup Ui := by
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUW⟩, hxU⟩
  let sf : ∀ i : ι, Γ(M, Ui i) := fun i => s i.1 i.2
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf Ui sf := by
    intro i j
    apply BenchOG1.sec_ext_affine
    intro V hV
    rw [BenchOG1.map_map M _ _ (homOfLE (hV.trans inf_le_left)),
      BenchOG1.map_map M _ _ (homOfLE (hV.trans inf_le_right))]
    change M.presheaf.map (homOfLE _).op (s i.1 i.2) = M.presheaf.map (homOfLE _).op (s j.1 j.2)
    rw [hs i.1 V i.2 (hV.trans inf_le_left), hs j.1 V j.2 (hV.trans inf_le_right)]
  obtain ⟨t, ht, huniq⟩ :=
    F.existsUnique_gluing' Ui W (fun i => homOfLE i.2) hcover sf hcompat
  refine ⟨t, fun U hU => ht ⟨U, hU⟩, fun t' ht' => huniq t' (fun i => ht' i.1 i.2)⟩


end P2MW.S_AlgebraicGeometry_Scheme_Modules_existsUnique_forall_map_eq_of_forall_affineOpens
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
