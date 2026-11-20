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
  Source file    : P2M/Sol/S_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections.lean
  Source sha256  : dd67e3ca8e878b7e46474a4b9cd039afc7b92e08d85840482b0da44c1c67c294
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections_of_isAffine
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing"

universe u

namespace ProdStalk
r2nos_namespace_dual

lemma map_maximalIdeal_of_isIso {A B : CommRingCat.{u}} (e : A ⟶ B) [IsIso e]
    [IsLocalRing A] [IsLocalRing B] : (maximalIdeal A).map e.hom = maximalIdeal B := by
  let e' : A ≃+* B := (asIso e).commRingCatIsoToRingEquiv
  have he : ∀ a, e' a = e.hom a := fun a ↦ rfl
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (mem_maximalIdeal _).mp ha
    have := hu.map e'.symm
    rwa [← he, e'.symm_apply_apply] at this
  · intro b hb
    have : b = e.hom (e'.symm b) := by rw [← he, e'.apply_symm_apply]
    rw [this]
    refine Ideal.mem_map_of_mem _ ?_
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (mem_maximalIdeal _).mp hb
    have := hu.map e'
    rwa [e'.apply_symm_apply] at this

lemma transport {W W' Y Z U V : Scheme.{u}} (ι : W' ⟶ W) [IsOpenImmersion ι]
    (f₁ : W ⟶ Y) (f₂ : W ⟶ Z) (g₁ : W' ⟶ U) (g₂ : W' ⟶ V) (jU : U ⟶ Y) (jV : V ⟶ Z)
    [IsOpenImmersion jU] [IsOpenImmersion jV]
    (h₁ : ι ≫ f₁ = g₁ ≫ jU) (h₂ : ι ≫ f₂ = g₂ ≫ jV) (w' : W')
    (H : maximalIdeal (W'.presheaf.stalk w') ≤
      (maximalIdeal _).map (g₁.stalkMap w').hom ⊔ (maximalIdeal _).map (g₂.stalkMap w').hom) :
    maximalIdeal (W.presheaf.stalk (ι w')) ≤
      (maximalIdeal _).map (f₁.stalkMap (ι w')).hom ⊔ (maximalIdeal _).map (f₂.stalkMap (ι w')).hom := by
  haveI hι : IsIso (ι.stalkMap w') := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 w'

  have key : ∀ {T T' : Scheme.{u}} (f : W ⟶ T) (g : W' ⟶ T') (j : T' ⟶ T) [IsOpenImmersion j]
      (h : ι ≫ f = g ≫ j),
      ((maximalIdeal _).map (f.stalkMap (ι w')).hom).map (ι.stalkMap w').hom =
        (maximalIdeal _).map (g.stalkMap w').hom := by
    intro T T' f g j _ h
    haveI hj : IsIso (j.stalkMap (g w')) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
    have hpt : f (ι w') = j (g w') := by rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    let c : T.presheaf.stalk (f (ι w')) ≅ T.presheaf.stalk (j (g w')) := T.presheaf.stalkCongr (.of_eq hpt)
    have e : (ι.stalkMap w').hom.comp (f.stalkMap (ι w')).hom =
        (g.stalkMap w').hom.comp ((j.stalkMap (g w')).hom.comp c.hom.hom) := by
      have e1 : (ι.stalkMap w').hom.comp (f.stalkMap (ι w')).hom = ((ι ≫ f).stalkMap w').hom := by
        rw [Scheme.Hom.stalkMap_comp]; rfl
      rw [e1, Scheme.Hom.stalkMap_congr_hom _ _ h w', Scheme.Hom.stalkMap_comp]
      rfl
    have hjc : (maximalIdeal (T.presheaf.stalk (f (ι w')))).map ((j.stalkMap (g w')).hom.comp c.hom.hom) =
        maximalIdeal (T'.presheaf.stalk (g w')) := by
      rw [← Ideal.map_map, map_maximalIdeal_of_isIso, map_maximalIdeal_of_isIso]
    rw [Ideal.map_map, e, ← hjc, Ideal.map_map]
  intro x hx
  have hαx : (ι.stalkMap w').hom x ∈ maximalIdeal (W'.presheaf.stalk w') := by
    rw [← map_maximalIdeal_of_isIso (ι.stalkMap w')]
    exact Ideal.mem_map_of_mem _ hx
  have := H hαx
  rw [← key f₁ g₁ jU h₁, ← key f₂ g₂ jV h₂, ← Ideal.map_sup] at this
  have hbij : Function.Bijective (ι.stalkMap w').hom :=
    ConcreteCategory.bijective_of_isIso (ι.stalkMap w')
  have hx' := Ideal.mem_comap.mpr this
  rwa [Ideal.comap_map_of_bijective (ι.stalkMap w').hom hbij] at hx'

end ProdStalk

open ProdStalk in
r2nos_open_dual "ProdStalk" in
theorem solution
    {k : Type u} [Field k] {Y Z : Scheme.{u}} (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ Y) (hy : y ≫ pY = 𝟙 _) (z : Spec (.of k) ⟶ Z) (hz : z ≫ pZ = 𝟙 _)
    (w : ↑(pullback pY pZ)) (hw : w = (pullback.lift y z (hy.trans hz.symm)) (closedPoint k)) :
    maximalIdeal ((pullback pY pZ).presheaf.stalk w) ≤
      (maximalIdeal _).map ((pullback.fst pY pZ).stalkMap w).hom ⊔
        (maximalIdeal _).map ((pullback.snd pY pZ).stalkMap w).hom := by
  subst hw

  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (y (closedPoint k))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (z (closedPoint k))) isOpen_univ
  let U' : Y.Opens := U
  let V' : Z.Opens := V
  haveI : IsAffine U' := hU
  haveI : IsAffine V' := hV

  have hpt : ∀ p : ↑(Spec (CommRingCat.of k)), p = closedPoint k := fun p ↦ Subsingleton.elim _ _
  have hry : Set.range y ⊆ Set.range U'.ι := by
    rintro _ ⟨p, rfl⟩
    rw [hpt p, Scheme.Opens.range_ι]
    exact hyU
  have hrz : Set.range z ⊆ Set.range V'.ι := by
    rintro _ ⟨p, rfl⟩
    rw [hpt p, Scheme.Opens.range_ι]
    exact hzV
  let y' := IsOpenImmersion.lift U'.ι y hry
  let z' := IsOpenImmersion.lift V'.ι z hrz
  have hy' : y' ≫ U'.ι = y := IsOpenImmersion.lift_fac _ _ _
  have hz' : z' ≫ V'.ι = z := IsOpenImmersion.lift_fac _ _ _
  let pU := U'.ι ≫ pY
  let pV := V'.ι ≫ pZ
  have hyU' : y' ≫ pU = 𝟙 _ := by rw [← Category.assoc, hy', hy]
  have hzV' : z' ≫ pV = 𝟙 _ := by rw [← Category.assoc, hz', hz]

  let ι := pullback.map pU pV pY pZ U'.ι V'.ι (𝟙 _) (Category.comp_id _) (Category.comp_id _)
  have h₁ : ι ≫ pullback.fst pY pZ = pullback.fst pU pV ≫ U'.ι := pullback.lift_fst _ _ _
  have h₂ : ι ≫ pullback.snd pY pZ = pullback.snd pU pV ≫ V'.ι := pullback.lift_snd _ _ _
  have hlift : pullback.lift y' z' (hyU'.trans hzV'.symm) ≫ ι = pullback.lift y z (hy.trans hz.symm) := by
    apply pullback.hom_ext
    · rw [Category.assoc, h₁, ← Category.assoc, pullback.lift_fst, hy', pullback.lift_fst]
    · rw [Category.assoc, h₂, ← Category.assoc, pullback.lift_snd, hz', pullback.lift_snd]
  have hw' : ι (pullback.lift y' z' (hyU'.trans hzV'.symm) (closedPoint k)) =
      pullback.lift y z (hy.trans hz.symm) (closedPoint k) := by
    rw [← Scheme.Hom.comp_apply, hlift]
  rw [← hw']
  exact transport ι _ _ _ _ U'.ι V'.ι h₁ h₂ _ (AlgebraicGeometry.maximalIdeal_stalk_pullback_le_of_sections_of_isAffine pU pV y' hyU' z' hzV' _ rfl)

#print axioms solution
end S_AlgebraicGeometry_maximalIdeal_stalk_pullback_le_of_sections
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
