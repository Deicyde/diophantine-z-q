/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

New actual TWO-OPEN module-iso gluing primitive for the diagonal/generic adapter.
It uses the proved real Zariski module gluing, not an effectiveness/Pic/desired
line-descent Fact. The global iso retains both prescribed chart homs; arbitrary
module morphism equality can be checked on those two actual opens.
Local compatibility remains explicit in this general primitive and is to be
DERIVED from the original generic-line iso in the specific transport adapter.
No ample-line extension or model existence is claimed by this primitive.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- Literal diagonal/generic two-open scheme family. -/
def twoOpenSchemes {X : Scheme.{u}} (D H : X.Opens) : Bool → Scheme.{u}
  | false => D.toScheme
  | true => H.toScheme

def twoOpenMaps {X : Scheme.{u}} (D H : X.Opens) : ∀ b, twoOpenSchemes D H b ⟶ X
  | false => D.ι
  | true => H.ι

theorem twoOpenMaps_isOpenImmersion {X : Scheme.{u}} (D H : X.Opens) (b : Bool) :
    IsOpenImmersion (twoOpenMaps D H b) := by
  cases b <;> dsimp only [twoOpenMaps, twoOpenSchemes] <;> infer_instance

/-- The actual ranges cover, without a hidden faithfully-flat/effective input. -/
theorem twoOpenMaps_cover {X : Scheme.{u}} (D H : X.Opens) (hDH : D ⊔ H = ⊤) :
    letI : ∀ b, IsOpenImmersion (twoOpenMaps D H b) := twoOpenMaps_isOpenImmersion D H
    ⨆ b, (twoOpenMaps D H b).opensRange = ⊤ := by
  letI : ∀ b, IsOpenImmersion (twoOpenMaps D H b) := twoOpenMaps_isOpenImmersion D H
  apply le_antisymm le_top
  intro x _
  have hx : x ∈ D ⊔ H := hDH.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  rcases hx with hx | hx
  · refine TopologicalSpace.Opens.mem_iSup.mpr ⟨false, ?_⟩
    change ∃ z : D.toScheme, D.ι z = x
    exact ⟨⟨x, hx⟩, rfl⟩
  · refine TopologicalSpace.Opens.mem_iSup.mpr ⟨true, ?_⟩
    change ∃ z : H.toScheme, H.ι z = x
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Actual global module-map equality from diagonal and generic restrictions. -/
theorem module_hom_ext_two {X : Scheme.{u}} (D H : X.Opens) (hDH : D ⊔ H = ⊤)
    {M N : modulesPseudofunctor.obj (.mk (op X))} {a b : M ⟶ N}
    (hD : (modulesPseudofunctor.map D.ι.op.toLoc).toFunctor.map a =
      (modulesPseudofunctor.map D.ι.op.toLoc).toFunctor.map b)
    (hH : (modulesPseudofunctor.map H.ι.op.toLoc).toFunctor.map a =
      (modulesPseudofunctor.map H.ι.op.toLoc).toFunctor.map b) : a = b := by
  haveI : ∀ b, IsOpenImmersion (twoOpenMaps D H b) := twoOpenMaps_isOpenImmersion D H
  apply module_hom_ext_openCover (twoOpenMaps D H) (twoOpenMaps_cover D H hDH)
  intro j
  cases j
  · exact hD
  · exact hH

/-- Two compatible prescribed local isos realize an ACTUAL global iso,
whose pullbacks on BOTH opens are literally the prescribed maps. -/
theorem exists_iso_twoOpen {X : Scheme.{u}} (D H : X.Opens) (hDH : D ⊔ H = ⊤)
    (M N : modulesPseudofunctor.obj (.mk (op X)))
    (eD : (modulesPseudofunctor.map D.ι.op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map D.ι.op.toLoc).toFunctor.obj N)
    (eH : (modulesPseudofunctor.map H.ι.op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map H.ι.op.toLoc).toFunctor.obj N)
    (hc : ∀ {T : Scheme.{u}} (q : T ⟶ X) (a : T ⟶ D.toScheme) (b : T ⟶ H.toScheme)
      (ha : a ≫ D.ι = q) (hb : b ≫ H.ι = q),
      pullHom eD.hom a q q ha ha = pullHom eH.hom b q q hb hb) :
    ∃ E : M ≅ N,
      (modulesPseudofunctor.map D.ι.op.toLoc).toFunctor.map E.hom = eD.hom ∧
      (modulesPseudofunctor.map H.ι.op.toLoc).toFunctor.map E.hom = eH.hom := by
  haveI : ∀ b, IsOpenImmersion (twoOpenMaps D H b) := twoOpenMaps_isOpenImmersion D H
  let e : ∀ j, (modulesPseudofunctor.map (twoOpenMaps D H j).op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map (twoOpenMaps D H j).op.toLoc).toFunctor.obj N :=
    fun j => match j with
    | false => eD
    | true => eH
  obtain ⟨E, hE⟩ := exists_iso_of_openCover_compatible (twoOpenMaps D H)
    (twoOpenMaps_cover D H hDH) M N e (by
      intro T q j k a b ha hb
      cases j <;> cases k
      · have hab : a = b := (cancel_mono D.ι).mp (ha.trans hb.symm)
        subst b
        rfl
      · exact hc q a b ha hb
      · exact (hc q b a hb ha).symm
      · have hab : a = b := (cancel_mono H.ι).mp (ha.trans hb.symm)
        subst b
        rfl)
  exact ⟨E, hE false, hE true⟩

#print axioms module_hom_ext_two
#print axioms exists_iso_twoOpen

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
