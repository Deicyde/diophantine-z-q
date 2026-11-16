/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Lean 4.35 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 compatibility declarations for the
H5 lane4 port of anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2 (source
written against Mathlib db584cd6d46c92f209a44c0f1c829460d327499d).

Mathlib db584 `Mathlib/AlgebraicGeometry/Sites/Small.lean` (Copyright (c) 2024 Christian Merten,
Apache License 2.0) defined `Scheme.overPretopology P S` with coverings
`{R | ∃ (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S), R = 𝒰.toPresieveOver}` and proved
`overGrothendieckTopology_eq_toGrothendieck_overPretopology`.  Mathlib 56a replaced that definition
by `((Scheme.precoverage P).over S).toPretopology` (arbitrary presieves whose image is a covering),
so a source proof destructuring a covering as `⟨𝒰, h𝒰, rfl⟩` no longer applies.  This file
restates the db584 definition and lemma VERBATIM (statements and proofs) under the port prefix
`ZInQ.Contrib.CloudW03NeronSurj.FLT` with the names `overPretopologyDb584` and
`overGrothendieckTopology_eq_toGrothendieck_overPretopologyDb584`; the Grothendieck topology
`Scheme.overGrothendieckTopology` they are compared with is Mathlib 56a's (unchanged:
`(Scheme.grothendieckTopology P).over S`).  No axiom.
NOTICE OF MODIFICATION (Apache-2.0 §4(b)), H5 lane4, 2026-11-14: extracted and renamed; proofs as in
db584 (they elaborate against Mathlib 56a unchanged except that db584's generalized field
`𝒰.bind` is spelled with the same constant `Precoverage.ZeroHypercover.bind`, and the structure field
`over` is written `«over»` because the opened namespaces make `over` a token).
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace AlgebraicGeometry.Scheme

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.Scheme

universe u

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}} [P.IsStableUnderBaseChange]
  [P.IsMultiplicative] [P.RespectsIso]

variable (P S)

set_option backward.isDefEq.respectTransparency false in
/-- db584 `Scheme.overPretopology`: coverings are the presieves of `P`-covers of `S`-schemes. -/
def overPretopologyDb584 : Pretopology (Over S) where
  coverings Y := {R | ∃ (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S), R = 𝒰.toPresieveOver}
  has_isos {X Y} f _ := ⟨coverOfIsIso f.left, inferInstance, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, rfl⟩
    refine ⟨𝒰.pullbackCoverOver' S f.left, inferInstance, ?_⟩
    simpa [Cover.toPresieveOver] using!
      (Presieve.ofArrows_pullback f (fun i ↦ (𝒰.X i).asOver S) (fun i ↦ (𝒰.f i).asOver S)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, rfl⟩ H
    choose V h hV using H
    refine ⟨𝒰.bind (fun j => V ((𝒰.f j).asOver S) ⟨j⟩), inferInstance, ?_⟩
    convert!
      Presieve.ofArrows_bind _ (fun j ↦ (𝒰.f j).asOver S) _ (fun Y f H j ↦ ((V f H).X j).asOver S)
        (fun Y f H j ↦ ((V f H).f j).asOver S)
    apply hV

/-- db584 `overGrothendieckTopology_eq_toGrothendieck_overPretopology`, for `overPretopologyDb584`. -/
lemma overGrothendieckTopology_eq_toGrothendieck_overPretopologyDb584 :
    S.overGrothendieckTopology P = (overPretopologyDb584 P S).toGrothendieck := by
  ext X R
  rw [GrothendieckTopology.mem_over_iff]
  constructor
  · intro hR
    obtain ⟨𝒰, hle⟩ := exists_cover_of_mem_grothendieckTopology hR
    rw [mem_grothendieckTopology_iff] at hR
    let (i : 𝒰.I₀) : (𝒰.X i).Over S := { hom := 𝒰.f i ≫ X.hom }
    let : 𝒰.Over S :=
      { «over» := inferInstance
        isOver_map := fun i ↦ ⟨rfl⟩ }
    use 𝒰.toPresieveOver, ⟨𝒰, inferInstance, rfl⟩
    rwa [Cover.toPresieveOver_le_arrows_iff]
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hT⟩
    rw [mem_grothendieckTopology_iff]
    use 𝒰
    rwa [Cover.toPresieveOver_le_arrows_iff] at hT

end AlgebraicGeometry.Scheme

end ZInQ.Contrib.CloudW03NeronSurj.FLT
