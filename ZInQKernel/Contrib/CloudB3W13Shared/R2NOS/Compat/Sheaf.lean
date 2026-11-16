/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Lean 4.35 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 compatibility declarations for the
H5 lane4 port of anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2 (source
written against Mathlib db584cd6d46c92f209a44c0f1c829460d327499d).

Mathlib db584 `Mathlib/CategoryTheory/Sites/Sheaf.lean` (Apache License 2.0, Mathlib authors)
contained, after `Sheaf J A` became `ObjectProperty.FullSubcategory (Presheaf.IsSheaf J)`:
  `abbrev Sheaf.val (F : Sheaf J A) : Cᵒᵖ ⥤ A := F.obj`,
  `lemma Sheaf.cond (F : Sheaf J A) : Presheaf.IsSheaf J F.obj := F.property` (deprecated),
  `alias Sheaf.Hom.mk := ObjectProperty.homMk` (deprecated).
Mathlib 56a deleted them.  They are restated VERBATIM below under the port prefix
`ZInQ.Contrib.CloudW03NeronSurj.FLT` so that the source's field notation (`F.val`, `F.cond`)
and `Sheaf.Hom.mk` resolve exactly as at db584 (every ported file opens the prefix).  No axiom.
NOTICE OF MODIFICATION (Apache-2.0 §4(b)), H5 lane4, 2026-11-14: extracted; deprecation
attributes dropped (they only affect warnings).
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace CategoryTheory

open _root_.CategoryTheory

universe w v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {A : Type*} [Category A]

abbrev Sheaf.val (F : _root_.CategoryTheory.Sheaf J A) : Cᵒᵖ ⥤ A := F.obj

lemma Sheaf.cond (F : _root_.CategoryTheory.Sheaf J A) : Presheaf.IsSheaf J F.obj := F.property

alias Sheaf.Hom.mk := _root_.CategoryTheory.ObjectProperty.homMk

end CategoryTheory

end ZInQ.Contrib.CloudW03NeronSurj.FLT
