/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension` (task ring-class).
module

public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

noncomputable section

namespace TauCeti

open IntermediateField

variable (K : Type*) [Field K]

variable {K} in
/-- Below every open subgroup `W` of `G_K` lies an open subgroup whose fixed field contains the
`p`-th roots of unity: the subgroup fixing `F(ζ_p)`, for `F` the fixed field of `W`. -/
theorem exists_le_hasEnoughRootsOfUnity (p : ℕ) [NeZero (p : K)]
    (W : OpenSubgroup (AbsoluteGaloisGroup K)) :
    ∃ (W' : OpenSubgroup (AbsoluteGaloisGroup K)) (E : IntermediateField K (SeparableClosure K)),
      W' ≤ W ∧ fixedField W'.toSubgroup = E ∧ FiniteDimensional K E ∧
        HasEnoughRootsOfUnity E p := by
  have : NeZero p := ⟨by
    intro hp
    exact NeZero.ne (p : K) (by simp only [hp, Nat.cast_zero])⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure K) p
  have : FiniteDimensional K K⟮ζ⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  let E := fixedField W.toSubgroup ⊔ K⟮ζ⟯
  refine ⟨⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩, E, ?_,
    InfiniteGalois.fixedField_fixingSubgroup E, inferInstance, ?_⟩
  · exact OpenSubgroup.toSubgroup_le.1 <|
      (IntermediateField.fixingSubgroup_antitone le_sup_left).trans
        (toSubgroup_eq_fixingSubgroup_of_fixedField_eq rfl).ge
  · have hζE : IsPrimitiveRoot
        (⟨ζ, (le_sup_right : K⟮ζ⟯ ≤ E) (mem_adjoin_simple_self K ζ)⟩ : E) p :=
      hζ.of_map_of_injective (f := E.val) Subtype.val_injective
    exact .of_card_le hζE.card_rootsOfUnity.ge

end TauCeti
