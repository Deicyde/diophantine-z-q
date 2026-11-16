/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback.lean
  Licence        : Apache License, Version 2.0 (copyright and licence terms of the source
                   project; see its LICENSE, NOTICE and ATTRIBUTION.md)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof step was
altered, weakened or omitted except as listed below:
  * `import P2M.Util` removed (no custom commands/tactics are used).
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT` (with an explicit `end P2MW.…` closing the
    source's file-level solution namespace before it).
  * `set_option maxHeartbeats 4000000` and `set_option synthInstance.maxHeartbeats 400000` added
    (the source lakefile sets these globally).
  * 1 top-level `open` command(s): each namespace written as `_root_.<ns>` so that it
    resolves to the Mathlib namespace and not to a same-named namespace under the port prefix
    (e.g. `ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry`).
-/

import Mathlib

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace P2MW.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback

set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem solution
    {X R Y X' R' Y' : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p)
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {gX : X' ⟶ X} (hX : IsPullback gX p' p g)
    {s' t' : R' ⟶ X'} {gR : R' ⟶ R} (hsq : IsPullback gR s' s gX) (htq : gR ≫ t = t' ≫ gX)
    (w' : s' ≫ p' = t' ≫ p') :
    IsFinite p' ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' ∧
      IsPullback s' t' p' p' ∧ Nonempty (IsColimit (Cofork.ofπ p' w')) := by

  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hX inferInstance
  haveI : Flat p' := MorphismProperty.of_isPullback (P := @Flat) hX inferInstance
  haveI : LocallyOfFinitePresentation p' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hX inferInstance
  haveI : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) hX inferInstance

  have hker : IsPullback s' t' p' p' := by
    refine IsPullback.of_isLimit' ⟨w'⟩ (PullbackCone.IsLimit.mk _ (fun c => ?_) (fun c => ?_)
      (fun c => ?_) (fun c m hm₁ hm₂ => ?_))
    ·
      refine hsq.lift (hR.lift (c.fst ≫ gX) (c.snd ≫ gX) ?_) c.fst ?_
      · rw [Category.assoc, Category.assoc, hX.w, ← Category.assoc, ← Category.assoc, c.condition]
      · rw [IsPullback.lift_fst]
    · exact hsq.lift_snd _ _ _
    ·
      apply hX.hom_ext
      · rw [Category.assoc, ← htq, ← Category.assoc, hsq.lift_fst, hR.lift_snd]
      · rw [Category.assoc, ← w', ← Category.assoc, hsq.lift_snd, c.condition]
    · apply hsq.hom_ext
      · rw [hsq.lift_fst]
        apply hR.hom_ext
        · rw [IsPullback.lift_fst, Category.assoc, hsq.w, ← Category.assoc, hm₁]
        · rw [IsPullback.lift_snd, Category.assoc, htq, ← Category.assoc, hm₂]
      · rw [hsq.lift_snd]
        exact hm₁

  have hk : IsKernelPair p' s' t' := hker
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, hker, ⟨?_⟩⟩
  exact hk.toCoequalizer (regularEpiOfEffectiveEpi p')

end P2MW.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback

end ZInQ.Contrib.CloudW03NeronSurj.FLT
