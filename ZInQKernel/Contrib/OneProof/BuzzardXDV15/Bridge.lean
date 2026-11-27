import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Defs
import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Sheaf
import ZInQKernel.Contrib.OneProof.BuzzardXDV15.LocInj
import ZInQKernel.Contrib.OneProof.BuzzardXDV15.BaseChange
import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Kappa5
import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5
import Mathlib

/-!
# `B1'` from Buzzard's literal `V₁(5)` moduli statement

Assume Buzzard's Thm 2.1 and Cor. 2.3 at `U = V₁(5)` in fine-moduli form, with his own level
structures (elements of `F_{A/S,H}(S)`, the étale sheafification of the `H`-orbits of full
level-5 frames), and assume that the orbit invariant `[P] ↦ ι(1 - e5) P` is étale-locally
surjective. Then `B1'`, phrased with concrete `V15`-points, holds for the same moduli scheme
and the same universal curve.

* The frame scheme is an étale `(O/5O)ˣ`-torsor (from Milne's Prop. 20.7 and Remark 8.4 at
  `n = 5`), so the orbit invariant is étale-locally injective. With local surjectivity and the
  sheaf property of `V15`-points, the evaluation `Φ : F_{A/S,H}(S) → V15(A/S)` is a bijection.
* The universal level structure `α` gives the universal `V15`-point `Φ(α)`.
* For a cartesian `O`-linear square `h` over `g`, the third bullet of Buzzard's morphisms holds
  for `α, α'` iff `h` carries `Φ(α')` to the pullback of `Φ(α)` along `g`. Hence existence and
  uniqueness of `g`, and uniqueness of `h`, transfer along `Φ`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj

namespace Y3Buzzard.XDV15

attribute [local instance] FEC.grp

/-- `B1'` from the literal `V₁(5)` leaf, with Milne's Prop. 20.7 and Remark 8.4 at `n = 5`,
given étale-local surjectivity of the orbit invariant: the moduli scheme and universal curve
are those of the leaf, and the universal `V15`-point is `Φ` of the universal level structure. -/
theorem b1_of_literal
    (hsurj : ∀ (S : Over Z30Base) (A : FEC S.left), Presheaf.IsLocallySurjective (etaleOver S.left)
      (Functor.whiskerRight (invOrb A) uliftFunctor.{1, 0}))
    (hL : BuzzardXDV15) (hM5 : MilneProp207 5) (hC5 : GeomCard5) : BuzzardThm21Cor23V15' := by
  have hB25 : BuzzardFrameRepTorsor 5 := Y3Buzzard.buzzardFrameRepTorsor5_of_milne hM5 hC5
  obtain ⟨X, A, α, hP, hSm, hproj, huniv, huniq⟩ := hL
  have := invOrb_locallyInjective hB25 X A
  have := hsurj X A
  have hsh := v15_isSheaf A
  refine ⟨X, A, v15SubEquiv A (Φ A hsh α), hP, hSm, hproj, ?_, ?_⟩
  · -- the universal property: transport `α'` to a level structure `β'` with `Φ β' = α'`
    intro S A' α'
    have := invOrb_locallyInjective hB25 S A'
    have := hsurj S A'
    have hsh' := v15_isSheaf A'
    obtain ⟨β', hβ'⟩ := (Φ_bijective A' hsh').2 ((v15SubEquiv A').symm α')
    have hQ' : (Φ A' hsh' β').1.left = α'.Q := by
      rw [hβ']
      exact congrArg V15.Q ((v15SubEquiv A').apply_symm_apply α')
    obtain ⟨g, ⟨h, hpb, hι, hfib⟩, hgu⟩ := huniv S A' β'
    refine ⟨g, ⟨h, hpb, hι, ?_⟩, ?_⟩
    · have e := (levelFibre_iff hpb hι hsh hsh' α β').1 hfib
      rw [hQ'] at e
      exact e
    · rintro g' ⟨h', hpb', hι', hQ⟩
      refine hgu g' ⟨h', hpb', hι', (levelFibre_iff hpb' hι' hsh hsh' α β').2 ?_⟩
      rw [hQ']
      exact hQ
  · -- uniqueness of the comparison map
    rintro S A' α' g h h' ⟨hpb, hι, hQ⟩ ⟨hpb', hι', hQ''⟩
    have := invOrb_locallyInjective hB25 S A'
    have := hsurj S A'
    have hsh' := v15_isSheaf A'
    obtain ⟨β', hβ'⟩ := (Φ_bijective A' hsh').2 ((v15SubEquiv A').symm α')
    have hQ' : (Φ A' hsh' β').1.left = α'.Q := by
      rw [hβ']
      exact congrArg V15.Q ((v15SubEquiv A').apply_symm_apply α')
    refine huniq S A' β' g h h' ⟨hpb, hι, (levelFibre_iff hpb hι hsh hsh' α β').2 ?_⟩
      ⟨hpb', hι', (levelFibre_iff hpb' hι' hsh hsh' α β').2 ?_⟩
    · rw [hQ']
      exact hQ
    · rw [hQ']
      exact hQ''

end Y3Buzzard.XDV15
