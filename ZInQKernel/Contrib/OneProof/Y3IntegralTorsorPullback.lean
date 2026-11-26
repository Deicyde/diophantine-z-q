import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Cartesian square of an equivariant map between torsors

The kernel-pair squares are the torsor identities from Stacks, Lemma 66.14.2 (Tag 07S7).
This file uses those identities; it does not assert representability of either quotient.
-/

open CategoryTheory CategoryTheory.Limits

namespace Y3IntegralDescent

/-- An equivariant map of kernel pairs is cartesian on the quotients if its square on the
second projections is cartesian and the source quotient is a cover for isomorphism descent. -/
theorem isPullback_of_equivariant_kernelPairs
    {C : Type*} [Category C] [HasPullbacks C]
    (Q : MorphismProperty C) [Q.IsStableUnderBaseChange]
    [(MorphismProperty.isomorphisms C).DescendsAlong Q]
    {RA RX A X B Y : C}
    {aA prA : RA ⟶ A} {aX prX : RX ⟶ X}
    {m : RA ⟶ RX} {p : A ⟶ X} {qA : A ⟶ B} {qX : X ⟶ Y} {b : B ⟶ Y}
    (hqA : Q qA) (hA : IsPullback aA prA qA qA) (hX : IsPullback aX prX qX qX)
    (hpr : IsPullback m prA prX p) (hact : m ≫ aX = aA ≫ p)
    (hb : qA ≫ b = p ≫ qX) : IsPullback qA p b qX := by
  let c : A ⟶ pullback b qX := pullback.lift qA p hb
  have hcB : c ≫ pullback.fst b qX = qA := by simp [c]
  have hcX : c ≫ pullback.snd b qX = p := by simp [c]
  have hR : IsPullback (aA ≫ c) prA (pullback.fst b qX) qA := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback b qX).flip
    · simpa only [Category.assoc, hcX, hact, hb] using hpr.paste_horiz hX
    · rw [Category.assoc, hcB]
      exact hA.w
  have hLocal : IsPullback (𝟙 RA) aA (aA ≫ c) c := by
    refine IsPullback.of_right ?_ (by simp) hR.flip
    simpa only [Category.id_comp, hcB] using hA.flip
  have hcCover : Q (aA ≫ c) := Q.of_isPullback hR.flip hqA
  have : IsIso c := (MorphismProperty.isomorphisms C).of_isPullback_of_descendsAlong
    hLocal hcCover (by change IsIso (𝟙 RA); infer_instance)
  exact IsPullback.of_iso_pullback ⟨hb⟩ (asIso c) hcB hcX

open AlgebraicGeometry

/-- For any `g : G ⟶ S` (no group structure or action axioms are used), the square on the second
projections is itself a pullback. Given the two torsor identities and an fppf source quotient map,
the equivariant structure map therefore exhibits `A` as the pullback of `B` to `X`. -/
theorem isPullback_of_fppf_torsor_quotients
    {S G A X B Y : Scheme} (g : G ⟶ S) (sX : X ⟶ S)
    (p : A ⟶ X) (qA : A ⟶ B) (qX : X ⟶ Y) (b : B ⟶ Y)
    [Surjective qA] [Flat qA] [LocallyOfFinitePresentation qA]
    (aA : pullback g (p ≫ sX) ⟶ A) (aX : pullback g sX ⟶ X)
    (hA : IsPullback aA (pullback.snd g (p ≫ sX)) qA qA)
    (hX : IsPullback aX (pullback.snd g sX) qX qX)
    (hact : pullback.lift (pullback.fst g (p ≫ sX)) (pullback.snd g (p ≫ sX) ≫ p)
      (by rw [Category.assoc, pullback.condition]) ≫ aX = aA ≫ p)
    (hb : qA ≫ b = p ≫ qX) : IsPullback qA p b qX := by
  let m : pullback g (p ≫ sX) ⟶ pullback g sX :=
    pullback.lift (pullback.fst g (p ≫ sX)) (pullback.snd g (p ≫ sX) ≫ p)
      (by rw [Category.assoc, pullback.condition])
  have hpr : IsPullback m (pullback.snd g (p ≫ sX)) (pullback.snd g sX) p := by
    refine IsPullback.of_right ?_ (by simp [m]) (IsPullback.of_hasPullback g sX)
    simpa only [m, pullback.lift_fst] using IsPullback.of_hasPullback g (p ≫ sX)
  have : (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme).IsStableUnderBaseChange :=
    { of_isPullback h hq :=
        ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h hq.1.1,
            MorphismProperty.of_isPullback (P := @Flat) h hq.1.2⟩,
          MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h hq.2⟩ }
  exact isPullback_of_equivariant_kernelPairs
    (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hA hX hpr hact hb

end Y3IntegralDescent
