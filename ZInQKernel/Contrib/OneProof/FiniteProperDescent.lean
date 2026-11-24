import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.Adjoin.Tower

/-! Descent of properness along a finite surjection with injective sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

private theorem isSeparated_of_finite_surjective_comp {X Z S : Scheme}
    (π : X ⟶ Z) (z : Z ⟶ S) [IsFinite π] [Surjective π]
    [IsSeparated (π ≫ z)] : IsSeparated z := by
  let f := π ≫ z
  let a : pullback f f ⟶ pullback z f :=
    pullback.map f f z f π (𝟙 X) (𝟙 S) (by simp [f]) (by simp)
  let b : pullback z f ⟶ pullback z z :=
    pullback.map z f z z (𝟙 Z) π (𝟙 S) (by simp) (by simp [f])
  have ha : IsPullback a (pullback.fst f f) (pullback.fst z f) π := by
    refine IsPullback.of_right (t := (IsPullback.of_hasPullback z f).flip) ?_ ?_
    · simpa [a, f] using (IsPullback.of_hasPullback f f).flip
    · simp [a]
  have hb : IsPullback b (pullback.snd z f) (pullback.snd z z) π := by
    refine IsPullback.of_right (t := IsPullback.of_hasPullback z z) ?_ ?_
    · simpa [b, f] using IsPullback.of_hasPullback z f
    · simp [b]
  have : IsFinite a := MorphismProperty.of_isPullback ha.flip inferInstance
  have : IsFinite b := MorphismProperty.of_isPullback hb.flip inferInstance
  have hcomp : pullback.diagonal f ≫ a ≫ b = π ≫ pullback.diagonal z := by
    apply pullback.hom_ext <;> simp [a, b]
  have hr : Set.range (pullback.diagonal f ≫ a ≫ b) = Set.range (pullback.diagonal z) := by
    rw [hcomp]
    change Set.range ((pullback.diagonal z) ∘ π) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr π.surjective, Set.image_univ]
  have hc : IsClosed (Set.range (pullback.diagonal f ≫ a ≫ b)) := by
    change IsClosed (Set.range ((a ≫ b) ∘ pullback.diagonal f))
    rw [Set.range_comp]
    exact (a ≫ b).isClosedMap _ (pullback.diagonal f).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (hr ▸ hc)⟩

/-- A finite surjection with injective section maps descends properness
over an affine noetherian base. -/
theorem isProper_of_finite_surjective_comp_of_injective_sections
    {X Z S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (π : X ⟶ Z) (z : Z ⟶ S) [IsFinite π] [Surjective π] [IsProper (π ≫ z)]
    (hinj : ∀ U : Z.Opens, IsAffineOpen U → Function.Injective (π.app U)) : IsProper z := by
  have hft : LocallyOfFiniteType z := by
    apply HasRingHomProperty.of_iSup_eq_top (P := @LocallyOfFiniteType)
      (Q := RingHom.FiniteType) (fun U : Z.affineOpens => U) (iSup_affineOpens_eq_top Z)
    intro U
    let A := Γ(S, ⊤)
    let B := Γ(Z, U.1)
    let C := Γ(X, π ⁻¹ᵁ U.1)
    let j : A →+* B := (z.appLE ⊤ U.1 (by simp)).hom
    let k : B →+* C := (π.app U.1).hom
    let _ : Algebra A B := j.toAlgebra
    let _ : Algebra B C := k.toAlgebra
    let _ : Algebra A C := (k.comp j).toAlgebra
    have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
    have hftcomp := (π ≫ z).finiteType_appLE (isAffineOpen_top _) (U.2.preimage π)
      (show π ⁻¹ᵁ U.1 ≤ (π ≫ z) ⁻¹ᵁ ⊤ by simp)
    have hfinite : (k.comp j).FiniteType := by
      change (z.appLE ⊤ U.1 _ ≫ π.app U.1).hom.FiniteType
      rw [π.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      exact hftcomp
    have hn : Module.Finite B C := π.finite_app U.1 U.2
    exact ⟨fg_of_fg_of_fg A B C hfinite.out hn.fg_top (hinj U.1 U.2)⟩
  have : IsSeparated z := isSeparated_of_finite_surjective_comp π z
  have : UniversallyClosed z := UniversallyClosed.of_comp_surjective π z
  exact ⟨⟩

end AlgebraicGeometry

#print axioms AlgebraicGeometry.isProper_of_finite_surjective_comp_of_injective_sections
