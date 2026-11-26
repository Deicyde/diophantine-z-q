import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Sites.Proetale

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt

universe u
variable {S : Scheme.{u}}

noncomputable def canonicalAffineObj (U : S.ProEt)
    (i : U.left.affineCover.I₀) : S.ProEt := by
  letI : IsOpenImmersion (U.left.affineCover.f i) := inferInstance
  letI : Etale (U.left.affineCover.f i) := inferInstance
  letI : WeaklyEtale (U.left.affineCover.f i) := inferInstance
  exact ProEt.mk (U.left.affineCover.f i ≫ U.hom)

noncomputable def canonicalAffineMap (U : S.ProEt)
    (i : U.left.affineCover.I₀) : canonicalAffineObj U i ⟶ U :=
  MorphismProperty.Over.homMk (P := @WeaklyEtale) (Q := ⊤)
    (A := canonicalAffineObj U i) (B := U) (U.left.affineCover.f i) rfl

/-- The affine open cover of the underlying scheme is a covering family on
the actual small pro-étale site. -/
theorem canonicalAffine_mem_precoverage (U : S.ProEt) :
    Presieve.ofArrows (canonicalAffineObj U) (canonicalAffineMap U) ∈ ProEt.precoverage S U := by
  have hle : Scheme.zariskiPrecoverage.{u} ≤ Scheme.etalePrecoverage.{u} := by
    change Scheme.precoverage @IsOpenImmersion ≤ Scheme.precoverage @Etale
    apply Scheme.precoverage_mono
    intro X Y f hf
    let : IsOpenImmersion f := hf
    exact (inferInstance : Etale f)
  have hbig : U.left.affineCover.presieve₀ ∈ Scheme.proetalePrecoverage U.left :=
    (le_trans hle Scheme.etalePrecoverage_le_proetalePrecoverage) U.left U.left.affineCover.mem₀
  rw [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  change U.left.affineCover.presieve₀ ∈ Scheme.proetalePrecoverage U.left
  exact hbig

/-- Pullback along the affine open family detects covering sieves, since an
arrow in its generated sieve factors through an actual affine open. -/
theorem mem_topology_iff_canonicalAffine (U : S.ProEt) (R : Sieve U) :
    R ∈ ProEt.topology S U ↔
      ∀ i, R.pullback (canonicalAffineMap U i) ∈ ProEt.topology S (canonicalAffineObj U i) := by
  constructor
  · intro h i
    exact (ProEt.topology S).pullback_stable (canonicalAffineMap U i) h
  · intro h
    have hT : Sieve.ofArrows (canonicalAffineObj U) (canonicalAffineMap U) ∈ ProEt.topology S U :=
      Precoverage.generate_mem_toGrothendieck (canonicalAffine_mem_precoverage U)
    refine (ProEt.topology S).transitive hT R ?_
    intro W g hg
    obtain ⟨i, a, rfl⟩ :=
      (Sieve.mem_ofArrows_iff (canonicalAffineObj U) (canonicalAffineMap U) g).1 hg
    rw [Sieve.pullback_comp]
    exact (ProEt.topology S).pullback_stable a (h i)

theorem mem_topology_iff_affine_sources (U : S.ProEt) (R : Sieve U) :
    R ∈ ProEt.topology S U ↔ ∀ (V : S.ProEt) (f : V ⟶ U), IsAffine V.left →
        R.pullback f ∈ ProEt.topology S V := by
  constructor
  · intro h V f _
    exact (ProEt.topology S).pullback_stable f h
  · intro h
    apply (mem_topology_iff_canonicalAffine U R).2
    intro i
    apply h (canonicalAffineObj U i) (canonicalAffineMap U i)
    change IsAffine (U.left.affineCover.X i)
    exact Scheme.isAffine_affineCover U.left i

end AlgebraicGeometry.Scheme.ProEt
