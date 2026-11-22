import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_HenselianLocalRing_exists_algHom_lift_of_etale
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale sections over henselian rings

The affine Hensel lifting theorem extends to a section of any étale
scheme over a henselian local ring.
-/

open CategoryTheory AlgebraicGeometry

namespace SmoothGroup

universe u

/-- A section of the fibre of an étale morphism over the residue field of
a henselian local ring lifts to a section over the ring. -/
theorem exists_section_over_residue_of_etale
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Etale f]
    (z : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hz : z ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ a : Spec (.of R) ⟶ X, a ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ a = z := by
  let x := z (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))
  let i := X.affineCover.idx x
  let g := X.affineCover.f i
  let y := IsOpenImmersion.lift g z (by
    rintro _ ⟨j, rfl⟩
    rw [Subsingleton.elim j (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))]
    exact X.affineCover.covers x)
  have hy : y ≫ g = z := IsOpenImmersion.lift_fac _ _ _
  let e := (X.affineCover.X i).isoSpec
  let j := e.inv ≫ g
  have : Etale (j ≫ f) := by
    dsimp [j]
    infer_instance
  obtain ⟨p, hp⟩ := Spec.map_surjective (j ≫ f)
  obtain ⟨q, hq⟩ := Spec.map_surjective (y ≫ e.hom)
  have hqj : Spec.map q ≫ j = z := by rw [hq]; simp [j, hy]
  have hqp : p ≫ q = CommRingCat.ofHom (IsLocalRing.residue R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hp, ← Category.assoc, hqj, hz]
  let := p.hom.toAlgebra
  have : Algebra.Etale R Γ(X.affineCover.X i, ⊤) := by
    apply RingHom.etale_algebraMap.mp
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp (hp ▸ ‹Etale (j ≫ f)›)
  let qA : Γ(X.affineCover.X i, ⊤) →ₐ[R] IsLocalRing.ResidueField R :=
    { q.hom with
      commutes' := fun r => congrArg (fun h : CommRingCat.of R ⟶
        CommRingCat.of (IsLocalRing.ResidueField R) => h.hom r) hqp }
  obtain ⟨a, ha⟩ :=
    ZInQ.Contrib.CloudR2NeronExistence.Henselian.HenselianLocalRing.exists_algHom_lift_of_etale _ qA
  let aR := CommRingCat.ofHom (a : Γ(X.affineCover.X i, ⊤) →+* R)
  refine ⟨Spec.map aR ≫ j, ?_, ?_⟩
  · rw [Category.assoc, ← hp, ← Spec.map_comp]
    have hpR : p ≫ aR = 𝟙 _ := by
      ext r
      exact a.commutes r
    rw [hpR, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, ← hqj]
    congr 2
    ext s
    exact ha s

#print axioms exists_section_over_residue_of_etale

end SmoothGroup
