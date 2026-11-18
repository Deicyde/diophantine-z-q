import HenselDivision.SepClosedPointsV001
import HenselDivision.AuditV001

/-!
# Integral, residual and geometric torsion points over a strictly henselian local ring

`R` henselian local with separably closed residue field `k` (strictly henselian), `Ω ⊇ k` a field
(for instance an algebraic closure), `G` a group scheme over `S = Spec R` with étale torsion scheme
`G[n] → S`. Then restriction gives bijections

  `G(S)[n] → G(Spec k)[n] → G(Spec Ω)[n]`,

where `Spec k → S` is the closed point and `Spec Ω → Spec k → S` a geometric point of the closed
fibre. The first map is Hensel lifting on `G[n]`, the second is rationality of points of the étale
closed fibre of `G[n]` over the separably closed field `k`. `G[n]` is never asserted to be finite.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  IsLocalRing
open scoped MonObj

namespace HenselDivision

universe u

variable {R : Type u} [CommRing R]

/-- A geometric point `Spec Ω → Spec k → Spec R` of the closed fibre, as an object over `Spec R`. -/
noncomputable abbrev geomObj (R : Type u) [CommRing R] [IsLocalRing R] (Ω : Type u) [Field Ω]
    [Algebra (ResidueField R) Ω] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R) Ω)) ≫ closedPt R)

/-- `Spec Ω → Spec k` over `Spec R`. -/
noncomputable abbrev geomToClosed (R : Type u) [CommRing R] [IsLocalRing R] (Ω : Type u)
    [Field Ω] [Algebra (ResidueField R) Ω] : geomObj R Ω ⟶ closedObj R :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R) Ω))) rfl

variable [IsLocalRing R] {Ω : Type u} [Field Ω] [Algebra (ResidueField R) Ω]

/-- Restriction from the closed point to a geometric point is bijective on morphisms into an étale
`S`-scheme, when the residue field is separably closed. -/
theorem over_geom_restrict_bijective [IsSepClosed (ResidueField R)]
    (X : Over (Spec (CommRingCat.of R))) [Etale X.hom] :
    Function.Bijective (fun g : closedObj R ⟶ X => geomToClosed R Ω ≫ g) := by
  constructor
  · intro g₁ g₂ h
    have h' : Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R) Ω)) ≫ g₁.left =
        Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R) Ω)) ≫ g₂.left := by
      have := congrArg (fun f => f.left) h
      simpa using this
    have hw₁ : g₁.left ≫ X.hom = closedPt R := by have h := Over.w g₁; exact h
    have hw₂ : g₂.left ≫ X.hom = closedPt R := by have h := Over.w g₂; exact h
    obtain ⟨y, -, hy⟩ := etale_sepClosed_relative_point_existsUnique (Ω := Ω) X.hom (closedPt R)
      (Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R) Ω)) ≫ g₁.left)
      (by rw [Category.assoc, hw₁])
    have e1 := hy g₁.left ⟨hw₁, rfl⟩
    have e2 := hy g₂.left ⟨hw₂, h'.symm⟩
    exact Over.OverMorphism.ext (e1.trans e2.symm)
  · intro h
    have hw : h.left ≫ X.hom =
        Spec.map (CommRingCat.ofHom (algebraMap (ResidueField R) Ω)) ≫ closedPt R := by
      have h' := Over.w h; exact h'
    obtain ⟨y, ⟨hy1, hy2⟩, -⟩ := etale_sepClosed_relative_point_existsUnique (Ω := Ω) X.hom
      (closedPt R) h.left hw
    refine ⟨Over.homMk y hy1, ?_⟩
    apply Over.OverMorphism.ext
    simpa using hy2

/-- **Residual and geometric `n`-torsion points of the closed fibre agree** (separably closed
residue field, `G[n]` étale). -/
theorem torsion_geom_bijective [IsSepClosed (ResidueField R)]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ) (hK : Etale (torsionKer G n).hom) :
    Function.Bijective (fun f : {f : closedObj R ⟶ G // f ^ n = 1} =>
      (⟨geomToClosed R Ω ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : geomObj R Ω ⟶ G // f ^ n = 1})) := by
  have hpre := over_geom_restrict_bijective (R := R) (Ω := Ω) (torsionKer G n)
  have hfun : (fun f : {f : closedObj R ⟶ G // f ^ n = 1} =>
      (⟨geomToClosed R Ω ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : geomObj R Ω ⟶ G // f ^ n = 1})) =
      (torsionKerHomEquiv G n (geomObj R Ω)) ∘ (fun g => geomToClosed R Ω ≫ g) ∘
        (torsionKerHomEquiv G n (closedObj R)).symm := by
    funext f
    apply Subtype.ext
    show geomToClosed R Ω ≫ f.1 =
      (geomToClosed R Ω ≫ (torsionKerHomEquiv G n _).symm f) ≫ torsionKerι G n
    rw [Category.assoc, ← torsionKerHomEquiv_apply G n (closedObj R)
      ((torsionKerHomEquiv G n _).symm f), Equiv.apply_symm_apply]
  rw [hfun]
  exact (Equiv.bijective _).comp (hpre.comp (Equiv.bijective _))

/-- **Integral and geometric `n`-torsion agree over a strictly henselian local ring**: restriction
`G(S)[n] → G(Spec Ω)[n]` along a geometric point of the closed fibre is bijective when `G[n] → S`
is étale. -/
theorem torsion_integral_geom_bijective [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ) (hK : Etale (torsionKer G n).hom) :
    Function.Bijective (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G // f ^ n = 1} =>
      (⟨toUnit (geomObj R Ω) ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : geomObj R Ω ⟶ G // f ^ n = 1})) := by
  have h1 := torsion_restrict_bijective_of_etale_ker G n hK
  have h2 := torsion_geom_bijective (Ω := Ω) G n hK
  have hfun : (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G // f ^ n = 1} =>
      (⟨toUnit (geomObj R Ω) ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : geomObj R Ω ⟶ G // f ^ n = 1})) =
      (fun f : {f : closedObj R ⟶ G // f ^ n = 1} =>
        (⟨geomToClosed R Ω ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
          {f : geomObj R Ω ⟶ G // f ^ n = 1})) ∘
      (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G // f ^ n = 1} =>
        (⟨toUnit (closedObj R) ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
          {f : closedObj R ⟶ G // f ^ n = 1})) := by
    funext f
    apply Subtype.ext
    show toUnit (geomObj R Ω) ≫ f.1 = geomToClosed R Ω ≫ toUnit (closedObj R) ≫ f.1
    rw [← Category.assoc, toUnit_unique (geomToClosed R Ω ≫ toUnit (closedObj R))
      (toUnit (geomObj R Ω))]
  rw [hfun]
  exact h2.comp h1

end HenselDivision

#check @HenselDivision.over_geom_restrict_bijective
#check @HenselDivision.torsion_geom_bijective
#check @HenselDivision.torsion_integral_geom_bijective
#print axioms HenselDivision.over_geom_restrict_bijective
#print axioms HenselDivision.torsion_geom_bijective
#print axioms HenselDivision.torsion_integral_geom_bijective
