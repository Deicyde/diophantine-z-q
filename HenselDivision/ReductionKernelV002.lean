import HenselDivision.SmoothCommTorsionV001

/-!
# Prime-to-the-residue-characteristic torsion injects under reduction

For a smooth commutative group scheme `G` over a henselian local ring `R` and `n` invertible in `R`,
an integral point `f ∈ G(R)` with `f^n = 1` whose restriction to the closed point (or, for
separably closed residue field, to a geometric point of the closed fibre) is trivial is itself
trivial. The same holds for a smooth Néron-type model, whose commutativity is derived from the
generic fibre and the mapping-property uniqueness.

Edition V002: the restriction equalities are stated in beta-reduced form before rewriting;
statements as in V001.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  IsLocalRing
open scoped MonObj

namespace HenselDivision

variable {R : Type} [CommRing R] [HenselianLocalRing R]

/-- **Reduction is injective on `n`-torsion** (`n` a unit, `G` smooth commutative). -/
theorem reduction_torsion_injective (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [Smooth G.hom] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : R))
    (f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) (hf : f ^ n = 1)
    (h1 : toUnit (closedObj R) ≫ f = 1) : f = 1 := by
  have hb := torsion_restrict_bijective_of_smooth_comm G n hn
  have := hb.1 (a₁ := ⟨f, hf⟩) (a₂ := ⟨1, one_pow n⟩)
    (Subtype.ext (by
      show toUnit (closedObj R) ≫ f = toUnit (closedObj R) ≫ 1
      rw [h1, MonObj.comp_one]))
  exact congrArg Subtype.val this

/-- **Geometric reduction is injective on `n`-torsion** over a strictly henselian base. -/
theorem geom_reduction_torsion_injective [IsSepClosed (ResidueField R)] {Ω : Type} [Field Ω]
    [Algebra (ResidueField R) Ω] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [Smooth G.hom] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : R))
    (f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) (hf : f ^ n = 1)
    (h1 : toUnit (geomObj R Ω) ≫ f = 1) : f = 1 := by
  have hb := torsion_integral_geom_bijective_of_smooth_comm (Ω := Ω) G n hn
  have := hb.1 (a₁ := ⟨f, hf⟩) (a₂ := ⟨1, one_pow n⟩)
    (Subtype.ext (by
      show toUnit (geomObj R Ω) ≫ f = toUnit (geomObj R Ω) ≫ 1
      rw [h1, MonObj.comp_one]))
  exact congrArg Subtype.val this

/-- **Néron-type form.** -/
theorem reduction_torsion_injective_of_generic_injective {S' : Scheme.{0}}
    (j : S' ⟶ Spec (CommRingCat.of R)) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [Smooth G.hom] (A : Over S') [GrpObj A] [IsCommMonObj A]
    (e : (Over.pullback j).obj G ≅ A)
    (he : letI : GrpObj ((Over.pullback j).obj G) := Functor.grpObjObj
      IsMonHom e.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
      Function.Injective fun f : Y ⟶ G => (Over.pullback j).map f ≫ e.hom)
    (n : ℕ) (hn : IsUnit (n : R)) (f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G)
    (hf : f ^ n = 1) (h1 : toUnit (closedObj R) ≫ f = 1) : f = 1 := by
  obtain ⟨hc, hE⟩ := etale_powHom_of_generic_injective j G A e he hN n hn
  have hb := torsion_restrict_bijective G n hE
  have := hb.1 (a₁ := ⟨f, hf⟩) (a₂ := ⟨1, one_pow n⟩)
    (Subtype.ext (by
      show toUnit (closedObj R) ≫ f = toUnit (closedObj R) ≫ 1
      rw [h1, MonObj.comp_one]))
  exact congrArg Subtype.val this

end HenselDivision

#print axioms HenselDivision.reduction_torsion_injective
#print axioms HenselDivision.geom_reduction_torsion_injective
#print axioms HenselDivision.reduction_torsion_injective_of_generic_injective
