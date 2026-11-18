import HenselDivision.ValuationStrictHenselV003
import HenselDivision.SmoothCommTorsionV001
import HenselDivision.ReductionKernelV002

/-!
# Torsion specialization over a valuation subring of an algebraically closed field

`Ω` algebraically closed, `w` any valuation subring of `Ω` (not necessarily discrete), `G` a smooth
commutative group scheme over `Spec w`, `n` (or `ℓ`) invertible in `w`. With the henselian property
of `w` and the separable closedness of `κ(w)` derived in `ValuationStrictHenselV003`, the torsion
specialization results hold with no strict-henselian hypothesis:
integral `n`-torsion is residual `n`-torsion (as groups), is geometric `n`-torsion over any field
`Ω' ⊇ κ(w)`, reduction is injective on `n`-torsion, and compatible geometric `ℓ`-power towers lift
uniquely to integral towers.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  IsLocalRing
open scoped MonObj

namespace HenselDivision

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] (w : ValuationSubring Ω)

theorem valuation_torsion_restrict_bijective (G : Over (Spec (CommRingCat.of w))) [GrpObj G]
    [Smooth G.hom] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : w)) :
    Function.Bijective (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of w))) ⟶ G // f ^ n = 1} =>
      (⟨toUnit (closedObj w) ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : closedObj w ⟶ G // f ^ n = 1})) := by
  haveI := henselianLocalRing_of_isAlgClosed w
  exact torsion_restrict_bijective_of_smooth_comm G n hn

/-- `G(w)[n] ≃* G(κ(w))[n]`. -/
noncomputable def valuationTorsionRestrictEquiv (G : Over (Spec (CommRingCat.of w))) [GrpObj G]
    [Smooth G.hom] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : w)) :
    torsionPts G (𝟙_ (Over (Spec (CommRingCat.of w)))) n ≃* torsionPts G (closedObj w) n :=
  haveI := henselianLocalRing_of_isAlgClosed w
  torsionRestrictEquivOfSmoothComm G n hn

theorem valuation_torsion_integral_geom_bijective {Ω' : Type} [Field Ω']
    [Algebra (ResidueField w) Ω'] (G : Over (Spec (CommRingCat.of w))) [GrpObj G]
    [Smooth G.hom] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : w)) :
    Function.Bijective (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of w))) ⟶ G // f ^ n = 1} =>
      (⟨toUnit (geomObj w Ω') ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : geomObj w Ω' ⟶ G // f ^ n = 1})) := by
  haveI := henselianLocalRing_of_isAlgClosed w
  haveI := isSepClosed_residueField w
  exact torsion_integral_geom_bijective_of_smooth_comm G n hn

theorem valuation_reduction_torsion_injective (G : Over (Spec (CommRingCat.of w))) [GrpObj G]
    [Smooth G.hom] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : w))
    (f : 𝟙_ (Over (Spec (CommRingCat.of w))) ⟶ G) (hf : f ^ n = 1)
    (h1 : toUnit (closedObj w) ≫ f = 1) : f = 1 := by
  haveI := henselianLocalRing_of_isAlgClosed w
  exact reduction_torsion_injective G n hn f hf h1

theorem valuation_compatible_geom_lift_existsUnique {Ω' : Type} [Field Ω']
    [Algebra (ResidueField w) Ω'] (G : Over (Spec (CommRingCat.of w))) [GrpObj G]
    [Smooth G.hom] [IsCommMonObj G] (ℓ : ℕ) (hℓ : IsUnit (ℓ : w))
    (x : ℕ → (geomObj w Ω' ⟶ G)) (hx0 : x 0 = 1) (hx : ∀ n, x (n + 1) ^ ℓ = x n) :
    ∃! f : ℕ → (𝟙_ (Over (Spec (CommRingCat.of w))) ⟶ G),
      f 0 = 1 ∧ (∀ n, f (n + 1) ^ ℓ = f n) ∧ ∀ n, toUnit (geomObj w Ω') ≫ f n = x n := by
  haveI := henselianLocalRing_of_isAlgClosed w
  haveI := isSepClosed_residueField w
  exact compatible_geom_lift_existsUnique_of_smooth_comm G ℓ hℓ x hx0 hx

end HenselDivision

#print axioms HenselDivision.valuation_torsion_restrict_bijective
#print axioms HenselDivision.valuationTorsionRestrictEquiv
#print axioms HenselDivision.valuation_torsion_integral_geom_bijective
#print axioms HenselDivision.valuation_reduction_torsion_injective
#print axioms HenselDivision.valuation_compatible_geom_lift_existsUnique
