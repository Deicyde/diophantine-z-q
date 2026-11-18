import HenselDivision.TorsionTowerV002
import HenselDivision.GenericCommutativityV004
import HenselDivision.T4HenselStatementsV001

/-!
# Torsion specialization from étaleness of the torsion scheme alone, and an axiom audit

`torsion_restrict_bijective_of_etale_ker` needs only that the torsion scheme `G[n] → S` is étale
(which follows from, but is weaker than, étaleness of `[n]` on all of `G`). The remaining lines
print the axioms of every main statement of this development.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  IsLocalRing
open scoped MonObj

namespace HenselDivision

universe u

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- **Integral and residual `n`-torsion points agree** when `G[n] → S` is étale. -/
theorem torsion_restrict_bijective_of_etale_ker (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (n : ℕ) (hK : Etale (torsionKer G n).hom) :
    Function.Bijective (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G // f ^ n = 1} =>
      (⟨toUnit (closedObj R) ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : closedObj R ⟶ G // f ^ n = 1})) := by
  have hpre := over_restrict_bijective (R := R) (torsionKer G n)
  have hfun : (fun f : {f : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G // f ^ n = 1} =>
      (⟨toUnit (closedObj R) ≫ f.1, by rw [← MonObj.comp_pow, f.2, MonObj.comp_one]⟩ :
        {f : closedObj R ⟶ G // f ^ n = 1})) =
      (torsionKerHomEquiv G n (closedObj R)) ∘ (fun g => toUnit (closedObj R) ≫ g) ∘
        (torsionKerHomEquiv G n (𝟙_ _)).symm := by
    funext f
    apply Subtype.ext
    show toUnit (closedObj R) ≫ f.1 =
      (toUnit (closedObj R) ≫ (torsionKerHomEquiv G n _).symm f) ≫ torsionKerι G n
    rw [Category.assoc, ← torsionKerHomEquiv_apply G n (𝟙_ (Over (Spec (CommRingCat.of R))))
      ((torsionKerHomEquiv G n _).symm f), Equiv.apply_symm_apply]
  rw [hfun]
  exact (Equiv.bijective _).comp (hpre.comp (Equiv.bijective _))

end HenselDivision

#print axioms HenselDivision.etale_existsUnique_lift
#print axioms HenselDivision.etale_section_existsUnique
#print axioms HenselDivision.etale_section_restrict_bijective
#print axioms HenselDivision.torsionKerHomEquiv
#print axioms HenselDivision.isClosedImmersion_torsionKerι
#print axioms HenselDivision.etale_torsionKer_hom
#print axioms HenselDivision.over_restrict_bijective
#print axioms HenselDivision.torsion_restrict_bijective
#print axioms HenselDivision.torsion_restrict_bijective_of_etale_ker
#print axioms HenselDivision.torsionRestrictEquiv
#print axioms HenselDivision.etale_powHom_pow
#print axioms HenselDivision.compatible_lift_existsUnique
#print axioms HenselDivision.isCommMonObj_of_map_injective
#print axioms HenselDivision.isCommMonObj_of_generic_injective
#print axioms HenselDivision.stacksHenselEtaleSection_proof
#print axioms HenselDivision.henselEtaleLift_proof
