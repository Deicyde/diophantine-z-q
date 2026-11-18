import HenselDivision.StrictTorsionV001

/-!
# Geometric `ℓ`-power torsion towers lift to integral towers (strictly henselian base)

`R` henselian local with separably closed residue field `k`, `Ω ⊇ k` a field, `G` a group scheme
over `Spec R` with `[ℓ]` étale. Every compatible system `x_n` of geometric torsion points of the
closed fibre (`x_0 = 1`, `x_{n+1}^ℓ = x_n`, points `Spec Ω → G` over `Spec Ω → Spec k → Spec R`)
is the restriction of a unique compatible system of integral points `f_n ∈ G(Spec R)`. At each
level the lift is the unique point given by Hensel lifting on the étale torsion scheme `G[ℓ^n]`
and rationality over `k`; compatibility of the lifts follows from uniqueness one level down.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  IsLocalRing
open scoped MonObj

namespace HenselDivision

universe u

variable {R : Type u} [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)]
  {Ω : Type u} [Field Ω] [Algebra (ResidueField R) Ω]

/-- **Unique integral lift of a compatible geometric torsion tower.** -/
theorem compatible_geom_lift_existsUnique (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (ℓ : ℕ) (hℓ : Etale (powHom G ℓ).left) (x : ℕ → (geomObj R Ω ⟶ G)) (hx0 : x 0 = 1)
    (hx : ∀ n, x (n + 1) ^ ℓ = x n) :
    ∃! f : ℕ → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G),
      f 0 = 1 ∧ (∀ n, f (n + 1) ^ ℓ = f n) ∧ ∀ n, toUnit (geomObj R Ω) ≫ f n = x n := by
  have hxt := pow_pow_eq_one_of_tower ℓ x hx0 hx
  have B : ∀ n, _ := fun n => torsion_integral_geom_bijective (Ω := Ω) G (ℓ ^ n)
    (etale_torsionKer_hom G (ℓ ^ n) (etale_powHom_pow G ℓ hℓ n))
  have uniq : ∀ n (g g' : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G), g ^ (ℓ ^ n) = 1 →
      g' ^ (ℓ ^ n) = 1 → toUnit (geomObj R Ω) ≫ g = toUnit (geomObj R Ω) ≫ g' → g = g' := by
    intro n g g' hg hg' h
    have := (B n).1 (a₁ := ⟨g, hg⟩) (a₂ := ⟨g', hg'⟩) (Subtype.ext h)
    exact congrArg Subtype.val this
  choose F hF using fun n => (B n).2 ⟨x n, hxt n⟩
  let f : ℕ → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) := fun n => (F n).1
  have hfres : ∀ n, toUnit (geomObj R Ω) ≫ f n = x n := fun n => congrArg Subtype.val (hF n)
  have hft : ∀ n, f n ^ (ℓ ^ n) = 1 := fun n => (F n).2
  have hf0 : f 0 = 1 := by
    have := hft 0
    rwa [pow_zero, pow_one] at this
  have hfs : ∀ n, f (n + 1) ^ ℓ = f n := by
    intro n
    apply uniq n
    · rw [← pow_mul, ← pow_succ']; exact hft (n + 1)
    · exact hft n
    · rw [MonObj.comp_pow, hfres, hfres, hx]
  refine ⟨f, ⟨hf0, hfs, hfres⟩, ?_⟩
  rintro f' ⟨h0, hs, hres⟩
  funext n
  apply uniq n
  · exact pow_pow_eq_one_of_tower ℓ f' h0 hs n
  · exact hft n
  · rw [hres, hfres]

end HenselDivision

#check @HenselDivision.compatible_geom_lift_existsUnique
#print axioms HenselDivision.compatible_geom_lift_existsUnique
