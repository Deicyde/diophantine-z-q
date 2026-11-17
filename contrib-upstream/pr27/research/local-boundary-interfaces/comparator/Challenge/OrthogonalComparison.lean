import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.Abel

/-!
# Orthogonal comparison preserves the actual global cohomology class

The degreewise mapping-fibre calculation uses the H22 convention. The homotopy
lemmas use Mathlib's actual HomologicalComplex and homology maps. The continuous
Galois Selmer application is supplied in the source-bound note, not defined by
this module. No boundary-cup adjunction, functional normalization or determinant
comparison is a premise or conclusion here. The frozen 39 sources are unchanged.
-/
namespace Research.DerivativeSwitch.OrthogonalComparison

section Fibre
variable {G₀ G₁ U₀ U₁ V₀ V₁ L₀ L₁ : Type*}
  [AddCommGroup G₀] [AddCommGroup G₁] [AddCommGroup U₀] [AddCommGroup U₁]
  [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup L₀] [AddCommGroup L₁]

/-- One degree of the H22 mapping-fibre differential: L has degree one less. -/
def fibreD (dG : G₀ →+ G₁) (dU : U₀ →+ U₁) (dL : L₀ →+ L₁)
    (loc : G₀ →+ L₁) (inc : U₀ →+ L₁) (z : G₀ × U₀ × L₀) :
    G₁ × U₁ × L₁ :=
  (dG z.1, dU z.2.1, loc z.1 - inc z.2.1 - dL z.2.2)

/-- Comparison induced by local maps and their inclusion homotopy. -/
def fibreComparison (a : U₀ →+ V₀) (h : U₀ →+ L₀)
    (z : G₀ × U₀ × L₀) : G₀ × V₀ × L₀ :=
  (z.1, a z.2.1, z.2.2 + h z.2.1)

/-- The inclusion homotopy constructs the chain map with the indicated sign. -/
theorem fibreComparison_commutes
    (dG : G₀ →+ G₁) (dU : U₀ →+ U₁) (dV : V₀ →+ V₁)
    (dL : L₀ →+ L₁) (loc : G₀ →+ L₁)
    (inc : U₀ →+ L₁) (inc' : V₀ →+ L₁)
    (a₀ : U₀ →+ V₀) (a₁ : U₁ →+ V₁)
    (h₀ : U₀ →+ L₀) (h₁ : U₁ →+ L₁)
    (ha : ∀ u, dV (a₀ u) = a₁ (dU u))
    (hh : ∀ u, inc u - inc' (a₀ u) = dL (h₀ u) + h₁ (dU u))
    (z : G₀ × U₀ × L₀) :
    fibreD dG dV dL loc inc' (fibreComparison a₀ h₀ z) =
      fibreComparison a₁ h₁ (fibreD dG dU dL loc inc z) := by
  sorry

omit [AddCommGroup G₀] in
@[simp]
theorem fibreComparison_global (a : U₀ →+ V₀) (h : U₀ →+ L₀)
    (z : G₀ × U₀ × L₀) : (fibreComparison a h z).1 = z.1 := by
  sorry

omit [AddCommGroup G₀] in
/-- The Nekovar local coordinate is the negative of H22's q-coordinate. -/
theorem fibreComparison_sign_change (a : U₀ →+ V₀) (h : U₀ →+ L₀)
    (g : G₀) (u : U₀) (l : L₀) :
    -(fibreComparison a h (g, u, -l)).2.2 = l - h u := by
  sorry
end Fibre

section Homology
open CategoryTheory Category
open HomologicalComplex
universe v u
variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V]
  {c : ComplexShape ι} {C D G L : HomologicalComplex V c}

/-- The constructed comparison preserves global projection, so any right
homotopy inverse preserves it up to the induced homotopy. -/
def inverse_preserves_global_homotopy
    (j : C ⟶ D) (k : D ⟶ C) (p : C ⟶ G) (q : D ⟶ G)
    (hj : j ≫ q = p) (hk : Homotopy (k ≫ j) (𝟙 D)) :
    Homotopy (k ≫ p) q := by
  sorry

/-- Equality of Mathlib's genuine homology maps. -/
theorem inverse_preserves_global_homology
    (j : C ⟶ D) (k : D ⟶ C) (p : C ⟶ G) (q : D ⟶ G)
    (hj : j ≫ q = p) (hk : Homotopy (k ≫ j) (𝟙 D))
    (i : ι) [D.HasHomology i] [G.HasHomology i] :
    homologyMap (k ≫ p) i = homologyMap q i := by
  sorry

/-- Localization is a chain map from the common global complex. -/
def inverse_preserves_local_homotopy
    (j : C ⟶ D) (k : D ⟶ C) (p : C ⟶ G) (q : D ⟶ G)
    (hj : j ≫ q = p) (hk : Homotopy (k ≫ j) (𝟙 D)) (loc : G ⟶ L) :
    Homotopy ((k ≫ p) ≫ loc) (q ≫ loc) := by
  sorry

/-- Every localized cohomology class, including derivative H1, is preserved. -/
theorem inverse_preserves_local_homology
    (j : C ⟶ D) (k : D ⟶ C) (p : C ⟶ G) (q : D ⟶ G)
    (hj : j ≫ q = p) (hk : Homotopy (k ≫ j) (𝟙 D)) (loc : G ⟶ L)
    (i : ι) [D.HasHomology i] [L.HasHomology i] :
    homologyMap ((k ≫ p) ≫ loc) i = homologyMap (q ≫ loc) i := by
  sorry
end Homology
end Research.DerivativeSwitch.OrthogonalComparison
