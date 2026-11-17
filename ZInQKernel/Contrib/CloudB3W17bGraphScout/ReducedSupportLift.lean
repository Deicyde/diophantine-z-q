import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
The algebraic factorization edge after (not before) an actual Zariski-closed
support has been constructed. This does not turn a closed analytic subset into
such a support. It is a private scout prototype, not GAGA.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGraphScout

/-- A morphism from a reduced scheme into a genuinely Zariski-closed set factors
through its reduced closed subscheme. The Zariski closed set is an explicit input. -/
theorem exists_lift_reducedClosed_of_range_subset
    {X Y : Scheme} [IsReduced X] (Z : Closeds Y) (f : X ⟶ Y)
    (hf : Set.range f ⊆ (Z : Set Y)) :
    ∃ g : X ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      g ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = f := by
  have hclosure : Closeds.closure (f '' (⊤ : Closeds X)) ≤ Z := by
    rw [Closeds.closure_le]
    simpa only [Closeds.coe_top, Set.image_univ] using hf
  have hI : Scheme.IdealSheafData.vanishingIdeal Z ≤ f.ker := by
    calc
      Scheme.IdealSheafData.vanishingIdeal Z ≤
          Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (f '' (⊤ : Closeds X))) :=
        Scheme.IdealSheafData.vanishingIdeal_antimono hclosure
      _ = (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).map f :=
        (Scheme.IdealSheafData.map_vanishingIdeal f (⊤ : Closeds X)).symm
      _ = f.ker := by
        simp only [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
          Scheme.IdealSheafData.map_bot]
  let g := IsClosedImmersion.lift
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι f (by simpa only
      [Scheme.IdealSheafData.ker_subschemeι] using hI)
  exact ⟨g, IsClosedImmersion.lift_fac _ _ _⟩

end ZInQ.Contrib.CloudB3W17bGraphScout
