import hecke.GoodHeckeComponent
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.EigenFromPrimes

/-!
# A bundled good Hecke eigenform in the original rational translate orbit

The joint component is bundled only after its actual prime eigenvector equations
and nonvanishing have been proved. No newness, first-coefficient normalization,
or special-value nonvanishing is asserted.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane HeckeRing.GL2
open scoped MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.ReverseHecke

/-- The rational-translate cusp submodule is finite-dimensional as an actual cusp submodule. -/
theorem cuspOrbit_finite (L : ℕ) [NeZero L] (k : ℤ) (f : ℍ → ℂ) :
    Module.Finite ℂ (cuspOrbit L k f) := inferInstance

/-- The orbit in one actual nebentypus space is finite-dimensional without an orbit hypothesis. -/
theorem characterOrbit_finite (L : ℕ) [NeZero L] (k : ℤ)
    (χ : (ZMod L)ˣ →* ℂˣ) (f : ℍ → ℂ) :
    Module.Finite ℂ (characterOrbit L k χ f) := inferInstance

/-- A nonzero principal cusp form produces an actual good Hecke eigenform in its finite
positive-rational translate orbit. This eigenform need not be new or normalized. -/
theorem principal_goodEigenform_rational_translates (N : ℕ) [NeZero N]
    (k : ℕ) (hk : 2 ≤ k)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) (k : ℤ)) (hf : f ≠ 0) :
    ∃ E : EigenformAwayFromLevel (N ^ 2) (k : ℤ),
      E.toCuspForm ≠ 0 ∧
        ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ α : Fin m → GL (Fin 2) ℚ,
          (∀ i, 0 < (α i : Matrix (Fin 2) (Fin 2) ℚ).det) ∧
            ⇑E.toCuspForm = ∑ i, c i •
              (⇑f ∣[(k : ℤ)] GeneralLinearGroup.map (algebraMap ℚ ℝ) (α i)) := by
  obtain ⟨χ, F, hF0, hFχ, ⟨a, heig⟩, m, c, α, hα, hrep⟩ :=
    principal_goodHecke_component N k hk f hf
  have hprime : ∀ p : ℕ, p.Prime → p.Coprime (N ^ 2) → ∃ b : ℂ,
      heckeRingHomCuspCharSpace (k : ℤ) χ (heckeTGeneratorGamma0 (N ^ 2) p)
        ⟨F, hFχ⟩ = b • ⟨F, hFχ⟩ := by
    intro p hp hpL
    refine ⟨a ⟨p, hp, hpL⟩, Subtype.ext ?_⟩
    rw [coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 (k : ℤ) χ hp,
      Submodule.coe_smul]
    exact heig p hp hpL
  let E := EigenformAwayFromLevel.ofForallPrime hFχ hF0 hprime
  refine ⟨E, E.ne_zero, m, c, α, hα, ?_⟩
  simpa only [E, EigenformAwayFromLevel.ofForallPrime_toCuspForm] using hrep

end ZInQ.Contrib.HeckePrimeRationality.ReverseHecke
