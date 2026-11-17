import ZInQKernel.Contrib.OneProof.CoeffRational
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelHeckeFromProducts
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.LowLevels

/-!
# Reduction of the original Hecke leaf to principal torsion-product spanning

The spanning property below is the genuine remaining producer. It concerns
actual principal-level modular forms of weight at least two, and remains an
explicit hypothesis of the reduction theorem. It is not proved here.

The reduction retains the original unrestricted levels, integer weights,
actual cusp forms and Hecke operator. The separately proved low levels cover
small N; a nonnegative integer-weight cast connects the remaining cases to
the actual homogeneous products. No original global hypothesis is discharged.
-/

noncomputable section
set_option autoImplicit false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality

/-- Principal torsion-product spanning at the original level. This is an
unproved producer property, not an axiom or a theorem supplied by this file. -/
def PrincipalProductSpanning : Prop :=
  ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ k : ℕ, 2 ≤ k →
    ∀ f : _root_.ModularForm ((Gamma N).map (mapGL ℝ)) (k : ℤ),
      ∃ m : ℕ, ∃ v : Fin m → Fin k → ℤ × ℤ,
        ∃ hv : ∀ j i, AllLevelForms.Good N (v j i), ∃ c : Fin m → ℂ,
          f = ∑ j, c j • AllLevelProducts.productForm N (NeZero.pos N) k (v j) (hv j)

/-- If the actual principal product-spanning producer is proved, the exact
original all-level Hecke leaf follows. The producer hypothesis is not removed. -/
theorem heckePrimeIntegralToRational_of_principalProductSpanning
    (hSpan : PrincipalProductSpanning) : CoeffRational.HeckePrimeIntegralToRational := by
  intro N _ k p g hk hp hgood hg
  by_cases hN : N ≤ 6
  · exact integral_input_hecke_rational_le_six N k p g hN hk hp hgood hg
  · have hk0 : 0 ≤ k := by omega
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    have hn : 2 ≤ n := by exact_mod_cast hk
    let f : _root_.ModularForm ((Gamma N).map (mapGL ℝ)) (n : ℤ) :=
      _root_.ModularForm.restrict (Subgroup.map_mono (Gamma_le_Gamma1 N))
        (g : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) (n : ℤ))
    obtain ⟨m, v, hv, c, hRep⟩ := hSpan N (by omega) n hn f
    exact AllLevelHeckeFromProducts.integral_input_hecke_rational_of_product_representation
      n hp g hg v hv c hRep

end ZInQ.Contrib.HeckePrimeRationality
