import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitivePeterssonSlashTransport
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinGcdData

/-!
# Actual primitive Eisenstein/cusp Petersson orthogonality

For N≥3 and k≥3, the actual gcd-one Eisenstein modular forms are orthogonal
to every actual principal cusp form on a genuine principal fundamental domain.
The coprime rows use the produced absolutely integrable unfolding and actual
integral transport. Nonprimitive rows vanish by their empty gcd-one gamma set.
This is orthogonality, not a full-space decomposition or a spanning theorem.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set UpperHalfPlane Complex Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm ComplexConjugate

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

/-- All actual primitive Eisenstein forms pair to zero with all principal
cusps. No orthogonality, unfolding, integrability or decomposition premise. -/
theorem actual_primitive_eisenstein_petersson_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ)) :
    UpperHalfPlane.peterssonInner (k : ℤ) (principalDomain N) f
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a) = 0 := by
  by_cases ha : IsCoprime (a 0) (a 1)
  · exact coprime_primitive_eisenstein_petersson_zero N hN k hk a ha f
  · rw [ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinGcdData.eisensteinSeriesMF_eq_zero_nonprimitive
      (by exact_mod_cast hk : (3 : ℤ) ≤ k) a ha]
    exact UpperHalfPlane.peterssonInner_zero_right _ _ _

/-- The conjugate orientation of the same genuine orthogonality statement. -/
theorem actual_primitive_eisenstein_petersson_zero_left (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ)) :
    UpperHalfPlane.peterssonInner (k : ℤ) (principalDomain N)
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a) f = 0 := by
  rw [← UpperHalfPlane.peterssonInner_conj_symm,
    actual_primitive_eisenstein_petersson_zero N hN k hk a f,map_zero]

/-- Integrability and orthogonality are simultaneous actual outputs, excluding
the nonintegrable Bochner-default zero interpretation. -/
theorem actual_primitive_integrable_orthogonality (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ)) :
    IntegrableOn (UpperHalfPlane.petersson (k : ℤ) f
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a))
      (principalDomain N) volume ∧
    UpperHalfPlane.peterssonInner (k : ℤ) (principalDomain N) f
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a) = 0 :=
  ⟨primitive_pairing_integrable N k hk f a,actual_primitive_eisenstein_petersson_zero N hN k hk a f⟩

end ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson
