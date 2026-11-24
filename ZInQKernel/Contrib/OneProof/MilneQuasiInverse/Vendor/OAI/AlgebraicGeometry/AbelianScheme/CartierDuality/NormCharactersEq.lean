/-
Vendored source provenance.
Upstream: https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/AlgebraicGeometry/AbelianScheme/CartierDuality/NormCharactersEq.lean
Revision: 4eaee87548250b2682affda7d05d947c05554bae
Git blob SHA-1: bce73e78700f482ddcbd354a3bc95aa6c653fb26
SHA-256: 834beed44e7298b8bdbbb772894dedaaf37f7a8ac3dd5ca596cdd08efd93a1a7
Adaptation: import and namespace relocation only; proof bodies preserved.
Modified for the Z-in-Q kernel (milne-compile): import paths and namespaces relocated; proof bodies unchanged.
-/
import Mathlib.RingTheory.Norm.Basic

/-! # Norm Characters Eq -/

namespace MilneQuasiInverse.Vendor.OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.NormCharactersEq.Construction.NormCharacters

noncomputable section

/-!
# CartierDuality: the norm calculation for finite-group exponents

An algebra automorphism preserves norms. If it multiplies a unit by a
base scalar, that scalar's power equal to the algebra rank is one.
-/

/-- The norm of a translated unit detects the finite-free rank exponent. -/
theorem scalar_pow_card_eq_one
    {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]
    (b : Module.Basis ι R A) (e : A ≃ₐ[R] A)
    (c : R) (x : A) (hx : IsUnit x) (he : e x = algebraMap R A c * x) :
    c ^ Fintype.card ι = 1 := by
  have h := Algebra.norm_eq_of_algEquiv e x
  rw [he, map_mul, Algebra.norm_algebraMap_of_basis b] at h
  have hu : IsUnit (Algebra.norm R x) := hx.map (Algebra.norm R)
  apply hu.mul_right_cancel
  simpa only [one_mul] using h

end

end MilneQuasiInverse.Vendor.OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.NormCharactersEq.Construction.NormCharacters
