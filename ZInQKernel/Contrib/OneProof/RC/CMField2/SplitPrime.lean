import ZInQKernel.Contrib.OneProof.RC.CMField2.Integrality
import ZInQKernel.Contrib.OneProof.RC.CMField2.Kronecker
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassFields.RingClass.Field

/-! The local comparison needed for ring class field inclusion. This uses only
degree-one primes splitting completely in the ring class field. Provenance (c). -/

noncomputable section
open NumberField Module TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
open Polynomial ModularCurve

namespace ZInQ.Manuscript.RC.CMField2

/-- A lift of a singular modulus at a degree-one prime splitting completely
in the ring class field has Frobenius-fixed reduction. The splitting criterion
supplies the multiplier, and Kronecker on the diagonal supplies fixedness. -/
theorem singularModulus_reduction_pow_eq_of_split
    {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K) (κ : K →+* ℂ)
    (I : O.invertibleProperFractionalIdeals) (p : ℕ) [Fact p.Prime]
    (J : integralIdealsPrimeTo O.conductorModulus) [(J : Ideal (𝓞 K)).IsMaximal]
    (hdegree : Ideal.absNorm (J : Ideal (𝓞 K)) = p)
    (hsplit : ((J : Ideal (𝓞 K)).primesOver (𝓞 (ringClassField O))).ncard =
      Module.finrank K (ringClassField O))
    {A k : Type} [CommRing A] [Field k] [CharP k p]
    (ι : A →+* ℂ) (hι : Function.Injective ι) (r : A →+* k)
    (x : A) (hx : ι x = singularModulus O hk hc κ I) :
    (r x) ^ p = r x := by
  obtain ⟨β, hβ, hspan⟩ := (ncard_primesOver_ringClassField_eq_finrank_iff O J).mp hsplit
  obtain ⟨D⟩ := nonempty_modularPolynomialData p
  have hnorm : Complex.normSq (κ (β : K)) = (p : ℝ) := by
    rw [← cast_absNorm_span_singleton_complex hk hc κ β, ← hspan, hdegree]
  have heq := prime_diagonal_eq_of_order_multiplier O hk hc κ I p D
    (β : K) (O.mem_toRingOfIntegers.mp hβ) hnorm
  let P := D.Φ.eval₂ (RingHom.id ℤ[X]) X
  change P.eval₂ (Int.castRingHom ℂ) (singularModulus O hk hc κ I) = 0 at heq
  have hp : P.eval₂ (Int.castRingHom A) x = 0 := by
    apply hι
    rw [hom_eval₂, map_zero, hx,
      show ι.comp (Int.castRingHom A) = Int.castRingHom ℂ from Subsingleton.elim _ _]
    exact heq
  have hr := congrArg r hp
  rw [hom_eval₂, map_zero,
    show r.comp (Int.castRingHom A) = Int.castRingHom k from Subsingleton.elim _ _] at hr
  apply pow_eq_of_modularPolynomial_diagonal_root p D
  rw [← eval_diagonal]
  exact hr


end ZInQ.Manuscript.RC.CMField2
