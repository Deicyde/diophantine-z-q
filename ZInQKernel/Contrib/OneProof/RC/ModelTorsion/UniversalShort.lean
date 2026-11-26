import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.AffineAlgebra
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # The universal short Weierstrass locus -/

namespace WeierstrassCurve.ModelTorsion

/-- The short Weierstrass equation with independent coefficients in variables
`0` and `1`, respectively. -/
noncomputable def shortEquation (R : Type*) [CommRing R] :
    WeierstrassCurve (MvPolynomial (Fin 2) R) :=
  ⟨0, 0, 0, MvPolynomial.X 0, MvPolynomial.X 1⟩

/-- The coefficient ring of the universal short Weierstrass locus. -/
abbrev ShortBase (R : Type*) [CommRing R] :=
  Localization.Away (shortEquation R).Δ

/-- The universal short Weierstrass equation with its discriminant inverted. -/
noncomputable def shortFamily (R : Type*) [CommRing R] :
    WeierstrassCurve (ShortBase R) :=
  (shortEquation R).map (algebraMap (MvPolynomial (Fin 2) R) (ShortBase R))

instance (R : Type*) [CommRing R] : (shortFamily R).IsElliptic := by
  constructor
  rw [shortFamily, WeierstrassCurve.map_Δ]
  exact IsLocalization.Away.algebraMap_isUnit (shortEquation R).Δ

/-- The prime ideal used to localize the rational integers. -/
def integerPrimeIdeal (l : ℕ) : Ideal ℤ := Ideal.span {(l : ℤ)}

instance (l : ℕ) [h : Fact l.Prime] : (integerPrimeIdeal l).IsPrime :=
  (Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr h.out.ne_zero)).2
    (Nat.prime_iff_prime_int.mp h.out)

/-- The coefficient DVR at the detecting prime. -/
abbrev LocalIntegers (l : ℕ) [Fact l.Prime] :=
  Localization.AtPrime (integerPrimeIdeal l)

/-- The affine torsion algebra of the universal short curve over
`ℤ` localized at `l`. The same result applies to the two levels `N`
and `p` of the moduli construction. -/
theorem universalAffineTorsion_finite_etale (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : ¬ l ∣ n) :
    let R := LocalIntegers l
    let W := shortFamily R
    Module.Finite (ShortBase R) (AffineTorsionAlgebra W n) ∧
      Module.Free (ShortBase R) (AffineTorsionAlgebra W n) ∧
        Algebra.Etale (ShortBase R) (AffineTorsionAlgebra W n) := by
  let R := LocalIntegers l
  have hmem : (n : ℤ) ∈ (integerPrimeIdeal l).primeCompl := by
    change (n : ℤ) ∉ Ideal.span {(l : ℤ)}
    simpa [Ideal.mem_span_singleton, Int.natCast_dvd] using hn
  have hu : IsUnit (n : R) := by
    simpa using IsLocalization.map_units R ⟨(n : ℤ), hmem⟩
  have hu' : IsUnit (n : MvPolynomial (Fin 2) R) := by
    simpa using hu.map (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R)
  exact affineTorsionAlgebra_finite_etale (shortFamily R)
    (by simpa using hu'.map (algebraMap (MvPolynomial (Fin 2) R) (ShortBase R)))

#print axioms universalAffineTorsion_finite_etale

end WeierstrassCurve.ModelTorsion
