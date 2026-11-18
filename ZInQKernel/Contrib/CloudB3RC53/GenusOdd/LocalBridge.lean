import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalCompare
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalCommon

/-!
# GenusOdd: the local polynomials of `LocalFactorK` as local polynomials of rational models (PROVED)

* `localPolyQ_eq`, `localPolyK_eq`: `L_p(E)` and `L_𝔭(E/K)` are the local polynomials of `E` mapped
  along `ℚ → ℚ_v` and `ℚ → K → K_𝔭`;
* `localPolynomial_map_smul`: replacing `E` by `C₀ • E` for a rational change of variables `C₀`
  does not change them;
* `ringEquivOfCard`: residue fields with `p` elements are isomorphic, of characteristic `p`.
-/

noncomputable section

open NumberField IsDedekindDomain WeierstrassCurve

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- `ℚ → K → K_𝔭`. -/
def iotaK {K : Type} [Field K] [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ℚ →+* 𝔭.adicCompletion K :=
  (algebraMap K (𝔭.adicCompletion K)).comp (algebraMap ℚ K)

/-- `L_p(E)` through `ℚ → ℚ_v` (PROVED, definitional). -/
theorem localPolyQ_eq (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    localPolyQ E v = (E.map (algebraMap ℚ (v.adicCompletion ℚ))).localPolynomial
      (v.adicCompletionIntegers ℚ) := rfl

/-- `L_𝔭(E/K)` through `ℚ → K → K_𝔭` (PROVED). -/
theorem localPolyK_eq (E : WeierstrassCurve ℚ) {K : Type} [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    localPolyK E 𝔭 = (E.map (iotaK 𝔭)).localPolynomial (𝔭.adicCompletionIntegers K) := by
  rw [localPolyK, iotaK, baseChange, baseChange, map_map]

/-- A rational change of variables does not change the local polynomial (PROVED). -/
theorem localPolynomial_map_smul {F : Type*} [Field F] {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra R F] [IsFractionRing R F] (ι : ℚ →+* F)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (C₀ : VariableChange ℚ) :
    ((C₀ • E).map ι).localPolynomial R = (E.map ι).localPolynomial R := by
  rw [← map_variableChange]
  apply ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_smul
  rw [map_Δ]
  exact (map_ne_zero ι).mpr E.isUnit_Δ.ne_zero

/-- Two finite rings with `p` elements are isomorphic (PROVED). -/
def ringEquivOfCard {A B : Type*} [CommRing A] [CommRing B] {p : ℕ} (hp : p.Prime)
    [Finite A] [Finite B] (hA : Nat.card A = p) (hB : Nat.card B = p) : A ≃+* B :=
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite B
  (ZMod.ringEquivOfPrime A hp (by rw [Fintype.card_eq_nat_card, hA])).symm.trans
    (ZMod.ringEquivOfPrime B hp (by rw [Fintype.card_eq_nat_card, hB]))

/-- A finite ring with `p` elements has characteristic `p` (PROVED). -/
theorem charP_of_natCard {A : Type*} [CommRing A] {p : ℕ} [Fact p.Prime] [Finite A]
    (hA : Nat.card A = p) : CharP A p :=
  letI := Fintype.ofFinite A
  charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card, hA])

end ZInQ.Contrib.CloudB3RC53.GenusOdd
