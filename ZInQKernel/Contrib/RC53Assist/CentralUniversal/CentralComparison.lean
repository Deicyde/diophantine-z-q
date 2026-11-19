import ZInQKernel.Contrib.RC53Assist.CentralUniversal.Arithmetic

/-!
# The central comparison with the constructed universal-coefficient map

Both the rational Kummer complex and the quadratic Selmer group are fixed to
those of the specified curve over the specified quadratic field. The rational
coordinates and the divisible-group map are constructed from the actual
integral free-part basis. The only model-side input is the retained cochain
comparison with the specialized matrix model.
-/

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Manuscript.RC53Assist.CentralUniversal

open CategoryTheory Matrix NumberField IsDedekindDomain
open ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Manuscript.RC53Assist.QuadraticDescent
open ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.BaseZeroLimit
open ZInQ.Manuscript.RC.CoefModules

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic]
  (hk : ¬ IsSquare (k : ℚ))
  (S : Set (HeightOneSpectrum (𝓞 (QuadraticField k))))
  (hFull : ∀ n : ℕ, FullTorsion (QuadraticField k) S
    ((Ecurve ℓ).baseChange (QuadraticField k)) (2 ^ n))
  (I : KummerCoefficientComparison ℓ k S hFull)
  (F : KummerCohomologyFinite ℓ k S hFull)
  {m : ℕ} (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
  (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
  (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
  (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
  (hzero : CU.d 0 1 = 0)
  (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
  (i : arithmeticRationalComplex ℓ k S hFull ⟶ scalarChangedComplex Rings.rhoT CU)
  [QuasiIsoAt i 1]

/-- The central Selmer comparison with no free rank, no free rational basis, and no free divisible-group map. -/
def centralSelmerComparisonOfCompactKummer :
    CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm :=
  centralSelmerComparisonOfQuadraticDescent hk Dm CU e1 e2 hzero hd
    (arithmeticRationalComplex ℓ k S hFull) i
    (arithmeticRationalH1Equiv ℓ k S hFull F)
    (arithmetic_j ℓ k S hFull I F)
    (arithmetic_j_boundedDefects ℓ k S hFull I F)

include hk S hFull I F CU e1 e2 hzero hd i in
/-- The base-zero matrix rank follows once the retained genuine model comparison is supplied. -/
theorem hcentral_of_compactKummer (hSel : SelmerCorankOneOverK ℓ k) :
    (Dm.map Rings.rhoT).rank = m :=
  hcentral_of_selmer hSel
    (centralSelmerComparisonOfCompactKummer ℓ k hk S hFull I F Dm CU e1 e2 hzero hd i)

include hk S hFull I F CU e1 e2 hzero hd i in
/-- The two central dimensions are one for the same genuine comparison and full Selmer hypothesis. -/
theorem central_dimensions_of_compactKummer (hSel : SelmerCorankOneOverK ℓ k) :
    (Dm.map Rings.rhoT).rank = m ∧
      Module.finrank ℚ_[2] (LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) = 1 ∧
      Module.finrank ℚ_[2]
        ((Fin (m + 1) → ℚ_[2]) ⧸ LinearMap.range (Dm.map Rings.rhoT).mulVecLin) = 1 := by
  let C := centralSelmerComparisonOfCompactKummer ℓ k hk S hFull I F Dm CU e1 e2 hzero hd i
  exact ⟨C.hcentral hSel.1 hSel.2, C.finrank_ker hSel.1 hSel.2,
    C.finrank_coker hSel.1 hSel.2⟩

end ZInQ.Manuscript.RC53Assist.CentralUniversal
