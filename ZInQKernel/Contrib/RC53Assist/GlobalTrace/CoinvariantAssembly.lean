import ZInQKernel.Contrib.RC53Assist.GlobalTrace.GoodReductionReading
import ZInQKernel.Contrib.RC53Assist.GlobalTrace.CoinvariantReadings

/-!
# The coinvariant representation assembly with the good-prime reading discharged

This module instantiates the good-prime reading of `GlobalTrace/CoinvariantReadings.lean` with its
proof `globalGoodReductionTraceReading_proved` of `GlobalTrace/GoodReductionReading.lean`.
The realization and comparison used here are the corrected coinvariant ones. The excluded
invariant-space statements are archived in `docs/research/g0-representation-route-invariants.md`,
not retained as Lean hypotheses.

* `localTatePolynomialCoinv_eq_localTatePolynomial_of_good`: at every good prime `p ≠ ℓ` the
  corrected local Tate polynomial is the existing `localTatePolynomial`, so nothing changes there.
* `liCarayolNewformOfModular_of_representations_coinv`: the exact G0 conclusion from the printed
  inputs of the representation route with the corrected Carayol reading and the corrected
  bad-prime reading.
* `liCarayolNewformOfModular_of_representations_coinv_of_inputs`: the same with the corrected
  bad-prime reading replaced by its inputs: the Tate-curve print, the local–global glue and the
  additive-case vanishing of coinvariants.

## Classification

PROVED from the displayed propositions; no new inputs.
-/

namespace ZInQ.Contrib.RC53Assist.GlobalTrace

open ZInQ.Contrib.RC53Assist.NewformGlueG0 ZInQ.Contrib.RC53Assist.NewformGlueG0.Completion
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary

/-- **PROVED**, at a good prime `p ≠ ℓ` the corrected local Tate polynomial is the existing
`localTatePolynomial`. Locators: `localTatePolynomialCoinv_eq_of_trivial_inertia` and the inertia
clause of `globalGoodReductionTraceReading_proved`. -/
theorem localTatePolynomialCoinv_eq_localTatePolynomial_of_good (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hgood : GoodReductionAt E (primeIdealQ p hp)) (D : LocalArithmeticFrobenius p) :
    localTatePolynomialCoinv E ℓ D = localTatePolynomial E ℓ D :=
  localTatePolynomialCoinv_eq_of_trivial_inertia E ℓ D
    ((globalGoodReductionTraceReading_proved goodReductionFrobeniusTraceDictionaryQ_proved
      E ℓ p hp hpℓ hgood).1 D)

/-- **PROVED**, at a good prime `p ≠ ℓ` the corrected local Tate polynomial is the
minimal-reduction polynomial. Locators: `localTatePolynomialCoinv_of_good`,
`globalGoodReductionTraceReading_proved`. -/
theorem localTatePolynomialCoinv_of_good_proved (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ)
    [Fact ℓ.Prime] (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hgood : GoodReductionAt E (primeIdealQ p hp)) (D : LocalArithmeticFrobenius p) :
    localTatePolynomialCoinv E ℓ D =
      (localPolynomialQ E (primeIdealQ p hp)).map (Int.castRingHom ℚ_[ℓ]) :=
  localTatePolynomialCoinv_of_good globalGoodReductionTraceReading_proved E ℓ p hp hpℓ hgood D

/-- **PROVED CONDITIONAL REPRESENTATION ASSEMBLY ON COINVARIANTS**, the exact G0 conclusion from
Shimura's conjugate eigenforms, Li's strong multiplicity one, the corrected Carayol realization,
Faltings's semisimplicity and the corrected bad-prime reading. The good-prime reading is
discharged. Locators: `liCarayolNewformOfModular_of_representations_coinv_of_good`,
`globalGoodReductionTraceReading_proved`. -/
theorem liCarayolNewformOfModular_of_representations_coinv
    (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
    (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986ThmARationalWeightTwoCoinv) (hFa : Faltings1983Satz3EllipticQ)
    (hB : BadReductionTatePolynomialReadingCoinv) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular :=
  liCarayolNewformOfModular_of_representations_coinv_of_good hS hL hC hFa
    globalGoodReductionTraceReading_proved hB

/-- **PROVED FROM THE DISPLAYED INPUTS**, the exact G0 conclusion with the corrected bad-prime
reading replaced by its inputs: the Tate-curve print (Silverman, Appendix C, Theorem C.14.1), the
local–global decomposition-group glue, and the additive-case vanishing of coinvariants. Locators:
`liCarayolNewformOfModular_of_representations_coinv`,
`badReductionTatePolynomialReadingCoinv_of_inputs`. -/
theorem liCarayolNewformOfModular_of_representations_coinv_of_inputs
    (hS : ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent.Shimura1973ConjugateEigenforms)
    (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986ThmARationalWeightTwoCoinv) (hFa : Faltings1983Satz3EllipticQ)
    (hT : TateCurveTateModulePrint) (hLG : DecompositionGroupLocalGlobalGlue)
    (hA : AdditiveReductionCoinvariantsVanish) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular :=
  liCarayolNewformOfModular_of_representations_coinv hS hL hC hFa
    (badReductionTatePolynomialReadingCoinv_of_inputs hT hLG hA)

end ZInQ.Contrib.RC53Assist.GlobalTrace
