import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Bridges
import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.GaloisCompletion

/-!
# Modularity in newform form from Theorem A, two prints and two readings

`PrintsAnalytic.ModularNewform` (every elliptic curve `E/ℚ` has a weight-two newform of trivial
nebentypus with the coefficients of `L(E, s)`, `IsNewformOf`) was an input of the proof of
Theorem 5.3 (the former field `RCLeaves.modularNewform`), a composite of Theorem A of
Breuil–Conrad–Diamond–Taylor and the passage from a `Γ₀(N)` eigenform with the curve's
coefficients to the newform (tex 1779–1784). Here that passage is a proof from printed statements:

* `PoleS12.BCDTThmA` (Breuil–Conrad–Diamond–Taylor, Theorem A, with the Introduction's condition
  (2); the blueprint's print `Prints.bcdt`): a weight-two `Γ₀(N)` cusp form with the coefficients
  of `L(E, s)`;
* `LiCarayolNewformOfModular` from four statements (a contributor's `RC53Assist/NewformGlueG0`):
  two prints, Shimura 1973, Theorem 1, pp. 525–526 (conjugate eigenforms and the finite
  coefficient field), and Li 1975, Theorem 5, p. 298 (strong multiplicity one, weight two, trivial
  character); and two GLUE readings: a joint reading of Shimura 1973, Theorem 1, at rational
  coefficient field, and Carayol 1986, §0.8 Corollaire, p. 411 (a rational newform has an elliptic
  curve whose minimal Weierstrass local polynomial at every prime is the newform's Euler
  polynomial; the newform–curve association is erased, not constructed), and Faltings 1983, §5,
  Korollar 2 (iii ⇒ iv), p. 361, read through the minimal Weierstrass local polynomials at the
  finite places (local factors equal almost everywhere are equal everywhere). The divisor-level
  extraction of the newform, the descent of its coefficient field to `ℚ` and the comparison of
  every positive-index coefficient are proved there.

`modularNewform_of_printed` gives `ModularNewform` from these five statements (Theorem A, the two
prints and the two readings).
-/

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Contrib.CloudB3RC53.ModularWeil (LiCarayolNewformOfModular)
open ZInQ.Contrib.RC53Assist.NewformGlueG0 (Li1975StrongMultiplicityOneWeightTwo)
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
  (Shimura1973ConjugateEigenforms Carayol1986RationalNewformEulerFactors
    Faltings1983EulerFactorRigidityQ liCarayolNewformOfModular_of_printed_corollaries)

/-- **Modularity in newform form from Theorem A and the newform of a modular curve** (PROVED):
the cusp form of Theorem A on `Γ₀(N)` with the curve's coefficients gives, by
`LiCarayolNewformOfModular`, a newform of level dividing `N`, trivial nebentypus and the same
coefficients. -/
theorem modularNewform_of_bcdt_liCarayol (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)
    (hLC : LiCarayolNewformOfModular) : ModularNewform := by
  intro E hE
  obtain ⟨N, hN, f, hf⟩ := hB E hE
  obtain ⟨M, hM0, F, -, hχ, hcoeff⟩ := hLC E hE N hN f hf
  exact ⟨M, hM0, F, hχ, fun n hn => by simpa [nfCoeff, lcoeff] using hcoeff n hn⟩

/-- **Modularity in newform form from Theorem A, two prints and two readings** (PROVED): Theorem A
of Breuil–Conrad–Diamond–Taylor with the prints Shimura 1973 Theorem 1 and Li 1975 Theorem 5 and
the GLUE readings of Shimura 1973 Theorem 1 with Carayol 1986 §0.8 Corollaire and of Faltings 1983
§5 Korollar 2 (iii ⇒ iv). -/
theorem modularNewform_of_printed (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ) :
    ModularNewform :=
  modularNewform_of_bcdt_liCarayol hB (liCarayolNewformOfModular_of_printed_corollaries hS hL hC hF)

end ZInQ.Manuscript.RC.PrintsAnalytic
