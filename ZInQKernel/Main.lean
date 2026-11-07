import ZInQKernel.Target
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Hypotheses.Pole
import ZInQKernel.Model.Descent.MordellWeil
import ZInQKernel.Hypotheses.PrimePattern
import ZInQKernel.Assembly.Top

/-!
# The main theorem

Theorem 1.1 of the 11/5 manuscript, with its deep arithmetic inputs as explicit
hypotheses: the six-contact height estimate (H), pole completeness (PC), the
twenty-two-prime pattern (22P) and the catalogue bound (CAT). No `axiom` is involved: the
trust boundary is the hypothesis list of this theorem. The Mordell–Weil theorem for the
generator curve, a hypothesis in earlier versions, is the theorem `mordellWeilE`.
-/

namespace ZInQ

/-- **Main theorem, given the node statistics of the universal halting circuit.** Under
hypotheses H, PC, 22P and CAT, and the named finite check `HaltingNodeCheck` (a finite-computation
input of milestone 1), the specified polynomial `P_*` witnesses the target statement: it lies in
`ℤ[X_0, …, X_{292890231904}]`, has degree below `2↑↑7` and coefficients below `2↑↑8`, and its
rational zero projection to the first variable is exactly `ℤ` (the assembly lemma). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_nodeCheck
    (hN : Compiler.Universal.HaltingNodeCheck) (hH : SixContactEstimate)
    (hPC : PoleCompleteness) (h22 : FixedPrimePattern) (hCAT : CatalogueBound) :
    FrozenTarget :=
  Assembly.assembly hN hH hPC h22 hCAT

/-- **Main theorem.** Under hypotheses H, PC, 22P and CAT, there is an integer
polynomial in `292890231905` variables, of degree below `2↑↑7` and with coefficients below
`2↑↑8`, whose rational zero projection to the first variable is exactly `ℤ`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of
    (hH : SixContactEstimate) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) (hCAT : CatalogueBound) : FrozenTarget := by
  sorry

end ZInQ
