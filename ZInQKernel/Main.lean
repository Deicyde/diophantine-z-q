import ZInQKernel.Target
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Hypotheses.Pole
import ZInQKernel.Model.Descent.MordellWeil
import ZInQKernel.Hypotheses.PrimePattern
import ZInQKernel.Assembly.Top
import ZInQKernel.Compiler.NodeBound

/-!
# The main theorem

Theorem 1.1 of the 11/5 manuscript, with its deep arithmetic inputs as explicit
hypotheses: the six-contact height estimate (H), pole completeness (PC), the
twenty-two-prime pattern (22P) and the catalogue bound CAT₈ (`CatalogueBound8`: twenty-two
primes in `(324, 2^(W⁸))` in every unit class modulo `W`). No `axiom` is involved: the trust
boundary is the hypothesis list of this theorem. The manuscript's catalogue bound CAT (cutoff
`2^(W³)`) implies CAT₈; the corollary
`exists_bounded_integer_polynomial_defining_integers_of_catalogueBound` takes CAT. The
Mordell–Weil theorem for the generator curve, a hypothesis in earlier versions, is the theorem
`mordellWeilE`.

The hypothesis 22P is used only through the slope representation `Mult.SlopeRepresentation`.
The two-slope pattern 22P₂ (`TwoSlopePattern`) also gives it, so the main theorem holds with 22P₂
in place of 22P (`exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern`); 22P₂
is a different prime pattern, not a consequence of 22P.
-/

namespace ZInQ

/-- **Main theorem, given the addition and multiplication bound of the universal halting
circuit.** Under hypotheses H, PC, 22P and CAT₈, and the bound `HaltingAddMulBound` on the
addition and multiplication counts of the universal halting circuit, the specified polynomial
`P_*` witnesses the target statement: it lies in `ℤ[X_0, …, X_{292890231904}]`, has degree
below `2↑↑7` and coefficients below `2↑↑8`, and its rational zero projection to the first
variable is exactly `ℤ` (the assembly lemma). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_addMulBound
    (hB : Compiler.NodeCheck.HaltingAddMulBound) (hH : SixContactEstimate)
    (hPC : PoleCompleteness) (h22 : FixedPrimePattern) (hCAT : CatalogueBound8) :
    FrozenTarget :=
  Assembly.assembly hB hH hPC (Mult.slopeRepresentation_of_fixedPrimePattern h22) hCAT

/-- **Main theorem, given the node statistics of the universal halting circuit** (the named
finite check `HaltingNodeCheck`, a finite-computation input of milestone 1). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_nodeCheck
    (hN : Compiler.Universal.HaltingNodeCheck) (hH : SixContactEstimate)
    (hPC : PoleCompleteness) (h22 : FixedPrimePattern) (hCAT : CatalogueBound8) :
    FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_addMulBound ⟨hN.2.2.1.le, hN.2.2.2.1.le⟩
    hH hPC h22 hCAT

/-- **Main theorem.** Under hypotheses H, PC, 22P and CAT₈, there is an integer
polynomial in `292890231905` variables, of degree below `2↑↑7` and with coefficients below
`2↑↑8`, whose rational zero projection to the first variable is exactly `ℤ`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of
    (hH : SixContactEstimate) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) (hCAT : CatalogueBound8) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_addMulBound
    Compiler.NodeCheck.haltingAddMulBound hH hPC h22 hCAT

/-- **Main theorem, under the two-slope pattern 22P₂.** Under hypotheses H, PC, 22P₂ and CAT₈,
there is an integer polynomial in `292890231905` variables, of degree below `2↑↑7` and with
coefficients below `2↑↑8`, whose rational zero projection to the first variable is exactly `ℤ`.
The polynomial is the same `P_*` as in the main theorem. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern
    (hH : SixContactEstimate) (hPC : PoleCompleteness)
    (h22 : TwoSlopePattern) (hCAT : CatalogueBound8) : FrozenTarget :=
  Assembly.assembly Compiler.NodeCheck.haltingAddMulBound hH hPC
    (Mult.slopeRepresentation_of_twoSlopePattern h22) hCAT

/-- **Main theorem, under the manuscript's catalogue bound CAT** (cutoff `2^(W³)`), which
implies CAT₈. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_catalogueBound
    (hH : SixContactEstimate) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) (hCAT : CatalogueBound) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of hH hPC h22
    (catalogueBound8_of_catalogueBound hCAT)

end ZInQ
