import ZInQKernel.Target
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Hypotheses.HeightMin
import ZInQKernel.Hypotheses.Pole
import ZInQKernel.Model.Descent.MordellWeil
import ZInQKernel.Hypotheses.PrimePattern
import ZInQKernel.Assembly.Top
import ZInQKernel.Compiler.NodeBound

/-!
# The main theorem

Theorem 1.1 of the 11/5 manuscript, with its deep arithmetic inputs as explicit
hypotheses: the six-contact height estimate (H), pole completeness (PC) and the
twenty-two-prime pattern (22P). H enters in its minimal form `SixContactMin`, the one instance
`h(u) ≤ H₆(D) M_{S_mul}(u)²⁴` that the proof uses; the manuscript's Theorem 4.1
(`SixContactEstimate`) implies it (`sixContactMin_of_sixContactEstimate`), and
`exists_bounded_integer_polynomial_defining_integers_of_sixContactEstimate` is the main theorem
with H as stated in the manuscript. No `axiom` is involved: the trust boundary is the hypothesis
list of this theorem. Two inputs that were hypotheses in earlier versions are theorems: the
Mordell–Weil theorem for the generator curve (`mordellWeilE`) and the catalogue bound CAT₈
(`catalogueBound8`: twenty-two primes in `(324, 2^(W⁸))` in every unit class modulo `W`, from
the effective Dirichlet theorem `Progressions.effective_dirichlet`).

The hypothesis 22P is used only through the slope representation `Mult.SlopeRepresentation`.
The two-slope pattern 22P₂ (`TwoSlopePattern`) also gives it, so the main theorem holds with 22P₂
in place of 22P (`exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern`); 22P₂
is a different prime pattern, not a consequence of 22P.
-/

namespace ZInQ

/-- Every prime of `S_mul` is at most `D`: `p ≤ R = D`, where `R = D` comes from the catalogue
bound (`H_max, c_* < D`). -/
theorem Mult.le_heightD_of_mem_S_mul {p : ℕ} (hp : p ∈ Mult.S_mul) : p ≤ heightD :=
  (Mult.le_R_of_mem_S_mul hp).trans_eq ((Size.R_eq_D catalogueBound8).trans Mult.D_eq_heightD)

/-- **H implies its minimal form.** `SixContactMin` is the instance `S = S_mul`, `R = D` of the
six-contact estimate, admissible because `S_mul` consists of primes, contains the primes
`≤ 324`, and `max S_mul ≤ D` (`Mult.le_heightD_of_mem_S_mul`). -/
theorem sixContactMin_of_sixContactEstimate (hH : SixContactEstimate) : SixContactMin :=
  fun u hu => hH Mult.S_mul (fun _ hp => Mult.prime_of_mem_S_mul hp)
    (fun _ hp h => Mult.mem_S_mul_of_le hp h) _ le_rfl
    (fun _ hp => by exact_mod_cast Mult.le_heightD_of_mem_S_mul hp)
    (by exact_mod_cast Compiler.Precision.ten_pow_twelve_le_heightD) u hu

/-- **Main theorem, given the addition and multiplication bound of the universal halting
circuit.** Under hypotheses H, PC and 22P, and the bound `HaltingAddMulBound` on the
addition and multiplication counts of the universal halting circuit, the specified polynomial
`P_*` witnesses the target statement: it lies in `ℤ[X_0, …, X_{292890231904}]`, has degree
below `2↑↑7` and coefficients below `2↑↑8`, and its rational zero projection to the first
variable is exactly `ℤ` (the assembly lemma). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_addMulBound
    (hB : Compiler.NodeCheck.HaltingAddMulBound) (hH : SixContactMin)
    (hPC : PoleCompleteness) (h22 : FixedPrimePattern) : FrozenTarget :=
  Assembly.assembly hB hH hPC (Mult.slopeRepresentation_of_fixedPrimePattern h22)

/-- **Main theorem, given the node statistics of the universal halting circuit** (the named
finite check `HaltingNodeCheck`, a finite-computation input of milestone 1). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_nodeCheck
    (hN : Compiler.Universal.HaltingNodeCheck) (hH : SixContactMin)
    (hPC : PoleCompleteness) (h22 : FixedPrimePattern) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_addMulBound ⟨hN.2.2.1.le, hN.2.2.2.1.le⟩
    hH hPC h22

/-- **Main theorem.** Under hypotheses H (in its minimal form `SixContactMin`), PC and 22P,
there is an integer polynomial in `292890231905` variables, of degree below `2↑↑7` and with
coefficients below `2↑↑8`, whose rational zero projection to the first variable is exactly `ℤ`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of
    (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_addMulBound
    Compiler.NodeCheck.haltingAddMulBound hH hPC h22

/-- **Main theorem, with H as in the manuscript.** Under the six-contact estimate (Theorem 4.1),
PC and 22P, there is an integer polynomial in `292890231905` variables, of degree below `2↑↑7`
and with coefficients below `2↑↑8`, whose rational zero projection to the first variable is
exactly `ℤ`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactEstimate
    (hH : SixContactEstimate) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of
    (sixContactMin_of_sixContactEstimate hH) hPC h22

/-- **Main theorem, under the two-slope pattern 22P₂.** Under hypotheses H (`SixContactMin`), PC
and 22P₂, there is an integer polynomial in `292890231905` variables, of degree below `2↑↑7` and with
coefficients below `2↑↑8`, whose rational zero projection to the first variable is exactly `ℤ`.
The polynomial is the same `P_*` as in the main theorem. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern
    (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : TwoSlopePattern) : FrozenTarget :=
  Assembly.assembly Compiler.NodeCheck.haltingAddMulBound hH hPC
    (Mult.slopeRepresentation_of_twoSlopePattern h22)

end ZInQ
