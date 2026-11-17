import ZInQKernel.Target
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Hypotheses.HeightMin
import ZInQKernel.Hypotheses.Pole
import ZInQKernel.Model.Descent.MordellWeil
import ZInQKernel.Hypotheses.PrimePattern
import ZInQKernel.Hypotheses.PrimeAP
import ZInQKernel.Hypotheses.GreenTao
import ZInQKernel.Multiplication.Completeness.AP
import ZInQKernel.Assembly.Top
import ZInQKernel.Compiler.NodeBound

/-!
# The main theorem

Theorem 1.1 of the 11/5 manuscript, with its deep arithmetic inputs as explicit
hypotheses: the six-contact height estimate (H) and pole completeness (PC, Theorem 5.2 of the
manuscript, for the manuscript's pole polynomial `Q_pole` with the curves `y² = x(x - ℓ)(x + 3ℓ)`).
No `axiom` is involved: the trust boundary is the hypothesis list of each theorem.

* H enters in its minimal form `SixContactMin`, the one instance `h(u) ≤ H₆(D) M_{S_mul}(u)²⁴`
  that the proof uses; the manuscript's Theorem 4.1 (`SixContactEstimate`) implies it
  (`sixContactMin_of_sixContactEstimate`).
* PC (`PoleCompleteness`, `ZInQKernel/Hypotheses/Pole.lean`) is the manuscript's Theorem 5.2, which
  the manuscript derives from its restricted converse Theorem 5.3. The Route K replacement of PC
  (congruent number curves, the certified-rank hypothesis CR₃ and the Tian–Yuan–Zhang and
  Gross–Zagier inputs) was removed from the tree (fork issue #77); it is kept at the tag
  `route-k-final`.
* The slope representation comes from one of three prime inputs: the twenty-two-prime pattern 22P
  (`exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness`), the progression
  hypothesis 22P_AP (`GoodPrimeAP`, Route AP: Proposition AP and Lemma P), or the two inputs of
  22P_AP, Green–Tao 2008 Theorem 1.2 in its dense form (`GreenTaoDense`) and Proposition D
  (`GoodPrimeDensity`). Both of the last are proved in Lean (`ZInQKernel/MainGreenTao.lean`), which
  gives the headline `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`
  with the hypotheses H and PC only.

Three inputs that were hypotheses in earlier versions are theorems: the Mordell–Weil theorem for
the generator curve (`mordellWeilE`), the catalogue bound CAT₈ (`catalogueBound8`: twenty-two
primes in `(324, 2^(W⁸))` in every unit class modulo `W`, from the effective Dirichlet theorem
`Progressions.effective_dirichlet`), and the prime pattern (through route AP, as above).
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

/-- **Main theorem, with PC and 22P.** Under hypotheses H (`SixContactMin`), PC
(`PoleCompleteness`, Theorem 5.2) and 22P, there is an integer polynomial in `292890231905`
variables, of degree below `2↑↑7` and with coefficients below `2↑↑8`, whose rational zero projection
to the first variable is exactly `ℤ`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness
    (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) : FrozenTarget :=
  Assembly.assembly Compiler.NodeCheck.haltingAddMulBound hH hPC
    (Mult.slopeRepresentation_of_fixedPrimePattern h22)

/-- **Main theorem, with PC, under the progression hypothesis 22P_AP.** Under hypotheses H
(`SixContactMin`), PC (`PoleCompleteness`) and 22P_AP (`GoodPrimeAP`: for every `K` the good slope
primes above `max S_b` contain an arithmetic progression of `K + 1` terms), there is an integer
polynomial in `292890231905` variables, of degree below `2↑↑7` and with coefficients below `2↑↑8`,
whose rational zero projection to the first variable is exactly `ℤ`. The polynomial is the same
`P_*` as in the main theorem.

22P_AP enters through Proposition AP (`Mult.slopeRepresentationAP_of_goodPrimeAP`): every integer
is a sum of three slopes satisfying field 2′, where a pole at an old prime is allowed when
`F(t) > 0`; completeness absorbs such a pole with the witness `q` (Lemma P,
`Mult.slope_complete_AP`). Route AP of `docs/research/nt-22p.md`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness_goodPrimeAP
    (hH : SixContactMin) (hPC : PoleCompleteness) (hAP : GoodPrimeAP) : FrozenTarget :=
  Assembly.assembly_AP Compiler.NodeCheck.haltingAddMulBound hH hPC
    (Mult.slopeRepresentationAP_of_goodPrimeAP hAP)

/-- **Main theorem, with PC, under Green–Tao (dense form) and Proposition D.** Under hypotheses H
(`SixContactMin`), PC (`PoleCompleteness`), Szemerédi's theorem in the primes (`GreenTaoDense`:
every set of primes of positive relative upper density contains arithmetic progressions of every
finite length) and the density part of Proposition D (`GoodPrimeDensity`: the good slope primes have
positive relative upper density in the primes), there is an integer polynomial in `292890231905`
variables, of degree below `2↑↑7` and with coefficients below `2↑↑8`, whose rational zero projection
to the first variable is exactly `ℤ`. The two last hypotheses give 22P_AP
(`goodPrimeAP_of_greenTaoDense`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness_greenTaoDense
    (hH : SixContactMin) (hPC : PoleCompleteness) (hGT : GreenTaoDense) (hD : GoodPrimeDensity) :
    FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness_goodPrimeAP hH hPC
    (goodPrimeAP_of_greenTaoDense hGT hD)

end ZInQ
