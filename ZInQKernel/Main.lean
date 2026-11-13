import ZInQKernel.Target
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Hypotheses.HeightMin
import ZInQKernel.Hypotheses.Pole
import ZInQKernel.Hypotheses.CertifiedRank
import ZInQKernel.RouteK.Assembly.PoleCompleteness
import ZInQKernel.Model.Descent.MordellWeil
import ZInQKernel.Hypotheses.PrimePattern
import ZInQKernel.Hypotheses.PrimeAP
import ZInQKernel.Hypotheses.GreenTao
import ZInQKernel.Multiplication.Completeness.AP
import ZInQKernel.Assembly.Top
import ZInQKernel.Compiler.NodeBound
import ZInQKernel.RouteK.Selmer.Prop0

/-!
# The main theorem

Theorem 1.1 of the 11/5 manuscript, with its deep arithmetic inputs as explicit
hypotheses: the six-contact height estimate (H), the certified-rank hypothesis for congruent
number curves (CR₃) and the twenty-two-prime pattern (22P). No `axiom` is involved: the trust
boundary is the hypothesis list of this theorem.

* H enters in its minimal form `SixContactMin`, the one instance `h(u) ≤ H₆(D) M_{S_mul}(u)²⁴`
  that the proof uses; the manuscript's Theorem 4.1 (`SixContactEstimate`) implies it
  (`sixContactMin_of_sixContactEstimate`), and
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactEstimate` is the main theorem
  with H as stated in the manuscript.
* CR₃ (`CertifiedRank`) replaces pole completeness PC (Route K). PC, for the Route K pole
  polynomial (curves `y² = x(x - ℓ)(x + ℓ)`), is now a theorem from CR₃
  (`poleCompleteness_of_certifiedRank`): the descent lemma DL (`RouteK.descent_lemma`, proved)
  produces, for every admissible input, two congruent number curves whose explicit 2-Selmer systems
  have dimension 3 and contain the class `β`; CR₃ turns these certificates into rational points, and
  the points give a zero of the pole polynomial. CR₃ concerns only curves `C_d` with
  `d ≡ 5 (mod 8)` and classes `|a| ≡ 7 (mod 8)`; it follows from Proposition 0 with
  Tian–Yuan–Zhang, Proposition N and Gross–Zagier with an auxiliary field (see its docstring and
  `docs/research/cr3-trust.md`; Kriz's 2-converse is an alternative that is not needed).
  `exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness` is the main
  theorem with PC in place of CR₃.
* The hypothesis 22P is used only through the slope representation `Mult.SlopeRepresentation`.
  The two-slope pattern 22P₂ (`TwoSlopePattern`) also gives it, so the main theorem holds with 22P₂
  in place of 22P (`exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern`); 22P₂
  is a different prime pattern, not a consequence of 22P.
* Route AP: the progression hypothesis 22P_AP (`GoodPrimeAP`, arbitrarily long arithmetic
  progressions of good slope primes) gives the slope representation under field 2′
  (`Mult.SlopeRepresentationAP`, Proposition AP), which is enough for completeness by Lemma P; so
  the main theorem holds with 22P_AP in place of 22P
  (`exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP`). 22P_AP follows from two
  inputs together, not from Green–Tao alone: Green–Tao 2008, Theorem 1.2 in its dense form
  (`GreenTaoDense`; complete proof in Tao–Ziegler 2008) and Proposition D of
  `docs/research/nt-22p.md` (`GoodPrimeDensity`: the good slope primes have positive relative upper
  density in the primes), by `goodPrimeAP_of_greenTaoDense`; so the main theorem holds with these
  two in place of 22P (`exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense`).

Three inputs that were hypotheses in earlier versions are theorems: the Mordell–Weil theorem for
the generator curve (`mordellWeilE`), the catalogue bound CAT₈ (`catalogueBound8`: twenty-two
primes in `(324, 2^(W⁸))` in every unit class modulo `W`, from the effective Dirichlet theorem
`Progressions.effective_dirichlet`), and pole completeness (from CR₃, as above).
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

/-- **Main theorem, with PC in place of CR₃.** Under hypotheses H (`SixContactMin`), PC (for the
Route K pole polynomial) and 22P, there is an integer polynomial in `292890231905` variables, of
degree below `2↑↑7` and with coefficients below `2↑↑8`, whose rational zero projection to the
first variable is exactly `ℤ`. The main theorem derives PC from CR₃
(`poleCompleteness_of_certifiedRank`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness
    (hH : SixContactMin) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) : FrozenTarget :=
  Assembly.assembly Compiler.NodeCheck.haltingAddMulBound hH hPC
    (Mult.slopeRepresentation_of_fixedPrimePattern h22)

/-- **Main theorem, given the addition and multiplication bound of the universal halting
circuit.** Under hypotheses H, CR₃ and 22P, and the bound `HaltingAddMulBound` on the
addition and multiplication counts of the universal halting circuit, the specified polynomial
`P_*` witnesses the target statement: it lies in `ℤ[X_0, …, X_{292890231904}]`, has degree
below `2↑↑7` and coefficients below `2↑↑8`, and its rational zero projection to the first
variable is exactly `ℤ` (the assembly lemma). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_addMulBound
    (hB : Compiler.NodeCheck.HaltingAddMulBound) (hH : SixContactMin)
    (hCR : CertifiedRank) (h22 : FixedPrimePattern) : FrozenTarget :=
  Assembly.assembly hB hH (poleCompleteness_of_certifiedRank hCR)
    (Mult.slopeRepresentation_of_fixedPrimePattern h22)

/-- **Main theorem, given the node statistics of the universal halting circuit** (the named
finite check `HaltingNodeCheck`, a finite-computation input of milestone 1). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_nodeCheck
    (hN : Compiler.Universal.HaltingNodeCheck) (hH : SixContactMin)
    (hCR : CertifiedRank) (h22 : FixedPrimePattern) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_addMulBound ⟨hN.2.2.1.le, hN.2.2.2.1.le⟩
    hH hCR h22

/-- **Main theorem.** Under hypotheses H (in its minimal form `SixContactMin`), CR₃
(`CertifiedRank`) and 22P, there is an integer polynomial in `292890231905` variables, of degree
below `2↑↑7` and with coefficients below `2↑↑8`, whose rational zero projection to the first
variable is exactly `ℤ`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of
    (hH : SixContactMin) (hCR : CertifiedRank)
    (h22 : FixedPrimePattern) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_addMulBound
    Compiler.NodeCheck.haltingAddMulBound hH hCR h22

/-- **Main theorem, with CR₃^Sel in place of CR₃.** Under hypotheses H (`SixContactMin`),
CR₃^Sel (`RouteK.Selmer.CertifiedRankSel`) and 22P, there is an integer polynomial in
`292890231905` variables, of degree below `2↑↑7` and with coefficients below `2↑↑8`, whose rational
zero projection to the first variable is exactly `ℤ`.

CR₃^Sel is a narrower hypothesis than CR₃: it speaks of the 2-Selmer group `Sel₂(C_d)` itself
(`RouteK.Selmer.Sel2`, defined by local solubility of the 2-coverings over `ℝ` and every `ℚ_p`),
not of the explicit linear system `Σ(𝒞_d)` with its Legendre symbols. In the literature's terms it
says: for squarefree `d ≡ 5 (mod 8)`, if `dim_{𝔽₂} Sel₂(C_d) = 3` and some Selmer class `(a, b)` has
`|a| ≡ 7 (mod 8)`, then every Selmer class comes from a rational point, i.e. `Ш(C_d)[2] = 0`
(equivalently `rank C_d(ℚ) ≥ 1`). This follows from Tian–Yuan–Zhang with Proposition N and
Gross–Zagier with an auxiliary field (`docs/research/cr3-trust.md`); Kriz's 2-converse theorem
with the corank lemma is an alternative that is not needed. Proposition 0
(`RouteK.Selmer.prop0Statement`, proved in Lean) identifies `Σ(𝒞_d)` with `Sel₂(C_d)`, which turns
CR₃^Sel into CR₃ (`RouteK.Selmer.certifiedRank_of_certifiedRankSel`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel
    (hH : SixContactMin) (hCRS : RouteK.Selmer.CertifiedRankSel)
    (h22 : FixedPrimePattern) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of hH
    (RouteK.Selmer.certifiedRank_of_certifiedRankSel hCRS) h22

/-- **Main theorem, with H as in the manuscript.** Under the six-contact estimate (Theorem 4.1),
CR₃ and 22P, there is an integer polynomial in `292890231905` variables, of degree below `2↑↑7`
and with coefficients below `2↑↑8`, whose rational zero projection to the first variable is
exactly `ℤ`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactEstimate
    (hH : SixContactEstimate) (hCR : CertifiedRank)
    (h22 : FixedPrimePattern) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of
    (sixContactMin_of_sixContactEstimate hH) hCR h22

/-- **Main theorem, under the two-slope pattern 22P₂.** Under hypotheses H (`SixContactMin`), CR₃
and 22P₂, there is an integer polynomial in `292890231905` variables, of degree below `2↑↑7` and with
coefficients below `2↑↑8`, whose rational zero projection to the first variable is exactly `ℤ`.
The polynomial is the same `P_*` as in the main theorem. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern
    (hH : SixContactMin) (hCR : CertifiedRank)
    (h22 : TwoSlopePattern) : FrozenTarget :=
  Assembly.assembly Compiler.NodeCheck.haltingAddMulBound hH (poleCompleteness_of_certifiedRank hCR)
    (Mult.slopeRepresentation_of_twoSlopePattern h22)

/-- **Main theorem, under the progression hypothesis 22P_AP.** Under hypotheses H
(`SixContactMin`), CR₃ (`CertifiedRank`) and 22P_AP (`GoodPrimeAP`: for every `K` the good slope
primes above `max S_b` contain an arithmetic progression of `K + 1` terms), there is an integer
polynomial in `292890231905` variables, of degree below `2↑↑7` and with coefficients below `2↑↑8`,
whose rational zero projection to the first variable is exactly `ℤ`. The polynomial is the same
`P_*` as in the main theorem.

22P_AP enters through Proposition AP (`Mult.slopeRepresentationAP_of_goodPrimeAP`): every integer
is a sum of three slopes satisfying field 2′, where a pole at an old prime is allowed when
`F(t) > 0`; completeness absorbs such a pole with the witness `q` (Lemma P,
`Mult.slope_complete_AP`). Route AP of `docs/research/nt-22p.md`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP
    (hH : SixContactMin) (hCR : CertifiedRank) (hAP : GoodPrimeAP) : FrozenTarget :=
  Assembly.assembly_AP Compiler.NodeCheck.haltingAddMulBound hH
    (poleCompleteness_of_certifiedRank hCR) (Mult.slopeRepresentationAP_of_goodPrimeAP hAP)

/-- **Main theorem, under Green–Tao (dense form) and Proposition D.** Under hypotheses H
(`SixContactMin`), CR₃ (`CertifiedRank`), Szemerédi's theorem in the primes (`GreenTaoDense`:
every set of primes of positive relative upper density contains arithmetic progressions of every
finite length) and the density part of Proposition D (`GoodPrimeDensity`: the good slope primes have
positive relative upper density in the primes), there is an integer polynomial in `292890231905`
variables, of degree below `2↑↑7` and with coefficients below `2↑↑8`, whose rational zero projection
to the first variable is exactly `ℤ`. The two last hypotheses give 22P_AP
(`goodPrimeAP_of_greenTaoDense`). -/
theorem exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense
    (hH : SixContactMin) (hCR : CertifiedRank) (hGT : GreenTaoDense) (hD : GoodPrimeDensity) :
    FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP hH hCR
    (goodPrimeAP_of_greenTaoDense hGT hD)

/-- **Main theorem from H, CR₃^Sel and route AP's two inputs.** Under H (`SixContactMin`), CR₃^Sel
(`RouteK.Selmer.CertifiedRankSel`, stated with the textbook 2-Selmer group), Szemerédi's theorem in
the primes (`GreenTaoDense`) and the density part of Proposition D (`GoodPrimeDensity`), there is an
integer polynomial in `292890231905` variables, of degree below `2↑↑7` and with coefficients below
`2↑↑8`, whose rational zero projection to the first variable is exactly `ℤ`. Proposition 0
(`RouteK.Selmer.certifiedRank_of_certifiedRankSel`) gives CR₃, and the last two hypotheses give
22P_AP. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_greenTaoDense
    (hH : SixContactMin) (hCRS : RouteK.Selmer.CertifiedRankSel) (hGT : GreenTaoDense)
    (hD : GoodPrimeDensity) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense hH
    (RouteK.Selmer.certifiedRank_of_certifiedRankSel hCRS) hGT hD

end ZInQ
