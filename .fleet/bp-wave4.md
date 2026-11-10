# bp-wave4 report: the blueprint records the work since Route K

No Lean file was edited. Five new chapters (74 leaf articles, 5 chapter READMEs, five new
locator files under blueprint/sources/) and two new main-theorem articles were added, and
several existing articles were updated. `lake build ZInQKernel` succeeds;
`autoform check blueprint --lean-root .` reports OK (499 articles, 1516 dependencies, 453 fully
proved, 1526 declaration names resolved, no warnings), and `autoform audit blueprint` passes
(coverage: 0 mapped, 13 decomposed, 1 deferred, 3 out). Article ids were taken from
`autoform migrate article-ids` (dry run) and inserted by hand into the new files only. The 32
older chapter READMEs that had no id still have none, as before.

## New articles

| Article | Lean names (first takes credit) | Status |
| --- | --- | --- |
| roadmap/route-ap/README.md |  | chapter README |
| roadmap/route-ap/assembly-ap.md | ZInQ.Assembly.assembly_AP | proved |
| roadmap/route-ap/completeness-ap.md | ZInQ.Mult.multiply_complete_AP, ZInQ.Mult.slopes_of_int_AP, ZInQ.Mult.completeness_core_AP | proved |
| roadmap/route-ap/good-prime-ap-from-green-tao.md | ZInQ.goodPrimeAP_of_greenTaoDense | proved |
| roadmap/route-ap/good-prime-ap.md | ZInQ.GoodPrimeAP | statement formalized (def) |
| roadmap/route-ap/good-slope-ap.md | ZInQ.Mult.GoodSlopeAP, ZInQ.Mult.OldBounds | statement formalized (def) |
| roadmap/route-ap/lemma-p-valuation.md | ZInQ.Mult.lemmaP_three, ZInQ.Mult.padicValRat_traceTheta_of_clear | proved |
| roadmap/route-ap/lemma-p.md | ZInQ.Mult.lemmaP_one, ZInQ.Mult.lemmaP_two, ZInQ.Mult.lemmaP_two_ball (+11 more) | proved |
| roadmap/route-ap/multiplication-exact-ap.md | ZInQ.Mult.multiplication_exact_AP | proved |
| roadmap/route-ap/pole-absorption-hypotheses.md | ZInQ.Mult.PoleAbsorbHyp, ZInQ.Mult.apContactNum | statement formalized (def) |
| roadmap/route-ap/pole-input-valuations-ap.md | ZInQ.Mult.pole_input_valuations_AP, ZInQ.Mult.GoodSlopeAP.contactQuot_eq_one | proved |
| roadmap/route-ap/progression-slope.md | ZInQ.Mult.goodSlopeAP_of_progression, ZInQ.Mult.contactPoly_pos_of_pos, ZInQ.Mult.contactPoly_pos_of_lt (+1 more) | proved |
| roadmap/route-ap/proposition-ap.md | ZInQ.Mult.slopeRepresentationAP_of_goodPrimeAP | proved |
| roadmap/route-ap/slope-completeness-ap.md | ZInQ.Mult.slope_complete_AP | proved |
| roadmap/route-ap/slope-representation-ap-of-slope-representation.md | ZInQ.Mult.slopeRepresentationAP_of_slopeRepresentation, ZInQ.Mult.GoodSlope.goodSlopeAP | proved |
| roadmap/route-ap/slope-representation-ap.md | ZInQ.Mult.SlopeRepresentationAP | statement formalized (def) |
| roadmap/route-ap/value-relation-ap.md | ZInQ.Assembly.exists_value_relation_iff_AP | proved |
| roadmap/route-ap/weak-approximation-targets.md | ZInQ.Mult.weak_approx_targets, ZInQ.Mult.padicNorm_le_zpow_iff_ap, ZInQ.Mult.exists_crt_idempotent_ap (+1 more) | proved |
| roadmap/green-tao/README.md |  | chapter README |
| roadmap/green-tao/dense-form.md | ZInQ.GreenTaoDense, ZInQ.ContainsArbitraryAPs, ZInQ.PrimesRelUpperDensityPos | statement formalized (def) |
| roadmap/green-tao/dense-theorem.md | ZInQ.greenTaoDense | proved |
| roadmap/green-tao/extraction.md | ZInQ.GreenTaoDense.containsAP_of_wTrickedSetWeight_offDiagMass_pos | proved |
| roadmap/green-tao/modulus-selection.md | ZInQ.GreenTaoDense.exists_prime_modulus_of_frequently_window, ZInQ.GreenTaoDense.exists_prime_scale_near, ZInQ.GreenTaoDense.card_window_le_card_quarter | proved |
| roadmap/green-tao/prime-modulus-transference.md | ZInQ.GreenTaoDense.hasPrimeModulusSubweightCounts, ZInQ.GreenTaoDense.HasPrimeModulusSubweightCounts, ZInQ.GreenTaoDense.hasPrimeModulusSubweightCounts_of_orderedRemoval_of_linearForms | proved |
| roadmap/green-tao/primes.md | ZInQ.greenTao_primes, Submission.green_tao | proved |
| roadmap/green-tao/residue-pigeonhole.md | ZInQ.GreenTaoDense.exists_reducedResidue_setWeight_mean_lower_bound, ZInQ.GreenTaoDense.quarterIntervalSetClass, ZInQ.GreenTaoDense.wTrickedSetWeight_untrickPrimeZMod (+2 more) | proved |
| roadmap/green-tao/set-weight.md | ZInQ.GreenTaoDense.wTrickedSetWeight, ZInQ.GreenTaoDense.wTrickedSetWeight_nonneg, ZInQ.GreenTaoDense.wTrickedSetWeight_le (+1 more) | statement formalized (def) |
| roadmap/green-tao/window-lemma.md | ZInQ.GreenTaoDense.frequently_window, ZInQ.GreenTaoDense.frequently_window_of, ZInQ.GreenTaoDense.card_filter_range_le_add_Ioc (+3 more) | proved |
| roadmap/green-tao/window-progressions.md | ZInQ.GreenTaoDense.containsAP_of_frequently_window | proved |
| roadmap/density/README.md |  | chapter README |
| roadmap/density/abel-summation.md | ZInQ.Density.abel_bound, ZInQ.Density.thetaS, ZInQ.Density.phiTerm (+8 more) | proved |
| roadmap/density/box-count.md | ZInQ.Density.GaussSieve.abs_card_box_dvd_sub_le, ZInQ.Density.GaussSieve.box, ZInQ.Density.GaussSieve.gaussFZ (+1 more) | proved |
| roadmap/density/character-sums.md | ZInQ.Density.pointCount_eq, ZInQ.Density.jac, ZInQ.Density.jac_sq_mul (+5 more) | proved |
| roadmap/density/description.md | ZInQ.Density.goodSlopePrime_iff, ZInQ.Density.InClass, ZInQ.Density.cp (+10 more) | proved |
| roadmap/density/dirichlet-density.md | ZInQ.Density.primesRelUpperDensityPos_of_dirichlet | proved |
| roadmap/density/four-divides-point-count.md | ZInQ.Density.four_dvd_pointCount, ZInQ.Density.four_dvd_pointCount_of_mod_four | proved |
| roadmap/density/gauss-bad-count.md | ZInQ.Density.card_gaussBad_le, ZInQ.Density.GaussBad, ZInQ.Density.mem_gaussBad_of_bad (+3 more) | proved |
| roadmap/density/good-prime-ap-from-dense-form.md | ZInQ.Density.goodPrimeAP_of_greenTaoDense', ZInQ.Density.goodPrimeAP_of_greenTaoDense_uniformBadBound | proved |
| roadmap/density/good-prime-density.md | ZInQ.GoodPrimeDensity | statement formalized (def) |
| roadmap/density/good-subset.md | ZInQ.Density.goodSlopePrime_of_mem_CL, ZInQ.Density.BadSet, ZInQ.Density.TL (+4 more) | proved |
| roadmap/density/jacobsthal.md | ZInQ.Density.jacobsthal, ZInQ.Density.jac_even, ZInQ.Density.sum_jac_sq | proved |
| roadmap/density/lattice-count.md | ZInQ.Density.sum_card_badSet_large_le, ZInQ.Density.BadSetOf, ZInQ.Density.latticePts (+5 more) | proved |
| roadmap/density/local-densities.md | ZInQ.Density.GaussSieve.card_zset_prod, ZInQ.Density.GaussSieve.ZSet, ZInQ.Density.GaussSieve.card_zset_prime (+1 more) | proved |
| roadmap/density/main-term.md | ZInQ.Density.phi_CL_lower, ZInQ.Density.summable_vonMangoldt_div_rpow | proved |
| roadmap/density/prime-tail.md | ZInQ.Density.sum_inv_sq_le_of_primes_gt, ZInQ.Density.prime_tail, ZInQ.Density.sum_log_div_sq_le | proved |
| roadmap/density/proposition-4-2.md | ZInQ.Density.uniformBadBound_holds, ZInQ.Density.uniformBadBound, ZInQ.Density.uniformGaussBadBound (+1 more) | proved |
| roadmap/density/proposition-d.md | ZInQ.Density.goodPrimeDensity | proved |
| roadmap/density/residue-set.md | ZInQ.Density.deltaL_ge, ZInQ.Density.QL, ZInQ.Density.modSet (+12 more) | proved |
| roadmap/density/selberg-sieve.md | SelbergSieve.selberg_bound_simple, SelbergSieve.selbergTerms, SelbergSieve.selbergBoundingSum (+7 more) | proved |
| roadmap/density/selberg-sum.md | ZInQ.Density.GaussSieve.selbergBoundingSum_ge_tau, ZInQ.Density.GaussSieve.prod_factors_sum_pow_mult, ZInQ.Density.GaussSieve.tauDiv (+9 more) | proved |
| roadmap/density/sieve-instance.md | ZInQ.Density.GaussSieve.siftedSum_le, ZInQ.Density.GaussSieve.gaussSieve, ZInQ.Density.GaussSieve.gsPrimes (+9 more) | proved |
| roadmap/density/theorem-d.md | ZInQ.Density.goodPrimeDensity_of_uniformBadBound, ZInQ.Density.card_TL_le, ZInQ.Density.exists_L (+1 more) | proved |
| roadmap/density/uniform-bad-bound.md | ZInQ.Density.UniformBadBound | statement formalized (def) |
| roadmap/selmer/README.md |  | chapter README |
| roadmap/selmer/bad-odd-primes.md | ZInQ.RouteK.Selmer.loc_padic_dvd_iff, ZInQ.RouteK.Selmer.padic_norm_natCast_of_squarefree, ZInQ.RouteK.Selmer.padic_norm_ne_zpow_odd | proved |
| roadmap/selmer/certified-rank-of-sel.md | ZInQ.RouteK.Selmer.certifiedRank_of_certifiedRankSel, ZInQ.RouteK.Selmer.certifiedRank_of_sel, ZInQ.RouteK.Selmer.exists_point_of_loc (+2 more) | proved |
| roadmap/selmer/certified-rank-sel.md | ZInQ.RouteK.Selmer.CertifiedRankSel | statement formalized (def) |
| roadmap/selmer/character-sums.md | ZInQ.RouteK.Selmer.exists_xi, ZInQ.RouteK.Selmer.sum_quadraticChar_mul_sub, ZInQ.RouteK.Selmer.cubicCharSum (+7 more) | proved |
| roadmap/selmer/covering-classes.md | ZInQ.RouteK.Selmer.loc_torsion, ZInQ.RouteK.Selmer.loc_mul_sq_iff, ZInQ.RouteK.Selmer.loc_congr_sq (+1 more) | proved |
| roadmap/selmer/covering-x-form.md | ZInQ.RouteK.Selmer.cov_iff_loc | proved |
| roadmap/selmer/coverings.md | ZInQ.RouteK.Selmer.Cov, ZInQ.RouteK.Selmer.Loc, ZInQ.RouteK.Selmer.SqEq (+5 more) | statement formalized (def) |
| roadmap/selmer/good-primes.md | ZInQ.RouteK.Selmer.loc_padic_good_iff, ZInQ.RouteK.Selmer.loc_padic_good_even, ZInQ.RouteK.Selmer.loc_padic_good_of_units | proved |
| roadmap/selmer/kummer-map.md | ZInQ.RouteK.Selmer.loc_iff_kummer, ZInQ.RouteK.Selmer.kummer | proved |
| roadmap/selmer/local-rows.md | ZInQ.RouteK.Selmer.loc_padic_selPair_iff_rows, ZInQ.RouteK.Selmer.classCond_dvd_iff_rows, ZInQ.RouteK.Selmer.loc_real_selPair_iff (+6 more) | proved |
| roadmap/selmer/padic-squares.md | ZInQ.RouteK.Selmer.isSquare_padic_iff, ZInQ.RouteK.Selmer.isSquare_two_adic_iff, ZInQ.RouteK.Selmer.unitPart (+8 more) | proved |
| roadmap/selmer/place-two.md | ZInQ.RouteK.Selmer.loc_two_adic_iff, ZInQ.RouteK.Selmer.loc_two_adic_iff_of_odd, ZInQ.RouteK.Selmer.loc_two_adic_five | proved |
| roadmap/selmer/proposition-0.md | ZInQ.RouteK.Selmer.prop0Statement, ZInQ.RouteK.Selmer.Prop0Statement, ZInQ.RouteK.Selmer.prop0 (+2 more) | proved |
| roadmap/selmer/real-place.md | ZInQ.RouteK.Selmer.loc_real_iff, ZInQ.RouteK.Selmer.loc_real_iff_int | proved |
| roadmap/selmer/selmer-group.md | ZInQ.RouteK.Selmer.Sel2, ZInQ.RouteK.Selmer.classInt, ZInQ.RouteK.Selmer.selPair (+2 more) | statement formalized (def) |
| roadmap/rank-5b/README.md |  | chapter README |
| roadmap/rank-5b/certified-rank-5b.md | ZInQ.RouteK.Rank5b.CertifiedRank5b | statement formalized (def) |
| roadmap/rank-5b/certified-rank-sel-of-5b.md | ZInQ.RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b | proved |
| roadmap/rank-5b/corollary-4-4.md | ZInQ.RouteK.Rank5b.det_M5b_eq_one, ZInQ.RouteK.Rank5b.natAbs_classInt_zero, ZInQ.RouteK.Rank5b.lam8_prod_pow | proved |
| roadmap/rank-5b/cross-checks.md | ZInQ.RouteK.Rank5b.det_M5b_21, ZInQ.RouteK.Rank5b.det_M5b_5, ZInQ.RouteK.Rank5b.Config.M5bc_of_iso (+12 more) | proved |
| roadmap/rank-5b/kernel-class-five.md | ZInQ.RouteK.Rank5b.Config.card_sols_eq, ZInQ.RouteK.Rank5b.Config.hEquivKer, ZInQ.RouteK.Rank5b.Config.solEquivTorsH (+29 more) | proved |
| roadmap/rank-5b/lemma-4-1.md | ZInQ.RouteK.Rank5b.sel2_ncard_eq_four_mul, ZInQ.RouteK.Rank5b.sel2HEquivKer, ZInQ.RouteK.Rank5b.sel2HEquivKer_apply (+2 more) | proved |
| roadmap/rank-5b/lemma-4-2.md | ZInQ.RouteK.Rank5b.det_border_eq_dotProduct, ZInQ.RouteK.Rank5b.border_mulVec_inl, ZInQ.RouteK.Rank5b.border_mulVec_inr (+1 more) | proved |
| roadmap/rank-5b/smith-matrices.md | ZInQ.RouteK.Rank5b.M5b, ZInQ.RouteK.Rank5b.M1, ZInQ.RouteK.Rank5b.Lmat (+17 more) | statement formalized (def) |
| roadmap/rank-5b/theorem-4-3.md | ZInQ.RouteK.Rank5b.det_M5b_eq_dot, ZInQ.RouteK.Rank5b.Config.det_M5bc_eq, ZInQ.RouteK.Rank5b.Config.ofKer_zero (+1 more) | proved |
| roadmap/main/main-theorem-two-hypotheses.md | ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeDensity, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense (+1 more) | proved |
| roadmap/main/main-theorem-selmer.md | ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_goodPrimeDensity, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_greenTaoDense (+2 more) | proved |

Hypotheses not proved here: CR₃^Sel (selmer/certified-rank-sel.md: Ш(C_d)[2] = 0 for these curves,
which rests on Kriz's 2-converse with Poonen–Stoll, or on Tian–Yuan–Zhang with
Gross–Zagier–Kolyvagin) and CertifiedRank5b (rank-5b/certified-rank-5b.md: rests on Smith's row-5b
identity with the genus sum, the proof of TYZ Theorem 3.5(2), Gross–Zagier–Kolyvagin and Kummer
surjectivity; logically stronger than CR₃^Sel). The definitions GoodPrimeAP, GreenTaoDense and
GoodPrimeDensity are statements that are now proved; each article says so and links the proof.

## Existing articles changed

| Article | Change |
| --- | --- |
| roadmap/README.md | Preface: two hypotheses; 22P not needed. Five chapters added to the list |
| main/README.md | Paragraphs and links for CR₃^Sel and row 5b, route AP, Green–Tao, Proposition D and the two new main-theorem articles |
| main/main-theorem.md | Says that 22P is not needed and links the two-hypothesis theorem (statement and Lean names unchanged) |
| main/prime-pattern.md | 22P is now used only by the three-hypothesis theorem and is not needed; links route AP and 22P_AP |
| main/certified-rank.md | Proposition 0 and Theorem 4.3 are now formalized (links); the rank-one theorems are not |
| main/main-theorem-selmer.md (new) | Also lists the CR₃^5b + 22P variant from ZInQKernel/RouteK/Rank5b.lean |
| route-k/selmer-system.md | "Proposition 0 is not formalized here" is replaced by a link to selmer/proposition-0.md |
| multiplication/completeness/README.md | Pointer to route AP |
| coverage/README.md | Section 6 row amended; Section 5.1 row notes that Proposition 0 is proved; five new DECOMPOSED rows (route AP, Green–Tao, Proposition D, Proposition 0, row 5b) |

## Statement corrections: the articles state the Lean where it differs from the research notes

- Route AP (nt-22p §3). Lemma P does not assume F(t) > 0; in parts (1) and (2) it only fixes the
  sign η = 1, and the condition sits in field 2′. Part (2) also gives a rational ball around a centre
  m/ℓ^k. Part (3) is stated for either sign η and needs only v_p(R₀) = 2e and v_p(t−1) = −e. Under
  field 2′ the pole input satisfies v_p(B) ≥ 4 at the old primes, not ≥ 103C_p + 8; pole completeness
  needs only 4. Weak approximation with p-adic residue targets is a new lemma.
- Green–Tao (gt-dense). The window lemma has no hypothesis that the set consists of primes. Its
  constant is c₁ = c·log 2/24, and it uses only Chebyshev's lower bound. The transference density is
  δ = α·c₁/192.
- Proposition D (pd-paper). Lean has no separate lower-Dirichlet-density theorem. theorem-d.md
  states the conditional result (a uniform bad-prime bound implies positive relative upper density),
  and proposition-d.md states Proposition D. The note's Proposition 5.3 (Dirichlet density implies
  relative upper density) is dirichlet-density.md. The constants differ from the note's: A = 14402
  with a non-explicit N₁, and a sharper prime tail. Lemma 1.5 holds for every odd p.
- Proposition 0 (nt-prop0). Solubility is stated in the x-form, which is equivalent to the projective
  covering for nonzero a, b. Lemma T holds for every odd d. That this set is the textbook Sel₂
  (Silverman X.1.4) is not formalized, and the article says so.
- Row 5b (tyz-5b). The Lean form of Corollary 4.4 assumes |a| ≡ 7 (mod 8), a special case of the
  note's "odd part ≡ 3 (mod 4)". Lemma 4.1 and Theorem 4.3 are first proved for every configuration
  of class 5 (kernel-class-five.md). The note's claim about C₂₁ comes from computation, not from Lean
  (cross-checks.md).

## Notes for the next agent

- The blueprint task prescribed density/proposition-5-3.md. It was renamed proposition-d.md,
  because the Lean's Proposition D is not the note's Proposition 5.3.
- `Submission.green_tao` (ThirdParty/GreenTao) resolves under `--lean-root .`.
- The 32 older chapter READMEs without article_id are a known gap from before this task. Assigning
  their ids is a separate step (`migrate article-ids --write`).
- The site and the dependency summary were not regenerated. The repository README and KERNEL_PLAN.md
  already describe this work and were not changed.
