# Version 18 source applications and derivations

This is the first replacement for [PR107](https://github.com/elliotglazer/diophantine-z-q/pull/107), split at the owner's request after both standard-budget reviews were incomplete. It changes only source applications, their connecting arguments and locators, two supporting-source access links, and the reproducible power-call certificate. Status-language removals and general prose/notation changes are deferred. The existing local inverse proof remains in place. The separate inverse-theorem adoption may follow this PR; it does not need to wait for unrelated cleanup.

Base manuscript SHA256: `8f4a6a99ce63b1bf6c7ab2fe71507795507a94281a775bf02fa07ca2be9359ae`. Candidate SHA256: `2a1d1c5137a863e5c575c19f4aae9f59f96dec819aa6aa4042a7a4ca8a1f51c0`. All line numbers below refer to the candidate. This is an author-prepared review submission, not an independent acceptance. The official selector still names Version 17. Released Versions 16 and 17, the polynomial, variable count, statement environments and labels are unchanged.

## Application and consumer locations


| Passage | Source and hypotheses | What the text uses |
|---|---|---|
| Local control, lines 19129-19164 and 19203-19232 | Nekovar, *Selmer complexes*, Asterisque 310 (2006), Corollary 8.4.8.2(i), p.215; Kato, Asterisque 295 (2004), (12.2.3), p.220. The actual coefficient is a finite free quadratic twist over the local real cyclotomic Z2 tower. | The specialization injection, local duality, and Nakayama show that the local characteristic element has no factor at the augmentation prime. Inverting 2 permits the fixed finite-sign decomposition. The two repeated applications now use the same argument. No new global H3 assertion is made. |
| Atkin–Lehner, lines 8999-9019 and 20463-20497 | Atkin–Lehner, *Hecke operators on Gamma_0(m)*, Math. Ann.185 (1970), Lemma8 p.138, Lemma9 p.139, Theorem3(iii) p.147, Lemma33(iii) p.156 and Theorem6 p.157. Divisors of the level are exact; the twist conductor actually used is odd and prime to the old level. | Cusp permutation and the differential give the translation formula. An explicit weight-two Mellin calculation supplies the global minus sign. Successive Legendre twists give the existing odd quadratic-twist formula. This is not a claim covering an arbitrary even twist conductor. |
| Quadratic Gauss sums, lines 18894, 18927 | Montgomery–Vaughan, *Multiplicative Number Theory I*, Theorem9.17, p.300. Primitive quadratic character and signed fundamental discriminant, with the manuscript's positive-exponential convention. | The existing signed square identity, including even discriminants. |
| Kummer pairing, lines 9674-9710 | Guillot, *A Gentle Course in Local Class Field Theory* (2018), Lemma1.20 and Theorem1.22, pp.11–13. Characteristic zero, the required roots of unity, and the finite radical subgroup. | The pairing for the actual possibly dependent radicands; no independence of the radicands is assumed. |
| Split-cubic halving, lines 22332-22360 | Direct tangent-line argument over a field of characteristic different from two with distinct split roots. | Only the necessary implication that halving a nonzero two-torsion point makes both root differences squares. No unavailable Bekker–Zarhin theorem number is imported. |

The relevant final source pages were inspected in local preparation, including the publisher-formatted Montgomery–Vaughan chapter and Guillot preview that contains the required pages. This statement records preparation scope, not a substitute for this PR's two reviewers. Public access points are [Nekovar](https://www.numdam.org/item/AST_2006__310__R1_0.pdf), [Kato](https://www.numdam.org/article/AST_2004__295__117_0.pdf), [Atkin–Lehner](https://doi.org/10.1007/BF01359701), [Montgomery–Vaughan chapter](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf), and [Guillot preview](https://api.pageplace.de/preview/DT0400.9781108389860_A35309221/preview-9781108389860_A35309221.pdf).

The remaining source changes are as follows. These are source-to-consumer statements for review, not claims to have independently verified each paper's full proof.

| Existing application | Citation or clarification | Retained limits |
|---|---|---|
| Surface Tate determinant and coefficient-prime-independent trace, lines 2571, 2583-2594, 2624-2636, 5765-5773, 6597-6627, 13551-13574 | Milne, *Abelian varieties* (1986), Section16 for the polarization pairing and Proposition12.9 for the endomorphism characteristic polynomial. [source 1](https://www.jmilne.org/math/articles/1986b.pdf) | The Tate-module convention is unchanged. The rank-four symplectic determinant is the square of the multiplier. |
| Division-polynomial recursion, lines 5402-5432 | Silverman, *The Arithmetic of Elliptic Curves*, ExerciseIII.3.7, with the author's 2015 correction for pp.105–106. [source 1](https://www.math.brown.edu/johsilve/AEC/AECErrata2015.pdf) | The actual formulas are unchanged; the citation now identifies the corrected numerator convention. |
| Primitive-form extraction, lines 2563-2577, 5691-5707, 5775-5805 | Deligne–Serre (1974), Sections1.6–1.9, pp.509–510, and the existing PartI modularity argument. [source 1](https://www.numdam.org/item/ASENS_1974_4_7_4_507_0/) | The primitive twisting character uses its least conductor. Li's uniqueness and Fricke statements remain separate inputs. Chebotarev and semisimplicity identify the same representation. |
| Pan local-ring inputs, lines 2561, 5808-5827 | Allen–Newton–Thorne (2020), Section3.1, Proposition3.1. [source 1](https://doi.org/10.1112/S0010437X20007484) | The published correction concerns the nilreduction of the trivial-character local ring. The separate project argument for distinct-character integral flatness is still identified as such. The final-Pan-body access limitation remains. |
| Dyadic character restriction, lines 6647-6672 | Serre, *Local class field theory*, Section2.4, p.141, norm functoriality. | The restriction is composition with the norm. The norm of a unit is a unit, and the quadratic local character has conductor at most four. The existing ramification argument then applies. |
| Ring-class fields and conductor kernels, lines 8895-8907, 8948-8956, 9098-9116, 9239-9243, 9703-9719 | Cox (1989), Sections7 and9, Proposition7.22, the proof of Theorem7.24, and Lemma9.3. [source 1](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf); [source 2](https://dacox.people.amherst.edu/primes/typos2.pdf); [source 3](https://dacox.people.amherst.edu/primes/typos3.pdf) | Cox prints the order-to-maximal-order sequence; the relative sequence is derived in the manuscript by comparing its two idelic quotients. The order conductor remains arbitrary. The arguments explicitly account for the only global units, plus or minus one, and for rational principal ideals prime to the conductor. |
| Unramified reduction and local cocycles, lines 7039-7056, 9165-9198, 12510-12523, 14898-14914 | Silverman VII.2.1–VII.2.2 and Lang (1956), Theorem1 and its corollary. | The model is minimal integral, the extension is unramified, and the connected smooth special fibre is the object to which Lang applies. |
| Global-to-local Brauer comparison, lines 2535-2537, 6525-6544, 13478-13500 | Milne, *Arithmetic duality theorems*, I.1.6(b), and proof of II.2.1, p.164. [source 1](https://www.jmilne.org/math/Books/ADTnot.pdf) | This repeats the source already used for the same comparison elsewhere in the manuscript. |
| Product decomposition at no greater stable height, lines 3193-3207, 36238-36276 | Remond (2017), Theorem1.6, p.1175, as a structural input to the existing Gaudron–Remond construction. [source 1](https://ems.press/content/serial-article-files/38664?nt=1) | This is not a claim that the 2017 theorem itself proves height monotonicity. The unverified final-2022-source comparison is still explicit. |
| Rooted-forest minors, lines 22479-22506 | Chaiken (1982), the all-minors matrix-tree identity. [source 1](https://epubs.siam.org/doi/10.1137/0603033) | This is a polynomial identity and does not require an invertible Laplacian. The manuscript's separate symbol and contraction identities still need their own proofs. |
| Natural-valued arguments to the precision circuit, lines 11974-11987, 12266-12289 | Direct traversal of the frozen arithmetic circuit, SHA256 `f3e163f5c60b972c98b48647274f956dd7d78428e27ddc0543574a5f18120b8c`. | All three arguments of each of 15,845 calls were checked using nonnegative constants, natural variables, addition and multiplication. Call outputs were not assumed nonnegative to prove their own arguments. |
| Singular-moduli source key and unchanged stack context, lines 13307-13317, 35737-35741 | Existing stack argument and a distinct Gross–Zagier (1985) singular-moduli bibliography key. [source 1](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1515/crll.1985.355.191/fulltext.pdf) | No coarse-model pullback is imported from Yuan's Lemma2.1. The separate Gross–Zagier Heegner-points reference remains unchanged. |
| Waldspurger locator correction, lines 19692-19708 | Waldspurger (1981), Proposition 17 and proof pp.461–465; Proposition 18 and proof pp.466–476; Lemma 41 and proof p.476. [source 1](https://mate.dm.uba.ar/~nsirolli/files/waldspurger.pdf) | These exact pages were visually compared in the local source comparison. The existing ICM citation is retained; this is not a new whole-theta-lift audit. |
| Deligne homogeneous-polarization bibliography correction, lines 6110-6117, 6123-6135, 44884-44887 | Deligne, Travaux de Shimura (1971), Variante 4.8, p.146. [source 1](https://www.numdam.org/item/SB_1970-1971__13__123_0.pdf) | The bibliography range now includes §4.8, matching the existing consumer. Page146 was visually compared in the local source comparison. |

## Reproducible power-call certificate

Finding `43663199880-1-fable-N107-1` asked for executable evidence of the added natural-argument assertion. [The checker](../../scripts/check_precision_call_arguments.py) is bound to the saved circuit SHA256 `f3e163f5c60b972c98b48647274f956dd7d78428e27ddc0543574a5f18120b8c`; [its tests](../../scripts/test_precision_call_arguments.py) exercise malformed references and uncertified arguments. The existing required construction CI job runs both, then retains `precision-call-arguments.json` in its artifact. No kernel workflow or contract pin is changed.

Each node gets one certification bit. Nonnegative decimal constants and declared explicit natural variables are certified. Sums and products inherit certification only when both earlier arguments have it. Call outputs are never certified. Induction on node order proves that each certified node is a polynomial with nonnegative integer coefficients. At every power call all three parameter expressions, including the proposed result, must have that bit. The final argument slot is a private-variable offset, not a DAG edge. Sparse explicit indices and disjoint private allocations are checked separately. Large constants are checked lexically, without integer conversion or expansion.

The frozen file has 293,620 nodes, 54,056 explicit natural variables and 15,845 calls. All 47,535 parameter occurrences pass. The variables include explicit natural witnesses, not only the five named input variables. Neither the parent root nor a private block is assumed to vanish. This check proves the stated finite domain property; it does not prove the arithmetic meaning of the power template or the whole Diophantine theorem.

## Prior findings and remaining review

PR107's original decisions remain at [run 43661223026](https://github.com/elliotglazer/diophantine-z-q/actions/runs/43661223026) and [run 43663199880](https://github.com/elliotglazer/diophantine-z-q/actions/runs/43663199880). Neither run accepted that larger change. Earlier favorable observations apply only to the passages actually inspected, not to the whole replacement.

* `43661223026-1-astra-S107`: exact Atkin-Lehner source comparison remains part of this PR's review. Fable resolved it in round two using institutional OCR with an explicit symbol-reading limitation; Astra did not complete it. Their distinct judgments are preserved.
* `43661223026-1-astra-C107` and `43661223026-1-fable-F107-1`: this PR narrows the changed scope and gives a full base/head map below. The remaining status and prose blocks are not accepted by exclusion; their review is deferred to their own PRs.
* `43661223026-1-fable-F107-2`: each changed source application still needs its published hypotheses checked. Access links and historical favorable observations do not replace that check. Nekovar's full source/correction comparison and Guillot access were incomplete in the prior gate reports. Fable reported obtaining two erratum pages without a chapter 8 entry, but could not exclude provider truncation.
* `43661223026-1-fable-F107-3`: status-language removal is not in this PR. Fable accepted the prior disclosure repair, while Astra left coverage and a consolidated manuscript pointer open. The later status PR must preserve these distinctions.
* `43663199880-1-fable-N107-1`: the committed checker, negative tests, required CI execution and in-text link are the proposed repair. They still require review.
* `43663199880-1-fable-N107-2`: H170's original obligation remains unchanged in this source-only manuscript. It is also explicitly carried in [the pending cleanup status](version18-cleanup-status.md), to prevent losing it when the separate status change or inverse adoption removes that passage.

## Atkin-Lehner access

The [official scan](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0185/LOG_0035.pdf) has SHA256 `18ca10d80324eeba53190fe06ebbfcd0a3d981e9a643e0e1b753b416b0ee1c91`. Institutional OCR is available for [p.138](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000148.xml), [p.139](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000149.xml), [p.147](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000157.xml), [p.156](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000166.xml), and [p.157](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000167.xml). Mathematical symbols in OCR must be compared with the scan. Nekovar's book correction list is [selerr.pdf](https://webusers.imj-prg.fr/~jan.nekovar/pu/selerr.pdf), not the parity-paper erratum. No source scan or extended book excerpt is added here.

## Complete changed-manuscript map

Read these paired ranges at base and head. This is the entire manuscript diff for this PR, not the 213-hunk scope of PR107.

| Block | Base lines | Candidate lines |
|---|---:|---:|
| S01 | 3196-3202 | 3196-3202 |
| S02 | 5417-5424 | 5417-5425 |
| S03 | 5762-5768 | 5763-5770 |
| S04 | 5787-5813 | 5789-5807 |
| S05 | 5821-5827 | 5815-5829 |
| S06 | 6604-6611 | 6606-6613 |
| S07 | 6653-6662 | 6655-6667 |
| S08 | 8895-8901 | 8900-8907 |
| S09 | 8942-8948 | 8948-8955 |
| S10 | 8995-9001 | 9002-9011 |
| S11 | 9097-9102 | 9107-9115 |
| S12 | 9158-9165 | 9171-9183 |
| S13 | 9219-9225 | 9237-9244 |
| S14 | 9674-9687 | 9693-9708 |
| S15 | 12251-12256 | 12272-12286 |
| S16 | 13460-13467 | 13490-13497 |
| S17 | 18208-18214 | 18238-18244 |
| S18 | 18514-18520 | 18544-18550 |
| S19 | 18860-18866 | 18890-18897 |
| S20 | 18892-18898 | 18923-18930 |
| S21 | 19102-19114 | 19134-19162 |
| S22 | 19157-19168 | 19205-19217 |
| S23 | 19652-19660 | 19701-19711 |
| S24 | 20419-20424 | 20470-20482 |
| S25 | 22274-22282 | 22332-22345 |
| S26 | 22433-22440 | 22496-22504 |
| S27 | 35670-35680 | 35734-35744 |
| S28 | 36196-36202 | 36260-36267 |
| S29 | 44819-44825 | 44884-44890 |
| S30 | 44834-44839 | 44899-44928 |
| S31 | 45447-45452 | 45536-45567 |
