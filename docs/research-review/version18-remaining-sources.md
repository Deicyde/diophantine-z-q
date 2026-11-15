# Version 18 remaining source applications and citations

This combines the remaining source-application and citation changes after
PR108 and PR111. It includes 25 body units, S01-S14, S16-S20, S23-S24 and
S26-S29, plus the remaining entries from bibliography blocks S30/S31. S15/S25
and S21/S22 are already incorporated. The three groups below are parts of one
candidate, not a sequence of future PRs. The current manuscript selector and
all released files remain unchanged.

The manuscript is an author proposal for independent review. This record maps
published inputs to their uses and preserves source-access qualifications.
It does not certify the complete theorem or erase historical objections.

Base manuscript SHA256: `ca1ea465a0ebae934162a2c278186ab09477a91f14b60eefa71c5398ee71a165`.
Candidate manuscript SHA256: `2761f01d08dc8d3e5453b4ae4a9a3e462cac53639f55134223849a31261b792c`.

The candidate includes the printed-source clarifications recorded below.
The exact source is rebuilt and checked before publication. The theorem statements, labels,
polynomial and variable count are unchanged. The inverse-theorem replacement
and status/prose cleanup are separate changes.

## Complete changed ranges

| Base lines | Candidate lines |
|---|---|
| 2505-2505 | 2505-2521 |
| 2627-2627 | 2643-2661 |
| 3098-3098 | 3132-3132 |
| 3199-3199 | 3233-3233 |
| 3568-3573 | 3602-3609 |
| 3602-3604 | 3638-3650 |
| 5168-5167 | 5214-5222 |
| 5420-5421 | 5475-5477 |
| 5765-5765 | 5821-5822 |
| 5790-5794 | 5847-5850 |
| 5799-5799 | 5855-5855 |
| 5801-5810 | 5857-5859 |
| 5824-5824 | 5873-5881 |
| 6607-6608 | 6664-6665 |
| 6643-6643 | 6700-6702 |
| 6656-6659 | 6715-6721 |
| 6672-6671 | 6734-6748 |
| 6676-6677 | 6753-6755 |
| 8898-8898 | 8976-8977 |
| 8945-8945 | 9024-9025 |
| 8998-8998 | 9078-9081 |
| 9100-9099 | 9183-9185 |
| 9161-9162 | 9247-9264 |
| 9222-9222 | 9324-9325 |
| 9677-9678 | 9780-9782 |
| 9684-9684 | 9788-9789 |
| 13472-13473 | 13577-13578 |
| 13668-13669 | 13773-13780 |
| 18220-18220 | 18331-18331 |
| 18526-18526 | 18637-18637 |
| 18872-18872 | 18983-18984 |
| 18904-18904 | 19016-19017 |
| 19677-19683 | 19790-19805 |
| 20448-20447 | 20570-20576 |
| 22467-22468 | 22596-22598 |
| 35704-35704 | 35834-35834 |
| 35708-35708 | 35838-35838 |
| 36230-36230 | 36360-36361 |
| 44853-44853 | 44984-44984 |
| 44868-44867 | 44999-45054 |
| 44928-44927 | 45115-45117 |
| 44930-44930 | 45120-45120 |

## Ring-class kernels and the actual conductor

Cox, *Primes of the form x^2+ny^2* (1989), Sections7 and9, Proposition7.22, the proof of Theorem7.24 and Lemma9.3 supply the order-to-maximal-order class-group sequence and conjugation description. The manuscript does not attribute the relative old-conductor sequence directly to the printed proposition. It compares the two idelic quotients to derive that sequence for the actual old conductor, retains the unit quotient, and notes why the available units are just plus or minus one in this application. Rational principal ideals prime to the conductor give trivial Artin action. No division by the old class number is introduced.

The consumers are the derivative-class descent and simultaneous radical prescriptions in the same finite-Heegner argument. The proof for arbitrary old conductor already incorporated from PR98 remains unchanged. The new citations identify the source input to that proof rather than replacing the relative argument with a more restrictive printed case.

Source access: [university-hosted Cox scan](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf), and the author's [second-edition corrections](https://dacox.people.amherst.edu/primes/typos2.pdf) and [third-edition corrections](https://dacox.people.amherst.edu/primes/typos3.pdf). These are locators for comparison; no book scan is committed.

## Atkin-Lehner translation and signs

For the exact-divisor involution used on the modular parametrization, equality of the pulled-back invariant differentials makes the two maps differ by a constant. Evaluating at infinity gives the stated cusp-translation formula. The elliptic-curve parametrization has trivial nebentypus, and the later quadratic twist has odd conductor prime to the old level. These are the hypotheses actually used; no arbitrary even-conductor twist is asserted.

The supplier is Atkin-Lehner, *Hecke operators on Gamma_0(m)*, Math.Ann.185 (1970): Lemma8 p.138, Lemma9 p.139, Theorem3(iii) p.147, Lemma33(iii) p.156 and Theorem6 p.157. The manuscript includes the weight-two Mellin calculation fixing the global minus sign and then applies the successive Legendre twists. The consumers are the finite-Heegner cusp relation and theta-weight parity calculation. The differential argument and the Mellin calculation are the manuscript's connecting proofs, not quotations of broader statements.

[Official scan](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0185/LOG_0035.pdf), SHA256 `18ca10d80324eeba53190fe06ebbfcd0a3d981e9a643e0e1b753b416b0ee1c91`. Institutional OCR is available for [p.138](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000148.xml), [p.139](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000149.xml), [p.147](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000157.xml), [p.156](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000166.xml), and [p.157](https://gdz.sub.uni-goettingen.de/gdzocr/PPN235181684_0185/00000167.xml). OCR symbols must be checked against the scan. Earlier reviews that read only OCR did not supply that visual comparison.

## Unramified minimality and local descent

Silverman VII.2.1-VII.2.2 gives the reduction sequence and formal-group identification for a minimal integral model. It does not itself prove that the model stays minimal after unramified extension. The candidate now supplies that additional input from Tate, *Algorithm for determining the type of a singular fiber in an elliptic pencil* (1975), Sections7-8, pp.47-52, with the short comparison of its two runs written at the use site.

The fields are finite extensions of Q_p, their residue fields are perfect, and the extension is unramified. Use the same uniformizer and the same original-ring lifts of each multiple root. The valuation tests and geometric root multiplicities agree; the double/triple roots needed for continuation already lie in the original perfect residue field. Thus minimality and rescaling decisions agree, including residue characteristics two and three. Extra splitting of distinct roots affects terminal component counts, not minimality. This statement was independently checked against every branch of Tate's printed algorithm in local preparation; it still requires the gate's review.

The unchanged consumer is (H10): the smooth-reduction and formal subgroups yield the stated local cohomology vanishing through Lang's theorem and the normal-basis argument. The use never divides by the unramified degree. The geometric component-group multiplier is retained.

Sources: [Tate's original paper scan](https://wstein.org/Tables/antwerp/tate/tate.pdf), SHA256 `8650805838f84ad1bc9afa169b1797bd345fb7d9ea4628cdf995c83a10aaccfc`; [institutional Silverman second-edition PDF](https://www.pdmi.ras.ru/~lowdimma/BSD/Silverman-Arithmetic_of_EC.pdf), with VII.2.1 on printed p.188 and VII.2.2 on p.191. Silverman's abbreviated VII.5.4 proof assumes residue characteristic at least five; it is not silently used for the dyadic case.

## Dependent-radicand Kummer pairing

Guillot, *A Gentle Course in Local Class Field Theory* (2018), Lemma1.20 and Theorem1.22, pp.11-13, give the perfect finite Kummer pairing. The field may be infinite over Q; it must contain the required roots of unity and the radical extension is finite. Independence of the chosen radicands is not a hypothesis.

The manuscript works over K(mu_(2^infinity)). At each odd prime with nonzero weight the cyclotomic layer is unramified. Valuations of every relation therefore give the needed divisibility, so the proposed multipliers define a character on the actual radical subgroup. The pairing realizes it by an automorphism. This checks relations rather than assuming independent generators and is the input to simultaneous moving characters.

[Publisher-formatted preview containing the complete statements](https://api.pageplace.de/preview/DT0400.9781108389860_A35309221/preview-9781108389860_A35309221.pdf), SHA256 `e70d9f19b7987a1c993e897234f2ecd566b375a6f366075cda537f40a23a0268`. This is a partial-book preview, not full-book access.

## History and remaining obligations

PR108's F108-2 objected to unavailable source comparisons, including Guillot and the Silverman passages. Its bounded acceptance withdrew those edits; it did not verify them. This candidate submits these applications again with the source comparison and additional minimality argument. PR107's Atkin-Lehner and coverage findings likewise retain their historical status. No earlier reviewer conclusion is promoted into approval of this combined candidate.

H170 remains open in the separate cleanup-status record. The pending inverse-theorem adoption and subsequent status/prose cleanup are outside this batch. Historical finding identifiers are background; a reviewer should use only the gate-provided prior-finding identifiers in its formal disposition list.


## Primitive-form extraction

The supplier is Deligne-Serre, *Formes modulaires de poids 1* (1974), Sections 1.6-1.9, printed pp.509-510: [official paper](https://www.numdam.org/article/ASENS_1974_4_7_4_507_0.pdf). Part I M3 applies its primitive/degeneracy decomposition to the actual nonzero twisted form h, whose first coefficient is one and whose ambient level is M r squared. Here r is the least conductor of the actual Dirichlet character. Good-prime Hecke operators commute with the degeneracy maps, so uniqueness of the decomposition gives a primitive constituent with the same eigenvalues. Normalization and the retained trace, semisimplicity and irreducibility argument identify the representation. This step gives no bound on the primitive level N. Li's separate uniqueness/Fricke result is not the existence supplier.

The [historical primitive application](https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/research/quartic214-protocol-d-progress/CURRENT_NATIVE_PRIMITIVE_APPLICATION.json), identifier `Q214-CURRENT-NATIVE-PRIMITIVE-EXISTENCE-20261112`, has SHA256 `f48bd1e36bb3c39eab9e217a3b76907748bdc067f4f8040df4564353829ffd87`. Its pending historical status is not upgraded here. The older Li-existence attribution in [direct-p5 SOURCES.md](https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/research/version14/proofs/direct-p5-modularity-v1/SOURCES.md) is superseded for this substep by M3/Deligne-Serre. The historical file is preserved unchanged.

## Three distinct local-ring claims

The immediate global modularity supplier remains the published statement of Pan's theorem in Calegari's ICM chapter, printed p.624: [official chapter](https://ems.press/content/book-chapter-files/33140?nt=1). This candidate does not replace it with a claimed complete project proof of Pan's work.

Allen-Newton-Thorne (2020), Section 3.1, Proposition 3.1, printed p.2406, concerns generic reducedness of `(R_v^1)_red/(lambda)` in its stated trivial-residual/trivial-character setup: [published paper](https://doi.org/10.1112/S0010437X20007484). Nilreduction is taken before passage to the special fibre. This is neither generic reducedness of the unreduced special fibre nor a proof of unreduced distinct-character integral flatness.

The latter assertion is supplied separately by the project's [local-ring proof](https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/research/version14/proofs/pan-local-rings-v1/PROOF.md), SHA256 `4eec0cf2d9c56a5ebd4880def6a232abc689d88c36a89227c6781ebd13cda5d7`, in its bounded n=2, p=5, q congruent to 1 modulo 5, distinct tame eigenvalue and fixed-determinant setting. Monic division and Cayley-Hamilton give the commuting matrix presentation without inverting an eigenvalue difference. The rank-one determinantal presentation is free over the coefficient DVR; its residual domain makes the indicated quadratic relation a non-zero-divisor. The determinant relation is monic. These give unreduced integral flatness in precisely that setting. The formal fixed/unrestricted-determinant comparison and reduced component comparisons retain their own hypotheses.

The [five-contract decision](https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/research/version14/proofs/pan-local-rings-v1/DECISION.json) is bounded source comparison and local connections, not acceptance of every branch or foundation of Pan's theorem. The consumers checked in local preparation are [Pan author v2](https://arxiv.org/pdf/1901.07166v2), Lemma 4.2.10(2), pp.45-46, and the component comparison on p.47. [Taylor's published paper](https://www.numdam.org/article/PMIHES_2008__108__183_0.pdf), Proposition 3.1/Lemma 3.2, pp.196-198, supplies the recorded reduced/component inputs. A complete comparison with the final Pan and Thorne publications remains outside this bounded record; existing limits are retained.

## Norm compatibility at two

The supplier is Serre, *Local class field theory*, Chapter VI in Cassels-Frohlich (1967), Section 2.4, printed p.141: [primary scan](https://www.math.arizona.edu/~cais/scans/Cassels-Frohlich-Algebraic_Number_Theory.pdf). The second diagram gives restriction of a base-field character as composition with the norm, with no degree multiplier. This is not a citation to Serre's 1979 book. The bibliography locator now includes Section 2.4.

In the manuscript, beta squared is the restricted character chi. The local factor of chi at two is quadratic with conductor at most four; the odd-conductor factors are unramified there. Norms take units to units, so beta to the fourth power is trivial on local units. The unchanged logarithm computation then makes beta trivial on the group of principal units of depth 3e+1, giving the stated break bound. No new ramification or splitting hypothesis is introduced.

## Evidence and limits

Local source preparation checked the actual M3 and native consumers, the bounded local-ring proof and decision, and Serre's printed page. The archive files linked above were read back at the exact archive commit and matched the inspected files byte for byte. The Serre PDF has SHA256 `01259375a6275b726e836ce209cee40ed6f98a5cefe1aa5ad40f2ad07a63169e`; its one-based PDF page 79 contains printed p.141. The complete-book web reader was unavailable on that check, so the downloaded page image was used. No scans are committed.

This section accounts for S04/S05/S07 and the Allen-Newton-Thorne bibliography atom, with the explicit Serre locator correction. Earlier findings, H170, the inverse-theorem adoption and later status/prose cleanup keep their separate status. Historical finding identifiers are context, not extra entries in a reviewer's gate-provided formal prior-findings list.


## Sources, supplied assertions and actual consumers

**S02 — division polynomials.** Silverman, *The Arithmetic of Elliptic Curves*, second edition (2009), Exercise III.3.7, printed pp.105–106, together with the [2015 author errata](https://www.math.brown.edu/johsilve/AEC/AECErrata2015.pdf), entry for that exercise on errata pp.10–11. On `y²=x³+Ax`, the general invariants specialize to `b2=b6=0`, `b4=2A`, `b8=-A²`. Removing `2y` from the even-index polynomials gives the existing recurrences; the corrected numerator has the displayed minus sign and denominator `4y`, hence the ordinate identity. Part(f) and the stated nonzero index/nonidentity point in the torsion-free carrier supply nonvanishing. The formulas are unchanged; the replacement cites their actual convention.

**S03/S06 — polarization and trace.** Milne, [“Abelian varieties” (1986)](https://www.jmilne.org/math/articles/1986b.pdf), §16, pp.131–132, gives the Galois-compatible Weil/Tate pairing and its alternating polarization form; Proposition 12.9, p.125, gives the coefficient-prime-independent characteristic polynomial of an endomorphism. For S03 the surface and polarization are over `F`; the nondegenerate rational pairing in dimension4 has multiplier `epsilon5`, so its top exterior form gives determinant `epsilon5²`. This requires no principal polarization or degree-prime-to-five condition. For S06 the preceding construction makes `u_p` an actual endomorphism of the reduced abelian variety, so its rational Tate trace is independent of `ell != p`. The following specialization and two-copy formula are separate retained arguments.

**S16 — Brauer comparison.** Milne, [*Arithmetic Duality Theorems*, second edition](https://www.jmilne.org/math/Books/ADTnot.pdf), I.Example 1.6(b), p.19, and the proof of II.Proposition 2.1, p.164. The latter explicitly gives `0 -> Br(K) -> direct_sum_all_v Br(K_v) -> Q/Z -> 0`. The difference class is in `H²(Q,mu2)=Br(Q)[2]` and vanishes at every finite place. Since Q has one real place, the invariant sum kills its remaining real localization, and injectivity kills the global class. I.1.6(c), also p.19, includes the real invariant normalization. This supports the finite-to-global step, not a new audit of the preceding character construction.

**S26 — rooted forests.** Chaiken, [“A combinatorial proof of the all minors matrix tree theorem”](https://doi.org/10.1137/0603033), SIAM J. Algebraic Discrete Methods 3(3) (1982), 319–329: unnumbered theorem/equation (2), p.319; restatement and proof pp.322–323; undirected specialization p.320. Its formal weighted minor identity supplies the grounded determinant and the cofactor sums. After multiplication by the attachment weights, these give `det(Q)` and `c_a^t adj(Q)c_b` under the manuscript's retained contraction rules. Polynomial specialization permits symmetric weights, the manuscript's coefficient ring and singular `Q`; no matrix inverse is required. This citation does not itself prove the contraction rules.

**S19/S20 — both Gauss-sum sites.** Montgomery–Vaughan, *Multiplicative Number Theory I* (2006), §9.3, Theorem 9.17, p.300, with the square identity discussed on p.299; [author-hosted chapter](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf). For the primitive quadratic character of fundamental discriminant `d`, the two sign cases give `tau²=d`. Here `d=Delta_h`, not necessarily `h`; for odd squarefree signed `h`, `Delta_h/h` is1 or4. Thus the displayed basis change has only its fixed dyadic factor, including the negative-discriminant and even-conductor cases. Both repeated consumers use this same convention.

**S23 — theta/Fourier locators.** Waldspurger, [“Correspondances de Shimura,” ICM1983](https://www.imj-prg.fr/wp-content/uploads/2020/prix/waldspurger1983.pdf): Theorem 1(1)–(2), p.529, gives nonvanishing from the central L-value and the local tensor-product identification; Proposition 1, p.527, places the nonzero lift in the irreducible space `A00`, defined in §1.4, p.526, by orthogonality to unary theta series. In *Sur les coefficients de Fourier des formes modulaires de poids demi-entier* (1981), Proposition 17 starts on p.462, with setup p.461 and proof pp.462–465, especially equation(16), p.463; Proposition 18 starts on p.466 and its proof ends on p.476. These supply the Fourier-functional factorization and central-value normalization. Lemma 41 and its proof, p.476, give the positive-frequency holomorphic constituent, of lowest weight `k/2=3/2` here. These are the roles of the enlarged locators; the retained change-of-character and downstream local construction are not replaced by an unrestricted assertion about Proposition 18.

**S01/S28 — product-source identity.** Rémond, [*Variétés abéliennes et ordres maximaux* (2017)](https://doi.org/10.4171/rmi/967), Theorem 1.6, p.1175, supplies decomposition over the chosen base field under its maximal-order hypotheses, including the condition on isogenous factors. The direct manuscript supplier remains the proof of Gaudron–Rémond, [*Nouveaux théorèmes d'isogénie* (2023)](https://doi.org/10.24033/msmf.484), Lemma 16.2(1), pp.97–98. That proof first uses its reference [28], Rémond 2022 Corollary 1.3, for an isogenous object with no greater stable height, and then [25], Rémond 2017 Theorem 1.6, for simple factors, allowing repetitions. The new citations identify this structural dependency; they do not assign the height inequality to Theorem 1.6. Retain the historical June-2021-version/final-publisher-access qualification at the first consumer.

**S27 — protected CM convention and source.** Silverman, *The Arithmetic of Elliptic Curves*, second edition, C.Theorem 11.4, p.427, states `j(Lambda)^Frob(p)=j(Lambda p^(-1))` in its printed convention. Its all-primes-of-`H` good-reduction hypothesis matches the consumer's exclusion of every bad prime of the finitely many chosen models. Retain that convention and the fixed maximal-order setting; do not impose a different arithmetic/geometric Frobenius label. Gross–Zagier, [*On singular moduli* (1985)](https://doi.org/10.1515/crll.1985.355.191), pp.198–199, opening proof of Corollary 2.5 on p.199, supplies the forward inert-prime supersingular-reduction criterion, including the small primes. Bounds in the later congruence assertion do not restrict this opening criterion. The old 1986 Heegner-points key was the wrong work. Neither the lifting direction nor the adjacent Fowler/Cai–Shu–Tian assertions is re-audited here.

**S29 — homogeneous polarizations.** Deligne, [*Travaux de Shimura*, exposé 389](https://www.numdam.org/item/SB_1970-1971__13__123_0/), Variante 4.8, p.146, treats the alternating form up to nonzero rational scalar, supplying the existing homogeneous-polarization discussion and allowed sign change. Expanding the bibliography range from §§4.9–4.17 to §§4.8–4.17 identifies this source. The existing Hodge-sign and PEL arguments are unchanged.

**S17/S18 — access, not a new proof premise.** At both sites use [the supporting-note index at commit 005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f](https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/research/version14/SUPPORTING-NOTES.md). Both checked tag/commit targets returned the intended identical 12,549-byte file: Git blob `13238494d325d166d6f5cf4ecfc2a81f6bff9925`, SHA256 `4e85619afbf17a48f872c4a441204a73928160bf565fc56c6568b3253f0a80b1`. The tag `review-archive-v17` peeled to this commit; pinning it removes tag-movement ambiguity. The index preserves source hypotheses and review qualifications. Keep the sentence distinguishing source identity from proof verdict. The check did not recursively audit its linked proofs.

## Five new bibliography atoms

| Saved atom | Consumers | Identified source |
|---|---|---|
| S30 `silverman-aec-errata2015` | S02 | Dated 2015 author errata, Exercise 3.7 entry |
| S30 `chaiken1982` | S26 | SIAM J. Algebraic Discrete Methods 3(3), 319–329 |
| S30 `remond2017-maximal` | S01/S28 | Revista Matemática Iberoamericana 33(4), 1173–1195 |
| S31 `montgomery-vaughan2006` | S19/S20 | Cambridge Studies in Advanced Mathematics 97 (2006) |
| S31 `gross-zagier-singular-moduli-1985` | S27 | J. reine angew. Math.355 (1985), 191–220 |

These are the five new atoms for this citation subgroup. S29 modifies existing `Deligne1971`; the other existing source keys remain. The actual bibliography entries are in the manuscript diff; no unrelated S30/S31 entries are imported.

## Evidence, access limits and corrections to prior summaries

Local preparation used the scoped C1/C2 report (SHA256 `204e703684b8db9d4d78274e703765762a909cae554711146e975faeb1e03019`) and C3/access report (SHA256 `53aa6753cd87678479d903867079de2bccf07a208269c713208f3ef71e088ff4`). They are working records, not files supplied by this PR. The source statements, applications, public source locators and access limits needed for review are recorded here. Preparation checks do not replace the required gate reviews.

These synthesize direct primary-page checks, not just previous verdicts. Exceptions to unrestricted access remain explicit: Chaiken's author-posted PDF text was read through the web reader, but direct download was blocked and no local image/hash is claimed. The 1981 Waldspurger scan was read from the pinned local copy; a new attempt at its recorded university URL timed out. The Silverman division-polynomial pages and specialized derivation were inspected during preparation; this does not claim fresh remote access by the gate. Other stated primary passages were inspected as described in the component records. No new independent source audit was performed for this synthesis.

Retain these corrections when referring to Carbon's consolidated report: ICM Proposition1 is the irreducibility/`A00` statement, while Theorem 1(1) gives L-value nonvanishing; Milne p.164 explicitly displays the field/all-place Brauer sequence, not merely the compressed `Br(U)` formulation in that summary; Rémond 2022's page range is 1589–1596, as identified by the published 2023 bibliography. These corrections do not create additional manuscript changes in this batch.

## Preservation and review boundary

S27 alone intersects the protected old full-source arithmetic slice 35691–35779. Its source-key and printed-convention corrections must survive inverse integration, with the arithmetic formulas, maximal-order setting and all-bad-primes exclusion retained. No selected block lies in the old removed inverse section. Partial H044/H201 status/prose material remains deferred. Preserve the existing distinctions between a source identity, a scoped historical review and present whole-proof acceptance.

This citation subgroup accounts for fourteen units and five bibliography atoms, including both pinned links. It does not claim a merged PR or independent gate acceptance. Source scans/page images are local evidence and are not publication artifacts. The inverse adoption, status/prose cleanup and final assembled-proof acceptance remain outside this record.


## Printed-source clarifications before submission

The later source check identified an omitted explanation in the full G_Q determinant calculation. The manuscript now transports the selected fixed-Rosati polarization through the actual B-linear conjugate isogenies. Its positive rational multiplier q satisfies degree(mu)=q^2, and the chosen normalization gives a^2 q=1. Milne's isogeny functoriality for the Tate pairing then gives multiplier b^-2 kappa on all G_Q; the square of the alternating pairing gives determinant b^-4 kappa^2 without a sign ambiguity. This uses the existing non-CM and B-linearity constructions, not a new hypothesis. Sources: Milne, Abelian Varieties (1986), Theorem 11.1 p.120 and Section16 pp.131-132, especially Lemma16.2(c).

The ramification locators distinguish Fröhlich's Chapter I from Serre's Chapter VI in Cassels–Fröhlich (1967). The lower subgroup rule is Fröhlich Section9 Proposition3 p.34; Hilbert's different formula is Proposition4 p.36; the Herbrand functions are equations (6)-(8) p.37, and the tower identity is Theorem2(i) p.38. Serre Section4.1 p.155 supplies the upper quotient and reciprocity conventions; his Section4.3 p.158 gives the Artin conductor sum. The text supplies the change of variables from that sum to tame codimension plus the upper Swan integral. It also writes the absolute subgroup conversion explicitly. The historical extract and its unknown original retrieval URL retain their historical status; a fresh printed-page inspection is recorded separately.

The global theta step now cites precisely Waldspurger's ICM Theorem1(1) p.529 for nonvanishing, part(2) for local identification, and Proposition1 p.527 for the unary-orthogonal spectrum. The nonzero Fourier functional is the general theta-theorem input recalled from [W], Theorem1 at the start of the 1981 proof of Proposition18, p.467, before its scalar coefficient decomposition. This does not apply the complete scalar Propositions17-18 without their standing hypothesis H2. Printed H2 is a disjunction of three alternatives, not their conjunction. The manuscript's existing optional high-conductor character choice and its same-squareclass Corollary2 proof are unchanged; no new arithmetic premise or route was introduced. The 1980 foundational proof was not independently reopened in this check: the published 1981 and ICM statements were compared with the actual consumer.

These source checks found no new mathematical obstruction. The changes above expose derivations and correct attribution; they remain subject to the gate's review of this candidate. No book scan, extended source excerpt, or complete source PDF is included.
