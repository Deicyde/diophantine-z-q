# Version 18 dependency and application delta for PR98

Additive inventory prepared after the first expanded review round, 14 November 2026. This record addresses I98 without replacing the historical Version 17 source, citation, or theorem-application inventories.

## Revision and review state

This record describes `manuscripts/quartic_v18.tex` at PR98 head `f02b28ffa00a0669538c1fe6048b7e32faa2a235`, against base `631aabecd67750ae1b9bbed0596d59a52e5a8fe5`. The manuscript SHA-256 is `8f4a6a99ce63b1bf6c7ab2fe71507795507a94281a775bf02fa07ca2be9359ae`. All manuscript line numbers below refer to those exact bytes.

The full [live Astra report](https://github.com/elliotglazer/diophantine-z-q/pull/98#issuecomment-6882956153), created 2026-11-14 at 19:24:51 UTC for run `43631033751`, says **changes requested**. It records favorable scoped mathematical checks, but leaves I98, the BLR source-access finding S98, and interrupted-history completeness finding H98 open. [Fable completed the same round and accepted](https://github.com/elliotglazer/diophantine-z-q/pull/98#issuecomment-6883004537), subject to its explicit scope limitations. There is no current cross-family acceptance, release approval, or whole-manuscript certification.

Status terms in this delta have separate meanings:

- **Proof supplied:** the argument is present in the pinned Version 18 text.
- **Internal same-family reviewed:** non-author project agents inspected the proposed proof or its integration. Their scoped records are evidence, not an outside-review or Protocol B acceptance.
- **Live outside-review observation:** the current Astra report inspected the stated application and records a favorable result or limitation. This does not change Astra's overall `changes_requested` decision. Fable's separate acceptance and exclusions are linked above.

## Squarefree reduction: new auxiliary proofs

The new subsection is `subsec:v18-squarefree-reduction`, lines 25166–25566. It defines an exact pullback of the published squarefree majorant on `Z/(En)`, with its own cutoff `(En)^kappa`. The target modulus `W=EQ` and final quadratic count are retained. It does not assert identity with the former cutoff-`n^kappa` weight or generic fixed-E versions of every source theorem.

| Auxiliary result | Supplied proof and dependencies | Immediate consumers | Review state |
| --- | --- | --- | --- |
| `v18tz:lem:mean`, conditional and interval means, 25274–25299 | Divisor-square expansion and CRT, using coprimality of surviving divisor moduli with E; published TZ equation (36) and one-form Theorem 15. Error `O(L^(2kappa-1) log L)` at fixed E. | Constant-factor conditioning at 25342–25353; boundary interval mean at 25129–25133 and 25359–25376. | Proof supplied; internal same-family reviewed; live Astra favorable scoped check. |
| `v18tz:lem:forms`, conditioned polynomial forms, 25301–25358 | Published squarefree Theorem 15 at the stated doubled complexity; independent-copy second moments; preceding mean lemma for the possible single constant factor. Exact profile rescaling supplies logarithmic endpoint slack without a cutoff comparison. | Pullback products in the weighted boundary argument at 25113–25128 and 25359–25376, including the enlarged true-count period. | Proof supplied; internal same-family reviewed; live Astra favorable scoped check. |
| `v18tz:lem:norm`, localized global norm identity, 25385–25417 | Source difference-multiset definition, exact residue-pair counting, and total variation. Step becomes `q/gcd(E,q)` and interval length is divided by `E/gcd(E,q)`; includes the probability weights and rounding error. | Gaussian global input transported at 25488–25503; the same-model comparison and concatenation at 25504–25520. | Proof supplied; internal same-family reviewed; live Astra favorable scoped check. |

The supporting exact pullback, average, prime-domination and endpoint arguments are at 25180–25266. They feed all three rows. Endpoint deletion is restored with a vanishing error, not assumed to preserve pointwise domination at the original cyclic zero.

## Published squarefree applications

The common source is Tao–Ziegler, *Polynomial patterns in the primes*, Forum of Mathematics, Pi **6** (2018), e1, [doi:10.1017/fmp.2017.3](https://doi.org/10.1017/fmp.2017.3). The source edition is the final published article. The live Astra report inspected the listed statements; its correction search was targeted, not an exhaustive literature audit.

| Source item | Exact Version 18 application and hypothesis check | Consumers |
| --- | --- | --- |
| §1.1, pp.8–11; equation (36), p.29 | Difference-multiset conventions at 25378–25417; published weight on the enlarged group and canonical representatives at 25180–25266. | Three auxiliary lemmas and the norm/model chain. |
| Theorem 15, pp.57–58 | 25274–25358: mixed unit residues, unrestricted constant coefficients, bounded nonconstant coefficients, nonconstant differences and independent copies. | Mean/forms lemmas; boundary localization at 25113–25138 and 25359–25376. |
| Theorem 11, p.28, and Proposition 4, pp.35–36 | 25228–25264 and 25442–25486: the endpoint-corrected lift is bounded by the published prime weight; use the PET-produced **linear step polynomials**, model exponent `rho/B0`, and one bounded model. | Both Corollary 3 approximations. The special model-one clause is not applied to Artin weights or residue-supported lifts. |
| Corollary 3, pp.38–39, equations (53)–(54) | 25465–25486: the same Proposition 4 model approximates global progression norms and averaged local box norms. | Compare `H` with `mu*1_C` at 25504–25520, without imposing support on H. |
| Theorem 9, p.21 | 25504–25520: divide `H-mu*1_C` by a fixed bound; use every required q and the corrected fine scale `M0/Q^(1/rho)`. The smallness threshold is independent of the coefficient parameter. | Local smallness for the exact lifted centered factor. |
| Theorem 13, p.41 | 25423–25462 and 25522–25535: actual lifted quadratic polynomials have **all** coefficients `O_E(Q)`, including constants, so fit `Q^(1/rho)`; mixed residues and quadratic differences are allowed. | Centered terms vanish; the pure mean's factor `1/E` cancels the exact averaging factor. |

These applications have supplied connecting proofs and internal same-family integration review. Astra's current report records favorable scoped checks of this chain and regards the written-reduction objection R2-F7 as resolved within that inspected mathematical scope. Its overall decision remains changes requested; this row is not an Astra acceptance claim. Fable also checked and accepted this squarefree reduction at the changed-draft scope.

Affected manuscript consumers are the Gaussian bridge and boundary calculation, 25020–25163; fixed-field polynomial count `prop:v5-artin-patterns`, 25589–25698, especially 25640–25667; prime-selection/final diagonal, 25839–25883; and interfaces P15–P20, 2316–2333, and C09–C10, 3361–3363. The updated summary is at 2016–2049. The unchanged Gaussian/GI, ray-density and obstruction-tail suppliers retain their prior scoped statuses. This delta does not re-prove or recertify them.

## H4 at an arbitrary allowed old conductor

The changed proof is 9007–9085, within the finite Heegner-descent setup beginning at 8888. Its target is equation (H4), 9004–9005. The old conductor need not be squarefree; maximality is used only at the new inert prime. All entries below feed that target and then the common-place derivative calculation H13–H19, 9214–9317, and immediate coefficient-push consumers through 9413.

| Source input | Version 18 application | Source/application review status |
| --- | --- | --- |
| Cai–Chen–Liu, *Heegner points on modular curves*, TAMS **370** (2018), §2.3/Theorem 2.15, p.3730 | Compatible CM lattice/level construction at 8972–8986 and 9007–9019; conductor changes only at the new inert prime. | Proof supplied; internal same-family reviewed; final publisher offprint and application inspected favorably in live Astra report. |
| Fowler, *Some uniform effective results on André–Oort for sums of powers in C^n*, §2.1, pp.612–613; [doi:10.1017/S0305004125101825](https://doi.org/10.1017/S0305004125101825) | Integral j-invariants for arbitrary orders at 9021–9022. | Internal source/application review; live Astra inspected final article and recorded favorable scoped check. |
| Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed. (2009), VII.5.5 | Potential good reduction and one common finite local extension, 9023–9024. | Internal same-family reviewed; live Astra checked statement and relevant author errata. |
| Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), §1.2 Definition 1 and Proposition 8, pp.12,15; bibliography `v18-blr`, 45442–45444 | Extend isogenies, duals and order actions at 9025–9028; extend the fixed modular map pi over the smooth source at 9068–9072. | Proof/application supplied; internal same-family review reports reading local scans. **S98 awaits reviewer disposition:** live Astra obtained only publisher preview/metadata. The owner-requested [PR source clarification](https://github.com/elliotglazer/diophantine-z-q/pull/98#issuecomment-6883007278) supplies brief quotation fragments, a summary and access to the exact pages. No scan or extended excerpt is included here. Fable accepted H4 but explicitly did not check these printed locators; no completed outside source-access check is claimed. |
| Silverman III.6.4(c), V.3.1; III.4.10(a), II.2.12 | Supersingularity contradiction at 9030–9038; one geometric kernel point, inseparable degree ell, and relative Frobenius factorization at 9048–9056. | Internal same-family reviewed; live Astra checked these statements and relevant errata favorably. |
| Stacks [02LS](https://stacks.math.columbia.edu/tag/02LS), Lemma 37.44.1; [039E](https://stacks.math.columbia.edu/tag/039E), Lemma 37.16.4 | Proper map with finite fibres is finite; fibrewise flatness gives finite locally free degree ell, 9040–9047. | Full online statements/proofs read internally and by live Astra. Application checked favorably, conditional on the preceding Néron extensions. |
| Diamond–Im, *Modular forms and modular curves*, §9.3, p.79 | Smooth proper coarse model of X0(N) at 9068–9069; enables the second Néron mapping-property application. | Internal same-family and live Astra source/application checks; the BLR dependency remains separately open. |

Prime-to-ell level specialization, including powers of two, is supplied at 9058–9066. The common-place finite-sum argument is supplied at 9077–9082. It preserves rational ell-power Frobenius in H4/H13, rather than replacing it by ell-squared Frobenius. Howard §1.7 equation (13), p.1456, is only a restricted-conductor corroborating reference at 9083–9085, not the supplier of the extended old-conductor scope. The separate conductor-one oriented-CM correspondence is not broadened by this repair.

## Evidence and limits

Internal project agents reviewed the proposed mathematical notes and their integration at bounded scopes before this live round. Those internal reviews are not substituted for the publicly linked Protocol B reports. The current independent evidence is Astra's report and Fable's report, each tied to the same manuscript bytes.

Fable accepted both changed arguments, but explicitly excluded printed-locator verification for Silverman, BLR, Diamond–Im, Howard and Fowler's published pagination; the unchanged Gaussian estimate and its suppliers; the internal proofs of Tao–Ziegler's theorems; a whole-file historical-wording scan; the 265-environment byte-identity check; and any Version 18 PDF/build. Its acceptance is for this draft-file change, not record promotion. Astra's report supplies some of these source checks, but still requests the BLR source access, interrupted-history account and this inventory delta. Their distinct scopes must not be combined into an assertion that every excluded item has been independently verified.

The [interrupted-review observations](reviews/pr98-interrupted-43624840610/README.md) preserve the original three Astra messages, the two original infrastructure-failure records and a full artifact manifest for H98. Neither an interrupted note nor an infrastructure label is an acceptance.

This record supplies the missing inventory artifact for I98; reviewer verification is still required. It does not close S98 or H98, promote Version 18, or certify source/PDF correspondence, unchanged foundations, polynomial data, variable counts or numerical records. Historical Version 17 inventories remain unchanged and retain their original revision bindings.
