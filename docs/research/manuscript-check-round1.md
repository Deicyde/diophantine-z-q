# Manuscript check, round 1: five tasks that finished before the standing ask

Task mcheck-r1, 2026-11-17. This file adds Manuscript check tables to five tasks that finished before Jack's standing
ask ("we want to check the correctness of his original manuscript"). The tables are built only from each task's
report and from the manuscript lines listed below, read for this file. No Lean was run.

Sources:

* the manuscript, `diophantine_zq.tex`. The four task branches carry a copy identical to origin/main's, and the lines
  quoted for pc-from-rc are the same in the copy at 4781de837;
* the reports, `docs/research/TASK.md` on each task branch (pc-from-rc: round 1, at commit 4781de837).

Verdicts:

* **OK**: the step as written is correct and complete, and the task formalized or checked it.
* **gap filled**: the text omits or only sketches something, and the task supplied it. ON THE SPOT marks items that
  are in neither the manuscript nor a print the task read.
* **error**: the text claims something false, or cites a source that does not support the claim.
* **unverified**: the task did not check the step, or checked it only against a print it did not read.

Where a task found a gap but did not fill it, the verdict is **unverified** and the reason says "gap (open)". Each such
gap is also listed under "Issues for the ledger".

## 1. y3-route-a: the integral model of `Y_3` (tex L423-477)

Report: `docs/research/y3-route-a.md` on origin/wip/y3-route-a. The task states the conclusion of L473-477 as one leaf,
`Y3RouteA.Y3FullThreeRepZ30`, and proves in Lean that the kernel's field `Y3Fix.Y3FineModuliAbP` follows from it.
Steps 2-5 of the derivation are not formalized (report §4).

| tex lines | step | verdict | reason | evidence |
|---|---|---|---|---|
| L423-441 | `N/(A_f^* K_3)` acts on `Y_3`; degree ≤ 324 | unverified | outside the task's scope: the report covers L443-477 only | reading only |
| L443-446 | Buzzard Thm 2.1 / Cor 2.3 applied at `V_1(5)` over `ℤ[1/30]` | unverified | the locator is UNVERIFIED (print not read). The task confirmed that the manuscript cites Buzzard only at level 5, which is prime to 6. The wrong level-3 citation was the kernel's, not the manuscript's | report §0 item 1, §2 step 1 |
| L447-449 | full five-marking: finite étale cover | unverified | not formalized; Mathlib lacks the tools (report §4) | report §2 step 2, §4 |
| L449-462 | `Isom_𝒪(𝒪/3𝒪, A[3])` finite étale and nonempty on geometric fibres (Tate lattice free over `𝒪_3`) | unverified | the task recorded the argument but did not check it | report §2 step 3, §4 |
| L464-472 | `G_5 = (𝒪/5𝒪)^*` acts freely; `1+3M_4(ℤ_3)` is torsion-free | unverified | not formalized. y3-audit's Serre-lemma rigidity is an alternative, which this task did not use | report §2 step 4, §2 last paragraph |
| L467, L474-475 | "polarized automorphism"; descent of "its canonical principal polarization" | gap filled (ON THE SPOT) | the text never says where the canonical principal polarization comes from. The task supplied it through relative Lemma P (it exists, is unique, and is compatible with isomorphisms). This is ON THE SPOT and not proved in the tree, and the claim that Buzzard's moduli problem is unpolarized is UNVERIFIED | report §0 item 2, §2 "No polarization" |
| L472-476 | `X_35/G_5` smooth projective; universal objects descend; represents the full-three problem | unverified | taken as the leaf `Y3FullThreeRepZ30` (kind consequence, GLUE), not proved. The Lean form is weaker (proper rather than projective; locally noetherian bases only) | report §1, §2 "How the Lean statement differs" |
| L476 | "its generic fiber is `Y_3`" | gap filled | the text does not say that it uses the identification of the moduli scheme over ℚ with `Sh_{K_3}`. The task proves that the generic fibre represents the problem over ℚ (`y3RepresentableQ_of_z30`), and the identification is the separate leaf `deligneCanonicalModelY3Every*` (Deligne, Bourbaki 389) | report §0 item 3; `Y3RouteA.y3RepresentableQ_of_z30` |
| L476-477 | the auxiliary five-marking adds no degree factor | unverified | not discussed in the report | reading only |

## 2. carirr-refold: Carayol at step D5 (tex L742-751, L791-794, L852-857, L9774-9806)

Report: `docs/research/carirr-refold.md` on origin/wip/carirr-refold. The task replaces the research row
`carayolThmAIrr` with a weaker leaf, `CarayolRefold.CarayolThmAFrob`. It proves oddness instead of assuming it, and it
proves that DDT 3.1 implies the new leaf. The conductor clause stays packaged as in DDT 3.1, because Carayol's form
(local Langlands) cannot be stated in Lean.

| tex lines | step | verdict | reason | evidence |
|---|---|---|---|---|
| L852-857 | D5: "local–global compatibility for the weight-two modular representation" bounds the primitive level `N` | gap filled | the sentence has no citation, and it needs both Carayol's Théorème (A) and Casselman's `a(π_p) = v_p(N)`. The project supplies Carayol A + local Langlands + Casselman Thm 1, packaged as the DDT 1997 Thm 3.1 conductor clause. D5 needs only `v_p(N) ≤` the conductor exponent. The locators are UNVERIFIED, and the leaf is flagged unread | report "Issues" items 1-2, §2 conductor row; `CarayolRefold.CarayolThmAFrob`, `carayolThmAIrr_of_frob` |
| L791-794 | the conductor is computed from `r_3` at 5 and from `r_5` at all other primes (including `p = 2` and `p ∣ N`) | unverified | the report records only which places D5 uses. The identification of `r_3` with the modular representation (L776-794) was not checked. That Carayol A covers every `p ≠ ℓ` comes from the locator audit's row R17, not from this task | report "Issues" item 1 |
| L742-751 | `r_ℓ` is odd (Betti comparison) | unverified | the task proves oddness of the leaf's `ρ` by a separate Chebotarev argument (`odd_of_frobDet`). It did not check the manuscript's Betti argument | report §1 "Proof of `odd_of_frobDet`" |
| L9774-9781 | Carayol §§0.3-0.7, Thm A, pp. 409-411 applied to `Π_f^∨` (place above 2, odd `p`) | unverified | the print was not read. This is the manuscript's only Carayol citation, and it serves Theorem 5.3, not D5 | report "Issues" item 1 |
| L9782-9796 | normalization: arithmetic Frobenius has good polynomial `X² − a_q X + qχ(q)` | unverified | the task adopted this reading as the source of the leaf's Frobenius clause, and `frob_of_DDT31` shows that it agrees with the DDT 3.1 transcription. Carayol's normalization itself was not read | report "Issues" item 3, §2; `CarayolRefold.frob_of_DDT31` |
| L9802-9806 | Casselman Thm 1, pp. 302-306 (newvector and conductor) | unverified | the print was not read; the report notes only that this is the manuscript's only Casselman citation | report "Issues" item 1 |

## 3. r16-shimura73: the r16 route (tex L768-794)

Report: `docs/research/r16-shimura73.md` on origin/wip/r16-shimura73. The task reroutes `r16CoreY` through the
manuscript's own sources, `LiFrickePrinted` and `ShimuraThm1Printed`. The reduction compiles, but it ends at an
unproved statement, `ShimuraTotalToComponents`.

| tex lines | step | verdict | reason | evidence |
|---|---|---|---|---|
| L768-770 | Li's Fricke formula (p. 296) makes the span of the coefficient conjugates Fricke-stable | gap filled | the text applies Li to every conjugate `f^σ`, which needs each conjugate to be a newform. Neither citation covers this, and the task supplied it as `ConjNewform` (Shimura 1971 Thm 3.52 + Galois stability of the new space; numbers UNVERIFIED). The deduction is proved. Li's locator is UNVERIFIED | report "Known issues" item 3, §3 step 1; `R16ShimuraLi.frickeStable_of_li` |
| L770-773 | Shimura 1973 Thm 1 (quotient + Euler-factor identity) ⇒ `r_5` is a constituent of `V_5(A_f)` | error | the locator audit read Thm 1 (pp. 526-527): it gives only the total Euler identity on `V_ℓ(A_f)`, which does not fix which embedding's traces each `K_f`-component carries (the `θ∘τ` remark, ON THE SPOT). The per-embedding statement needs Eichler–Shimura (Shimura 1971 Thm 7.9/7.14, or DS 9.6.5), which is not cited here. Not repaired. A reading of Shimura 1973 §0 and Thm 2 is still pending | report "Known issues" item 1, §3 step 3; `R16ShimuraLi.ShimuraTotalToComponents` (named, unproved) |
| L770-773 | Euler identity only up to finitely many Euler factors | unverified | the exceptional set is UNVERIFIED. Report item 2 concerns the Lean field, which asks for every `p ∤ Nℓ`. The manuscript itself uses only primes outside `T ∪ {3,5}` and the level (L778, L789-791), plus Chebotarev (L792) | report "Known issues" item 2; reading L776-794 |
| L773-774 | equivalently, `r_5^∨` is a cohomological constituent; the duality preserves the conductor | unverified | not discussed in the report | reading only |
| L776-794 | the same constituent statement used at `ℓ = 3` for `r_3` | unverified | the Lean route does not use r16 at three; not checked | report §4 |

## 4. pc-from-rc, round 1: Theorem 5.2 from Theorem 5.3 (tex L1005-1121)

Report: `docs/research/pc-from-rc.md` at commit 4781de837. Main theorem:
`ZInQ.Manuscript.PoleRC.poleCompleteness_of_restrictedConverse_final`, which proves PC from RC. Its open hypotheses are
`Lemma54At`, `KolyvaginRankOne`, `MordellWeil`, `MatrixRealization` and four local Kummer images. The report cites
some lines 2-4 below where they stand in the tex at that commit (for example "line 1062" and "line 1068"); the rows
below use the tex's own numbers.

| tex lines | step | verdict | reason | evidence |
|---|---|---|---|---|
| L1020-1031 | squareclass bookkeeping: choice of `m`, `β ≡ 17`, `θ ≡ 1 (mod 24)`, mutual local squares | OK | proved in Lean with no extra hypotheses | report §4 step 1; `bookkeeping` (Contrib/PoleRC/Bookkeeping.lean) |
| L1033-1035 | the simultaneous construction of `n`, `nθ` is credited to S11-S12 | unverified | S11-S12 were not used; the step enters as the GLUE hypothesis `MatrixRealization` | report §0 item 1 |
| L1036-1042 | matrix conditions: `ker K = ⟨1, 1_β⟩` and `λ ∉ im K` on both supports | unverified | stated in Lean as `MatrixConditions`, but their realization is not proved. Numerical evidence: 60 random `(β, θ)`, plus `ℓ = 323` and `ℓ = 5627` | report §2, §5; `MatrixConditions`, `MatrixRealization` |
| L1042-1056 | slot construction, `K♯ = K + λaᵗ`, nonsingular block, Boolean assignment, Dirichlet realization | unverified | gap (open): this is a sketch. The vector `a` is undefined, the link to `ker K` and `λ ∉ im K` is not spelled out, and the report's reading of "full-product coefficient" is SPECULATIVE. Not formalized | report §0 item 4, §7 item 1 |
| L1058-1059 | shape of a Selmer representative: no factor 2, positive first coordinate | gap filled | asserted without proof. It follows from the real image (`LocalReal`, proved) and the 2-adic image `{a odd, b ≡ 1 (mod 4)}` for `ℓ ≡ 3 (mod 4)`, which the text does not state. `LocalTwo` is a hypothesis, checked by sampling | report §0 item 2, §5 `local2.py`; `localReal`, `LocalTwo` |
| L1060-1065 | the necessary local equations | gap filled | stated without derivation. The task derives them (together with the 2-adic equation `sᵗv = σ`) in Lean from the four local images. Those images are GLUE hypotheses, matched by brute force for 55 values of `ℓ < 700` | report §4 step 3, §5 `compare.py`; `dimThreeCount_of_local` |
| L1065-1067 | the matrix properties force `v = 0`, `δ = 0`, `u ∈ ker K`, so at most eight classes | gap filled | the claim is correct, but it needs facts the text does not state: three reciprocity identities for `K`, a duality step, `rank Kᵀ = rank K`, the 2-adic equation and the classes with negative second coordinate. All are proved in Lean | report §0 item 3; `kmat_forces`, `dimThree_linear_algebra`, `kmat_transpose`, `sgn_dot_one`, `lam_dot_one` |
| L1067-1070 | the extra class is local everywhere and independent, so the dimension is three | gap filled | asserted. The task proves that the eight classes `(3^σ c, (−ℓ)^σ)` lie in `SelM`, conditional on the local-image hypotheses | report §4 step 3 "Sufficiency"; `dimThreeCount_of_local` |
| L1072-1084 | Lemma 5.4: dimension three gives corank one (Cassels–Tate, Poonen–Stoll) | unverified | enters only as the interface `Lemma54At`, because the Selmer predicate is abstract | report §0 item 6 |
| L1086-1109 | Lemma 5.5: forward rank 0/1 (BCDT Thm A, Kolyvagin Thm 1, Kato Cor 14.3) | unverified | the printed leaf `KolyvaginRankOne` (rank only) has not been read. Kolyvagin is cited as the MPIM preprint MPI/90-69, not a refereed print, and BCDT as the author manuscript (the refereed version is JAMS 14, 2001). The route needs only rank ≥ 1; Kato is not used | report §0 items 5 and 7, §3 |
| L1111-1114 | apply RC to `n` and `nθ`; rank one and `Ш[2] = 0` make the Kummer class come from rational points | OK | the complete 2-descent `descentGlueM` is proved. `CRM` follows from RC + Lemma 5.4 + Lemma 5.5 + Mordell–Weil. Only a point of infinite order is used | report §4 step 5, §0 item 7; `crm_of_restrictedConverse`, `descentGlueM` |
| L1114-1121 | rescale to the eleven witnesses with `w = (eHz)⁻¹`; `θ = 1` case | OK | proved in Lean | report §4 step 4; `witnesses_of_points`, `poleCompleteness_of_crm` |

## 5. r3prime-etale: holomorphic charts (Lean-side bridge)

None. The bridge `ZInQ.R3Etale.isHolChart_iff_isSerreChart'` relates two Lean chart notions. It relies on no step of
the manuscript, which uses the stable Faltings height of the literature (L598, L872). The report marks the
identification ON THE SPOT, outside the manuscript.

## Issues for the ledger

* **error**, L770-773 (r16-shimura73): Shimura 1973 Thm 1, as the locator audit read it, gives only the total Euler
  identity, not the per-embedding constituent `r_5 ⊂ V_5(A_f)`. The missing citation is Eichler–Shimura (Shimura 1971
  Thm 7.9/7.14, or DS 9.6.5). A reading of Shimura 1973 §0 and Thm 2 is pending.
* **gap filled**, L768-770 (r16-shimura73): Li is applied to every conjugate `f^σ`, which needs the conjugates to be
  newforms. Uncited; supplied as `ConjNewform`.
* **gap filled**, L852-857 (carirr-refold): D5's "local–global compatibility" has no citation. It needs Carayol A and
  Casselman Thm 1, which the manuscript cites only in the appendix (L9778, L9802-9806). The project's leaf packages
  the conductor clause as DDT 1997 Thm 3.1.
* **gap filled (ON THE SPOT)**, L467 and L474-475 (y3-route-a): the source of the "canonical principal polarization"
  is not stated. The task supplied relative Lemma P, which is not proved in the tree.
* **gap filled**, L476 (y3-route-a): "generic fiber is `Y_3`" uses the canonical-model identification with `Sh_{K_3}`
  without saying so.
* **gap (open)**, L1042-1056 (pc-from-rc): the Boolean-assignment construction is a sketch (`a` in `K♯ = K + λaᵗ` is
  undefined; the link to `ker K` and `λ ∉ im K` is missing). It is not formalized; numerical evidence only.
* **gap filled**, L1058-1059 (pc-from-rc): the shape of the Selmer representative needs the 2-adic Kummer image
  `{a odd, b ≡ 1 (mod 4)}`, which the text does not state.
* **gap filled**, L1060-1065 (pc-from-rc): the necessary local equations are stated without derivation. They are
  derived in Lean from the local images.
* **gap filled**, L1065-1067 (pc-from-rc): "the matrix properties force `v = 0`, `δ = 0`, `u ∈ ker K`" needs the
  reciprocity identities for `K`, a duality step and the 2-adic equation. All are proved in Lean.
* **gap filled**, L1067-1070 (pc-from-rc): the sufficiency of the eight classes is asserted. It is proved in Lean
  from the local images.
