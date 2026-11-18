# r16-thm1b (done 2026-11-17)

**GLUE count: 5/24 on 29 -> 5/24 on 29 (strict and strictest). Count-neutral; no --allow-rise** (round 2's two-row
version was +1). Out: afShimura, heckeJ1DS (GLUE). In: shimuraThm1Af, bShStandardModel (consequence, GLUE, pending
review).

**Result.**
* Merge check: R16ShimuraLi, R16CoreYDS965 and R16Thm1 build on the merged tree (e7ac05a33). Nothing broken.
* Ruling (a): one row, `R16Thm1b.ShimuraThm1Af` (ZInQKernel/Contrib/OneProof/R16Thm1b.lean): there is a triple with
  Shimura's (i)-(iii) and IsAfQuotient (C = I_f J), unique up to a nu-compatible iso over Q, and K_f is finite.
  Kind consequence, GLUE. Flag: the print (Ker nu p. 525, uniqueness p. 526, m = 1 / tangent space p. 527,
  C from the ideal ∩ End(J) p. 526) plus the ON THE SPOT steps (C = I_f J via ker rho, saturation and the Hecke
  relations both ways; (ii) for all n from p, p^2; nu-compatible isos). `afShimura_of_thm1Af` is proved (standard
  axioms). shimuraQuotientIsAf is dropped, and so is the DS 6.6.4 / Shimura 1971 Thm 7.14 citation.
* (b) xi_{p^2} = T_p^2 - p<p> is a theorem step on the row (the xiSq docstring is fixed).
* (c) The misprint is located in the f_sigma sentence before (iv), p. 526. Fixed in Known issues 1, in the
  R16Thm1.lean docstring and in the flag.
* (d) B-Sh: "the Hecke ring is rational" (p. 526) covers only the rationality part. Left ON THE SPOT: (B1) the
  kernel's IsX1Gen model is Shimura's standard model (defined by the print's citation of Shimura 1971), and (B4) the
  double-coset convention dictionary. So the 1971 departure shrinks but does not vanish.
* (e) ShimuraTotalToComponents is not in this fold.

**Compiles:** R16Thm1b.lean; scratch/r16-thm1b/FoldCheck.lean (sixContactMin_of_open77 standard). #discharges:
afShimura by R16Thm1b.afShimura_of_thm1Af, heckeJ1DS by R16Thm1.heckeJ1DS_of_bSh. The exact kinds rows are in
report section 5 and kinds-diff.txt. Spec: scratch/r16-thm1b/autofold.json.

**Remains:** a review of shimuraThm1Af's three steps against pp. 525-527; B-Sh (B1)/(B4); Jack's ruling on
L770-773 vs DS 9.6.5. Report: docs/research/r16-thm1b.md (has the Manuscript check).
