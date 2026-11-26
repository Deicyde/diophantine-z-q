# GZRank: `hRank` replaced by single-print rows (work in progress)

This directory prepares, additively, the replacement of the root hypothesis `hRank`
(`ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne`) of
`ZInQ.OneProof.frozenTarget` by refereed single-print rows. Nothing existing is changed.
Base: `main` at `9f98d2946011ebbab63aee3e144075b275badafd`.

## Files

* `Row.lean`: the rows `GZThm73NonTorsion` (Gross–Zagier (7.3)(1)) and `CarayolCor08`
  (Carayol Cor. 0.8), with the printed text quoted.
* `Consumer.lean`: the pole proof's consumer, copied with `NonTorsionOfAnalyticRankOne` in place
  of the rank hypothesis.
* `Glue.lean`: modularity in Gross–Zagier's form from BCDT and Carayol, and the point of infinite
  order.
* `FoldCheck.lean`: `frozenTarget_with_GZ`, the body of `frozenTarget` with `hRank` replaced by
  the rows.

## Why the consumer needs less than `hRank`

`PoleRC.crm_of_restrictedConverse_M` (`Contrib/PoleRC/MordellWeilM.lean`) reads its rank
hypothesis `KolyvaginRankOne` once, through `exists_not_isOfFinAddOrder_of_rank`, and passes the
point of infinite order to `DescentGlueM`. `Consumer.lean` copies `crm_of_restrictedConverse_M`,
`crm_of_restrictedConverse_proved` and `SilvermanRank.poleCompleteness_of_rankOne` with
`NonTorsionOfAnalyticRankOne` (analytic rank one gives a point of infinite order) in their place.
The other inputs (`mordellWeilM`, `descentGlueM`, `lemma54At_of_casselsTatePairing`,
`PoleRC.poleCompleteness_of_crm`, `simultaneousConstruction`) are used unchanged, as
`frozenTarget` uses them. `simultaneousConstruction` lives in
`Contrib/OneProof/PoleCompletenessFromRCGenuine.lean`, a module that imports `PoleS12.Leaves`;
that module was not read, and the new rows mention no constant of it.

## Design choice for modularity: a Carayol row, not a Lean proof

Gross–Zagier's Chapter V, §2 (p. 310) assumes a newform `f` of weight 2 and level `N` with
`L(E, s) = L(f, s)`. BCDT's printed Theorem A gives an eigenform on `Γ₁(N)` with all coefficients
`a_n(E)`; the tree proves that it has trivial nebentypus (`BCDTPrint`) and extracts a newform `g`
of a level `M ∣ N` with `a_p(g) = a_p(E)` at almost all primes (`NewformGlueG0`). Equality at the
primes dividing `N / M` cannot be proved from the Hecke theory in the tree: the BCDT form is in the
span of the level raises `g(dz)`, and the local identities are consistent with `L_p(E) ≠ L_p(g)`
(additive reduction at `p ∤ M`, where `f = g − a_p(g) g(pz) + p g(p²z)` is not excluded; or
multiplicative reduction at `p ∤ M`, excluded only by the Ramanujan bound). The missing input is
local-global compatibility at the bad primes, which no Lean statement here covers, so no proof of
reasonable size exists. `Glue.lean` therefore uses the minimal extra row, Carayol's Cor. 0.8, read
from the numdam page images (p. 411) and quoted in `Row.lean`.

## Fold plan

The fold would replace the argument `hRank` of `frozenTarget` by `hGZ`, `hB` and `hC`, with
`frozenTarget_with_GZ` as the new body (the H bundles, `hRC` and `hCT` unchanged).

* removed: `hRank`, `SilvermanRank.SilvermanAEC_C_16_5_5_RankOne`; consequence, GLUE (rated:
  Miller's Thm 4.4 assembles cited results).
* added: `hGZ`, `GZRank.GZThm73NonTorsion`; published, unread (the page was read here by an AI;
  it needs the adversarial reading).
* added back: `hB`, `BCDTPrint.BCDTThmAPrinted`; published, LEAF/LEAF when it was a row (until
  the forward-rank fold of 2026-11-20 removed it), journal check MATCH (JAMS 14, pp. 843–845);
  its review row records the verdict CONSEQUENCE (AI audit of the author manuscript).
* added: `hC`, `GZRank.CarayolCor08`; published, pending reading on two dictionary items (`E_f`
  read through its isogeny class; "rationnelle" left implicit).

Counts: 22 open hypotheses (19 H + `hRC`, `hCT`, `hRank`) become 24 (19 H + `hRC`, `hCT`,
`hGZ`, `hB`, `hC`). Outside H the strict count goes from 0 LEAF / 3 GLUE to 1 LEAF / 4 GLUE
(`hB` LEAF; `hGZ` and `hC` glue until read), and to 3 LEAF / 2 GLUE if both readings clear.
The rows also give less than `hRank` claimed: no row asserts rank one, only a point of infinite
order, which is all the pole proof uses.

## Rows that still need a reading

* `hGZ`: Theorem (7.3)(1), p. 231, with the standing assumption of Chapter V, §2, pp. 309–310,
  and the proof on p. 312 (Gross–Zagier, Invent. Math. 84 (1986); the GDZ scan, PDF SHA-256
  `d0c9d7761c6fc5395e2335bd02b58af400f1910e3f708adbe5aa81c96d1a1751`). Inside the proof the
  choice of `K` cites Waldspurger and Vignéras (p. 309) and the covering map cites Faltings
  (p. 310); (7.3) itself is Gross–Zagier's own theorem.
* `hC`: Corollaire 0.8, p. 411 (Carayol, Ann. Sci. ÉNS (4) 19 (1986); the numdam scan, PDF
  SHA-256 `d4a5fb6b1cd76f944f8948e06df1c7ad5656ae5ee14b9189178ee1e8f2b0dab8`). The reading must
  rule on (ii) `E_f` read as any elliptic curve with `a_p(E) = a_p(f)` at almost all primes, and
  (iii) the rationality of `f` left implicit (see the docstring).
* `hB`: already rated; the conductor item (the level of condition (2) is not identified with
  `N(E)`) is unchanged.

Before a merge the integrator also needs `docs/research/locators.md` rows and `kinds.tsv` rows
for `hGZ` and `hC`; they are outside this directory and so not part of this pull request.
