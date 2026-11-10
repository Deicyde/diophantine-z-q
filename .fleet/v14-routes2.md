# v14-routes2 report: the published Version 14 against Version 13, and our hypotheses

Deliverable: `docs/research/v14-routes.md`, revised. Scripts and log: `scratch/v14-routes2/`
(`hunks.py`, `stmts.py`, `log.md`). Upstream's TeX, guide and the diff are kept outside the
repository and were not committed.

## Summary

- **Every hunk is classified (VERIFIED).** The diff of Version 13 against Version 14 has 72
  hunks. Git counts +2,953 −693; with carriage returns removed it is +2,948 −688, because five
  lines differ only in line ends. The classes:
  - the new section `sec:v14`: 1 hunk (V14 L22784-23739). It matches the `addition.tex` read by
    the first task at line offset +22783;
  - quartic constructions: 17 hunks;
  - the main construction's arithmetic argument: 34 hunks;
  - exposition, attribution and audit records, including the bibliography: 20 hunks.

  Each hunk is listed by label and line ranges in both files in §1 of the note.
- **No hypothesis is weakened, removed or replaced (VERIFIED).** These statements are
  byte-identical in 11/5, Version 13 and Version 14 (checked with `stmts.py`): Theorem 4.1,
  including every constant of `H₆(S;R)`, Lemma 5.1, Theorems 5.2 and 5.3, Lemmas 5.4 and 5.5,
  Proposition 6.2, `prop:generator` and `lem:assembly`. Our Lean statements `SixContactMin`,
  `CertifiedRankSel` and `GoodPrimeDensity` are unaffected.
- **The first task's main conclusion was wrong.** It had read only the new section and concluded
  that the main construction's arithmetic was unchanged. In fact Version 14 rewrites much of the
  proof of Theorem 4.1, tightens the proofs of Lemmas 5.4 and 5.5, changes the inverse-theorem
  source of Proposition 6.2 and repairs several steps of RC's proof. The note now says this.

## Changes that matter

**SixContactMin: the justification changed; the statement did not.**
- The proof of Theorem 4.1 grows from 557 to 987 lines, and Appendix H (`lem:de-rham-descent`)
  is deleted.
- Modularity is now the new Lemma `lem:qm-modularity-descent` (V14 L480-680).
  - Its supplier is "the published statement in [Calegari, ICM 2022, p. 624]; Pan's work is its
    proof source".
  - Berger's monodromy theorem and Conrad's local-algebraicity preprint are no longer cited.
  - The twist and weight are fixed by a new argument from Deligne–Serre, Kato 2004, Shimura and
    Li.
  - I checked the cited sentence in the arXiv source of Calegari's survey (2109.14145v1). It is a
    survey sentence, not a numbered theorem: Pan proves modularity up to twist of any geometric
    odd `ρ: G_ℚ → GL₂(Q̄_p)` with distinct Hodge–Tate weights, `p ≥ 5`. "Geometric" includes
    irreducibility and pst ⟺ de Rham.
- Baba–Granath's printed principal form is six times the determinant-one form, and their Lemma
  3.1 has a "local index slip" (V14 L699-702, L23870-23872).
- The integral model and its identification with the adelic level-3 curve are proved in full,
  through Deligne's PEL theory.
- Conductors are compared at every prime through Carayol 1987. h-leaves' uncited input I1 is now
  cited; I2, the reduction of `μ_σ`, is still uncited (V14 L1459-1460).
- Published editions are now cited: Baba–Granath 2008, Buzzard 1997, Lin–Yang (Math. Z. 2020),
  Igusa 1967, Milne 1986, Fontaine 1994.
- Five upstream proof supplements carry parts of the argument. They are not in the TeX and were
  not read (UNCHECKED).

**CertifiedRankSel: the citations improved; nothing is removed.**
- Lemma 5.5 (GZK) now cites Kolyvagin's address in *Proc. ICM Kyoto 1990*, pp. 429-436, instead
  of the MPIM preprint that nt-tyz §5.2 flagged. This narrows, but does not close, that issue:
  an ICM address is not a refereed proof (SPECULATIVE), and its text could not be read here
  (UNCHECKED).
- BCDT now comes through Silverman's Theorem C.13.6.
- Lemma 5.4's proof pins Poonen–Stoll's Corollaries 4 and 7 and Theorem 8. It matters only for
  the Kriz alternative.
- The RC repairs do not affect Route K. These are the parity citation changing to
  Dokchitser–Dokchitser 2010, Cornut–Jetchev replaced by a project supplement, and the Kato
  conventions in Appendix E.

**GoodPrimeDensity: unaffected.**
- Proposition 6.2's proof now takes GI(20) from `local-gi`, an unpublished project supplement
  dated 8 November 2026, instead of Green–Tao–Ziegler arXiv v5 with the erratum.
- That affects only the justification of 22P. 22P is still a hypothesis of the base theorem, but
  not of the narrowest variant.
- Proposition D's justification does not use the GTZ machinery (nt-22p L539).

**The quartic route.** Its height proof now uses the same Calegari/Pan lemma; Version 13's
"UNAPPLIED CANDIDATE … published Pan match pending" marker is gone. Its prime appendix replaces
Dodos–Kanellopoulos by Green–Tao's Proposition 10.1 with `local-gi`. Adopting it would still
cost months and remove no hypothesis (SPECULATIVE).

## Does the earlier recommendation change?

The order does not change. One cheap step is added.
1. **Finish GoodPrimeDensity.** GreenTaoDense is already proved, on `wip/gt-dense2`.
2. **Then CertifiedRankSel: its elementary half into Lean** (tyz-5b §4, Lemma 4.1 through
   Theorem 4.3 over `ZMod 2`). This is unchanged.
3. **New, for SixContactMin:** before more paper-side work (nt-h §5), re-base the h-leaves
   inventory on Version 14 §4 (L448-1680). h-leaves audited the 11/5 proof, and upstream has
   since replaced several of its leaves, partly as h-leaves itself recommended. The Serre-route
   plan of ser-ell now replaces `lem:qm-modularity-descent`, not Pan with Berger and Conrad.
   - *Success:* every `\cite` in that range is accounted for, and h-leaves' §6 open checks are
     restated.
   - *Chance:* high. About one session.

## Process notes

- **Earlier diff files in the repository.** The first task committed
  `scratch/v14-routes/main.diff` and `app.diff`: diffs of 11/5 against Version 13, 688 lines,
  which contain Version 13 text. This task's rules forbid committing such diffs. I left them in
  place because they are outside my scope; removing them from the branch is your call.
- Only `docs/research/v14-routes.md`, this report and `scratch/v14-routes2/` were changed. No
  manuscript, blueprint, Lean file or other note was edited. Everything is committed on
  `wip/v14-routes2`.
