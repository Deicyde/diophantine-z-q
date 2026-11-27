# Gaudron–Rémond, Duke 163 (2014): the copy read is the version of record

Checked 2026-11-27. Records only: no Lean change.

## The copy

- URL: https://lmbp.uca.fr/~gaudron/art13.pdf (the first author's institutional page).
- SHA-256: `6d62ddb8a0aa8f8b8f803d70060c6a26c7a6f2a00936b85867c830946cf3db12`.
- 52 pages (`pdfinfo`).

This is the file the adversarial AI reading of `gaudronRemondThm14GR1` used
([item-m-adversarial-readings.md](item-m-adversarial-readings.md)), recorded there and in
`docs/one-proof/reviews.tsv` as "the authors' copy with the Duke pagination".

## It is Duke's typeset version of record

- **Footer of p. 1** (`pdftotext -f 1 -l 1`), verbatim:

  > DUKE MATHEMATICAL JOURNAL
  > Vol. 163, No. 11, © 2014 DOI 10.1215/00127094-2782528
  > Received 4 October 2012. Revision received 4 November 2013.

  followed by the 2010 Mathematics Subject Classification line and the page number 2057.
- **Page range:** the first page is numbered 2057 and the last (p. 52 of the file, `pdftotext -f 52 -l 52`) is
  numbered 2108, so the file runs over pp. 2057–2108, 52 pages.
- **Crossref** (https://api.crossref.org/works/10.1215/00127094-2782528): "Polarisations et isogénies", Éric Gaudron
  and Gaël Rémond, *Duke Mathematical Journal* 163, issue 11, pages 2057–2108, published 2014-08-15, publisher Duke
  University Press.

The volume, issue, DOI and pagination of the file match the Crossref record exactly, and the file is the journal's
typeset text (footer, running heads and page numbers of the journal). So the "Duke journal text" whose comparison
the row's flag asked for is the text that was read: the journal-text check is satisfied by this copy. It is the
author-posted final typeset file; it was not byte-compared with Project Euclid's copy (paywalled; Euclid downloads
usually carry a cover page, which this file lacks).

## Effect

`gaudronRemondThm14GR1` is rated published, LEAF under the strict reading (AI-READ, the maintainer's general rule of
2026-11-26, docs/DECISIONS.md) and GLUE under the strictest reading, the lead to confirm. The height argument steps
that the row's earlier flag named are Lean theorems since #234 (commutativity of semi-abelian models; stalk lattice equal to the global-sections lattice) and
#237 (θ bijective; stalks of e*Ω¹ injecting into the generic fibre; spans), except for two residual readings, those of
`ZInQKernel/Contrib/OneProof/HeightModelM3/README.md`: Mathlib has no sheaf of relative differentials, so the stalk
formula and `globalOmega` stand in for Γ(S, e*Ω¹), and the one-factor wedge identity in the Hodge line is not
proved. A strict reading of the 11-26 ruling (a reading step is not a direct instance; `colmez1992DeRhamAbVar`) would
ask for a Lean theorem for that identity, which keeps the row GLUE until the lead rules. The converse (GR1 height ⇒ Néron-model height) is not proved, and the implication to the replaced field
`gaudronRemondThm14Printed` goes through `egaIV_9_7_7_OL` (EGA IV₃ (9.7.7)).

Strict count of the H part: 5/14 (the strictest reading), 6/13 without the one strictest-reading flag.

## Also used by

The open pull request #232 (`gaudronRemondSec9LowerGR1Weak`, Duke p. 2101) reads the same file (same SHA-256).
