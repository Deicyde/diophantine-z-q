# ℤ is Diophantine in ℚ: the 5 November manuscript, linked to two Lean repositories

[Literature Links](https://github.com/mathlib-initiative/literature-links) annotations that tie
passages of the 5 November 2026 manuscript to Lean declarations in two repositories:

| | Repository | Commit |
|---|---|---|
| Manuscript | `diophantine_zq.tex` in [elliotglazer/diophantine-z-q](https://github.com/elliotglazer/diophantine-z-q) | `97cec7fdd757d9a8e4f468151a47a6d3610fb2f2`, sha256 `cb1148cd…d792b` |
| fork | [Deicyde/diophantine-z-q](https://github.com/Deicyde/diophantine-z-q) | `636c2761c6bc6099cd76b9fb9a515149beec7f6d` (18 November) |
| upstream | [elliotglazer/diophantine-z-q](https://github.com/elliotglazer/diophantine-z-q) | `d8266eaf8108f30bba88ca55dc467e52a8ac7e9a` (18 November) |

**These are links, not verdicts.** Every link is harvested from a repository's own blueprint.
No annotation carries a `relation`: nothing here says a declaration states its passage
exactly, closely or at all. Nobody has reviewed the result.

## What is here

- [INDEX.md](INDEX.md): the 71 numbered statements and the 136 cited passages, each with the
  declarations linked to it in either repository.
- `annotations/fork/`, `annotations/upstream/`: one JSONL file per blueprint chapter, one
  annotation per line.
- `annotations/unlinked.jsonl`: the numbered statements nothing links to.
- `summary.json`: the counts below, by machine.
- `build/`: the three scripts that produced all of it.

## Counts

| | fork | upstream |
|---|---|---|
| Blueprint pages read | 701 | 597 |
| Pages that cite no manuscript passage | 363 | 261 |
| Annotations | 559 | 554 |
| Declaration links | 1,615 | 1,646 |
| Distinct declarations | 919 | 947 |
| Annotations whose page names no declaration | 10 | 0 |

- 136 manuscript passages are linked. For 130 of them the two repositories name the same
  declarations.
- The 6 that differ are the headline theorems. The fork links Theorems 1.1, 4.1 and 5.2 and
  Proposition 6.2 to its headline from `SixContactMin` and `PoleCompleteness`. Upstream links
  Theorem 1.1 and the two height passages to its Route K headlines.
- 11 of the 71 numbered statements have a link in some repository: Theorems 1.1, 4.1 and
  5.2, Lemmas 1.2, 5.1, 11.1 and 11.2, and Propositions 3.1, 6.1, 6.2 and 12.1.
- 60 have none: Theorem 5.3, Lemmas 5.4 and 5.5, everything in Sections 7 to 9 and 13, and
  Appendices E to H. That is the proof of the restricted converse and the corollaries.
  `unlinked.jsonl` records them as unlinked, which is not a claim that no counterpart exists.

## How the links were obtained

Both repositories keep a `blueprint/` folder. Each page under `blueprint/roadmap/` names Lean
declarations in a `lean:` field and lists its sources. A source is a section of a locator
file under `blueprint/sources/`, and eight of those files give line ranges of
`diophantine_zq.tex`.

1. `build/items.py` numbers the manuscript's 71 theorem-like environments from the TeX.
2. `build/harvest.py` reads every page, follows its source links, and reads each locator
   section's line ranges (or its TeX label, for `manuscript.md`). It indexes the
   repository's Lean files and resolves every declaration name to a file and line.
3. `build/generate.py` writes one annotation per page and passage. The subject is the
   passage, as `lines` or a `label`. The object is the page's declarations, taken together.

Checks that passed:

- `literature-links scan annotations`: 1,173 annotations from 19 files, 0 problems
  (checker at `d3d7c2c`).
- Every declaration name resolved to exactly one source line, and that line contains the
  name, in both repositories.
- Every line range lies inside the manuscript, and every label is one of its 71.
- The pinned manuscript URL serves bytes with the pinned sha256.

## Limits

- **Nothing was built.** Names were resolved by reading the Lean source with a script that
  tracks `namespace` and `end`, not by Lean.
- **Passages are as coarse as the locator sections.** One passage can span a whole
  subsection and be cited by dozens of pages.
- **Pages that cite only project notes are not linked**, even where they concern a
  manuscript section (Route K, route AP, the height decomposition, the rank chapters).
- **Fifteen locator sections name saved artifacts**, not manuscript lines, and were skipped.
- **There is no PDF overlay yet.** The subjects are TeX line ranges. The formal-companion
  viewer needs page regions of the PDF, and the repository's PDF predates this TeX by two
  days by its own metadata.
- formal-companion's exporters do not read this blueprint layout, so the scripts in
  `build/` stand in for `cf overlay export`.

## Reproduce

```sh
python3 build/items.py diophantine_zq.tex build/items.json
python3 build/harvest.py <fork checkout> build/items.json harvest-fork.json
python3 build/harvest.py <upstream checkout> build/items.json harvest-up.json
python3 build/generate.py build/items.json . \
  fork=harvest-fork.json=https://github.com/Deicyde/diophantine-z-q=<commit> \
  upstream=harvest-up.json=https://github.com/elliotglazer/diophantine-z-q=<commit>
literature-links scan annotations
```

Written by Claude Code, at Jack's request.
