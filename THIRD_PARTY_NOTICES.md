# Third-party sources and dependencies

Project licensing applies only to original project material. It does not relicense the upstream software, papers, source excerpts, or theory files referenced or preserved by this project. Keep any notices supplied with those materials.

## Mathematical sources

- Sohail Farhangi with ChatGPT 6, [*A conditional Diophantine definition of Z in Q from four arithmetic inputs*](October%2011%20Manuscript/ZIsDiophantineInQBySohailsGPT-6.pdf), October 11, 2026. The 10/11 manuscript is preserved without modification alongside [comparison notes](October%2011%20Manuscript/README.md).
- OpenAI, [*Hilbert's tenth problem over the rational numbers*](https://github.com/openai/math/blob/main/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/main.pdf), October 6, 2026. This is a mathematical input cited in both the 10/11 and 11/5 manuscripts, not a proof produced by this repository.
- Jonas Bayer, Marco David, Benedikt Stock, Abhik Pal, Yuri Matiyasevich, and Dierk Schleicher, [*Diophantine Equations and the DPRM Theorem*](https://isa-afp.org/entries/DPRM_Theorem.html), Archive of Formal Proofs, June 6, 2022. The entry is distributed under the BSD license linked on its page. The alpha-sequence and exponentiation constructions are credited in the relevant project sources. The curated construction directory does not vendor the Isabelle development.
- Other mathematical sources for the 11/5 manuscript are identified in its bibliography and source-application appendices. The 10/11 manuscript has its own bibliography. Historical review reports preserve their particular citations and scope.

## Build and proof dependencies

| Dependency | License/source of terms | How it is used |
| --- | --- | --- |
| Lean 4 | [Apache 2.0](https://github.com/leanprover/lean4/blob/v4.35.0/LICENSE) | Compiler and proof kernel; installed separately |
| Mathlib 4 and its dependencies | [Mathlib license](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/LICENSE), plus each dependency's notices | Imported by Lean; exact repositories and revisions are in `lean/lake-manifest.json` |
| Tectonic | [Upstream licenses](https://github.com/tectonic-typesetting/tectonic/tree/tectonic%400.17.0) | Downloaded, hash-checked paper compiler; not committed here |
| TeX packages and fonts | Notices in the pinned Tectonic/TeX bundle and the respective package sources | Downloaded build inputs; not committed here |
| GitHub Actions | Each pinned action's upstream license | CI orchestration; referenced by commit hash |

The curated Lean files retain their original comments and attributions. A clean checkout fetches dependencies from their declared upstream repositories; it does not substitute a private dependency tree.

## Historical research archive

The research handoff is a provenance archive with a broader scope than the curated source tree. It includes third-party PDF references, Isabelle theory files, and source excerpts. Those files retain their own authorship and terms.

[Archive reference inventory](docs/archive-reference-inventory.json) groups the saved PDF references and Isabelle theory files by content hash and records their original paths. It is not a complete license audit of every excerpt in the archive. The 11/5 manuscript's bibliography, archive source manifests, and original documents should be used to resolve attribution and redistribution terms.

Before making the historical archive public, complete the per-source rights review. Where redistribution is not permitted or remains unresolved, distribute a reference and source URL instead of a copy. Do not apply the project's original-work license to the entire archive as a single undifferentiated work.

## Vendored Lean code

- `ThirdParty/GreenTao/`: a complete Lean proof of the Green–Tao theorem (`Submission.green_tao`), copied from
  Vilin97/Autoformalization, directory `green-tao/`, commit `0dc67d87416c19690dd641a178ada32cca95c651`, under the
  Apache License 2.0 (`ThirdParty/GreenTao/LICENSE`). Produced with GPT-5.6 Sol in Codex under the direction of
  Vasily Ilin as a lean-eval benchmark submission. Ported to Lean 4.35.0 / Mathlib v4.35.0 with local proof edits;
  provenance and the list of modifications are in `ThirdParty/GreenTao/NOTICE.md`. Used by
  `ZInQKernel/External/GreenTaoPrimes.lean`.

## NOTICE: vendored Selberg sieve (PrimeNumberTheoremAnd)

The files `ZInQKernel/Sieve/AuxResults.lean`, `ZInQKernel/Sieve/Basic.lean`,
`ZInQKernel/Sieve/Selberg.lean` and `ZInQKernel/Sieve/SelbergBounds.lean` are copies of
`PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/{AuxResults,Basic,Selberg,SelbergBounds}.lean` from

- source repository: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- tag `v4.35.0`, commit `127b50e33f6033e2147921167a117af96d9ba4ea` (it pins Mathlib `v4.35.0`, the
  revision this repository uses)
- license: Apache License 2.0; the upstream license text is copied to `ZInQKernel/Sieve/LICENSE`.
  Copyright (c) 2023 Arend Mellendijk (per the file headers, which are kept unchanged).

Change made: only the `import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.X` lines were replaced by
`import ZInQKernel.Sieve.X`. No other line was modified. The module `ZInQKernel/SieveVendor.lean`
(original to this project) imports the four files.

Adapted lemma: `ZInQ.Density.GaussSieve.prod_factors_sum_pow_mult` in
`ZInQKernel/Density/GaussSieve/SelbergSum.lean` is a copy of `Sieve.prod_factors_sum_pow_compMult` from
the same upstream file `SelbergBounds.lean` (same tag, commit and license). Change made: the name, and
the hypothesis "completely multiplicative" is weakened to "multiplicative" (one line of the proof,
`hf.isMultiplicative.map_prod`, becomes `hf.map_prod`). The file header records the origin.
