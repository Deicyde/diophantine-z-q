# Version 18 research package

Read the complete [manuscript](../../manuscripts/quartic_v18.pdf) and [TeX](../../manuscripts/quartic_v18.tex). Version 18 incorporates Brox's reduction from Conant's 198 coordinates to 196, preserving the same rational input projection for every fixed integer `N >= 1`. The manuscript proves the parent arithmetic characterization and then fixes `N=BB(2^1000)`. It includes all 182 reduced quadratic rows and their 2,943-term sum of squares.

The selected coefficients are integer polynomials in `A=149^(2*BB(2^1000)+1)`. Their maximum absolute value is `A^2 < BB(2^2000)`. The 196 coordinates include the input; the coefficient parameter is fixed. The original construction, the separate 314-variable decimal quartic, the complete 198 parent proof and the 214-variable foundation remain in the manuscript.

## Read or reproduce

- [Release notes](RELEASE-NOTES.md) describe the mathematical corrections and changed inverse-theorem dependency.
- [Artifact index](ARTIFACT-INDEX.md) distinguishes selected files, parent inputs and historical provenance.
- [Reproduction guide](REPRODUCTION.md) links the portable 196 and 198 checks.
- [Build record](BUILD.json) binds the actual source and PDF. The [current-manuscript profile](../../docs/current-manuscript.json) selects the pair for CI.
- [Cumulative handoff](CUMULATIVE-HANDOFF.md) describes the archive preparation and preservation rules.

## Proof and review scope

The complete argument is in the manuscript, including the inherited arithmetic, the 198-to-196 elimination, a uniform parameter threshold, its Busy Beaver specialization and the coefficient bound. Separate notes and historical archives are supporting evidence, not substitutes for that argument. The printed table is the selected unbalanced presentation from Brox commit `5c35db3253a70b0875acec4b451cdaac4da3c8fd`.

The independent finite replays check algebraic identities, guard preservation, coordinate maps, expansions and coefficient statistics. The 196 replay completed 48,690 assertions; the 198 replay completed 50,684. These checks do not prove the arithmetic characterization or compute BB. Component reports retain their exact scopes; final acceptance must cover the assembled manuscript and source/PDF correspondence under the repository's active Protocol B review.

The retained upstream table still describes an ineffective sufficiently-large-parameter family. Its bytes are unchanged. Version 18 supplies the fixed BB specialization separately. The coefficient crossover at `N=7` is not a defining threshold. Earlier released manuscripts are preserved byte for byte.
