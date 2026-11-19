# Contributors

Everyone whose work is in this repository, or who took part in the open work on [#14](https://github.com/Deicyde/diophantine-z-q/issues/14). This repository is a fork of [elliotglazer/diophantine-z-q](https://github.com/elliotglazer/diophantine-z-q); this file lists everyone in one place. Contributed proofs and statement checks are also credited in [docs/one-proof/credits.tsv](docs/one-proof/credits.tsv) and the [credits section of OPEN.md](docs/one-proof/OPEN.md#credits).

## The manuscript

- **Elliot Glazer** ([@elliotglazer](https://github.com/elliotglazer)): the manuscript [*ℤ is Diophantine in ℚ*](diophantine_zq.pdf), produced with Astra 6, Sol 6.1 and Opus 5.5 and audited by Fable 5.1, and the upstream repository this fork came from.
- **Sohail Farhangi**: the earlier conditional manuscript of October 11, 2026, *A conditional Diophantine definition of Z in Q from four arithmetic inputs* (with ChatGPT 6), kept unmodified in [`October 11 Manuscript/`](October%2011%20Manuscript/README.md).

## Credited by the upstream project

Upstream's README says the project "uses the collective agentic notes from" the people below. They are listed here as upstream lists them; this file does not say which part of the work each one did.

- **Stefan Baranczuk**
- **Jose Brox** ([@JoseBrox](https://github.com/JoseBrox)), whose [repository](https://github.com/JoseBrox/diophantine-z-q_improvements) upstream points to for later results. His 195- and 196-variable quartics are in upstream's Versions 18 and 19, which this fork's Lean does not cover.
- **Gabe Conant**
- **Sohail Farhangi**
- **Cameron Freer**
- **James Freitag**
- **Elliot Glazer**
- **Jennifer Park**
- **Caroline Terry**

## Contributed work on `main`

- **loning** ([@loning](https://github.com/loning)): Lean from upstream pull requests [#14](https://github.com/elliotglazer/diophantine-z-q/pull/14), [#22](https://github.com/elliotglazer/diophantine-z-q/pull/22), [#29](https://github.com/elliotglazer/diophantine-z-q/pull/29), [#33](https://github.com/elliotglazer/diophantine-z-q/pull/33), [#70](https://github.com/elliotglazer/diophantine-z-q/pull/70) and [#150](https://github.com/elliotglazer/diophantine-z-q/pull/150), imported in [#71](https://github.com/Deicyde/diophantine-z-q/pull/71) and [#73](https://github.com/Deicyde/diophantine-z-q/pull/73).
- **Chey Loveday** ([@CheyLoveday](https://github.com/CheyLoveday)): the evidence packets of upstream [#15](https://github.com/elliotglazer/diophantine-z-q/pull/15) and [#27](https://github.com/elliotglazer/diophantine-z-q/pull/27) (imported in #73), and the abscissa-parity proof step of the blueprint from [#84](https://github.com/Deicyde/diophantine-z-q/pull/84) (in [#88](https://github.com/Deicyde/diophantine-z-q/pull/88)).
- **Carlos Toledo** ([@carlostoledo1891](https://github.com/carlostoledo1891)): the frozen target's statement from eight explicit hypotheses and the audit files of upstream [#5](https://github.com/elliotglazer/diophantine-z-q/pull/5) and [#6](https://github.com/elliotglazer/diophantine-z-q/pull/6) (imported in #71 and #73).
- **Cameron Freer** ([@cameronfreer](https://github.com/cameronfreer)): quadratic rows and durable tables for the quartic stack, upstream [#23](https://github.com/elliotglazer/diophantine-z-q/pull/23) (imported in #73).
- **Junyan Xu** ([@alreadydone](https://github.com/alreadydone)): the statement check of `javanpeykarThm111An` ([#91](https://github.com/Deicyde/diophantine-z-q/pull/91)), which corrected the row's semistability note, and a survey of the Picard rows' formalization status on #14.
- **Ryan McCorvie** ([@mccorvie](https://github.com/mccorvie)): the reduction of `neronSchemeExtensionDedekind` to its discrete-valuation-ring case (`neronSchemeExtensionDedekind_of_dvr`, BLR §1.3 Cor. 2 with §1.4 Prop. 1 and Thm 3), [#137](https://github.com/Deicyde/diophantine-z-q/pull/137).

## Claims and discussion on #14

- **zachbaugher** ([@zachbaugher](https://github.com/zachbaugher)): claimed `hCM`, worked on a lattice-level file for it (offered on request), and released the claim when the project took the row over.

## The project

- **Jack McCarthy** ([@Deicyde](https://github.com/Deicyde)) maintains the fork. Most of its Lean was written by AI agents (Claude Code) working for him; their commits are under his account.
