# tc-license (fleet report)

**Result.** The vendored Tau Ceti code now meets the Apache-2.0 §4 conditions on branch
wip/tc-license. The license copy, NOTICE, THIRD_PARTY_NOTICES entry and §4(b) modification notices
are done. Only comment lines changed in Lean files. No Lean declarations were proved, so none are listed.

**Files added**
- ThirdParty/TauCeti/LICENSE: byte copy of ~/tc-oct16/LICENSE (Tau Ceti has no NOTICE file).
- ThirdParty/TauCeti/NOTICE: source repo, commits 5a01f5fe (tc-port) and 97a5b235 (kw-new), location
  ZInQKernel/Contrib/TauCeti/, "Copyright 2026 The Tau Ceti contributors", Apache-2.0 pointer, the
  modified-file convention and list.
- docs/research/tc-license.md, scratch/tc-license/{log.md, diffcheck.py, addnotes.py}, this file.

**Files changed**
- THIRD_PARTY_NOTICES.md: Tau Ceti bullet under "Vendored Lean code" (like the Green–Tao bullet).
- 8 vendored files under ZInQKernel/Contrib/TauCeti/, one comment line each under the provenance line:
  NumberTheory/ClassFieldTheory/Formation/InvariantKernel.lean,
  RepresentationTheory/Homological/ContCohomology/Coinduced/Discrete.lean,
  RepresentationTheory/Homological/GroupCohomology/PrimeIndex.lean,
  RepresentationTheory/Homological/TateCohomology/TrivialityCriterion.lean,
  Topology/Algebra/Group/Profinite/Generation.lean,
  Topology/Algebra/Group/Profinite/Sylow/{Basic,Containment,Existence}.lean.
- ZInQKernel/Contrib/TauCeti/MathlibBackport/Sylow.lean: the project's usual header (none), with no
  Tau Ceti attribution; the docstring says the file is original work.

**Compiles (VERIFIED):** all 9 changed modules rebuilt with lake build, one at a time. The diff check
(diffcheck.py) shows the other 1110 vendored files are byte-identical to tcport.py output.

**Remains:** origin/wip/kw-new has 19 modified nov01 files without the modification line (list in
scratch/tc-license/log.md). They need the same one-line notice, and the NOTICE list needs extending,
after kw-new is merged.
