# tc-license: Apache-2.0 compliance of the vendored Tau Ceti code

**Main result.** The vendored Tau Ceti code (ZInQKernel/Contrib/TauCeti/) now meets the Apache-2.0 §4
conditions on this branch: (a) a copy of the license is in ThirdParty/TauCeti/LICENSE (byte copy of
Tau Ceti's LICENSE at 5a01f5fe); (b) every vendored file modified beyond the mechanical import
rewrite and provenance line carries a prominent "Modified for the Z-in-Q kernel" comment; (c) Tau
Ceti's copyright headers are kept in all vendored files; (d) Tau Ceti has no NOTICE file, so we
wrote ThirdParty/TauCeti/NOTICE (attribution, source commits, location, modified-file list), and
THIRD_PARTY_NOTICES.md has a Tau Ceti entry modelled on the Green–Tao one.

No Lean declaration is proved or added (license task; only comment lines changed). Hence there is no
`#print axioms` output; the axiom audit of the vendored code is in docs/research/tc-port.md.

## How the modified files were found (VERIFIED, computed)
`scratch/tc-license/diffcheck.py` regenerates each vendored file from the Tau Ceti source module
named in its provenance line (tcport.py's transformation) and compares byte for byte. On this
branch: 1120 files, 1110 identical, 2 original project files (MathlibBackport/Sylow.lean,
Notice.lean), 8 modified: exactly the eight changes listed in docs/research/tc-port.md.

## Changes
- 8 vendored files: one line `-- Modified for the Z-in-Q kernel: <change>.` under the provenance line:
  NumberTheory/ClassFieldTheory/Formation/InvariantKernel,
  RepresentationTheory/Homological/ContCohomology/Coinduced/Discrete,
  RepresentationTheory/Homological/GroupCohomology/PrimeIndex,
  RepresentationTheory/Homological/TateCohomology/TrivialityCriterion,
  Topology/Algebra/Group/Profinite/{Generation, Sylow/Basic, Sylow/Containment, Sylow/Existence}.
- MathlibBackport/Sylow.lean (original work of tc-port): the leading licence comment naming Tau Ceti
  removed (the project's own Lean files carry no header); the module docstring says the file is
  original to this project and is not copied from Tau Ceti (no matching code in ~/tc-oct16,
  ~/tc-nov01, ~/tc-main: VERIFIED by grep).

## Compile (VERIFIED)
`lake build ZInQKernel.Contrib.TauCeti.<M>` one at a time for the 9 changed modules: all succeed.

## Open (for task kw-new / the integrator)
On origin/wip/kw-new (0cd896f3), 19 nov01-sourced vendored files differ from their Tau Ceti source
and lack the modification line; the list is in scratch/tc-license/log.md. After kw-new is merged,
each needs the same one-line notice (the NOTICE text already covers the convention and the
97a5b235 commit), and the list in ThirdParty/TauCeti/NOTICE should be extended.
