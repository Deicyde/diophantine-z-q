# tc-port2 results log

## Setup (2026-11-13 04:07 PST)
- Merged origin/main (e90faaf2), origin/wip/kw-new (0cd896f3; adds 81 vendored files: 44 nov01 modules,
  36 Backport files, 1 Mathlib backport), origin/wip/diff-bridge (33733d09; adds 11 oct16 modules). Clean merges.
- Vendored tree now: 1212 .lean files under ZInQKernel/Contrib/TauCeti. VERIFIED (find).

## Step 1: licensing
- ~/tc-oct16, ~/tc-nov01, ~/tc-main: LICENSE only, no NOTICE file (ls -a). VERIFIED.
- LICENSE identical at all three (sha256 b40930bb…e1), Apache 2.0, unfilled appendix template. VERIFIED.
- Copied to ThirdParty/TauCeti/LICENSE (byte-identical, cp). VERIFIED.
- ThirdParty/TauCeti/NOTICE.md written (provenance + modification list), GreenTao pattern.
- scratch/tc-port2/regen_diff.py regenerates each provenance-carrying file from its commit:
  identical 1146, modified 27 (8 oct16 by tc-port, 19 nov01 by kw-new), no provenance line 39
  (36 nov01 Backport helpers with "Backported from" header, Backport/Mathlib/Polynomial.lean,
  MathlibBackport/Sylow.lean, Notice.lean). VERIFIED (scratch/tc-port2/regen_diff.txt).
- Finding: none of the 27 modified files carries a "changed in this repository" line (Apache 2.0 §4(b));
  GreenTao has one per modified file. Listed in NOTICE.md instead; recommended to integrator.
- Finding: Backport/Mathlib/Polynomial.lean carries the Tau Ceti copyright header but its proof was
  written by kw-new (header comment says so).
