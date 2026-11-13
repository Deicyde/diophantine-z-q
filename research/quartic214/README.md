# A 214-variable quartic family over the rationals

This is a public author proposal. It includes the full 214-coordinate construction, all 188 quadratic rows, their expanded quartic, the selected internal arithmetic and height proofs, exact source mappings, and portable finite checks. Fresh public mathematical review and the protected Protocol controller decision remain required. No contributor-authored file is an independent acceptance.

The assertion is: there exists a fixed, ineffective integer N0 such that every integer N≥N0 gives a quartic P_N with integer coefficients satisfying, for every rational x,

```text
x ∈ Z  ⇔  ∃ y ∈ Q^213 : P_N(x,y)=0.
```

Here A_N=149^(2N+1) is a fixed coefficient, and x is coordinate 1. The separate coefficient statement is H(P_N)=149^(4N+2)+1 for N≥53. **No assertion that N=53 defines Z is made.**

Read [PROOF.md](PROOF.md) for the assembly and the map of application boundaries. [SOURCE_PATH_MAP.json](SOURCE_PATH_MAP.json) binds every selected private proof adaptation to its original whole-file hash and line range and binds the exact reused public predecessor and manuscript. Original private path names in proof text are historical locators; the map's `reading_aliases` gives their public destinations. Public files contain the actual selected proofs, so private repository access is unnecessary to read the argument.

Run from the repository root with Python 3 (standard library only):

```sh
python3 -B research/quartic214/construction/build.py
python3 -B research/quartic214/construction/check_exact.py
python3 -B research/quartic214/height/numeric_certificate.py --self-test
python3 -B research/quartic214/check_port.py
```

The builder reads the exact public raw224 predecessor and writes only the selected 214 family. In [construction/artifacts/candidate214-brox/](construction/artifacts/candidate214-brox/), `candidate214-ir.json` gives every coordinate and primitive integral quadratic row; `candidate214-polynomial.json` gives the full sum-of-squares expansion, with symbolic powers of A_N; `STATISTICS.json` describes the table. The coefficient format is exact: a term with `parameterPower=a`, coordinate multiset `monomial=m`, and integer `coefficient=c` means c A_N^a ∏_(i∈m) X_i. The parameter is never a coordinate.

The Laurent checker imports no builder. It reconstructs all twenty changed factor identities, all 162 untouched rows, and all deleted definitions, and re-expands the full sum of squares. It also checks coefficient height for all N≥53, variable coverage, degree and content, and rejects deliberate corruptions. The isolated H4 certificate proves only finite rational inequalities. Neither finite check proves modularity, the analytic prime theorem, or the arithmetic defining theorem.

Earlier public and private work is attributed in [PROVENANCE.json](PROVENANCE.json). Earlier scoped reviews retain their historical scope; this public adaptation requires its own review. The governing [Astra policy](../../docs/research-review/ASTRA-REVIEW-POLICY.md) requires the designated independent review and protected controller attestation for final public acceptance.

Copied proof texts preserve their authors’ dated scope and pending-status statements. The current public [disposition overlay](../quartic214-protocol-d-public/RECORDS.json) and its separately authored reviewer records govern the exact public adoption. An older access or inherited-scope qualification must be read with that later, exact disposition; the old text is retained as evidence rather than silently rewritten.
