# Candidate: explicit quartic in 229 variables and 74,007 canonical bytes

## Change and scope

This is a **candidate mathematical improvement**, not yet an official new record release. The proposed primitive integer quartic has **229 rational coordinates including the input**, degree **4**, **3,312 monomials**, coefficient height **149^30** (217 bits), and an exactly **74,007-byte** fully expanded ASCII representation in the repository's specified canonical notation (strict limit: 100,000 bytes). It improves upon the **247-variable, 96,712-byte** explicit quartic in published Version 20 (merged PR #153), subject to proof and independent review.

The branch is based on the Version 20 main commit `54a4e576f1c8c577f33b0b97a2cedb5ca96af642`, and adds only files in `research/brox-explicit229-v68/`. It does not modify any frozen release, current manuscript, policy, CI, Lean or audit-history file.

## Mathematical argument and source dependencies

Let `Q_j`, `j=1,...,207`, be the pinned source 229-coordinate integer quadratic system at the fixed parameter `C=149^15`. The complete exponent vectors `a_i` and `b_j` in `transformation.json` specify the integer quadrics

```text
x_i = 149^(a_i) y_i;
R_j(y) = 149^(b_j) Q_j(149^(a_1)y_1,...,149^(a_229)y_229);
P_hat(y) = sum_j R_j(y)^2.
```

Every transformed quadratic row is integral and primitive; `a_1=0`. Each scaling factor is nonzero in Q, so the diagonal coordinate map is an automorphism of Q^229 fixing the input. Since a sum of rational squares is zero exactly when all its summands are zero, the projected rational zero sets agree *exactly*, including all guards and boundary strata. The diagonal map transfers the **new source proof of the N=15 theorem**, which is stronger than the effective statements published in Version 20; the full added argument is subject to review and not merely inherited from the prior 195-variable record. These include elliptic-group, modular-height, fixed-prime-pattern and prepared-pole results, which are **not independently re-proved** by this finite computation.

The source system is pinned to `JoseBrox/diophantine-z-q_improvements@7501669160c1662a742ddd54baed364a47c82ddc`, source quadratic SHA-256 `f0e6fc3f62525d7b251a10fc5f4cf0e6663c3f6f08beeef3cb28092b2e1555a8`. `paper.tex` now includes the source arithmetic argument, full compact normalization, and a new source-input-audit section with the small-prime extraction proof, the explicit height-corollary application, and the graft binding. The complete torsion-inclusive supplier is in `suppliers/effective_torsion_sums_20261117_v62.tex`; `source_paper.tex` allows exact comparison of the original arithmetic body.

## Independent computations and reproduction

The repaired package additionally includes the original 195-coordinate parent table, 34-coordinate/31-row graft certificates, the full torsion-height proof, explicit cutoff-free local extraction and arithmetic support checks. The package includes all 207 transformed quadrics, every one of the 3,312 expanded coefficients, the literal expression, diagonal exponents, source tables, independent checker scripts and reference measuring program. Run within `research/brox-explicit229-v68/`:

```sh
python -B build.py
python -B check_graft.py
python -B check_arithmetic.py --output arithmetic_certificate_replay.json
python -B check.py
python -B upstream/measure_plain_text.py polynomial.json --verify-text quartic229-N15.txt
python -B check_independent.py --package . --repo . --manuscript paper.tex --output independent_certificate_replay.json
```

The first three commands require Python's standard library; the fourth additionally requires SymPy. Source v68 certificates record PASS. A separate GPT-6 exact-BigInt reconstruction checked all **1,132 source terms**, all **207 transformed rows**, **3,312 quartic coefficients**, content 1, all 229 occurring variables, the input-preserving substitution, height `149^30`, and equality to the canonical **74,007-byte** ASCII literal. The pinned reference measurer reports `within_limit=true`. Literal SHA-256: `45bdea1ea7876bf6ec10b5427f9403cf1f94c144fab35817aa545bcb2cea1975`.

## Review, integration and limits

The original standard-library and SymPy certificates and the additional BigInt computation concern **finite algebra and representation**; they are not an authorized Protocol B outside review. The new source-input proofs require fresh independent evaluation. Fable's review of the preceding head identified F1 (height supplier missing), F2 (graft binding missing), and F3 (small-prime local extraction not justified), while Astra and Fable both reported incomplete review coverage. This revision supplies the missing materials and new proof, without claiming that reviewers have accepted them. The inherited mathematical theorem and all external arithmetic applications require the project's review standard. No fresh hosted CI result or unrecorded human review is claimed.

A **complete updated current TeX project and matching PDF**, their hashes, next ordinary integer manuscript version, independent whole-argument acceptance and separate release approval are **not included** at this candidate-note stage. Maintainers must integrate accepted work and review the current TeX/PDF pair before announcing an official record. This proposal leaves the published Version 20 intact. `scripts/check_audit_history.py --self-test` was not rerun in this upstream tree, as no audit-history or current-manuscript file was changed.

**Attribution and AI involvement:** the underlying 195/229-coordinate constructions originate in José Brox's project. The upstream three-detector effective-height construction is attributed to Gemini Carbon, building on Brox's work; the reflected center 3/11 was an already documented alternative. The fixed compact diagonal normalization is detailed in Brox's v68 package. GPT-6 performed the additional independent exact-BigInt audit, repository comparisons and package/PR preparation. Neither human peer-review nor cross-family Protocol B acceptance is claimed.

See `README.md` and `REVIEW_NOTE.md` in this directory for source-level citations, details and limitations.
