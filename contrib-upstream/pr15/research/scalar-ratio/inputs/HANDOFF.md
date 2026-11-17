# Repo-agent handoff: the next connecting theorem

## Task

Develop and check the four source candidates under `lean/Research/DerivativeSwitch/`
on an isolated research branch or sidecar using the source repo's pinned Lean
4.35.0 and Mathlib revision. They contain no intended proof holes but have NOT
been compiled in this preparation environment. Treat ordinary mathematics and
candidate formal source separately.

## First pass: complete the formal gate without weakening the statement

1. Run the exact Python suite normally and under `-O`.
2. Run `verify_lean.py` with a fresh output directory and the pinned dependency
   caches. Preserve a failing log and repair elaboration/library-interface
   issues as necessary. Do not weaken hypotheses/conclusions, redefine the
   coordinate as the desired formula, add an axiom, or assert arithmetic
   normalization merely to make the file compile.
3. Review the elaborated HasCoordinate, CommonStrictData, UnitRelated and
   BoundaryCupIdentity definitions and all exported target statements. The
   exact unit ring must remain R, not its fraction field.
4. Record fresh source hashes, compiler output and the actual transitive
   axiom set. Native compilation does not supply independent review. Keep
   external-checker and arithmetic-instantiation statuses separate.

## Mathematical dependency order

- Coordinate: full adjugate tensor definition; covariance under genuine
  frame changes; rank-one diagonal normal form; coordinate uniqueness.
- CommonStrict: explicitly construct the source frames and the swapped/common
  target frames from D0, AF, AS, the ACTUAL cycles and a fractional complement.
  Derive the raw matrix identities and the two scalar formulas.
- UnitCriterion: deduce the discrepancy and integral-unit equivalence, keeping
  common nonunit factors and zero-functional cases.
- BoundaryCup: use full local adjunctions on the SAME actual functionals to
  derive the normalization defect and the common-normalization consequence.

## Then instantiate, not rename, the arithmetic inputs

Read ARITHMETIC_CONTRACT.md. Trace the actual H19--H22 and duality maps to each
input. The outstanding work is the common boundary--cup normalization in the
required localizations and retained limits. No identity-on-strict complex map
is required. No new variable-reduction track is needed for this contribution.

## Integration boundary

Keep the accepted 48-module snapshot, frozen target, dependency pins, manuscript,
release manifests and prior acceptance hashes unchanged. Use a separate research
library/checker. This bundle grants no publication, merge, visibility change or
new independent acceptance. Remote actions remain subject to the owner's actual
instructions and the repository's current policy.

A useful contribution is the compiled common-strict connecting theorem plus its
explicit arithmetic adapter. Another receipt for the old six lemmas alone does
not advance this mathematical target.
