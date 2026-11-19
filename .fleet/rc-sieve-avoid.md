# Appendix F coefficient support

The restricted old-level, formwise Hecke, and inertia proofs use the actual coefficient support without changing the type modulus. The per-stage realization, exact and finite precision readings, and all three dictionary ports have variants on the allowed domain. Omission selects four representatives outside the support and root; the two prescribed-prime ports explicitly require that exclusion. No manuscript Hecke reading needs a sieve prime (tex 9670–9674, 9919–9926).

The prepared abstract data and budget precede the actual stage. The manuscript's full odd type is fixed during the stage and includes its reduction prime; prime representatives are chosen afterwards (tex 2016–2029, 10579–10585). A later stationary exclusion preserves the intrinsic source. A new squareclass coordinate refines the type.

The remaining step for a coarser retained type is `SieveInertia`: inertia at any sieve prime unrecorded by the type or active bits must die in the reduced elementary trace quotient. Tex 9745–9750 does not give that stronger bound. The common-space bridge is proved conditional on this local statement. The actual stage, analytic laws, and attachment inputs remain as listed in [the report](../docs/research/rc-sieve-avoid.md). No manuscript or printed-source error established.

All ten new Lean files compile. All 50 axiom checks list only `propext`, `Classical.choice`, and `Quot.sound`. No new prints.

Final implementation SHA: `249e03d086e2a067a22eb99cb87b2357b7357c66`. The final handoff commit is the commit adding this note; its SHA is resolved by `git log --diff-filter=A -1 --format=%H -- .fleet/rc-sieve-avoid.md`.
