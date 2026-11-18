# Results

- Base: `09b2537ca`; `frozenTarget` research bundle `HDec.HSyn.OpenResearchLeaves61`.
- `SZRaynaud.wildPeriodCoprime_proof : SZRaynaud.WildPeriodCoprime`.
- `SZRaynaud.elliot_of_semistableUnipotent_of_period_proof :
  ReductSplit.SemistableUnipotent → SZRaynaud.ElliotWildInertiaTrivial`.
- `SZRaynaud.WildPeriod.exists_coprime_period`: if `ℓ` is prime and a unit at the base,
  the wild automorphism has a period prime to `ℓ` at every abelian variety point.
  Eight private helper statements: see the table in `docs/research/elliot-wild.md`.
- Core compile: direct Lean 4.35.0, exit 0. `#print axioms` for
  `valuation_apply_eq`, `smallDisplacement_mul`, `smallDisplacement_pow`,
  `fix_of_pow`, `valuation_natCast_eq_one`, `exists_coprime_fix_field`,
  `exists_fixing_field`, `galAct_iterate` and `exists_coprime_period`:
  `[propext, Classical.choice, Quot.sound]` for each.
- Interface compile: `python3 scratch/elliot-wild/check_interface.py > .lake/WildPeriodInterfaceCheck.lean`;
  direct Lean on the generated file with the compiled core, exit 0.
  Output:
  ```text
  'SZRaynaud.wildPeriodCoprime_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
  'SZRaynaud.elliot_of_semistableUnipotent_of_period_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
  The first audit uses the verbatim target and proof body; the second is relative
  to the existing reduction taken as an explicit parameter. The actual contribution
  imports the real declarations.
- Direct contribution check: missing `ZInQKernel.Contrib.OneProof.SZRaynaud.olean`.
  Approximate source dependency scan: 3,150 uncached repository modules for that import,
  stopping at existing artifacts. Integration build unverified.
- Manuscript L815: `|GL₄(𝔽₃)| = 24261120`, `|GL₄(𝔽₅)| = 116064000000`, computed from
  `∏_{i=0}^3 (q^4 − q^i)` at the two orders.
- `SilverbergZarhinThm35`: conclusion semistability only. `NOSSepDict.NeronOggShafarevichSep`:
  good reduction. No producer of `SemistableUnipotent` from the current bundle/read prints found.
- Missing: semistable reduction implies square-zero action on the Tate module for wild inertia.
  No replacement statement installed. H 24/24 GLUE before and after; whole theorem 25/25.
