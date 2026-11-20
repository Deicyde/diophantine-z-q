# Special-fibre quotient handoff

**Scoped stop: the Lean implementation is unchecked.** The draft in
`ZInQKernel/Contrib/OneProof/RC/PMQuotient/` defines the quotient from the
Néron extension of the fixed rational parametrization. The residue readout
extends additively to degree-zero divisors; the staged constructor takes
the integral CM diagram and the rational cusp data and uses this same
quotient for the Atkin–Lehner, CM specialization and cusp equations.

The initial `Model` build reported Lean elaboration errors. The draft
was edited, but the next build was rejected by automatic review because
another Lean process was active. Further guarded attempts did not launch.
No revised module or focused `#discharges` and axiom audit has passed.
Resume by building `Model`, then `Operators`, `Cusps`, `CM` and
`Assembly` serially, and run the focused audit. Do not integrate the
draft before verification.

The mathematical inputs left are the good integral modular model and
operator dictionary, the generic signed and Hecke equations for the
same fixed map, the CM source and target coordinate comparisons at the
detector's place, and the actual cuspidal class with its fixed rational
torsion annihilator. No new printed leaf. The inherited source errors
were recorded first in `.fleet/rc-pm-quotient-verdict.md`. The full
input table and results are in `docs/research/rc-pm-quotient.md` and
`scratch/rc-pm-quotient/log.md`.

Implementation and report SHA: `568c039d02a6eb3194f306a53129a0cb0678ec0e`.
The final handoff SHA is the result of
`git log -1 --format=%H -- .fleet/rc-pm-quotient.md`; its literal hash
cannot be included in its own contents.
