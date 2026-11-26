# Invariant theory for the stack-free integral model

The invariant-theory lane is complete. For an arbitrary commutative base, finite-group averaging splits the inclusion of invariants when the group order is a unit. The ambient algebra is integral over its invariant algebra. The invariant algebra inherits flatness when the group order is a unit and finite type when the base is Noetherian. Finite-group invariants and degree zero both commute with arbitrary base change under the stated hypotheses. When the action preserves the grading the two comparisons compose for $(S^G)_0$.

Over an algebraically closed field, the finite quotient identifies group orbits. With a homogeneous unit of nonzero degree, restriction to degree zero is surjective and its fibres are exactly the orbits under scaling by the weight of each homogeneous component. The discriminant-open short Weierstrass chart has degree-zero algebra $R[j]$ when $6$ is a unit, with points given by their $j$-values.

All eight modules under `ZInQKernel/Contrib/OneProof/RC/ModelInvariants/` passed targeted `lake build`. The theorem axiom checks allow only `propext`, `Classical.choice` and `Quot.sound`. The report `docs/research/rc-model-reynolds.md` contains the statements, provenance, unverified print locators and manuscript check. The results log is `scratch/rc-model-reynolds/log.md`.

The model still needs the finite étale level cover and its rescaling action, smoothness and the comparison with the chosen generic model, the Néron extension of the fixed parametrization, and the degeneracy and Atkin–Lehner comparisons. These are the inputs still needed to apply the quotient results to the special-fibre geometry in (O.7).

The verified code and report are at `9cb64778cc99d6ed24b00dcf8a286ca47156d117`. Resolve the final handoff commit SHA with `git log -1 --format=%H -- .fleet/rc-model-reynolds.md`.
