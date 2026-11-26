# Torsion for the integral modular curve

Lean proves the geometric count \(n^2\), separability and degree of the abscissa polynomial, and the unit discriminant of its coordinate algebra. The affine nonidentity torsion algebra is finite free and étale of rank \(n^2-1\). The even-level branch has a unique ordinate satisfying the Weierstrass and vertical two-torsion equations. Both algebras commute with scalar extension. The universal short Weierstrass specialization over the integers localized at the detecting prime works for all invertible levels.

Eight modules built with the required limits. Every new theorem's axiom audit uses only `propext`, `Classical.choice` and `Quot.sound`. There are no printed-form leaves.

**Scoped stop.** The level covers need a scheme-level group law on the finite étale torsion, including the identity component. From that interface the exact-order and basis loci are clopen, and finite étale descent gives the cyclic quotient without inverting \(\varphi(N)\). The level algebra \(S\), its coordinate-change grading, and assembly of the quotient remain pending. The research report gives the moduli definition, descent argument, and reductions for smoothness, generic-fibre comparison, the parametrization, \(W_Q\) and \(T_\ell\).

- Research report and manuscript check in `docs/research/rc-model-torsion.md`
- Statements and build outcomes in `scratch/rc-model-torsion/log.md`
- Verified source and report through commit `53fc8f94a9d5fb457c267db4f8c1e0eb8d80e245`
- Final handoff SHA is the output of `git log -1 --format=%H wip/rc-model-torsion -- .fleet/rc-model-torsion.md`
