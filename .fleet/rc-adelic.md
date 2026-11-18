# Appendix F: adelic algebra

The explicit quaternion algebra now has a level-N Eichler order for every
positive N coprime to the detecting prime, including dyadic levels. The proof
recovers a rational lattice from its completions and patches any finite
collection of full local lattice changes. The restricted adelic unit group
gives the ideal class set by double cosets; the class stabilizer is the unit
group of the rational intersection of the conjugate local orders.

The one-place Atkin–Lehner action is an involution, and right multiplication
by the division uniformizer is a permutation. At good primes the actual
Hecke double coset descends with multiplicities and gives the existing ideal
neighbours line by line. `Adelic.algebraicGeometry` packages the algebraic
inputs to RC/PM; the supersingular curves comparison, specialization, and
the Frobenius and eigenvalue identities of the parametrization are the
geometric handoff.

All eleven new files under `ZInQKernel/Contrib/OneProof/RC/Adelic/` compile
individually. The axiom checks list only `propext`, `Classical.choice`, and
`Quot.sound`. No printed-form leaf was added. No manuscript error was found in the checked steps.

Report: `docs/research/rc-adelic.md`. Results: `scratch/rc-adelic/log.md`.

Proof and report SHA: `21f9f49cf2015eb96b4bbb0be271e899895cc265`.
Final handoff SHA: the commit adding this file, given by
`git log -1 --format=%H -- .fleet/rc-adelic.md`.
