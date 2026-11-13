# fleet: fibre-qm-period (2026-11-13)

**Result.** g0-thetapoint's glue Prop `ThetaPt.FibreQMPeriod` (some uniformization lattice of the fibre over
J(u) is linearly isomorphic to bp-analytic's QM lattice ι(𝒪)(τ,1)ᵀ with jNum/jDen(Ω(τ)) = J(u)) is not false or
vacuous (model review). The statement is unchanged; it is now proved in Lean, with no sorry and standard axioms only,
from named Props. Step 1 restates it for the leaf's own triple via qm-pin (`fibreQMPeriod_of_own`, using
`Pin.MobiusGlue`, which mobius-glue proved). Step 2 proves the own-triple form (`fibreQMPeriodAt_of`). Final form
`HSyn.G0Split.FibreQM.fibreQMPeriod_main`:
- leaves: `PkgI1.QMHauptmodul` (existing); T35 and T11a (verbatim copies of kernel textbook leaves);
  `QMClassNumberOne` (textbook, Eichler); `R1bFamily`, a new **concrete R1(b)**
  (Shimura's period map ℍ → Y(ℂ) composed with π, holomorphic; replaces the opaque `R01b_ComplexUniformization`
  at the triple);
- glue: `PeriodMapGlue` (large), `HauptmodulUnique` (complex analysis), `QMDenZeroCM3` (zeros of ψ₄∘Ω only at
  the −3 CM point), `CPtsTransport` (complex points of the base change, plus rigidity).

Proved along the way: Skolem–Noether over ℂ for N5's order (`qmSkolemNoetherC_proof`, an eigenvector argument), transport of uniformizations along linear maps, uniqueness of analytic lifts, T11a's lifts
form a ring hom, normalization of QM lattices with the unit 1+i (`FibreQMNorm.normalize`), lattice transport via
`ZLattice.comap`, and the reductions of R1(b)(a) (`QMComplexUnif`), `QMLatticeAlgebra` and `UnifTransport`.
`QMDenZeroCM3` has numerical support: weights 8 and 20 and vanishing orders 2, 2 at P₋₃ (mpmath), which with the
valence formula for signature (0;2,4,6) exclude other zeros.

**Compiles.** `scratch/fibre-qm-period/FibreQM.lean`, assembled by `build.sh` from ThetaPoint.lean with qm-pin's
full R1fpProps edit, part_pin.lean and part_fqm.lean: 0 errors, 0 sorry, 31 `#print axioms` lines standard
(run_full5).

**Remains.** The four glue Props above and the textbook fact `QMClassNumberOne`. A human check of `R1bFamily`'s
faithfulness to Shimura's Main Theorem I. The SPECULATIVE premise bp-qmmoduli §2.2 is inherited. Integration needs
qm-pin's R1fpProps patch. Report: docs/research/fibre-qm-period.md.
