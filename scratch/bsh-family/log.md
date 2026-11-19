# Results log

- Baseline: the prime trace comparison accepts a Galois family of embeddings with simultaneous local coordinate matching. The family is not present at the baseline.
- Build configuration: `-j 1` was rejected by Lake. A subsequent prerequisite build with `-Kjobs=1` started concurrent Lean subprocesses, breaching the single-process rule. An initial cancellation did not take effect; the overlapping build was then interrupted through its process session. Subsequent Lean invocations have an exclusive compiler lock and run the host load and memory checks.
- Splitting approach: nonzero torsion sections in each prime direction come from changing basis for the holomorphic Weber mark at level `p`. A monic polynomial remainder transfers pointwise root exhaustion to the germ field without assuming simple roots.
- `BShFamily.dvd_prod_pow_of_exhaustion`: a split polynomial with all roots in a finite list divides a power of its linear-factor product; compiled.
- `BShFamily.splits_of_eventually_exhaustion`: a monic polynomial with eventual pointwise root exhaustion over an algebraically closed field splits over the field supplying its germ coefficients and those roots; compiled.
- `lake build +ZInQKernel.Contrib.OneProof.BShFamilySplittingCriterion`: passed; both axiom scans contain only `propext`, `Classical.choice`, and `Quot.sound`.
- `BShFamilySections`: built as part of the family build. The Möbius change of basis and meromorphic torsion sections have only `propext`, `Classical.choice`, and `Quot.sound` in their axiom scans.
- `BShFamilyLattice`, `BShFamilyTorsion`, `BShFamilySplit`: built as part of the family build. The division-root atlas, multiplication and x-coordinate comparison, and restriction of meromorphic germs have only the three allowed axioms.
- `BShFamilyResidues`, `BShFamilyLocal`, `BShFamilyKernels`: built as part of the family build. Nonzero residue permutations, splitting at every local meromorphic field, and Galois equivariance of both algebraic Vélu coordinates have only the allowed axioms.
- `BShFamilyAtlas`, `BShFamilyAssembly`: built as part of the family build. Exhaustion and multiplication for the actual local roots, and the descent from simultaneous kernel profiles to the fixed prime trace, have only the allowed axioms.
- `lake build +ZInQKernel.OneProof.Discharges`: target built for the focused check.
- `BShFamilyLocalKernels`: built as part of the family build. The splitting-field lift, mark test, and bijection with the allowed local branches have only the allowed axioms.
- `BShFamilyCoordinates`: built as part of the family build. The short Vélu sums on the weighted kernel agree with the lattice sums and pass to germs; all four axiom scans have only the allowed axioms.
- `BShFamily.local_kernel_profiles`: built. A single lift of the splitting field and a single bijection of kernels match both coordinates at every parameter.
- `BShFamily.exists_primeTrace`: built. Every prime has the fixed `IsPrimeTrace` on each admissible model.
- `BShFamily.bShStandardModel_proof : R16Thm1.BShStandardModel` and `BShFamily.heckeJ1DS_proof : AfTateLam.HeckeJ1DS`: built.
- `lake build +ZInQKernel.Contrib.OneProof.BShFamily +ZInQKernel.OneProof.Discharges`: passed offline. All 74 new theorem scans are subsets of `[propext, Classical.choice, Quot.sound]`.
- Focused `#discharges`: `DISCHARGES [bShStandardModel] by BShFamily.bShStandardModel_proof`; still assumes `[]`; axioms `[propext, Classical.choice, Quot.sound]`. The scan checked 1652 theorems and also reported the predecessor's conditional theorem.
