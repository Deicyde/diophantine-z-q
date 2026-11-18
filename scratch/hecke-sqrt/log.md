# Results

| Declaration | Result |
|---|---|
| `SGRDirect.HeckeSqrt.cm24_fixed` | CM(−24) over ℚ̄ implies a QM isomorphism from the `rep 3` twist. Lean exit 0; standard three axioms. |
| `SGRDirect.HeckeSqrt.fixed_level` | Twist fixed on pairs implies fixed on full level classes after a unit adjustment. Lean exit 0. |
| `SGRDirect.HeckeSqrt.Chart.exists_aut` | A π-preserving endomorphism induces a Galois action on the finite chart. Lean exit 0. |
| `SGRDirect.HeckeSqrt.inertia_iff_stabilizes` | Inertia at the kernel of a geometric point map is its stabilizer. Lean exit 0. |
| `SGRDirect.HeckeSqrt.Chart.exists_hecke` | Every Galois automorphism acts by a twist and a marking change, on all finite chart points. Lean exit 0; standard three axioms. |
| `trace_of_action`, `trace_rep`, `trace_mul` | Outer twist on underlying pairs exists, and traces compose by `xr`. Lean exit 0. |
| `trace_unique`, `trace_index` | Trace is unique by the fibre over 1; each Galois element has that trace. Lean exit 0; uniqueness has standard three axioms. |
| `sign_xr`, `sign_sq` | Second bit sign is multiplicative and has square 1. Lean exit 0. |
| `trace_sign_at_zero`, `exists_inertia_trace_three` | Inertia sign is positive over 0; a CM(−24) chart point has a stabilizer of trace 3. Lean exit 0; standard three axioms. |
| `mem_inertia_iff` | Mathlib inertia is equivalent to chart inertia. Lean exit 0. |
| `squarefree_eigenvector` | A nontrivial sign character gives a nonzero sign eigenvector with squarefree polynomial square. Lean exit 0; standard three axioms. |
| `prime_support`, `radicand_mem_of_neg` | A prime dividing the squarefree radicand has nontrivial sign inertia; a negative inertia element forces the radicand into the underlying prime. Lean exit 0; standard three axioms for `prime_support`. |

Build cache: root cache present, upstream dependency cache copied into the worktree; direct Lean uses those caches. Host load and available memory checked before each invocation.

| Declaration | Result |
|---|---|
| `exists_residue_hom` | Quotient by a prime over a rational linear prime extends evaluation to a geometric point. Lean exit 0. |
| `inertia_trivial_of_ramificationIdx_eq_one` | Index 1 forces trivial inertia in the characteristic-zero chart. Lean exit 0. |
| `cm_objects` | Existing Y₃ row gives CM(−4), CM(−3), CM(−24) pairs. Lean exit 0. |
| `SGRDirect.heckeSqrtBranchAny_of_y3` | Sign character, CM, and finite branch support give the unchanged square-root statement. Lean exit 0. |
| `SGRDirect.heckeSqrtBranchAny_proof` | Only argument: `Y3P1j.Y3ToP1j`. Lean exit 0; axioms: `propext`, `Classical.choice`, `Quot.sound`. |

| Check | Result |
|---|---|
| `HeckeSqrtFold.lean` | Lean exit 0. `OpenResearchLeaves60Y3` has 30 fields; the next `SixContactMin` theorem has the standard three axioms. |
| `MainDryRun.lean` | Lean exit 0. `ZInQ.OneProof.frozenTarget` has the standard three axioms. Output: `maindryrun-out.txt`. |
| `Discharges.lean` | Lean exit 0. `heckeSqrtBranchAny_proof` discharges the target from the existing `Y3P1j.Y3ToP1j`. A comparison of the two elaborated open lists confirms 34 → 33 including pole completeness, only the target removed. Output excerpt: `discharges.txt`. |
| H only, strict and strictest | Before 5 LEAF / 28 GLUE on 33; after 5 LEAF / 27 GLUE on 32. No new kinds rows. |
