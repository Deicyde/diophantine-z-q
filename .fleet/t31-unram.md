# t31-unram: fleet report

**Main result.** Leaf T31 is proved outright:

- `ZInQ.Contrib.T31.leafUnramified : GlueDescent.B2Q.LeafUnramified`
  (ZInQKernel/Contrib/T31/Main.lean). No hypotheses; `#print axioms`: propext,
  Classical.choice, Quot.sound. The leaf's definition in ZInQKernel/HDecomp/Descent/B2Glue.lean
  and its copy in scratch/h-decomposition/Leaves.lean are textually identical (diff), so this is
  the `t31` field of the leaf list.
- Wiring (same axioms): `ZInQ.Contrib.T31.b2_of_leaves_T31` and
  `ZInQ.Contrib.T31.b3_degree_le_QM_of_T14_T15_T31` (Contrib/T31/Wired.lean) are
  `b2_of_leaves` and `GlueWP3.b3_degree_le_QM_of_T14_T15` without `hUnr`.

**What compiles.** `lake build ZInQKernel.Contrib.T31.Wired` (9140 jobs) and
`lake build ZInQKernel.Contrib.T31.Main` (9129 jobs) succeed. New files only:
Contrib/T31/{Cyclic,Good,Local,Main,Wired}.lean (about 720 lines). No existing file edited,
no Tau Ceti module newly vendored.

**Proof.** (1) `signCob_of_cyclic_even` (Cyclic.lean, Mathlib only): a sign cocycle pulled back
through a cyclic quotient `⟨φ⟩` of order `2f` that only sees classes mod `⟨φ^f⟩` is a coboundary
(inflation `H²(ℤ/f,±1) → H²(ℤ/2f,±1)` is zero). (2) `exists_base` (Good.lean, Mathlib only): at a
prime `w` with `e = 1` there is `b₀` with `(minpoly b)'(b) ∉ w` for all `b ∈ b₀ + p𝓞L` (trivial
inertia + residue generator + prime avoidance). (3) `exists_unramifiedExtension` (Local.lean):
with `w = {v(ι x) < 1}` for the spectral valuation of `ℚ̄_p`, Tau Ceti's criterion
`isUnramified_of_adjoin_eq_top_of_isUnit_aeval_derivative` makes each `ℚ_p(ι b)` unramified, so
`ι(L) ⊆ ℚ_p^{ur}` and hence `ι(L) ⊆ K_f`. (4) Main.lean: `Gal(K_{2f}/ℚ_p)` is cyclic of order
`2f` (Tau Ceti `isCyclic_algEquiv`, `finrank_unramifiedExtension`), `φ^f` fixes `K_f`; apply (1).

**Deviation.** The suggested Brauer/Kummer route (Brauer/Unramified.lean, Torsion.lean,
`h2MuToBr_injective`, continuous-cohomology comparison, `decompositionEquiv`) was not needed, so
Torsion.lean's 7 modules were not vendored.

**Remains.** Nothing for T31. Other consumers of `hUnr` (`b3_of_leaves`, `b3_degree_le_QM`, …)
can be given `leafUnramified` in a later Contrib file. Details: docs/research/t31-unram.md,
scratch/t31-unram/log.md.
