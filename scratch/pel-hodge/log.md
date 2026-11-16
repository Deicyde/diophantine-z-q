# pel-hodge results log

Base: 60a3fac7 (leaf-fold28b) + merges of origin/wip/unif-topology (dbf043a4, includes unif-printed 9c2e1809) and
origin/wip/holfam (93220b34); both merged cleanly.

Build tree: copied (reflink) from ~/dzq-wt/holfam (.lake/build, lean/.lake/build; fold25 sources) plus
UniformizationPrinted.olean from ~/dzq-wt/unif-printed. The early chain modules used (TailC, TailQ, HDecomp/*) have
identical sources in fold25 and fold28b; TailX..TailZ36 differ (igusaGL2 removed), so modules importing TailZ40
(HolFamilyPrinted) are checked against the fold25 build of their (unchanged) imports.

## Compile outcomes
- T1.lean (definitions H1, loopClass, IsHodgeFibre): compiles (VERIFIED, 2026-11-16 00:10).
- T2.lean: `isUniformization_of_H1` (H1 form -> lattice form, from UniformizationLeafAll) and
  `exists_H1_of_isUniformization` (converse) compile, no sorry (VERIFIED, 2026-11-16 ~01:00).
  Mathlib API used: IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite(_injective, _apply_mk_eq),
  Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup, ZLattice.rank, IsZLattice.span_top,
  finrank_real_of_complex, LinearMap.injective_iff_surjective_of_finrank_eq_finrank.
- Pitfall: `γ` is a reserved token under these opens (use `lp`).
