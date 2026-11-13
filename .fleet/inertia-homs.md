# inertia-homs (fleet summary)

**Verdict / main result.** g4-weilres's input `InertiaFixesHoms` is false as stated: it covers
all morphisms of schemes, and a constant map to a point not fixed by inertia breaks it. Its
only consumer uses homomorphisms. The corrected form `InertiaFixesHomsMon` (homomorphisms only,
places over a prime) is **proved in Lean** from two existing leaves,
`PkgI2.NeronOggShafarevich` (Serre–Tate 1968 Thm 1) and `PkgI3.HomFreeFinite` (Mumford §19
Thm 3): `G4WeilRes.inertiaFixesHomsMon_of_leaves`. So G4 now rests on leaves only, namely
`HomFreeFinite`, `MorphismsDescend` and NOS: `G4WeilRes.homField_of_model_leaves'`. It also
keeps g4-weilres's glue hypotheses hK (G2), hgood (G3) and hdim.

**What compiles.** `scratch/inertia-homs/InertiaHoms.lean`, 2095 lines, is G4.lean verbatim
followed by the new part. It has no sorry or axiom, 0 errors, and checks in ~40 s; every printed
theorem uses only propext, Classical.choice and Quot.sound. The new glue, all proved:
- `conj_agree`: equivariance of conjugation on test points;
- `secFst`: torsion of sections maps to torsion of `K`-points (a monoid homomorphism);
- `isInertia_iff` and `inertia_transport`: Mathlib's inertia subgroup, written elementwise, and
  transported along `K̄ ≅ ℚ̄`;
- `exists_closure_equiv`: `K̄ ≅ ℚ̄` extending an embedding `e`;
- `point_fixed`: NOS applied to the conjugate `A ×_{K,e} ℚ̄`;
- `comap_isDVR`: a place of ℚ̄ over p restricts to a DVR on every number field;
- `isUnit_prime_of_liesOver`, `ptIso`, and the Tate-module assembly through
  `tateHom_injective`.

**What remains.** G4's `hdim` (dimension of a base change, missing from Mathlib), hK (G2) and
hgood (G3), all outside this task. h-decomposition's row G4 should cite
`homField_of_model_leaves'` and record that `InertiaFixesHoms` was replaced. Report:
docs/research/inertia-homs.md.

Last updated 2026-11-13 02:21 PST.
