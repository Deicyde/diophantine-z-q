# mul-rigidity (fleet note)

**Verdict.** `RigidityHom` is **proved** from Mathlib: `G0FibreSimple.rigidityHom : RigidityHom`, with no
hypotheses. `MulIsogeny` is **reduced to two glue statements, leaving no literature leaf**:
`mulIsogeny_of_cotangent : KerUnitOpenOfCotangentSurj → CotangentMulN → MulIsogeny`. There is also a
reduction to the single leaf `KerUnitOpen` (`A[n]` is unramified at the origin), which Lean derives from
the published "`[n]` étale for char ∤ n" (`kerUnitOpen_of_mulEtale`). Both statements are copied verbatim
from scratch/g0-fibresimple and are unchanged.

**What compiles** (VERIFIED). `lake env lean scratch/mul-rigidity/MulRigidity.lean` exits 0 in 12 s with no
sorry. All nine `#print axioms` give propext, Classical.choice, Quot.sound. `Rigidity.lean` and `Mul.lean`
also compile on their own.
- Rigidity: a two-sided rigidity lemma over `K̄` (Mathlib's Stacks 0BFD proof, generalized from the
  commutator to any `c` that is constant on the two axes), then the homomorphism case, then any field by
  faithful monoidal base change.
- `[n]`: proved from Mathlib along the way:
  - formally unramified + locally of finite type ⇒ locally quasi-finite;
  - proper + locally quasi-finite ⇒ finite (ZMT);
  - a locally quasi-finite closed self-map of an irreducible Noetherian scheme is surjective (generic-point
    orbit). So the "dimension-theory" input `QuasiFiniteEndSurjective` is a theorem;
  - `Δ_f` is the base change of the unit section of `ker f`;
  - a section of an unramified morphism is an open immersion.
- Consumers (proofs copied from g0-fibresimple): FS2 `endDivisionOfSchemeIso` now holds unconditionally;
  FS3 holds from T6 + `KerUnitOpen` (`end0Division_of_homFree_kerUnitOpen`).

**What remains.** Two glue Props on the cotangent space `m₀/m₀²` of `𝒪_{A,0}`, stated over Mathlib's
`stalkMap` and `Ideal.mapCotangent`:
- `CotangentMulN`: `[n]` acts on `m₀/m₀²` as `n • id` (the group law to first order);
- `KerUnitOpenOfCotangentSurj`: if the cotangent map is surjective, the unit section of `ker f` is open
  (fibre local ring, Nakayama).

Both are standard but unproved: Mathlib v4.35 has no lemmas on stalks of fibre products. The degree
`n^{2g}` is not needed and is not stated. Locators (Mumford §4, Milne Thm 8.2 / Cor. 2.2) are UNVERIFIED.

Files: docs/research/mul-rigidity.md; scratch/mul-rigidity/{Rigidity,Mul,MulRigidity}.lean,
fs_tail.lean.part, assemble.sh, log.md.
