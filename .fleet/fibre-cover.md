# fibre-cover: FibreCoverExists (G2: Prop. TS + Lemma NV)

**Verdict.** `G0ModField.FibreCoverExists` (scratch/g0-mod-field) is not refuted, and the
relabeling of rv-g0pieces does not break it.

- **G2's output depends only on the residue field of the point.** `fibreCoverOut_iff`: from R1fp
  alone, `FibreCoverOut Y Φ u P` holds iff `ℚ(y)` lies in the splitting field of a separable
  `f` of degree `≤ 324` that is unramified outside `T(u)`. The rational fibre `PK/K` and its
  model are proved for every `K ⊇ ℚ(y)`.
- **The moduli bijection does not matter.** `fibreCoverOut_indep`: two bijections `Φ, Φ'` on the
  same `Y` give the same answer at the same point.
- **The pinning problem is in `(Y, π)`, not `Φ`.** R1fp and R2fp constrain `(Y, π)` only through
  field points. Proposition TS can therefore be proved from the leaves only after `(Y, π)` is
  pinned up to isomorphism (`CurvePinned`).
- **The degree step needs no pin.**

**What compiles.** `scratch/fibre-cover/FibreCover.lean` has 0 errors and 0 warnings. Every
`#print axioms` lists only `[propext, Classical.choice, Quot.sound]`. Main theorems:

- `fibreCoverExists_of_twistClassCard : TwistClassCard → FibreUnramified → UnramifiedConjugates → FibreCoverExists`;
- `fibreCoverExists_of_pinned (Y₀ π₀) : TwistClassCard → CurvePinned Y₀ π₀ → FibreUnramifiedOn Y₀ π₀ → UnramifiedConjugates → FibreCoverExists`;
- supporting results: `fibreDegree_of` (degree bound from the intrinsic twist-class count, via
  "a subfield of `ℚ̄` with `≤ n` embeddings has degree `≤ n`"), `fibreUnramified_of_pinned`,
  `rationalFibre_of_le`, `fibreCoverOut_iff`, `fibreCoverOut_indep`.

**What remains** (each a `def … : Prop` with a docstring):

- `FibreUnramifiedOn Y₀ π₀` (glue): Prop. TS + Lemma NV on one curve, the large G2 item. It
  needs integral models and function-field Galois theory.
- `TwistClassCard` (`≤ 4·81` classes in an `Aut 𝒪`-twist class) is proved from `TorsionBound3`
  and `InnerTwistCount` (`twistClassCard_of`). Those two remain:
  - `TorsionBound3`: `|A(ℚ̄)[3]| ≤ 81`, a bridge from the leaf `TorsionStructure`;
  - `InnerTwistCount`: `|N_B(𝒪)/ℚ^×𝒪^×| ≤ 4`, glue.
- `CurvePinned` (glue once qm-pin lands): Yoneda, Galois quotient, Möbius.
- `UnramifiedConjugates` (textbook): the Galois closure of an unramified field is unramified.

Whether an exotic `(Y, π)` exists, that is, a second Belyi-type map on `Y₃` compatible with a
field-point relabeling, is open (UNSURE). Report: docs/research/fibre-cover.md.
