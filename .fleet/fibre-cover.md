# fibre-cover: FibreCoverExists (G2: Prop. TS + Lemma NV)

**Verdict.** `G0ModField.FibreCoverExists` (scratch/g0-mod-field) is not refuted, and the
relabeling of rv-g0pieces does not break it.

- **G2 depends only on the residue field of the point.** `fibreCoverOut_iff` (from R1fp alone):
  G2 holds iff `ℚ(y)` lies in the splitting field of a separable `f` of degree `≤ 324`,
  unramified outside `T(u)`. The rational fibre and its model are proved for every `K ⊇ ℚ(y)`.
- **The moduli bijection does not matter.** `fibreCoverOut_indep`: two bijections `Φ, Φ'` on the
  same `Y` give the same answer at the same point.
- **What is unpinned is `(Y, π)`, not `Φ`.** R1fp and R2fp see `(Y, π)` only through field
  points. Proposition TS therefore needs either the pin `CurvePinned` (`(Y, π)` up to
  isomorphism, as qm-pin's repair will give) or Proposition TS for every admissible cover
  (`PropTSAll`). Both are argued true (SPECULATIVE: Hilbert irreducibility forces `π` to be
  Galois with indices `4, 6, 2`), but neither is provable from the existential leaves alone.

**What compiles.** `scratch/fibre-cover/FibreCover.lean` (745 lines) has 0 errors and 0 warnings.
All 14 `#print axioms` lines list only `[propext, Classical.choice, Quot.sound]`. The headline
theorems:

- `fibreCoverExists_of_propTS (Y₀ π₀) : PkgI2.TorsionStructure.{0} (T5) → InnerTwistCount → CurvePinned Y₀ π₀ → PropTS Y₀ π₀ → UnramifiedConjugates → FibreCoverExists`;
- `fibreCoverExists_of_propTSAll : T5 → InnerTwistCount → PropTSAll → UnramifiedConjugates → FibreCoverExists`.

On the way, these are proved:

- `fibreDegree_of`: `[ℚ(y):ℚ] ≤ 324` from the intrinsic twist-class count, with no pin.
- `twistClassCard_of`: Glazer's `4·81`, via transport of level structures and inner twists.
- `torsionBound3_of_t5`: `|A(ℚ̄)[3]| ≤ 81` from the bundle's leaf T5.
- `fibreUnramifiedOn_of_propTS`: the valuation analysis, via
  `GlueRepo.PR.inertia_trivial_iff_not_dvd`.
- `fibreUnramified_of_pinned`, `rationalFibre_of_le`.

**What remains** (each a `def … : Prop` with a docstring):

- `PropTS` (glue from Beckmann 1991 Prop. 4.2 or T1-T2 + R1(d)): Prop. TS on the genuine
  `Y₃ → P¹` in Beckmann's inertia form. This is the large item.
- `InnerTwistCount` (glue): `|N_B(𝒪)/ℚ^×𝒪^×| ≤ 4`.
- `CurvePinned` (qm-pin) or `PropTSAll`.
- `UnramifiedConjugates` (textbook): the Galois closure of an unramified field is unramified.

Report: docs/research/fibre-cover.md. Log: scratch/fibre-cover/log.md.
