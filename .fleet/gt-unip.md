# gt-unip (2026-11-15)

**Verdict.** The field `semistableUnipotent : ReductSplit.SemistableUnipotent` is discharged with its statement
unchanged. There is no glue. It rests on one new printed-base leaf and two leaves already in the bundles:
`UnipotentForward.semistableUnipotent_of_forwardGeom (hP : SGA7_IX_3_5_ForwardGeom) (hE : MulEtaleAbelianScheme)
(hN : GapSHPair.NeronBaseChangeStrictHenselization)`, in `ZInQKernel/Contrib/OneProof/UnipotentForward.lean`.

**The new leaf.** It is SGA 7 IX 3.5, forward direction only, `(σ-1)² = 0` one `σ` at a time. It is stated over a
strictly henselian DVR, with `K^s` and `T_ℓ = lim A(K^s)[ℓⁿ]` (number UNVERIFIED). Its one open reading axis is the
residue field: semistability is read on the geometric fibre, and this matters only for imperfect `k(s)`, the same
kind of risk the chain already accepts for `raynaudSemistableSH`.

**Reading-robust alternative.** `semistableUnipotent_of_forward` assumes semistability over both `k(s)` and the
geometric fibre, so it follows from the print under either reading. It costs the GLUE `SemiAbelianDescendsSepClosed`,
proved here only for perfect `k(s)`.

**Consumers (read in source).** r6 (`raynaudCriterion_leaves`) uses only the forward direction at `σ = τ`, with
`Ω = K̄`. The field was already exactly that, so no consumer site needs rerouting. r8 is inert.

**New proof.** `ReductGlue.StrictHenselizationInside` is proved from the chain's leaf
`NeronBaseChangeStrictHenselization`, using gt-shpair's inertia field. The `K^s` axis and the `k(s)` fibre lemmas
are unipotent-b's proofs, copied into the contribution.

**Compiles (VERIFIED).**
- The contribution compiles with no errors or warnings, and the lake build of Main, Discharges and the contribution
  succeeds.
- `#discharges` reports `OpenResearchLeaves19.semistableUnipotent` discharged by both theorems, with standard axioms
  only.
- The autofold dry run (`scratch/gt-unip/autofold-spec.json`) compiles and gives the strict count 49/12 → 50/11
  (GLUE −1).

**Remains.**
- Read SGA 7 IX §3 (Déf. 3.1, Prop. 3.5) to settle the `k(s)` reading and the number.
- `SemiAbelianDescendsSepClosed` is unproved for imperfect separably closed residue fields; it is needed only on the
  robust route.
- The fold, a locators.md row and a kinds.tsv row are left to the integrator.

Report: `docs/research/gt-unip.md`; log: `scratch/gt-unip/log.md`.
