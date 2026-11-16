# Source-to-project dictionary

This maps a **tangent-trace prerequisite**, not the `R1fpAb` witness.
All original files below are pinned to
https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .
Adapted helpers use `ZInQ.Contrib.OneProof.Y3FineModuli.Source`.
Original LICENSE, NOTICE and ATTRIBUTION are byte-preserved under
`Vendor/AnthropicFLT`; compatibility changes are in `NOTICE.md`.

## Actual objects

`SchemeHomOver` and `RelativeGroupLaw` reuse the defining modules of the
existing `CloudW03NeronSurj` port. They remain actual scheme morphisms over an
affine base and pointwise relative group operations. They are **not silently
identified with the target `QMAbScheme` group object**.

`SourceTangentPoints.lean` copies the Points/Tangent sections of
`Definitions/Def_CerednikDrinfeld_QMModuli.lean` into the port namespace:
`mapPt`, `pushPt`, `FactorsThrough`, `nsmulPt`, `geomPoint`, `tangentBase`,
`tangentZero`, `tangentScale`, and `IsTangentVector`. The tangent base is the
actual `Spec(DualNumber k)`; the zero restriction is the scheme's identity
point. No four-dimensional Tate module is substituted.

## Proof bodies

- `CotangentLifts.lean`: the actual solutions
  `S_AlgHom_exists_cotangent_linearMap_of_fst_eq` and
  `S_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap`, from
  `P2M/Sol/`. Both scalar actions and `IsCentralScalar` are retained.
  New names are `Source.AlgHom.exists_cotangent_linearMap_of_fst_eq` and
  `Source.AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap`.
- `TangentDimension.lean`: the actual
  `P2M/Sol/S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.lean`
  body, with import/helper qualification and scoped activation changes. Its
  `Source.P2MW.…solution` derives `finrank = d` from smooth relative dimension
  `d` and the full compatible tangent map. The original dimension theorem
  assumes `Field k`, **not** algebraic closedness, characteristic zero or
  finite `V`. The elaboration option added for Lean 4.35 is documented in NOTICE.
- `TangentOperators.lean`: the actual construction method/body of
  `P2M/Sol/S_CerednikDrinfeld_QM_exists_moduleEnd_apply_eq_pushPt_of_isTangentVector.lean`,
  specialized to the genuine unital ring `LeafQM.O`. Source lattice membership
  witnesses for 1/multiplication become the literal ring operations. A linear
  ring action `ρ` is constructed through `τ`, and `ρ m = Φ` is proved by
  injectivity and actual intertwining.
- `LiteralOrderTrace.lean`: a **new proof** from the project's actual
  `oi² = 2`, `oj² = −3`, and anti-commutation relations. Cyclic trace annihilates
  `oi`, `oj` and `oi*oj`; the literal twice-`ofInt` coordinate identity then
  yields trace `2n₀+n₂`, equal to integer reduced trace. It assumes no generic
  maximal-order/ramification theorem or hidden R1 witness.
- `CharZeroTrace.lean`: the fixed-order counterpart of the genuine source
  `CerednikDrinfeld.QM.trace_eq_intCast_of_charZero_of_smoothOfRelativeDimension_two`
  (its `Theorems/Thm_…` and `P2M/Sol/S_…` pair). The proof derives dimension,
  constructs the operators, and applies the new literal-order trace proof.
  All source-style universe-zero scheme/tangent/action hypotheses remain,
  including `IsAlgClosed`, `CharZero` and finite `V`. Generic quaternion
  parameters/lattice are replaced by `LeafQM.B`/`LeafQM.O`; the generic
  arithmetic hypotheses are not assumed or hidden—the fixed-order proof needs
  none. Separate maximal-order/ramification suppliers are not duplicated.

## Quantifier and validation boundaries

The main geometric statement retains its actual affine base, every test
scheme in the action clauses, every algebraically closed characteristic-zero
field, every finite compatible tangent model, and every intertwined linear
operator. `finrank=2` is an explicit premise only of the separate algebraic
lemma and is a **derived conclusion** in the geometric composition.

The entry imports defining modules, not `OneProof.Main`. It proves no open
field and supplies no target-object bridge, full level/torsion transport,
moduli curve, `Qbar` point, `PtEquiv`, global family or classification.
See `VERIFICATION.md` for exact checked revisions and limitations.
