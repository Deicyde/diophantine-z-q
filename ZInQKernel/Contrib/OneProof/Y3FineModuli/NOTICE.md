# Y3 tangent-trace source and change notice

This directory contains a partial prerequisite contribution for the unchanged
`LeafQM.AV.R1UnivRigid.R1fpAb` goal, not a fine-moduli witness or an H10 proof.

## Existing definitions and suppliers

- The literal order, `oi`, `oj`, and their relations are imported from
  `ZInQKernel.HDecomp.QM.Structures`; they are not redefined.
- The actual `SchemeHomOver` and `RelativeGroupLaw` definitions are reused from
  the current `CloudW03NeronSurj` source port. Their namespace is
  `ZInQ.Contrib.CloudW03NeronSurj.FLT`, and their structures and field types were
  compared with the original public source.
- The separate maximal-order and ramification proofs in fork PR30/upstream
  PR130 are not duplicated or replaced by this contribution.

## Public source pin

Copied proof/definition material is from
https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .
Its Apache-2.0 LICENSE, NOTICE and attribution are retained byte-for-byte under
`Vendor/AnthropicFLT`.

Source material:

1. `Definitions/Def_CerednikDrinfeld_QMModuli.lean`, Points and Tangent sections:
   `SourceTangentPoints.lean` retains actual scheme morphisms and dual-number
   tangent points. It does not replace `FakeEllipticCurve` by an invented model.
2. `S_AlgHom_exists_cotangent_linearMap_of_fst_eq.lean` and
   `S_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap.lean`:
   proof bodies and mathematical signatures retained in `CotangentLifts.lean`.
3. `S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.lean`:
   actual tangent-dimension body ported in `TangentDimension.lean`.
4. `S_CerednikDrinfeld_QM_exists_moduleEnd_apply_eq_pushPt_of_isTangentVector.lean`:
   operator construction specialized to the actual ring `LeafQM.O` in
   `TangentOperators.lean`; a ring homomorphism and its uniqueness are derived
   through the exhaustive tangent-point map.
5. `CerednikDrinfeld.QM.trace_eq_intCast_of_charZero_of_smoothOfRelativeDimension_two`:
   the same geometry/operator/trace composition is used for the literal order
   in `CharZeroTrace.lean`. The scalar trace proof is new and uses only the
   actual order relations and cyclic trace, not generic maximality/ramification
   or a four-dimensional Tate representation.

## Mechanical port changes

- New helper names are isolated in
  `ZInQ.Contrib.OneProof.Y3FineModuli.Source`; original names and their mappings
  are documented above rather than hidden or attributed to the original file.
- Imports are retargeted to the current defining/supplier modules.
- Unused `P2M.Util` imports are omitted. No custom elaborator, macro, `#eval`,
  `run_cmd`, initialization-based bypass or new axiom is introduced.
- Source scoped-reactivation commands are replaced by ordinary Lean scoped
  activation, with current helper namespace qualification. Compilation must
  verify their sufficiency; this notice is not a compilation receipt.
- Root qualifications distinguish Mathlib definitions from namespaced helpers.
- `TangentDimension.lean` additionally sets
  `backward.isDefEq.respectTransparency.types` to `false` for ordinary Lean 4.35
  coercion, stalk-map and smooth-base-change elaboration. This compatibility
  option affects elaboration only; it changes no kernel trust setting, source
  geometric hypothesis or proof conclusion.
- Source namespace scopes left implicit at EOF are closed explicitly.
- Whitespace/line wrapping is changed without claiming raw byte identity for
  the adapted Lean files. The original license/notice/attribution files alone
  are byte-preserved.

## Boundaries

No `PtEquiv`, proper smooth moduli curve, universal family, global
classification/gluing, or geometric nonempty point is constructed here.
No inverse Level3-to-FullLevel generation/full-81-torsion proof is claimed.
In particular, a kernel `3O` condition is not treated as the source's full
geometric generation clause. No full degree/cardinality provider or other
held Shimura/CM/coarse-moduli clause is taken over.

Native compilation, closed-type checks, standard-three axiom output and
independent review are separately required before any proof grade is stated.
