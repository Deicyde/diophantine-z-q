# Supplemental source/change notice: new affine M1 core

This notice covers six **new, unpublished** files beside the unchanged frozen
trace-helper draft. It supplements their per-file change headers; it does not
replace or alter the historical `NOTICE.md` or the original upstream notices.

- `GrpObjRelativeGroupLaw.lean`: actual forward group-object construction from
  `Definitions/Def_AlgebraicGeometry_RelativeGroupLawGrpObj.lean`, lines 57–110,
  at anthropics/fermats-last-theorem
  `6e837e75355538c7f80bab5b956861e86c4eacc2`. The source body is retained with
  current imports and isolated namespace. Exact primitive bytes were restored
  from the journal and rechecked after the earlier worker was retired.
- `GrpObjActionTrace.lean`: new actual Over-category transport of the source
  action clauses, using pinned Mathlib categorical monoid-hom/point operations.
- `CanonicalTangentModel.lean`: new extraction of a concrete actual cotangent-dual
  model from the source tangent-dimension proof. It reuses `pointOf`, `γJ`,
  square-zero lifts and smooth cotangent equivalences without altering the
  frozen source proof. It adds named base-cast/range lemmas and enables the
  ordinary `backward.isDefEq.respectTransparency.types=false` elaboration option,
  already used by the source port. No kernel trust option is changed by it.
- `GrpObjCanonicalTrace.lean`: new composition constructing the order action on
  that genuine tangent model and deriving rank two and reduced trace.
- `GrpObjActionCommutative.lean`: new algebraic proof of relative point-group
  commutativity from the actual additive/unital order action and the IsMonHom
  property of its -1 endomorphism; no geometric-integrality/commutativity premise.
- `GenericOverFieldTrace.lean`: new transport for the genuine generic Over-object
  and proof of field characteristic zero from the actual ℚ-algebra map composed
  with its field point. The source universal tangent quantifiers are retained.

The original Apache-2.0 LICENSE, NOTICE and ATTRIBUTION for the pinned reused
source remain byte-identical under `Vendor/AnthropicFLT`. Adapted/new files are
not claimed byte-identical to upstream. Their source and changed portions are
identified above and in their own headers. All new proofs use ordinary Lean
and only the allowed standard axioms; no new custom macro, elaborator or
build-time proof bypass is introduced. Existing inherited source macros are
not new proof code, and producer/import cache limitations remain explicit.

These files are prerequisites, not the full source structure on target objects,
full-level generation/81-torsion, a universal family, `PtEquiv`, a `Qbar` point
or an R1/H10 witness. The real TailZ16 consumer remains uncompiled. Source,
compiler and non-author review limits are retained in the private evidence.
