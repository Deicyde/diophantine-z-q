# inner-twist results log

Base f90cf864 (wip/integrate-w38b). Targets: `G0ModField.InnerTwistCount` and
`G0ModField.UnramifiedConjugates` from `scratch/fibre-cover/FibreCover.lean`.

## InnerTwist.lean (imports ZInQKernel.HDecomp.QM.Structures, ZInQKernel.HDecomp.Textbook.SkolemNoether)
- `lake build` of QM.Pairs, Descent.B2Glue, Textbook.SkolemNoether, QM.Structures: success (1m54s). VERIFIED.
- File = scratch/aut-o-finite/AutOFinite.lean unchanged + header note + §IT.
- §IT: `InnerTwistCount` copied verbatim (docstring + body, namespace G0ModField); a script checked the
  748-character block of FibreCover.lean (docstring to end of def) is a substring of InnerTwist.lean. VERIFIED.
- `G0ModField.ad_comp_eq_comp_ad`: Ad v ∘ t = t ∘ Ad(t⁻¹ v).
- `G0ModField.innerTwistCount : InnerTwistCount` (W = image of the four reps of
  `Exact.autO_mod_inner_exact`, i.e. conjugation by 1, i, j, ij).
- `G0ModField.innerTwistCount_sharp`: every covering W has `4 ≤ W.card`.
- run (06:36, ~25 s): exit 0, 0 errors (linter warnings only, inherited §8); all 7 `#print axioms`
  [propext, Classical.choice, Quot.sound] (run_innertwist.txt). VERIFIED (compiled).

## UnramConj.lean (imports ZInQKernel.HDecomp.QM.Pairs, ZInQKernel.HDecomp.Descent.B2Glue)
- `UnramifiedConjugates` copied verbatim (docstring + body, namespace G0ModField, `Qbar` = LeafQM.AV.Qbar,
  `UnramifiedAt` = GlueDescent.B2Q.UnramifiedAt); script check: the 830-ish-character block of
  FibreCover.lean is a substring of UnramConj.lean. VERIFIED. An `example … := rfl` in the file checks the
  Prop unfolds to the statement over `AlgebraicClosure ℚ` and `GlueDescent.B2Q.UnramifiedAt`. VERIFIED.
- Mathlib instances found automatically for number fields K → L, L/ℚ Galois: IsScalarTower ℤ (𝓞K) (𝓞L),
  FaithfulSMul, IsIntegrallyClosed (𝓞K), Module.Finite/Flat (𝓞K) (𝓞L), IsGaloisGroup Gal(L/ℚ) ℤ (𝓞L),
  HasSeparableResidueFieldsAt ℤ (𝓞L) p. VERIFIED (compiled test, deleted).
- `inertia_le_fixing`: g ∈ I(Q) fixes algebraMap (𝓞K) (𝓞L) y, when K unramified at p, p ∈ Q.
  Proof: H = fixingSubgroup of range(𝓞K), `IsGaloisGroup.of_isScalarTower`; `HasSeparableResidueFieldsAt.tower_top`;
  `card_inertia_eq_ramificationIdxIn` for G and for H, `ramificationIdx_tower`, `subgroupOf_map_subtype`,
  `card_map_of_injective`, `eq_of_le_of_card_ge`.
- `inertia_fixes_field` (via `IsFractionRing.div_surjective`), `conj_mem_inertia` (σ⁻¹gσ ∈ I(σ⁻¹Q)),
  `numberField_of_fd`, `unramifiedConjugates : UnramifiedConjugates` (roots conjugate by
  `Normal.minpoly_eq_iff_mem_orbit`; trivial inertia ⇒ e = 1 as in unram-tate).
- run (06:50, ~30 s): exit 0, no errors, no warnings; axioms of inertia_le_fixing, unramifiedConjugates:
  [propext, Classical.choice, Quot.sound] (run_unramconj.txt). VERIFIED (compiled).
