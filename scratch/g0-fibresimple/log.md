# g0-fibresimple results log

## Setup
- 01:45 merged origin/wip/g0-split (base for Split.lean). FibreSimple's statement is identical in
  origin/wip/leaf-adopt3's Leaves.lean (VERIFIED by grep).
- Infrastructure: `olean/FSPrefix.lean` = verbatim copy of scratch/g0-split/Split.lean (gitignored; regenerate
  with build_prefix.sh), compiled to an olean; `olean/Tail.lean` imports it (`ctail.sh`).
- `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` was needed first (OK).
- 01:53 prefix olean built (231 s, exit 0).

## Decomposition (Tail.lean)
- 02:00 `G0FibreSimple.fibreSimple_of_pieces : QMDichotomyYu → EndDivisionDescent → EndDivisionOfSchemeIso →
  EndDivisionOfEnd0Division → CentralizerOfMatrixEnd0 → FibreComTrivial → HSyn.G0Split.FibreSimple` COMPILED
  (exit 0, 38 s against the prefix olean); `#print axioms`: propext, Classical.choice, Quot.sound.
  Also `fibreSimple_of_leaves (t : TextbookLeaves) (p : FibreSimplePieces)` (T27 is `TextbookLeaves.t27`).
- Proved glue (VERIFIED, compiled): `B6_isUnit` (B = (2,-3) division, from GlueDescent.aniso_rat),
  `qm_embeds_end0` (QMStr gives ℍ[ℚ,2,-3] →ₐ[ℚ] End0 A via QuaternionAlgebra.Basis.liftHom, i ↦ 1⊗ι(i), j ↦ 1⊗ι(j)
  with j = 2·(1+j)/2 − 1 ∈ 𝒪).

## Finding: R1fpProps/R2fpProps do not pin down Φ on closed points
- 02:10 COMPILED (exit 0, 101 s): `PtAuto Y` (natural automorphism σ of the field-point functor), `twistBy Φ σ`,
  `r1fpProps_twistBy` (R1fpProps invariant, no condition), `r2fpProps_twistBy` (R2fpProps invariant if σ permutes the
  π-fibres of ℚ̄-points and fixes the fibres over 0, ∞, −16/27), `fibreComTrivial_twisted`. Standard axioms.
- Consequence (argument, SPECULATIVE in its arithmetic part): with the true data (Y₃, Φ, π), a natural σ exchanging
  the π-fibre over t₁ = J(u) with the fibre over a rational non-branch CM value t₂ exists iff the two fibres are
  isomorphic Gal(ℚ̄/ℚ)-sets (closed points with ℚ-isomorphic residue fields). For such σ, FibreSimple at
  (Y₃, Φ∘σ, π) asks a CM surface to be simple: false. So FibreSimple ⇔ NoCM ∧ "no such coincidence"; the second
  conjunct is not a published theorem and is not decided here.
