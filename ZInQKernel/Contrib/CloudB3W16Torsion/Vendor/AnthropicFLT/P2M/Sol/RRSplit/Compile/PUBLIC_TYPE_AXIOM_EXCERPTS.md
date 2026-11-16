# Public type and axiom output — labeled excerpts

**This file is a selection, not a raw compiler transcript.** The type and axiom
lines below are copied verbatim from the original successful combined check at
frozen proof snapshot `42a9645da2ffe4390cfbc6053aeb3836a9d59515`. Command, timing,
warning, diagnostic, and environment-specific lines are not included here.
Complete original raw output remains unchanged in private archival storage;
it has not been rewritten and represented as raw public evidence.

These are recorded outputs, not new proof assumptions or a new verification run.
Generic local reproduction instructions are in `../REPRODUCING.md`.

## Six original solution types and complete axiom lists

```text
P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.solution.{u_1} (K : Type u_1) [Field K] [IsAlgClosed K]
  [DecidableEq (RatFunc K)] [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
  [AlgebraicCurve.HasCanonicalDivisor] [∀ (v : AlgebraicCurve.Place K (RatFunc K)), v.DCoordGenerates] :
  AlgebraicCurve.ResidueTheoremK K (RatFunc K)
'P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.solution.{u_1, u_2} {K : Type u_1} {F : Type u_2} [Field K]
  [IsAlgClosed K] [DecidableEq (RatFunc K)] [Field F] [Algebra K F] [AlgebraicCurve.HasCanonicalDivisor]
  [∀ (w : AlgebraicCurve.Place K F), w.DCoordGenerates] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F] [AlgebraicCurve.HasLocalResidue K F]
  [∀ (w : AlgebraicCurve.Place K F), w.FiniteResidue] [Nontrivial Ω[F⁄K]] [AlgebraicCurve.IsCurveOver K F]
  [AlgebraicCurve.IsCurveOver K (RatFunc K)] [∀ (u : AlgebraicCurve.Place K (RatFunc K)), u.FiniteResidue]
  [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasPrincipalDivisors K F]
  [Algebra.IsSeparable (RatFunc K) F] [Nontrivial Ω[RatFunc K⁄K]]
  [∀ (v : AlgebraicCurve.Place K (RatFunc K)), v.DCoordGenerates] : AlgebraicCurve.ResidueTheoremK K F
'P2MW.S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.solution.{u_1, u_2} {K : Type u_1}
  {F : Type u_2} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)] [Field F] [Algebra K F]
  [AlgebraicCurve.HasCanonicalDivisor] [∀ (w : AlgebraicCurve.Place K F), w.DCoordGenerates] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F] [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
  [AlgebraicCurve.HasLocalResidue K F] [∀ (w : AlgebraicCurve.Place K F), w.FiniteResidue] [Nontrivial Ω[F⁄K]]
  [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
  [∀ (u : AlgebraicCurve.Place K (RatFunc K)), u.FiniteResidue] [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
  [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F] [Nontrivial Ω[RatFunc K⁄K]]
  [∀ (v : AlgebraicCurve.Place K (RatFunc K)), v.DCoordGenerates] [FiniteDimensional (RatFunc K) F]
  [AlgebraicCurve.HasSeparableResidue K F] (hRTK : AlgebraicCurve.ResidueTheoremK K F) :
  AlgebraicCurve.FunctionFieldRiemannRoch K F
'P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
P2MW.S_AlgebraicCurve_tateAgreement.solution.{u_1, u_2} {K : Type u_1} {L : Type u_2} [Field K] [Field L] [Algebra K L]
  [AlgebraicCurve.IsCurveOver K L] [PerfectField K] [∀ (u : AlgebraicCurve.Place K L), u.FiniteResidue]
  (hfin : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L) : ModularCurve.KwF4gRRTate.KwF4gRRTateAgreement K L hfin
'P2MW.S_AlgebraicCurve_tateAgreement.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.solution.{u_1, u_2, u_3} {K : Type u_1} {F : Type u_2} [Field K]
  [Field F] [Algebra K F] {E : Type u_3} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
  [Algebra.IsIntegral E F] [Algebra.IsSeparable E F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
  [AlgebraicCurve.HasCanonicalLocalResidueKStar K E] [∀ (w : AlgebraicCurve.Place K F), w.FiniteResidue]
  [∀ (v : AlgebraicCurve.Place K E), v.FiniteResidue] (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F)
  (hfinE : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K E) :
  ModularCurve.KwF4gRRTate.KwF4gRRTateTraceCompat K F E hfinF hfinE
'P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.solution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
P2MW.S_AlgebraicCurve_tateChainRule.solution.{u_1, u_2, u_3} {K : Type u_1} {F : Type u_2} [Field K] [Field F]
  [Algebra K F] {E : Type u_3} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
  [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K E]
  [∀ (w : AlgebraicCurve.Place K F), w.FiniteResidue] (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F) :
  ModularCurve.KwF4gRRTate.KwF4gRRTateChainRule K F E hfinF
'P2MW.S_AlgebraicCurve_tateChainRule.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Auxiliary cancellation lemma: selected axiom output

```text
'P2MW.CloudB3W16RRSplit.conj_symm_conj' depends on axioms: [propext, Quot.sound]
```

The residue input of the conditional RR theorem and the finiteness inputs of
the Tate theorems remain visible above. The separate proved global residue
theorem supplies the original residue input. This source-support evidence does
not establish a final H102 `#discharges` result or geometric integration.
