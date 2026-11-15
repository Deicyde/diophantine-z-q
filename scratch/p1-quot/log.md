# p1-quot results log

Target: `HDec.MCRGlue.QuotientP1Coordinate` (ZInQKernel/OneProof/H/TailW.lean L202), bundle field
`HDec.HSyn.OpenGlue7.quotientP1Coordinate`. Base 24f97774 (wip/w72).

## Setup
- Build tree: copied (cp --reflink) from ~/dzq-wt/yu-prune-base (c2ad4181); diff to base in ZInQKernel/ is
  docstring-only in LPrefix/TailA/C/F/H plus TailZ33/Main/two contributions (VERIFIED by git diff).

## Port0/Port1 (mcr-quot over the chain)
- Port0.lean = header (import TailW + CloudW07 ProjectiveLine.Geometry/RelativeCoordinates, namespace HDec,
  TailW's attribute line) + MCRQuot.lean L4406-end (mcr-glue parts 5-6, mcr-quot parts 1-24) minus #print.
  34 errors: name resolution only (ImagePlane.*, curveFacts, smoothStalkDimOne under namespace HDec;
  transportLevel ambiguous Pin vs HDec.G0ModField), plus a stray `end HDec`.
- Port1.lean = Port0 with `_root_.LeafQM.AV.Pin.` qualification of those names: VERIFIED compiles, exit 0, no
  errors (port1_out.txt). So all of mcr-quot holds verbatim over the chain's constants (HDec.MCRGlue.*).

## P1SchemeQ (P1Test.lean)
- P1Test.lean: `P1SchemeQ` (verbatim test copy of MCRQuot.lean L8549 with verbatim copies of
  `IsP1CoordinateQ`, `baseToSectionsOver`) proved: VERIFIED, `#print axioms` = [propext, Classical.choice,
  Quot.sound]. P = `ProjectiveSpace (ULift (Fin 2)) (Spec ℚ)` (CloudW07 relative line), τ.f = `coordRatio i0 i1`,
  τ.g = `coordRatio i1 i0`; universal map from CloudW07 `Scheme.CoordinateCover.hom` on the cover {σ.U, σ.V}
  with ratios 1, σ.f, σ.g, 1; smoothness via charts ≅ 𝔸¹ (`standardOpenIso`, Mathlib
  `AffineSpace.smoothOfRelativeDimension_of_card_eq`); chart bijectivity via
  ℚ[X] ≃ MvPolynomial ≃ Γ(Spec) ≃ Γ(𝔸) ≃ Γ(chart).
- P1Scheme.lean: same over `import ZInQKernel.OneProof.H.TailW` with the chain's `HDec.MCRGlue.IsP1CoordinateQ`
  and `baseToSectionsOver`: VERIFIED (24 s), standard axioms.

## Port2.lean (single-file composite)
- = P1Scheme.lean + Port1 body + final section. VERIFIED compiles (16 s warm), port2_out.txt:
  `HDec.MCRQuot.p1SchemeQ : P1SchemeQ` and
  `HDec.MCRQuot.quotientP1Coordinate_of_leaves' (L1..L6) (hT : ObjBridge.TorsionStructure) (hC : CurveBijIso)
   (hYI : PropTSGlue.HeckeIrreducible) (hO : CMStabObj) : MCRGlue.QuotientP1Coordinate`, both
  [propext, Classical.choice, Quot.sound].
- Port3.lean = Port2 + `import ZInQKernel.OneProof.H.TailR` + `quotientP1Coordinate_of_printed` (CurveBijIso from
  `_root_.CurveSplit.curveBijIso`): VERIFIED compiles, standard axioms (port3_out.txt).

## Contribution files (py/gen_contrib.py generates them from P1Scheme.lean, Port1.lean, Port3.lean)
- ZInQKernel/Contrib/OneProof/QuotientP1/{MCRQuotA (130 KB), MCRQuotB (114 KB), P1Scheme (18 KB)}.lean,
  ZInQKernel/Contrib/OneProof/QuotientP1Coordinate.lean (5 KB). Each compiled with `lake env lean -o` in order:
  VERIFIED no errors.
- Discharges.lean (#discharges over Main + Discharges + the contribution; Main olean of the copied c2ad4181 tree):
  VERIFIED `DISCHARGES [OpenGlue7.quotientP1Coordinate] by HDec.MCRQuot.quotientP1Coordinate_of_printed`, still
  assumes L1-L6, PkgI2.TorsionStructure, HDec.PropTSGlue.HeckeIrreducible, HDec.MCRQuot.CMStabObj; axioms standard
  (discharges_out.txt).

## L5 from Edixhoven (FixedTest.lean)
- New leaf `HDec.MCRQuot.EdixhovenFixedSmooth` (Edixhoven 1992 Prop. 3.4, cyclic group, S = Spec ℤ_(p); fixed scheme
  = equalizer of σ and id in Over S): `Smooth (equalizer (Over.homMk σ hσ) (𝟙 𝒴)).hom` for 𝒴 smooth, σ^n = 1, p ∤ n.
- `tameFixedPointsDisjoint_of_edixhoven : EdixhovenFixedSmooth → TameFixedPointsDisjoint`: VERIFIED compiles,
  [propext, Classical.choice, Quot.sound]. Uses the vendored FLT theorem
  `Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing` (CloudW03) for domain stalks of F,
  `Scheme.range_fromSpecStalk` for the common generization, and `infinite_qbar_closure` (Jacobson generic fibre).

## C1 without L5, L6 (FixedTest2.lean → FixedAll.lean → QuotientP1/FixedDisjoint.lean)
- Leaf `EdixhovenFixedSmooth2` (Edixhoven Prop. 3.4 for G = ⟨σ, τ⟩ finite, p ∤ |G|, S = Spec ℤ_(p); X^G = fibre
  product over X of the two equalizers): `Smooth (pullback.fst ι_σ ι_τ ≫ ι_σ ≫ 𝒴.hom)`.
- `isClosed_ptOf_of_qbar` (point of a Q̄-point of a ℚ-scheme LFT is closed: kernel of R → Q̄ maximal, Jacobson),
  `eq_of_specializes_generic`, `fixed_smooth_of_two` (τ = σ: pullback of a mono with itself),
  `fixed_generization`, `disjoint_closure_of_two` (VERIFIED, standard axioms):
  distinct Q̄-points fixed by σ, τ (finitely many fixed points each, ⟨σ,τ⟩ finite tame) have disjoint closures.
  Proof: common point z ∈ X^G; X^G smooth ⇒ flat ⇒ generalizing ⇒ ζ ⤳ z over the generic point of Spec ℤ_(p);
  in X^σ (domain stalks) the point of y generizes ζ, same for y'; specializations of the point of a Q̄-point
  inside the generic fibre are trivial.
- `tameFixedPointsDisjoint_of_edixhoven2 : EdixhovenFixedSmooth2 → TameFixedPointsDisjoint` (L5 as corollary).
- `cMSectionsDisjoint'_of (hE) (gA) (A-fix) (C1a) (CMStabNontrivial) (C1d) : CMSectionsDisjoint'` (C1 without the
  premises L5, L6; no StabFixesClosure, no involutions). `cMStabNontrivial_of : CMStabObjWeak → CMStabNontrivial`
  (needs neither CurveBijIso nor ModelYIrreducible). All VERIFIED, standard axioms.
- Final `quotientP1Coordinate_of_printed (L1 L2 L3 L4) (hE : EdixhovenFixedSmooth2) (hT) (hYI) (hO : CMStabObjWeak)`:
  VERIFIED (module compiled), #discharges: DISCHARGES [OpenGlue7.quotientP1Coordinate], still assumes L1-L4,
  EdixhovenFixedSmooth2, PkgI2.TorsionStructure, HeckeIrreducible, CMStabObjWeak; standard axioms.

## CMStabObjWeak reduced to its ℤ[√−6] clause (CMTest.lean → QuotientP1/CMStab.lean)
- `rightMul_fix_of_unit` (T5): an invertible φ in the commutant gives a unit u with rightMul u [P] = [P] and
  φ(η a) = η(a u₀), u u₀ ≡ 1 mod 3. VERIFIED.
- `rightMul_moves_cm24`: given `AutCM24` (automorphisms of a ℤ[√−6] pair are ±1), rightMul u moves its class
  unless u ≡ ±1. VERIFIED.
- `autCM24_of : HeckeRest.QMAutCard → AutCM24` (|QMIso q q| = 2 at a point with CM24, units of com q). VERIFIED.
- `not_act_neg_one` (T5, a point of order 9 over the algebraic closure of Q̄): φ² − φ + 1 = 0 in the commutant
  ⇒ φ does not act by −1 on A[3]. VERIFIED.
- `cmStab4_of`, `cmStab3_of`: the ℤ[i] and ℤ[ζ₃] clauses of CMStabObjWeak (α = id, T = rightMul u, moved
  witness: a ℤ[√−6] object). VERIFIED, standard axioms.
- `CMStab24` (glue: the ℤ[√−6] clause), `cMStabObjWeak_of_cm24 (hT) (hQ : QMAutCard) (h24) (hCM)`. VERIFIED.
- Main theorem now `quotientP1Coordinate_of_printed (L1..L4) (hE) (hT) (hYI) (hQ : HeckeRest.QMAutCard)
  (h24 : CMStab24)`; `quotientP1Coordinate_of_fields` derives T5, HeckeIrreducible, QMAutCard from chain fields
  (mumfordTorsionAlgClosed, mumfordRigidityCore, deligneComponentsY3PrintedAb, uniformizationLeafAll,
  gagaMorphism; T11b proved). #discharges VERIFIED (discharges_out.txt), standard axioms.

## HeckeIrreducible without Mumford's rigidity (HeckeIrrAb.lean → FromFields)
- `QuotientP1Proof.DeligneAb.heckeIrreducible_of_ab : ShimuraGlue.DeligneComponentsY3PrintedAb →
  HDec.PropTSGlue.HeckeIrreducible`: VERIFIED, standard axioms. Copies of the chain's orbit computation
  (`y3Connected_of_deligne`, `deligneComponentsY3_of_printed`) and `phi_part` with the clause list cut to what they
  use (a Q̄-point; proper, smooth, R1famProps), plus `r1famProps_of_r1famAbProps` (no rigidity).
- `quotientP1Coordinate_of_fields` now assumes L1-L4, EdixhovenFixedSmooth2, mumfordTorsionAlgClosed,
  deligneComponentsY3PrintedAb, uniformizationLeafAll, gagaMorphism, CMStab24 — no mumfordRigidityCore.
  #discharges VERIFIED.
