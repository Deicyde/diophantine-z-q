# hecke-glue results log

## Plan (route chosen)
ConstOnTauPoints is proved over ℚ (no base change to ℂ, no geometric irreducibility):
the x_ρ point lands on a closed point of X (jX(x_ρ)=j(ρ)=0, jX≠0); q = g(p_ρ) is closed
(Mathlib closedPoints_subset_preimage_closedPoints); F = g⁻¹{q} closed contains all p_τ;
if η ∉ F then F finite (CloudW07 IsOpen.finite_compl_of_topologicalKrullDim_le_one, dim ≤ 1 from
CloudW07 topologicalKrullDim_le_of_smoothOfRelativeDimension), so finitely many x_τ (finitely many
ℂ-points over a closed point: κ(p) finite over ℚ), so j has finite range on ℍ: contradiction.
So g(η)=q, q closed ⇒ q = g(P₀)=e, κ(e)=ℚ ⇒ g and 1 agree on Spec κ(η) ⇒ g = 1
(Mathlib ext_of_fromSpecResidueField_eq).

## ConstOnTauPoints
- VERIFIED (compiles, `lake env lean scratch/hecke-glue/ConstOnTau.lean`, no sorry):
  `constOnTauPoints_of_x1TauPoints : X1TauPoints → ConstOnTauPoints`.
  Inputs: Mathlib (closedPoints_subset_preimage_closedPoints, SpecToEquivOfField,
  ext_of_fromSpecResidueField_eq, finite_of_finite_type_of_isJacobsonRing, AlgHom.fintype),
  CloudW07 (topologicalKrullDim_le_of_smoothOfRelativeDimension, eq_genericPoint_of_not_isClosed,
  IsOpen.finite_compl_of_topologicalKrullDim_le_one), WeberField (Jf, diffOn_Jf, Jf_I, Jf_ρ,
  exists_good_point, Dlf_ne), HeckePin (const_of_countable).
- Note: ConstOnTauPoints is not provable without the points: with no x_τ its hypothesis is vacuous.
  So the theorem takes X1TauPoints; isHeckeT_unique / isDiamond_unique then need X1TauPoints only.

## X1TauPoints reduced to the analytic GLUE TauPlace
- VERIFIED (compiles, scratch/hecke-glue/HeckeGlueWip.lean): `exists_cpt_of_place` (valuative criterion
  of properness, Mathlib `UniversallyClosed.eq_valuativeCriterion`; center p, local hom 𝒪_{X,p} → O;
  O = 𝒪_{X,p} since 𝒪_{X,p} is a valuation ring (CloudW07 `valuationRing_stalk`) dominated by O)
  and `x1TauPoints_of_tauPlace : TauPlace → X1TauPoints`.
- TauPlace (GLUE, analytic): a valuation subring O ⊆ K(X) with local ev : O → ℂ containing every
  P/Q whose analytic quotient has a limit c at τ, with ev = c. To be proved from the
  meromorphy of evAn (WeberField diffOn_ez, evAn_eq) and IsX1Gen.
- So X1TauPoints is NOT a leaf: it is glue (no published input beyond the definition of IsX1Gen).

## TauPlace proved; X1TauPoints and ConstOnTauPoints proved outright
- VERIFIED (compiles, `lake env lean scratch/hecke-glue/HeckeGlue.lean`, no sorry; axioms
  [propext, Classical.choice, Quot.sound] for x1TauPoints, constOnTauPoints, tauPlace,
  isHeckeT_unique', isDiamond_unique', evF_eq_zero_of_heckeJ_eq_zero_of_abelJacobi,
  killsIf_iff_IfDS_of_abelJacobi).
- tauPlace: O = {a ∈ K(X) : the meromorphic function P(j,f₁)/Q(j,f₁) of a has a finite limit at τ}
  (Mathlib meromorphicOrderAt: order ≥ 0 ⇒ limit, order < 0 ⇒ cobounded ⇒ a⁻¹ → 0); ev = limit.
  Well-defined by IsX1Gen + identity theorem (WeberField eq_zero_or_eq_zero, eq_zero_of_eventually),
  bad points (g₂g₃ = 0) isolated, evAn = ez on good points (WeberField evAn_eq).
- Consequence: isHeckeT_unique / isDiamond_unique hold with NO hypothesis; gap 1 needs only AbelJacobiX1.

## atTau_unique, final checks
- VERIFIED (compiles in ZInQKernel/Contrib/OneProof/HeckeGlue.lean, std axioms): `atTau_unique` — two complex
  points satisfying AtTau at τ are equal (local ring = place O_τ; valuative uniqueness; germ values).
- VERIFIED `lake build ZInQKernel.Contrib.OneProof.HeckeGlue` succeeds.
- VERIFIED #discharges (scratch/hecke-glue/Discharges-output.txt): 35 open hypotheses, 10617 theorems checked;
  r16CoreY by AfTateLam.r16CoreY_of_ds965 with the same five leaves; all HeckeGlue theorems std axioms.
- VERIFIED Target.lean: copies of X1TauPoints/AbelJacobiX1/ConstOnTauPoints are Iff.rfl to the originals.
- VERIFIED autofold dry run: strict count 11/18 on 29 -> 15/17 on 32 (unchanged).
- AbelJacobiX1: remains open; printed statement DS Thm 6.1.2 VERIFIED at 2005 printing pp. 214-215 (pdftotext);
  no Lean printed form possible (no Riemann-surface Jacobian / H_1 / path integrals in Mathlib 4.35).
