# y3-p1j log

## 2026-11-17

- Read (VERIFIED): docs/research/y3-route-a.md, .fleet/y3-route-a.md, scratch/y3-route-a/log.md; diophantine_zq.tex L400-640.
- Manuscript L410-441 (VERIFIED by reading): B=(2,-3), O=Z[i,(1+j)/2], mu=2j+ij (L411-412); Riemann form, Rosati (L412-420);
  "normalizer quotient is P^1_j, branch values 0, oo, -16/27, indices 4,6,2 [babagranath, linyang]" (L420-422);
  K_0, K_3 (L423-424); N normalizes K_3, local normalizers, |N/(A_f^* K_0)| = 4 (L425-429); central ideles act
  trivially (L430-434); Y_3 with all determinant components admits N/(A_f^* K_3) with quotient P^1_j,
  deg(Y_3 -> P^1_j) <= 4|(O/3O)^*| <= 4*81 = 324 (L434-440).
- Computed (VERIFIED, scratch/y3-p1j/units_mod3.py, exact arithmetic on the basis (1,i,(1+j)/2,(i+ij)/2)):
  |O/3O| = 81, |(O/3O)^*| = 72 (36 of norm 1 mod 3, 36 of norm -1). So 4|(O/3O)^*| = 288 <= 324 (manuscript's
  bound holds), and |N/(A_f^* K_3)| = 4*72/2 = 144 (the central (Z/3)^* = {+-1} is in A_f^* K_3).
- Kernel facts (VERIFIED, read): R2fpProps (HDecomp/QM/Leaves.lean:94) is R2 on Y_3 (pi : Y -> P^1, fibres = Aut(O)-twist
  classes of underlying pairs, CM values). R1heckeProps (twist alpha, rightMul u realised by automorphisms of Y) is
  proved from any fine witness: heckeOfFine_proof (TailU:2220). FactorThroughSurj proved (factorThroughSurj_proof,
  TailZ20:1076) for targets that are proper smooth curves (Over objects), not for ToP1 charts.
- Row r1r2 = LeafAdopt.R1R2fpRepW (LPrefix:5248), built by x6Rows_of_leavesW (TailZ21:1603) from BabaGranathRational
  (R2X6PropsIff + surjectivity of pi_6), GonzalezRotgerX6 (X6 witness + R5ptProps), RayClassCM, T5; producers in the
  current chain: babaGranathRationalAb := babaGranathRationalAb_of_printed (elkiesX6StarPrinted_of_functionField
  n.elkiesX6StarFunctionField) ... (EichlerBoundCopy etc.), elkiesX6StarFunctionField from elkiesX6StarEvery and
  x6CoarseModuli (TailZ59:83, EichlerBoundCopy:3703), gonzalezRotgerX6Ab from x6CoarseModuli (TailZ59:78).
- Computed (VERIFIED, scratch/y3-p1j/gram.py -> gram.txt, exact rationals): with mu = 2j+ij (nrd 6, mu^2 = -6) the matrix of
  Trd(mu^{-1} x ybar) in the basis (1,i,(1+j)/2,(i+ij)/2) is exactly the printed matrix of L414-416, determinant 1.
- Lean, ZInQKernel/Contrib/OneProof/Y3ToP1j.lean (namespace Y3P1j), `lake build +ZInQKernel.Contrib.OneProof.Y3ToP1j` OK;
  #print axioms (scratch/y3-p1j/axioms.txt) [propext, Classical.choice, Quot.sound] for action_of_z30, sigmaR_neg_one, isoT,
  hauptmodulOfX6_of_y3ToP1j, r1r2W_of_y3ToP1j, y3ToP1jAt_noDeg_of_row (VERIFIED).
  * opP alpha u (twist by alpha in Aut O, then rightMul by u in O^x) on QMAbSchemeP S; rightMulP u = opP refl u, twistP alpha = opP alpha 1.
    (Pitfall: elaborating the two special cases as separate structure instances loops in whnf; with alpha free it does not.)
  * Yoneda on Y3FullThreeRepZ30's representing scheme: sigmaR/sigmaT unique with sigma^*A = T A; composition laws
    sigmaR_comp (sigma_u >> sigma_v = sigma_{vu}), sigmaT_comp; isoR, isoT automorphisms; sigmaR_neg_one: -1 acts as identity
    (via iota(-1) = [-1]); summary action_of_z30.
  * Leaf Y3ToP1j (every fine witness (Y,Phi) with R1fpProps has pi : ToP1 Y with Y3ToP1jAt: fibres = Aut(O)-twist classes of
    underlying pairs, CM(-4),CM(-3),CM(-24) <-> 0, oo, -16/27, onto P^1(Qbar), Qbar-fibres finite with <= 324 points).
  * Glue ToP1DescendsAlongSurj (descent of a ToP1 map along a surjection of proper smooth curves; = proved FactorThroughSurj
    with X' = P^1_Q plus the chart dictionary; not proved here).
  * hauptmodulOfX6_of_y3ToP1j : Y3ToP1j -> ToP1DescendsAlongSurj -> PairsLift -> HauptmodulOfX6;
    r1r2W_of_y3ToP1j : CanonicalModelY3 -> CoarseX6OfFineW -> Y3ToP1j -> ToP1DescendsAlongSurj -> ReciprocityOfFine ->
    ResidueOfX6 -> R1R2fpRepW (PairsLift from pairsLift_of_t5 and the proved mumfordTorsionAlgClosed_proof).
  * y3ToP1jAt_noDeg_of_row : R1R2fpRepW -> (a witness with every clause of Y3ToP1jAt except the degree bound), pi = pi6 o fY.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: OK (up to date; scratch/y3-p1j/build-main.tail.txt).
- #discharges with Y3ToP1j imported (scratch/y3-p1j/discharges.txt): no line mentions Y3P1j (VERIFIED): no theorem of the new
  file has the type of a bundle field (HauptmodulOfX6 and R1R2fpRepW are not fields).
- grep over the whole tree (scratch/y3-p1j/grep-x6.txt, VERIFIED): x6CoarseModuliIdeal and elkiesX6StarEveryIdeal are read only in
  the TailZ71/TailZ74 conversions to x6CoarseModuli and elkiesX6StarEvery. Their readers: x6CoarseModuli -> gonzalezRotgerX6Ab
  (X6 witness + R5ptProps; TailZ59:78) and elkiesX6StarFunctionField (TailZ59:83); elkiesX6StarFunctionField -> elkiesX6StarPrinted
  (TailZ36:102) and babaGranathRationalAb (TailZ37:91); elkiesX6StarPrinted -> elkiesEquationsX6Ab (TailZ29:106; -> x6ConicModel ->
  x6KummerFibre -> NoCM, EichlerBoundCopy:2668) and HeckeSqrtBranchAny (sgr-direct, EichlerBoundCopy:3221, Lemma NV route).
  So re-sourcing R2 (babaGranathRationalAb) leaves both fields read: neither can be dropped on this base.
- ToP1DescendsAlongSurj PROVED (VERIFIED, compiled, standard axioms): ZInQKernel/Contrib/OneProof/Y3ToP1jDescent.lean,
  `Y3P1j.Descent.toP1DescendsAlongSurj_proof`. Ingredients: p1-quot's P1Scheme.lean copied (namespace Y3P1j.P1;
  `ProjectiveSpace` qualified as `AlgebraicGeometry.ProjectiveSpace`, else ambiguous with Mathlib's root ProjectiveSpace),
  giving the CloudW07 projective line proper + smooth of rel. dim 1 + IsP1CoordinateQ + every ToP1 a pullback (p1SchemeQ_body);
  new `pt_eq_of_val` (points of a P^1-coordinatized Q-scheme determined by the coordinate; X6Glue.ev_injective + ext_rat +
  evaluation_eq_zero_iff_notMem_basicOpen at infinity), `val_congr`; then factorThroughSurj_proof.
  Corollaries: `hauptmodulOfX6_of_y3ToP1j' : Y3ToP1j -> HauptmodulOfX6`, `r1r2W_of_y3ToP1j'` (no new glue).
  `lake build +ZInQKernel.Contrib.OneProof.Y3ToP1jDescent` OK; axioms in scratch/y3-p1j/axioms.txt.
- #discharges rerun with Y3ToP1jDescent imported: still no line mentioning Y3P1j (VERIFIED).
- Scratch Lean drafts (Action.lean, P1.lean, Descent.lean, T1.lean) removed after promotion to ZInQKernel/Contrib/OneProof/Y3ToP1j.lean and Y3ToP1jDescent.lean (the canonical sources); build log trimmed to build-main.tail.txt.
