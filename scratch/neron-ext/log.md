# neron-ext results log

Base: origin/main 0caafe66 (w80). Build copied (reflink) from the homfree-proof worktree (base 0caafe66, only a new Contrib file).

## Statement (VERIFIED, read)
`ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (ZInQKernel/Contrib/NeronC/NeronGroup.lean:82): for every field K,
AbVar A/K, number field L ⊇ K: a smooth, separated, qc `N` over Spec 𝓞_L with `e : N_L ≅ A_L` such that every
L-morphism `Y_L → A_L` (Y smooth over 𝓞_L) extends to `Y → N`. = existence half of BLR §1.4 Thm 3 over 𝓞_L.

## Consumers (grep, VERIFIED)
- TailM L387 `t41_of_extension5` → T41 `ZInQ.H5Neron.NeronModelExists` (TailN L225, TailO L2875):
  feeds the stable-Faltings-height rows (TailY: r18–r22, heightAdditivity), at every finite L.
- TailZ4 L153/L173 `neronModelExists_of_extension` → N1 for R20 (heightRows_of8).
- TailZ26 L174/L182 `GapNeron.neronSchemeModelExistsNF` (N1 at L = K, then BLR 1.2/4 to DVRs O of K) →
  r6 at number fields (`raynaudCriterionNF_of14`: Raynaud's criterion, used to PROVE semistable/good reduction of
  QML3 objects and in the G15/LTLocal chain) and SS1/SS3 (`ss1_ss3_of14NF`, semistable reduction theorem).
- Field passing only: TailX L145, TailZ9 L76, TailZ11 L29, TailZ32 L25, TailZ42 L24 bundles.
- T41 consumers (VERIFIED, `ReachT41.lean` → `reach-t41.txt`, closure of `ZInQ.OneProof.frozenTarget`): 30 constants;
  real uses `G0Split.heightAdditivity_of_h5neron`, `heightAdditivity_unfolded`, `H5Neron.stableFaltingsHeight_add_le(')`,
  `HeightSplit.{r18,r19,r20Lower,r21,r22}_of_*`, `exists_semistable_neron`, `stableFaltingsHeight_ne_{bot,top}`,
  `stableHeightFinite_of(')`, `stableFaltingsHeight_eq_of_*`, `TailZ4.heightRowsNo20_of8`. These use N1 at
  every finite extension L of a number field (the stable height is an infimum over L).
- N1 consumers (VERIFIED, `reach.txt`, partial scan, 17 constants): bundles only, plus `t41_of_extension5`,
  `neronModelExists_of_extension`, `GapNeron.neronSchemeModelExistsNF` (→ `raynaudCriterionNF_of14`,
  `ss1_ss3_of14NF`).

## Verdict on narrowing (VERIFIED by reading the consumers)
No narrowing to abelian schemes: r6 (Raynaud's criterion, `raynaudCriterionNF_of14`) applies N1 to abelian varieties
of a priori bad reduction (it is how good reduction of QML3 objects is proved); SS1 likewise; the height rows need
a Néron model over 𝓞_L for every L, including places of bad reduction. Test schemes Y: arbitrary smooth (group
law from Y = N, N×N, N×N×N; uniqueness and localization arguments use arbitrary smooth Y).

## Results (all VERIFIED: compiled, `#print axioms` = [propext, Classical.choice, Quot.sound])
1. `NeronExt.glued` (Glue.lean → Contrib `NeronExtGlue`): Néron models over the opens of a cover of Spec 𝓞_L glue
   (Mathlib `Scheme.Cover.RelativeGluingData`), = neron-lg's glue N1-g3, proved.
2. `NeronExt.neronOn_of_local'` (`NeronExtLocal`): the Néron property over an open U is local at the maximal
   ideals of U (copy of gt-blr's `local_pt` with a set T of maximal ideals); `isJacobsonRing_int`.
3. `NeronExt.isNeronModelOver_of_grpObj` (`NeronExtAb`): smooth proper GrpObj over a DVR is a Néron model
   (vendored FLT argument; the bundle's `connectedFibres` is never used, so dropped) = neron-lg's N1-ab.
4. `NeronExt.exists_spread_sep`, `spread_generic` (`NeronExtSpread`): spreading out smooth separated qc schemes
   from R_p to R[1/s] (8.8.2(ii), 17.7.8(ii), Stacks 01ZP on the diagonal) and generic morphisms (01ZC).
5. `NeronExt.near` (glue N1-g2), `goodModel` (N1-g1 + N1-ab), `extension_of_dvrLocal`:
   `EGAIV_8_10_5_xii → NeronDVRLocal → NeronSchemeExtensionExists`.
6. `NeronExt.dvrLocal_of_extension`: `NeronSchemeExtensionExists → NeronDVRLocal` (the new leaf is not stronger).
- `#discharges` (scratch/neron-ext/discharges.txt): `DISCHARGES [OpenTextbookLeaves12.neronSchemeExtensionExists]
  by NeronExt.extension_of_dvrLocal; still assumes: [ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii, NeronExt.NeronDVRLocal]`.
- autofold dry run (`AutofoldDry.lean`) compiles; strict count 34/11 on 45 -> 34/11 on 45.
