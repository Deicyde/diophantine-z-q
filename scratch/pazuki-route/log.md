# pazuki-route results log

- Merged c0f3d085 (origin/main leaf-fold33) and 7f58b0149 (origin/wip/pazuki-inputs) into fee21695: both clean. VERIFIED.
- Build of Main + PazukiInputs on the merged tree: `Build completed successfully (14229 jobs)` (build0.txt). VERIFIED.
- (A) consumer audit by reading (VERIFIED, read): the only reader chain is `r22_of_upper` (TailY) -> `R22_Pazuki`
  -> `r22Concrete_of` -> `thetaPazuki` (LPrefix) with `ThetaPointOfFibre` (proved, TailK `thetaPointOfFibre_of_qm_atQM`
  from `FibreQMPeriod` + `ThetaRatiosAtQM`). There `A` is a number-field model of a `QML3` fibre (no polarization in
  `QML3`, Structures.lean:222), `Omega = Omega(tau)` (analytic type-mu polarization), `z` from `ThetaRatiosAtQM`,
  inequality `pazuki_upper_of_upper` at `X = max(1, x+3)`. No algebraic principal polarization is available on `A`.
- FieldTaint run (copy of fold33-pic's) killed twice (20 min limit / blocked Lean dev); rerun later.
- scratch/pazuki-route/Route.lean compiles, no errors, no warnings (lake env lean). VERIFIED. Axioms of
  finrank_bcMap, symmPrincipalDefinedOver_of_class, symmClassDefinedOver_of_countable, pazukiCor13Upper_of_route:
  [propext, Classical.choice, Quot.sound] (axioms-output.txt). VERIFIED.
  New Props: SymmClassDefinedOver (GLUE composite, class-level core), AmpleDescendsFieldExt (LEAF, EGA IV 2.7.2),
  SymmetricClassesCountable (GLUE composite), CountablePointsDefinedOver (GLUE, AG). Proved: h0 descent along
  bcMap (flat base change), SymmPrincipalDefinedOver <= SymmClassDefinedOver + AmpleDescendsFieldExt,
  SymmClassDefinedOver <= PicRepresentableAbVar + SymmetricClassesCountable + CountablePointsDefinedOver.
- SymmetricClassesCountable PROVED (symmetricClassesCountable_of_fields) from picRepresentableAbVar,
  kleimanPicZeroProper, mumfordTorsionAlgClosed (+ proved picLocFinType, identityComponentLFT, Cartier, homFreeFiniteC,
  card_isDT_le0, mu_pic_of_isTI0). VERIFIED (compiled, standard axioms).
- CountablePointsDefinedOver PROVED (countablePointsDefinedOver_proof; CP.lean then Route.lean): affine open, Spec of
  f.t. K-algebra, transcendence bases of C (IsAlgClosure.equivOfEquiv over K[X] with two algebra structures),
  countability of algebraic numbers over countable K. VERIFIED.
- Main: PazukiRoute.pazukiCor13Upper_of_fields (GAGAMorphism, PazukiCor13UpperPP, RiemannPPAV, PicRepresentableAbVar,
  KleimanPicZeroProper, MumfordTorsionAlgClosed, AmpleDescendsFieldExt). Axioms standard (axioms-output.txt). VERIFIED.
- Build +Main +Discharges +Contrib.OneProof.PazukiRoute: Build completed successfully (14231 jobs). VERIFIED.
- #discharges: DISCHARGES [OpenResearchLeaves31.pazukiCor13Upper] by PazukiRoute.pazukiCor13Upper_of_fields, still
  assumes the 7 above; 35 open hypotheses, 9960 theorems checked, 39 discharge one. VERIFIED.
- autofold dry run (no --allow-rise needed): strict count 11/18 on 29 -> 13/18 on 31 (GLUE neutral, +2 LEAF);
  FoldCheck.lean compiles, sixContactMin_of_open49 standard axioms. VERIFIED.
