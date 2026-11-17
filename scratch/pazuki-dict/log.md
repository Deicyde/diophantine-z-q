# pazuki-dict results log

Task: make `pazukiCor13Upper : ZInQ.HeightSplit.PazukiCor13Upper` printed (base origin/main 2880fef1).

## Statement located (VERIFIED, read)
- kinds.tsv row 15: `research pazukiCor13Upper published LEAF LEAF` (Pazuki, Bull. SMF 140 (2012) Cor. 1.3(2), upper half).
- Definition: `ZInQKernel/OneProof/H/TailY.lean:778` `def PazukiCor13Upper : Prop` (namespace `ZInQ.HeightSplit`).
- Its objects: `ZInQ.LeafPush2.{CPts, IsUniformization, IsSiegel, IsPeriodMatrix, Char2, thetaConst, pazukiC2}`
  (`ZInQKernel/HDecomp/LeafPush2/R22.lean`), `absLogHeightL2` (TailY), `IsStableFaltingsHeight` (TailY).
- Consumer: `ZInQ.HeightSplit.r22_of_upper` (TailY:812) → `R22_Pazuki` → `r22Concrete_of`/`thetaPazuki` (LPrefix),
  whose Ω comes from `FibreQMPeriodAll` (QM lattice period matrix `Ω(τ)`, an *analytic* polarization).

## Gaps of the field as stated (VERIFIED by reading the statement)
1. `IsUniformization` (LeafPush2) is the weak predicate: surjective analytic homomorphism with kernel Λ;
   no local-coordinate / inverse-continuity clause. Using it as "the uniformization" of the print is a step
   (lead's 11-16 ruling).
2. `IsPeriodMatrix Λ Ω ∧ IsSiegel Ω` is an *analytic* principal polarization of ℂ²/Λ; Pazuki's (A, L) is algebraic.
3. Pazuki Def. 2.6 level-2 coordinates vs classical θ[a;b](0,Ω): UNVERIFIED (unchanged; reading item).

## Build
- 11-16 05:05 copied ~/dzq-wt/pic-dict/.lake/build (+ lean/.lake/build); `lake build TailY TailQ TailZ24`.

## Contrib file (11-16 05:30)
- `ZInQKernel/Contrib/OneProof/PazukiCor13Upper.lean` drafted. Test copy `scratch/pazuki-dict/Test.lean` = same file
  without the TailZ24 import and with `T09Pic.IsAmple B.X.left L ∧` removed from `IsSymmPrincipal` (TailZ24 chain
  not yet rebuilt): compiles, no errors; `#print axioms pazukiCor13Upper_of_printed`, `analyticPPAlgebraic_of_split`:
  [propext, Classical.choice, Quot.sound] (VERIFIED, compiled 05:31).

## Full build and checks (11-16 05:45)
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PazukiCor13Upper`:
  Build completed successfully (13699 jobs), 16m45s; the real file (with `T09Pic.IsAmple`) built in 6.7 s, 0 errors
  (VERIFIED, `build2.out`).
- `#discharges` (`scratch/pazuki-dict/Discharges.lean`, output `discharges-output.txt`, VERIFIED):
  `DISCHARGES [OpenResearchLeaves26.pazukiCor13Upper] by PazukiDict.pazukiCor13Upper_of_printed`,
  still assumes `[BPAnalytic.Uniformization.UniformizationLeafAll, PazukiDict.AnalyticPPAlgebraic,
  PazukiDict.PazukiCor13UpperPP]`, axioms `[propext, Classical.choice, Quot.sound]`;
  `#discharges: 56 open hypotheses, 2885 theorems checked, 8 discharge one`.
- `#synth Module Γ(X, ⊤) Γ(M, ⊤)` = `Scheme.Modules.instModuleCarrier…` (natural instance; Test2.lean).
- autofold dry run (`autofold.json`): without `--allow-rise` refused: "strict count: 34/11 on 45 -> 34/12 on 46;
  strictest 34/11 -> 34/12". With `--allow-rise`, output minus line 1 = `FoldCheck.lean`: compiles,
  `HDec.HSyn.sixContactMin_of_open36` axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
