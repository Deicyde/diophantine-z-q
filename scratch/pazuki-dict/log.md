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
