# sga7-35-proof results log

Base: origin/main 0caafe66 (worktree ~/dzq-wt/sga7-35-proof, branch wip/sga7-35-proof).
Target field: `sga7_IX_3_5_ForwardGeom : UnipotentForward.SGA7_IX_3_5_ForwardGeom`
(statement: ZInQKernel/Contrib/OneProof/UnipotentForward.lean; bundle field of OpenResearchLeaves26, TailZ41;
kinds.tsv row 25: research / published / LEAF / LEAF, unverified-locator).

## 2026-11-16

- Environment: `lean/.lake/build` missing in the worktree ("unknown module prefix 'ZInQ'"); reflink-copied from
  ~/dzq-wt/weil-proof (identical lean/ZInQ). VERIFIED (scratch test compiles, 26 s).
- Statement definitions checked (VERIFIED, read): `HasSemistableReduction` (TailZ7 L205) = Néron model whose
  geometric special fibre has `HasSemiAbelianIdentityComponent` (TailY L76: open connected subgroup U, flat
  surjective hom onto an abelian variety with kernel 𝔾_m^r in the functor of points). `IsNeronModel` = Néron
  mapping property. `galTΩ` = `Tate.map (galAct σ)`. Genuine objects; no vacuity found.
- Consumers (VERIFIED, read): ForwardGeom → `UnipotentForward.semistableUnipotent_of_forwardGeom` (TailZ33) →
  `semistableUnipotent` → `GapNeron.raynaudCriterion_leavesNF` (TailZ26) → r6 at number fields
  (`RaynaudCriterionNF`) → TailH `raynaudPlace_rational`, `raynaudPlace_of_R6` (dim A = 2, σ wild),
  `tateWildK_of_R6`, `localGlue_*`; TailF `qmModelG3_of`; TailI `linkedTateLocal_of_leaves3`.
- Available fields that could feed the proof: raynaudSemistableSH (converse direction: rational A[m] ⇒
  semistable), sga7_IX_3_3_SH (N⁰ base change), neronBaseChangeStrictHenselization, r7a (NOS), mulEtale
  (proved), and in OpenAddedLeaves17: picRepresentableAbVar, picZeroAbVar, weilPairingMumford (dual abelian
  variety Pic⁰ and Mumford's ē_n, perfect and Galois-equivariant).
- Analysis (STANDARD content, SGA 7 IX §§2-3; numbers UNVERIFIED): the forward direction needs Grothendieck's
  orthogonality theorem (T_t = kernel of the Weil pairing on T_f × T'_f) plus rank counts; raynaudSemistableSH
  is the converse direction; sga7_IX_3_3_SH + Néron fields give only T^{I'} = T^I for open I' ⊆ I, which does not
  force unipotence over a strictly henselian base (no Frobenius). Verdict: not provable outright from the fields.
- Orth.lean (scratch) COMPILES, axioms [propext, Classical.choice, Quot.sound] (VERIFIED):
  `SGA7Orth.sga7_IX_3_5_ForwardGeom_of_orth (hOrth : GrothendieckOrthogonalitySS) (h1 : PicRepresentableAbVar)
  (h2 : PicZeroAbVar) (h4 : WeilPairingMumford) : UnipotentForward.SGA7_IX_3_5_ForwardGeom`.
  Glue proved: `exists_isPrimitiveRoot_O` (Hensel lift of a primitive N-th root, N unit in SH O),
  `gal_fixes_rootsOfUnity` (μ_N(K̄) ⊆ K), `galMu_eq_self`, `unipSq_tors` ((σ-1)² = 0 on A(K̄)[ℓⁿ]), K^s → K̄
  transport by `IsAlgClosed.lift` + `AlgEquiv.liftNormal` + `extPt_injective`/`extPt_galAct`.
- New leaf `GrothendieckOrthogonalitySS`: rated consequence (GLUE) — finite-level, Mumford-pairing form of
  SGA 7 IX 2.4 + semistable rank count. kinds.tsv: consequence rows count GLUE/GLUE (VERIFIED, 8 rows), so the fold
  would move 1 LEAF → 1 GLUE; NOT recommended.
- Consumers' narrowing (VERIFIED, read): A6 `goodReduction_of_QM_rational3` uses r6 at ℓ = m = 3 on QM surfaces;
  TailH uses wild σ on abelian surfaces. Both need unipotence in general; no narrowing avoids orthogonality.
- Build: first `lake build +Main +Discharges +Contrib` started a cascade rebuild (my lean/.lake/build copy from
  weil-proof was in flux); stopped; copied .lake/build and lean/.lake/build from raynaud-proof (same Main.lean).
