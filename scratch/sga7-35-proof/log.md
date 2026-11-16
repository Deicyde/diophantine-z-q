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
