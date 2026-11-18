# c8-conrad results log

Base: wip/c8-conrad at d67ea55f6 (origin/main is an ancestor). Top: `ZInQ.OneProof.frozenTarget` with
`OpenAddedLeaves27 = {picRepresentableAbVar, kleimanPicZeroProper954SiteQ}` (TailZ72).

## 1. Why the appeal to Conrad was replaced (VERIFIED, read in the named files)

- h-trust.md C8 (L637-639, L697-700, L1034-1036): "it replaces N5's appeal to local algebraicity"; the determinant
  argument is "Version 14's argument, kept in Version 16 at V16 L660-667"; adopted by task h-v16-adopt "after up-h §4
  item 1". No defect is recorded.
- up-h.md L307-312 (§4 item 1, "Shortening h-trust.md: marginal"): adopt V14's determinant argument; "This removes
  the conrad-local-characters row ... and the class-field-theory step of C8". A shortening, not a correction.
- rv-h-c8.md §4 (L172-192): N5's chain (HT character -> Tate/Sen local algebraicity -> CFT -> finite order) is
  "VERIFIED as an argument; the cited theorems STANDARD". Only remark: N5 asserts finiteness of psi on inertia at
  l != 5 "without argument ... it is elementary" (item 3). §3.1: de Rham is not needed, Hodge-Tate suffices.
- rv-h-trust.md §1.2 item 1: the missing input is (HT) for eigenforms (needed in both routes), not Conrad.
- h-leaves.md L581, L638, h-v14.md L83, L567, nt-h.md: Conrad's paper is an unrefereed preprint; upstream Version 14
  removed it (citation count 0, v14-routes.md L239-258), with Serre 1968 Ch. III / Tate 1967 §3.3 named as refereed
  replacements.
- Verdict: no defect in the manuscript's use of Conrad App. B is recorded. Recorded caveats: (a) unrefereed
  preprint; (b) the l != 5 inertia finiteness is elementary but unstated in N5.

## 2. Consumers of the two Picard rows at the current top (source reading; VERIFIED by grep)

- TailZ72: `openAddedLeaves26_of_OpenAddedLeaves27` turns `kleimanPicZeroProper954SiteQ` into
  `kleimanPicZeroProper954`.
- TailZ69 `openAddedLeaves22PZ_of_OpenAddedLeaves26`: both rows -> `PicZeroAbVar0`, entering
  `sixContactMin_of_open45_pz_eb` (EichlerBoundCopy L3291), which reads them in
  (i) `openAddedLeaves18_of_OpenAddedLeaves22_pz` -> phiAmpleIsogeny, weilPairingMumford -> t09SymmIsogenyExists ->
      `detTate_of_leaves4_pz` -> `DetTate` (C8, G12Det) in `gluePieces_of_open4_hf_pz_eb` (EichlerBoundCopy L2703);
  (ii) `openTextbookLeaves13HF_of_open16_22_pz` -> `poincareComplement` (T8, Poincare reducibility) ->
      `glueOutputs_of_leaves3_hf_pz_eb` L2602 `t.t8` (step E1-E2, manuscript L865 "Poincare reducibility").
- TailZ74 L381 (current top): `hodgeTateDecompAbVar := hodgeTateDecompAbVar_of_open_k954 ... l.picRepresentableAbVar
  l.kleimanPicZeroProper954` (iii): HT multiplicities a = b from the Weil pairing (hodgetate-from-dr), feeding C3/G9.
- So the Picard rows have three live consumers; C8 is one of them.

## 3. Conrad App. B source

- WebFetch https://math.stanford.edu/~conrad/papers/locchar.pdf: refused ("Unable to verify if domain math.stanford.edu
  is safe to fetch"). No copy in the worktree. Statement taken from the theorem-application audit report
  (docs/theorem-application-audit/evidence/parallel-galois-height-report.md L102, L104): "locally algebraic exactly
  when its underlying Q_p-representation is Hodge-Tate"; arithmetic Artin normalization; L = Q_5 gives x -> x^n.
  Flag: unread.
- Tau Ceti local Artin map available: TauCeti.ClassFieldTheory.artinMap (Local/ArtinMap.lean L115), arithmetic
  normalization chi_cyc(Art(p^k u)) = u^{-1} (ExplicitCyclotomicSymbol/ArtinMap.lean,
  abelianizedLocalCyclotomicCharacter_artinMap_padic). Kronecker-Weber proved (Contrib/KroneckerWeber).

## 4. Consumer of C8 in the chain

- `HDec.G0Galois.G12DetPZ` (PicZeroCharZeroCopy L44), used via `g12Det_of_pz m.r14det m.detTate m.finIndex ...` in
  `g8_g12_of_leaves3_hf_pz_eb` (EichlerBoundCopy L2485). Inputs at that call site: r.r14 EigenformRepExists, r.r13
  PkgI4.EigenformHT, r.r10 PkgI4.DeRhamComparison, h9 G9GlueNoT23.
- G12DetPZ's conclusion is existential in (H, dr, eps, chi): it follows from finiteness of psi alone
  (H = ker psi, dr = psi^2, eps = chi = 1).

## 5. Compile results (VERIFIED)

- lake build ZInQKernel.OneProof.Main: ok (16214 jobs), frozenTarget standard axioms.
- scratch/c8-conrad/C8Conrad.lean: compiles (2 fixes: QuotientGroup.mk for the Artin-lift coercion; coe_range).
  Copied to ZInQKernel/Contrib/OneProof/C8Conrad.lean; lake build ok; axioms standard for c8TwistFinite_of_conrad,
  g12DetPZ_of_twistFinite, g12DetPZ_of_conrad.
- #discharges: 36 open, 15748 checked, 19 discharge one; none from C8Conrad (no field discharged).
- FieldTaint (seeds picRepresentableAbVar, kleimanPicZeroProper954SiteQ): terminals gluePieces_of_open4_hf_pz_eb
  (t09SymmIsogenyExists -> DetTate, C8), glueOutputs_of_leaves3_hf_pz_eb (t8, Poincare), g8_g12/afterG7/gluePieces
  via r10 <- hodgeTateDecompAbVar (R10). Three consumers confirmed.
