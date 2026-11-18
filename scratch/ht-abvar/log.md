# ht-abvar results log

## 2026-11-17 setup
- Base: bfcab3800 (derham-scholze); merged origin/main (d973b8e8d) and origin/wip/c8-conrad2 (6d7cee6e2) for the
  C8/Poincare dry-run inputs. Build tree: reflink copy of ~/dzq-wt/cm-branch/.lake/build (+ lean/.lake/build),
  whose Main.lean is byte-identical.

## (1) The field and its Picard route (VERIFIED by reading the tree)
- Field: `hodgeTateDecompAbVar : ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` (TailS.lean L347): for every
  finite F/Q_p, A : PkgI4.I3.AbVar F, g with A.dim = g: G_F-equivariant C_p (x) V_p(A) ~ C_p(1)^g x C_p^g.
- Filled at TailZ74 L381 (`openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf`):
  `hodgeTateDecompAbVar_of_open_k954 n.hodgeTateDecompExists t.mumfordTorsionAlgClosed l.picRepresentableAbVar
  l.kleimanPicZeroProper954` (TailZ69 L55): (a,b) from HodgeTateDecompExists, a=b from the Weil pairing of a
  symmetric isogeny A -> A^vee (t09SymmIsogenyExists0_of_open_k954, the Picard rows), a+b=2g.
- `n.hodgeTateDecompExists` comes from the open field `hodgeTateDecompOr` (TailZ79:
  `hodgeTateDecompExists_of_or n.hodgeTateDecompOr`); its only reader is the line above.

## (2) Do ScholzeDeRhamAlg + T10_TateDuality supply the field? (VERIFIED by reading the statements)
- No. ScholzeDeRhamAlg gives de Rham + `HodgeRange … i` (Fil^0 = D_dR, Fil^{i+1} = 0) only; T10 is an iso
  H^1 ~ T_p^vee. Neither contains a dimension of a graded piece, so the multiplicities (a, b), a + b = 2g, are not
  determined (derham-scholze's `hodgeTateDecompOr` is exactly what they give: some (a, b)).
- Smallest reroute: one leaf `DeRhamScholze.HTAbVar.HodgeNumberH1AbVar`:
  dim_{Q_p} Fil^1 D_dR(H^1_et(A_Fbar, Q_p)) = [F:Q_p] g  (manuscript L10996 Hodge numbers via Scholze's filtered
  comparison). Kind consequence (H_dR not in Mathlib). ELLIOT (L10996 uncited) + CITED (Scholze Cor. 1.8).

## Lean (VERIFIED, compiled 11-17, standard axioms)
- `ZInQKernel/Contrib/OneProof/HTAbVarScholzeDims.lean` (imports DeRhamScholzeHT): leaf def; `finrank_fil1_bounds`
  (dim(D cap Fil^1) <= dim Hom_G(V,C_p(1)); dim D <= dim Hom_G(V,C_p) + dim(D cap Fil^1)); `hom_decomp_of_basis`;
  `hodgeTate01_dims` (Hom-form decomposition with a + h = dim V, b = h).
- `ZInQKernel/Contrib/OneProof/HTAbVarScholze.lean` (imports Dims, DeRhamScholzeT): `finrank_filD_dual` (Fil^1 along
  milneE), `hodgeTateDecompAbVar_of_scholze : ScholzeDeRhamAlg → T10_TateDuality → HodgeNumberH1AbVar →
  HodgeTateDecompAbVar`.
- Pitfall: in DeRhamScholzeT's environment `StrongRankCondition ℚ_[p]` synthesis times out (isDefEq), and
  `rw [Module.finrank_eq_rank]` with a let-bound submodule ran >10 min; fix = split file, lemma in a clean context.
- `lake build ZInQKernel.Contrib.OneProof.HTAbVarScholze`: ok. `scratch/ht-abvar/Axioms.lean`: verbatim copy of the
  field `Iff.rfl` with TailS's; axioms [propext, Classical.choice, Quot.sound] (axioms-output.txt).
- `#discharges` (Discharges.lean, discharges_out.txt): 34 open, 16518 checked, 25 discharge one; none by HTAbVar
  (expected: hodgeTateDecompAbVar is not an open field).

## Dry run (VERIFIED, compiled)
- `scratch/ht-abvar/HTDryRun.lean` = c8-conrad2's generated copy (C8DryRun.lean up to its top) + gen/top_a, r35,
  top_b. Tops `HDec.HSyn.sixContactMin_of_open72_ht`, `sixContactMin_of_open73HT (r : OpenResearchLeaves53)
  (t : OpenTextbookLeaves19HT) (l : OpenAddedLeaves28HT)`, `ZInQ.OneProof.frozenTarget_ht`: standard axioms
  (dryrun_out.txt). No hypothesis carries a Picard row (OpenAddedLeaves27 not taken; OpenResearchLeaves53 has none).
- Field taint from frozenTarget_ht (HTDryRunTaint.lean, dryrun_taint_out.txt, closure 304102): seeds
  picRepresentableAbVar, kleimanPicZeroProper954SiteQ, hodgeTateDecompOr; only edge
  openResearchLeaves36EBCF_of_OpenResearchLeaves53 : hodgeTateDecompExists <- hodgeTateDecompOr; no TERM.
  So hodgeTateDecompOr also leaves the route.
- Count (kinds.tsv H rows): 5/24 on 29 -> 5/30 on 35 (remove 3 GLUE; add 9 GLUE at entry). (iii) share: +2.

## Dry run over c8-conrad3 (VERIFIED, compiled 11-17)
- Merged origin/wip/c8-conrad3 (three C8 glue Props proved; C8 from `C8Leaves` = conradAppBQp +
  tateTwistInvariantsInertia). HTDryRun.lean rebuilt: same generated body (identical to c8-conrad3's
  C8FoldDryRun.lean body, diff empty), `OpenAddedLeaves28HT` = {conradAppBQp, tateTwistInvariantsInertia,
  scholzeDeRhamAlg, t10TateDuality, hodgeNumberH1AbVar}, C8 via `c8Inputs_of_leaves`. Tops: standard axioms.
- Taint rerun (closure 304201): same result, Picard rows unread, hodgeTateDecompOr only into the ignored
  hodgeTateDecompExists.
- Count: 5/24 on 29 -> 5/27 on 32; net GLUE +3 ((iii) share +2); +2 if PR #86's poincareComplement_proof lands.
- Line numbers corrected: Hodge numbers sentence is L10996, "Consequently" L10997, Faltings remark L11003-11006.
