# derham-print results log

## 2026-11-16 16:00 setup
- Merged origin/main (c1e4ed1b8, fast-forward); origin/wip/integrate-w82 (5e235a40a) already in HEAD.
- lean/.lake/build copied from ~/dzq/lean/.lake/build (lean/ZInQ identical, diff -rq empty).
- claims.tsv: no row for deRhamH1AbVarT (VERIFIED, grep).

## Field (VERIFIED, read)
- `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (ZInQKernel/OneProof/H/TailS.lean:1992): for every p, finite F/Q_p and
  pkg-I4 AbVar A over F, `finrank_{Q_p} (BdR p ⊗ V_p(A)^∨)^{G_F} = [F:Q_p] · finrank V_p(A)^∨`
  (`IsDeRhamTensorOver p (A.galRep p).dual`). Bundle field `OpenResearchLeaves28.deRhamH1AbVarT` (TailZ45).
- kinds.tsv: consequence, GLUE/GLUE; flag: Milne 1986 Thm 15.1(a) step (H^1_et = Hom(V_p A, Q_p)) and, for Scholze
  Cor. 1.8, the rigid comparison.

## Consumers (VERIFIED, grep + read)
- Only reader: TailX.lean:195 `deRhamComparisonHT_of_leavesT r.hodgeTateDecompAbVar l.tateTwistInvariants
  l.axSenTate r.deRhamH1AbVarT` (all other occurrences are bundle-to-bundle copies in TailZ*).
- deRhamComparisonHT_of_leavesT (TailS:2059) converts it by `isDeRhamOver_iff_tensor_dual` to
  `IsDeRhamOver p (A.galRep p)` (I4Layer:1202: finrank Hom_{G_F}(V, B_dR) = [F:Q_p]·dim V), the first conjunct of
  R10 (`DeRhamComparisonHT`). Downstream: `PkgI4.DeRhamComparison` is the argument `hR10` of `G9GlueNoT23`
  (TailA:2017) whose output `G9Out` contains `LocalIsDeRham` (TailA:1948): the de Rham clause is genuinely
  consumed (G9: r_5 de Rham at 5, for Pan's theorem via Berger).
- So the consumers need exactly the dimension of D_dR (no Hodge filtration, no D_dR = H^1_dR identification).

## Overlap check (VERIFIED)
- hodgetate-from-dr (origin/wip/hodgetate-from-dr) consumes hodgeTateDecompAbVar, not this field: no duplication.
- dict-galois (origin/wip/dict-galois 81d1f67f, not folded: leaf-fold32 took only its r7a part) proved the field from
  `DeRhamDict.DeRhamVpAbVarT` (V_p A de Rham, Berger 2004 I.3) + `DeRhamDict.BdRInvariantsOver` + mumfordTorsionAlgClosed.
  Its leaves are read through Berger's B_dR; OPEN.md's kernel-wide B_dR reading says a [1/t] print is a step
  (t not constructed). This task closes that step in Lean (below) and reuses dict-galois's generic algebra.

## 2026-11-16 16:30-17:40 Lean (all VERIFIED: `lake env lean`, no errors)
- scratch/derham-print/Statement.lean: verbatim copy + rfl checks: compiles (1m19s first import load).
- scratch/derham-print/TDict.lean (development, uses local notation): compiles. Contents:
  mkSeq/untilt_mkSeq; dvd_of_norm_le (tilt divisibility by |untilt|); RootSystem; norm_p_le
  (|p| <= |1 - zeta_{p^2}|^{p(p-1)} via cyclotomic_eq_prod_X_sub_primitiveRoots + eval_one_cyclotomic_prime_pow);
  pFlat_dvd; ker_theta_eq_omega (ker theta = (omega) via ker_eq_span_of_mod_p); xe = [eps]-1 in (xi)\(xi^2);
  logPlus (xi-adic limit, IsPrecomplete.prec), logPlus_unique; tt = log[eps]; tt_eq_varpi_mul_unit;
  bdREquivAwayT : BdR ≃ₐ[B_dR^+] Localization.Away t; ext_of_extends, transport_extends; rootSystem (existence).
- Instantiating transport_extends at pkg-I4's bdrAct fails: DR.genMonoid is a def (I4Layer:387), KerTheta's
  genMonoid an abbrev -> Algebra instance on BdR not found across the two copies. Generic lemma kept.
- ZInQKernel/Contrib/OneProof/DeRhamPrintTDict.lean = TDict with notation written out (no `notation`): compiles,
  `lake build ZInQKernel.Contrib.OneProof.DeRhamPrintTDict` OK.
- ZInQKernel/Contrib/OneProof/DeRhamPrint.lean: leaves DeRhamVpAbVarPrinted, BdRInvariantsPrinted; Gen section
  copied from dict-galois (81d1f67f, lines 57-275, unchanged); finiteness lemmas from dict-galois's
  HodgeTateDecompAbVar.lean (needed `open ... MonObj in` for AddCommMonoid (A.T p)); deRhamH1AbVarT_of_leaves,
  isDeRhamOver_of_leaves: compiles.

## 2026-11-16 18:00 checks (VERIFIED)
- lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.DeRhamPrint:
  14103 jobs, success.
- #discharges (Discharges-output.txt): DISCHARGES [OpenResearchLeaves28.deRhamH1AbVarT] by
  DeRhamPrint.deRhamH1AbVarT_of_leaves, still assumes [DeRhamVpAbVarPrinted, BdRInvariantsPrinted,
  AvSplit.MumfordTorsionAlgClosed], standard axioms.
- Axioms-output.txt: all main constants standard axioms.
- autofold --dry-run: strict 16/21 on 37 -> 18/20 on 38 (GLUE -1, both columns); FoldDryRun.lean compiles,
  sixContactMin_of_open39 standard axioms.
