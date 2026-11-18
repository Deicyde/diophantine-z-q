#!/usr/bin/env python3
"""fold-b115 fold 3: the queue29 row edits (inbox 73) with inbox 75's amendment of the panPrintedF flag, in
docs/one-proof/kinds.tsv. Columns kind, flag, strict, strictest, source, rated_by, flag_class; the others unchanged.
panPrintedF's kind becomes consequence in the same edit as its flag (with the pending marker gone, published would
render LEAF). The texts are the integrator's, verbatim (inbox 75's two replacements applied to 73's panPrintedF flag).
Idempotent: rerunning leaves the file unchanged. Run from the repository root."""
import csv, sys

ROWS = {
    'panPrintedF': dict(
        kind='consequence',
        flag="reviewer verdict queue29 (11-17): consequence, GLUE/GLUE: Pan arXiv:1901.07166v2 Conj. 1.0.1 and Thm 1.0.4 checked clause by clause against the v2 LaTeX source (p = 3 proviso only, HT(eps) = -1, geometric Frobenius, iota_p fixed); pst is Brinon-Conrad's dimension form (5.2 pp. 67-68, Thm 9.3.5 p. 148) and the pst model clause is proved (PstModel.localIsPstF_iff_forall); deciding step: Brinon-Conrad define B_st abstractly (Def. 9.2.3 p. 138) and BstFOf is its image in B_dR, so identifying them needs the injectivity of Thm 9.2.10 p. 143, not proved in Lean (BergerBst.LogPTildeTranscendental is an open Prop); co-steps: LocalDistinctHTP on some finite model is equivalent to every model (HTModel.localDistinctHTP_iff_forall); BC define A_cris abstractly (p. 128) and AcrisOf is BC's printed description of its image in B_dR^+ (p. 129, proof omitted); LEAF once both are proved or ruled definitional; earlier: q22 GLUE (model clause, survey ring)",
        strict='GLUE', strictest='GLUE',
        source="Pan, The Fontaine-Mazur conjecture in the residually reducible case, arXiv:1901.07166v2 (the version the manuscript cites), Thm 1.0.4 with Conj. 1.0.1 (published J. Amer. Math. Soc. 35 (2022), 1031-1169); 'potentially semi-stable in the sense of Fontaine' in Brinon-Conrad's dimension form (CMI notes, preliminary version June 24, 2009, 5.2 pp. 67-68, Thm 9.3.5 p. 148) over the image in B_dR of Brinon-Conrad's B_st (Def. 9.2.3 p. 138, abstract; embedded pp. 140-142 with log p = 0; injective by Thm 9.2.10 p. 143), B_cris Def. 9.1.4 p. 131, A_cris p. 128 (abstract) with its image in B_dR^+ p. 129 (p-adic topology), on a model V = E^n (model-independent: PstModel.localIsPstF_iff_forall); LocalIsPstF over BstFOf in Contrib/OneProof/PanBergerFontaine.lean",
        rated_by='pb-p1 (unreviewed); pb-dimform; queue29 verdict 11-17',
        flag_class='note'),
    'bergerSurveyF': dict(
        kind='consequence',
        flag="reviewer verdict queue29 (11-17): consequence, GLUE/GLUE: re-routed (Jack 11-17) to Brinon-Conrad Thm 9.3.5 p. 148, 'only if' half (de Rham implies potentially semistable), stated in BC without proof as a result of Berger and Andre-Kedlaya-Mebkhout; the conclusion is BC's dimension form (5.2 pp. 67-68), so the dimension-to-basis step is gone; de Rham matches BC since B_dR^{G_Qp} = Q_p is proved in Lean (BdRInv.bdRInvariantsPrinted_proof); deciding step: BC define B_st abstractly (Def. 9.2.3 p. 138) and BstFOf is its image in B_dR, so BC's conclusion gives the Lean's only through the injectivity of Thm 9.2.10 p. 143, not proved in Lean (BergerBst.LogPTildeTranscendental is an open Prop); co-step: BC define A_cris abstractly (p. 128) and AcrisOf is BC's printed description of its image (p. 129, proof omitted); LEAF if both are proved or ruled definitional; earlier: q22 GLUE (dimension-to-basis, survey ring)",
        strict='GLUE', strictest='GLUE',
        source="Brinon-Conrad, CMI summer school notes on p-adic Hodge theory, preliminary version June 24, 2009 (bibitem brinon-conrad), Thm 9.3.5 p. 148 ('only if' half), with semistable = B_st-admissible in the dimension form (5.2 pp. 67-68), B_st Def. 9.2.3 p. 138 (abstract) embedded in B_dR pp. 140-142 (log p = 0) and injective by Thm 9.2.10 p. 143, B_cris Def. 9.1.4 p. 131, A_cris p. 128 (abstract) with its image in B_dR^+ p. 129 (p-adic topology), de Rham = B_dR-admissible (5.2; Thm 4.4.13 p. 64); the manuscript cites Berger, Invent. Math. 148 (2002), Theoreme 0.6 (= Theoreme 5.19 of arXiv:math/0102179v3) at tex 739-741; IsPstF (dimension form, BergerBst.IsAdmissible) over BstFOf in Contrib/OneProof/PanBergerFontaine.lean",
        rated_by='pb-p1 (unreviewed); pb-dimform; queue29 verdict 11-17',
        flag_class='note'),
}

P = 'docs/one-proof/kinds.tsv'
lines = open(P).read().split('\n')
cols = lines[0].split('\t')
done = set()
for i, l in enumerate(lines[1:], 1):
    if not l:
        continue
    r = l.split('\t')
    if len(r) > 1 and r[1] in ROWS:
        for c, v in ROWS[r[1]].items():
            r[cols.index(c)] = v
        lines[i] = '\t'.join(r)
        done.add(r[1])
if done != set(ROWS):
    sys.exit(f'row_edits_q29: rows missing: {set(ROWS) - done}')
open(P, 'w').write('\n'.join(lines))
print('edited', sorted(done))
