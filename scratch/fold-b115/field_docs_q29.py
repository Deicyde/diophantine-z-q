#!/usr/bin/env python3
"""fold-b115 fold 3: the panPrintedF / bergerSurveyF field docstrings ("basis form" -> Fontaine's dimension form over
the image in B_dR of Brinon-Conrad's B_st; the integrator's replacement texts) in the current bundle copy and in the
copy the fold before it generated (TailZ83, TailZ84); with --allcontrib also HTModel.lean appended to AllContrib
(fails to import on a head without wip/contrib-clashes: the Different clash). Docstring-only for the
H modules. Idempotent. Run from the repository root; pass other TailZ files as arguments if the bundle moved."""
import sys
ALLC = '--allcontrib' in sys.argv
FILES = [a for a in sys.argv[1:] if a != '--allcontrib'] or ['ZInQKernel/OneProof/H/TailZ83.lean', 'ZInQKernel/OneProof/H/TailZ84.lean']
PAN_OLD = ("printed form with \"potentially semi-stable in the sense of Fontaine\" over Fontaine's B_st = B_cris[log p~] inside B_dR "
           "(Berger, arXiv:math/0210184v1, II.3.1 and II.3.3), basis form, on a model V = E^n")
PAN_NEW = ("printed form with 'potentially semi-stable in the sense of Fontaine' in Fontaine's dimension form (Brinon-Conrad §5.2 pp. 67-68, "
           "Thm 9.3.5 p. 148) over the image in B_dR of Brinon-Conrad's B_st (Def. 9.2.3 p. 138, abstract; embedded pp. 140-142 with "
           "log p = 0; injective by Thm 9.2.10 p. 143, not proved in Lean), A_cris p. 128 with its image in B_dR^+ p. 129, on a model "
           "V = E^n (model-independent: PstModel.localIsPstF_iff_forall)")
BER_OLD = ("in the printed form of Berger, An introduction to the theory of p-adic representations (arXiv:math/0210184v1, IV.5.1 p. 30, "
           "IV.5.3 p. 31): a de Rham p-adic representation V = E^n of G_Qp is potentially semistable over Fontaine's B_st = "
           "B_cris[log p~] (II.3.1, II.3.3), basis form (I.2.3).")
BER_NEW = ("in the printed form of Brinon-Conrad Thm 9.3.5 p. 148 ('only if' half): potentially semistable over the image in B_dR of "
           "Brinon-Conrad's B_st (as above), dimension form (Brinon-Conrad §5.2 pp. 67-68), for a de Rham p-adic representation V = E^n "
           "of G_Qp.")
for f in FILES:
    s = open(f).read()
    for a, b in [(PAN_OLD, PAN_NEW), (BER_OLD, BER_NEW)]:
        if a in s:
            s = s.replace(a, b)
        elif b not in s:
            sys.exit(f'field_docs_q29: {f}: neither old nor new text found')
    open(f, 'w').write(s)
if not ALLC:
    print('ok'); sys.exit(0)
A = 'ZInQKernel/Contrib/AllContrib.lean'
imp = 'import ZInQKernel.Contrib.OneProof.HTModel\n'
s = open(A).read()
if imp not in s:
    open(A, 'w').write(s if s.endswith('\n') else s + '\n')
    open(A, 'a').write(imp)
print('ok')
