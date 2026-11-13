# integ/99d_proofs.lean = this task's proofs (parts/10 NLG block, parts/20 without the copied
# `GoodRedTorsion` definition, parts/40, parts/50), to be compiled after linked-tate's parts,
# which already contain every other copied definition under the same names.
import os
d = os.path.dirname(os.path.abspath(__file__)) + '/..'
p10 = open(d + '/parts/10_copies.lean').read()
a = p10.index('namespace LTGoodRed.NLG'); b = p10.index('end LTGoodRed.NLG') + len('end LTGoodRed.NLG')
nlg = ('/-! ## lt-goodred (integration copy): neron-lg\'s DVR classification (from parts/10_copies.lean) -/\n\n'
       'section LTGoodRedNLGSec\n\nnoncomputable section\n\n' + p10[a:b] + '\n\nend\n\nend LTGoodRedNLGSec\n')
p20 = open(d + '/parts/20_goodred.lean').read()
a = p20.index('namespace HSyn.LinkedTate'); b = p20.index('end HSyn.LinkedTate') + len('end HSyn.LinkedTate')
p20 = p20[:a] + '-- (`HSyn.LinkedTate.GoodRedTorsion` is linked-tate\'s own definition here)' + p20[b:]
p40 = open(d + '/parts/40_qmrank.lean').read()
p50 = open(d + '/parts/50_split.lean').read()
open(d + '/integ/99d_proofs.lean', 'w').write(nlg + '\n' + p20 + '\n' + p40 + '\n' + p50)
