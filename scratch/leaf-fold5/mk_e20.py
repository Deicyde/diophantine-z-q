#!/usr/bin/env python3
"""leaf-fold5: part parts/e20_avb2.lean = scratch/av-b2/olean/AVB2Main.lean from `namespace AVB2` to `end AVB2`
(verbatim; av-b2 compiled it inside `namespace HDec` over leaf-fold3's chain, which leaf-fold4's chain extends).
Its kernel import ZInQKernel.Contrib.AVB2.SerreLemma is added to TailM's imports (assemble.sh)."""
s = open('../av-b2/olean/AVB2Main.lean').read()
a = s.index('namespace AVB2'); b = s.index('end AVB2') + len('end AVB2')
open('parts/e20_avb2.lean', 'w').write('-- (leaf-fold5) mk_e20.py: scratch/av-b2/olean/AVB2Main.lean, `namespace AVB2` ... `end AVB2`, verbatim\n'
  'noncomputable section\n\n' + s[a:b] + '\n\nend\n')
print('ok')
