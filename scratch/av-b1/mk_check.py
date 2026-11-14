#!/usr/bin/env python3
"""av-b1: build the single-file check scratch/av-b1/AVB1Check.lean (not committed; ~110k lines).
= leaf-fold3's flat file scratch/leaf-fold3/Leaves3.lean (unchanged)
+ ZInQKernel/Contrib/AVB1/{BaseChange,AlgClosed,Poincare}.lean, minus imports and `#print` lines,
  with `_root_.PkgI3` -> `_root_.HDec.PkgI3` (the same edit as leaf-fold3's mk_abvarbc.py; the kernel's
  HDecomp/Objects.lean and Leaves3's HDec.PkgI3 carry identical text, scratch/av-b1/verbatim_check.py),
  each in its own section inside `namespace HDec` (so `ZInQ.Contrib.AbVarBC` is Leaves3's copy)
+ scratch/av-b1/check_tail.lean: the theorems giving leaf-fold3's fields t6, t7, t8 (HDec.PkgI3.*)
  and `#print axioms`.
Run from the repository root."""
out = [open('scratch/leaf-fold3/Leaves3.lean').read().rstrip('\n'), '',
       '/-! ## av-b1: ZInQKernel/Contrib/AVB1/*.lean, copied; see scratch/av-b1/mk_check.py -/', '',
       'namespace HDec', '']
for f in ['BaseChange', 'AlgClosed', 'Poincare']:
    s = open('ZInQKernel/Contrib/AVB1/%s.lean' % f).read()
    s = s.replace('_root_.PkgI3', '_root_.HDec.PkgI3')
    s = '\n'.join(l for l in s.split('\n') if not l.startswith('import ') and not l.startswith('#print'))
    out += ['-- ===== ZInQKernel/Contrib/AVB1/%s.lean' % f, 'section AVB1_%s' % f, s, 'end AVB1_%s' % f, '']
out += ['end HDec', '', open('scratch/av-b1/check_tail.lean').read()]
open('scratch/av-b1/AVB1Check.lean', 'w').write('\n'.join(out))
