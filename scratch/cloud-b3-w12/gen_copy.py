import subprocess
def show(p): return subprocess.run(['git','show','origin/wip/p1-quot3:'+p],capture_output=True,text=True,check=True).stdout
CREDIT = """/-
Copied from task p1-quot3 (branch `wip/p1-quot3`, commit b533b204d640ee45ac924ee030497d427ec9926e), file
`{src}`, by the owner's task p1-quot3 (report docs/research/p1-quot3.md §2 on that branch; p1-quot2.md).
Changes for Cloud Worker 12 (task H-91): module path moved under `ZInQKernel.Contrib.CloudB3W12Tame`, every
declaration namespace renamed ({ren}) so nothing clashes if p1-quot3 is folded later{extra}.
-/

"""
base='ZInQKernel/Contrib/OneProof/QuotientP1/'
# QuotProper
s=show(base+'QuotProper.lean')
s=s.replace('namespace HDec.MCRGlue.QuotProper\n','namespace HDec.CloudB3W12Tame.QuotProper\n\nopen HDec.MCRGlue\n',1)
s=s.replace('end HDec.MCRGlue.QuotProper','end HDec.CloudB3W12Tame.QuotProper')
s=s.replace('namespace HDec.MCRGlue\n','namespace HDec.CloudB3W12Tame\n\nopen HDec.MCRGlue\n',1)
s=s.replace('end HDec.MCRGlue\n','end HDec.CloudB3W12Tame\n')
s=s.replace('`HDec.MCRGlue.QuotProper`','`HDec.CloudB3W12Tame.QuotProper`').replace('`HDec.MCRGlue.TameQuotientSmoothRelDim`','`HDec.CloudB3W12Tame.TameQuotientSmoothRelDim`').replace('`HDec.MCRGlue.tameQuotientSmooth_of_relDim','`HDec.CloudB3W12Tame.tameQuotientSmooth_of_relDim')
assert 'MCRGlue.QuotProper' not in s
open('ZInQKernel/Contrib/CloudB3W12Tame/QuotProper.lean','w').write(CREDIT.format(src=base+'QuotProper.lean',ren='`HDec.MCRGlue.QuotProper` → `HDec.CloudB3W12Tame.QuotProper`, the `HDec.MCRGlue` section → `HDec.CloudB3W12Tame` with `open HDec.MCRGlue`',extra='; no proof changed')+s)
# TameInvariants
s=show(base+'TameInvariants.lean')
s=s.replace('QuotientP1Proof.TameQuot','HDec.CloudB3W12Tame.TameQuot')
open('ZInQKernel/Contrib/CloudB3W12Tame/TameInvariants.lean','w').write(CREDIT.format(src=base+'TameInvariants.lean',ren='`QuotientP1Proof.TameQuot` → `HDec.CloudB3W12Tame.TameQuot`',extra='. The hypothesis `RegularSmoothPerfect` (Stacks 00TV) of `smooth_of_invariants_field` and `smooth_of_invariants` is REMOVED: its one use is replaced by a proof (vendored FLT `Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField` at DVR localizations, Mathlib `Algebra.FormallySmooth.of_perfectField` at field localizations), and the definition `RegularSmoothPerfect` is dropped')+s)
# TameQuotSmooth
s=show(base+'TameQuotSmooth.lean')
s=s.replace('import ZInQKernel.Contrib.OneProof.QuotientP1.TameInvariants','import ZInQKernel.Contrib.CloudB3W12Tame.TameInvariants')
s=s.replace('import ZInQKernel.Contrib.OneProof.QuotientP1.QuotProper','import ZInQKernel.Contrib.CloudB3W12Tame.QuotProper')
s=s.replace('import ZInQKernel.OneProof.H.TailR','import ZInQKernel.OneProof.H.TailW')
s=s.replace('namespace HDec.MCRGlue.TameQuotScheme\n\nopen QuotientP1Proof.TameQuot VertWitness','namespace HDec.CloudB3W12Tame.TameQuotScheme\n\nopen HDec.MCRGlue HDec.CloudB3W12Tame.TameQuot VertWitness')
s=s.replace('QuotientP1Proof.TameQuot','HDec.CloudB3W12Tame.TameQuot')
i=s.index('end HDec.MCRGlue.TameQuotScheme')
s=s[:i]+'end HDec.CloudB3W12Tame.TameQuotScheme\n'
open('ZInQKernel/Contrib/CloudB3W12Tame/TameQuotSmooth.lean','w').write(CREDIT.format(src=base+'TameQuotSmooth.lean',ren='`HDec.MCRGlue.TameQuotScheme` → `HDec.CloudB3W12Tame.TameQuotScheme`',extra='. The hypothesis `hRS : RegularSmoothPerfect` is REMOVED from `smooth_appLE` and the main theorem (renamed `tameQuotientSmoothRelDim_proof`); the trailing `HDec.MCRGlue` wrappers that took `CurveSplit.RegularSmoothPerfect` are dropped; the import of `TailR` is replaced by `TailW`')+s)
print('ok')
