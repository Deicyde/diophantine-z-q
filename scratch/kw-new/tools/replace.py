"""replace.py MODULE REASON : write the whole nov01 version of shared module MODULE (TauCeti.X) to
ZInQKernel/Contrib/TauCeti/Backport/X.lean as a replacement of the oct16 version (same names)."""
import sys,os,re
m=sys.argv[1]; reason=sys.argv[2]
src=open(os.path.expanduser('~/tc-nov01/')+m.replace('.','/')+'.lean').read()
src=re.sub(r'^(\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)TauCeti\.',r'\1ZInQKernel.Contrib.TauCeti.',src,flags=re.M)
note=(f'-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module\n'
 f'-- {m}), Apache-2.0. This is the whole nov01 module: {reason}\n'
 f'-- It REPLACES the oct16 version `ZInQKernel.Contrib.{m}` (same declaration names) and must not be\n'
 f'-- imported together with it; no vendored oct16 module of the Kronecker-Weber closure imports that version.\n')
i=src.find('-/\n'); src=src[:i+3]+note+src[i+3:]
d='ZInQKernel/Contrib/TauCeti/Backport/'+'/'.join(m.split('.')[1:])+'.lean'
os.makedirs(os.path.dirname(d),exist_ok=True); open(d,'w').write(src); print('wrote',d)
