"""assemble-port: parts/e13_kummercomp.lean = kummer-comp's appendix: scratch/kummer-comp/KummerComp.lean after its prefix, which
is scratch/ts-kummer/KummerTS.lean byte for byte (checked here), minus `#print` lines; preceded by the file-level opens of
PropTSGlue.lean L26-27 (active there) and followed by an `end` per unclosed `noncomputable section`; then open_zinq.
Proves `KummerComp.kummerCompositum_final : PropTSGlue.KummerCompositum`. Run from scratch/assemble-port."""
import re, subprocess, sys
kt = open('../ts-kummer/KummerTS.lean').read(); kc = open('../kummer-comp/KummerComp.lean').read()
assert kc.startswith(kt)
P = open('../prop-ts-glue/PropTSGlue.lean').read().split('\n')
body = '\n'.join(l for l in kc[len(kt):].split('\n') if not l.startswith('#print'))
k = len(re.findall(r'^noncomputable section\s*$', body, re.M)) - len(re.findall(r'^end\s*$', body, re.M))
txt = ('/-! ## assemble-port: kummer-comp (`KummerCompositum` proved): KummerComp.lean after its KummerTS.lean prefix (mk/mk_e13.py) -/\n\n'
       + P[25] + '\n' + P[26] + '\n\n' + body + '\n' + '\nend  -- assemble-port: closes the appendix\'s `noncomputable section`\n' * max(0, k))
open('parts/e13_kummercomp.lean', 'w').write(txt)
subprocess.run([sys.executable, '-I', 'mk/open_zinq.py', 'parts/e13_kummercomp.lean'], check=True)
print('ok', k)
