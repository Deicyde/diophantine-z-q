"""assemble-port: parts/e16_heckerest.lean = hecke-rest's new parts (scratch/hecke-rest/assemble.py, HeckeRestAll.lean below
its copies): FibreSizesMain, NoVertMain, CurveChartMain, InfFnMain, PointsMain, ProperMain, AllMain (.lean.part), verbatim
minus `#print` lines, in that order (as in HeckeRestAll.lean). Its copies are not repeated: TSHecke.lean (parts e10, e14,
a57, b20) and image-plane's AlgDepProof.lean L15-171, 277-322 (in part b20). Then mk/open_zinq.py and an `end` per unclosed
`noncomputable section`. Run from scratch/assemble-port."""
import re, subprocess, sys
H = '../hecke-rest/'
names = ['FibreSizesMain', 'NoVertMain', 'CurveChartMain', 'InfFnMain', 'PointsMain', 'ProperMain', 'AllMain']
txt = '/-! ## assemble-port: hecke-rest, its new parts (mk/mk_heckerest.py) -/\n\n' + '\n'.join(
    '\n'.join(l for l in open(H + n + '.lean.part').read().split('\n') if not l.startswith('#print')) for n in names)
k = len(re.findall(r'^noncomputable section\s*$', txt, re.M)) - len(re.findall(r'^end\s*$', txt, re.M))
txt += '\n' + '\nend  -- assemble-port: closes an unclosed `noncomputable section`\n' * max(0, k)
open('parts/e16_heckerest.lean', 'w').write(txt)
subprocess.run([sys.executable, '-I', 'mk/open_zinq.py', 'parts/e16_heckerest.lean'], check=True)
print('ok', k)
