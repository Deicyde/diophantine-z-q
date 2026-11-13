"""leaf-fold: build scratch/h-decomposition/Leaves.lean from the base file (89a5e60e).

python3 scratch/leaf-fold/assemble.py [OUT]
 1. wrap.py (namespace HDec, imports, _root_ renames);
 2. insert parts/t2.lean and parts/tail.lean before the `#print axioms` block;
 3. append the new `#print axioms` lines before `end HDec`.
"""
import subprocess, sys, os
D = os.path.dirname(os.path.abspath(__file__))
out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(D, '..', 'h-decomposition', 'Leaves.lean')
base = os.path.join(D, 'Leaves.base.lean')
wr = os.path.join(D, 'Wrapped.lean')
subprocess.run(['python3', os.path.join(D, 'wrap.py'), base, wr], check=True)
txt = open(wr).read()
mark = '#print axioms HSyn.weight_match\n'
i = txt.index(mark)
ins = open(os.path.join(D, 'parts', 't2.lean')).read() + '\n' + open(os.path.join(D, 'parts', 'tail.lean')).read() + '\n'
txt = txt[:i] + ins + txt[i:]
NEW = """-- leaf-fold: the closed leaves, the repairs and the open bundles
#print axioms HDec.TBrauerPurity.abhyankarDVR
#print axioms HSyn.t2_proved
#print axioms HSyn.t15_proved
#print axioms HSyn.t16a_proved
#print axioms HSyn.t17_proved
#print axioms HSyn.kroneckerWeber_proved
#print axioms HSyn.t18_proved
#print axioms HSyn.frobeniusDense_proved
#print axioms HSyn.t20_proved
#print axioms HSyn.t21_proved
#print axioms HSyn.t25_proved
#print axioms HSyn.t30_proved
#print axioms HSyn.t30_proved'
#print axioms HSyn.t31_proved
#print axioms HSyn.t14_of_kummerIndexBound
#print axioms HSyn.eigenformRepExists_of_r14Det
#print axioms PkgI4.deRhamComparisonHT_iff
#print axioms HSyn.researchLeaves_of_open
#print axioms HSyn.textbookLeaves_of_open
#print axioms HSyn.sixContactMin_of_open
"""
end = '\nend HDec\n'
assert txt.endswith(end)
txt = txt[:-len(end)] + '\n' + NEW + end
open(out, 'w').write(txt)
print('wrote', out, txt.count('\n'), 'lines')
