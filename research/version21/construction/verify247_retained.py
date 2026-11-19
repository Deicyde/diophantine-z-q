"""Require literal equality for the retained 247-coordinate transformations."""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import json
import sys
sys.set_int_max_str_digits(0)

ROOT=Path(__file__).resolve().parents[2]
PACKAGE=ROOT/'version20/construction/inputs/carbon'
def load(p):return json.loads((PACKAGE/p).read_bytes())
def poly(row):
 out={}
 for t in row['terms']:
  key=t.get('parameterPower',0),tuple(t['monomial'])
  assert key not in out
  out[key]=F(t['coefficient'])
 return {k:v for k,v in out.items() if v}

def main():
 certificate=load('certificates/v20-normalization244-certificate.json')
 normalized=load(certificate['normalized244_target'])['residuals']
 explicit=load('tables/explicit247/explicit247-quadratic.json')['residuals']
 perm={int(k):int(v) for k,v in certificate['permutation_247']['old_to_new'].items()}
 assert len(normalized)==216 and len(explicit)==219
 assert set(perm)==set(perm.values())==set(range(1,248))
 for i,row in enumerate(normalized):
  expected=defaultdict(F)
  for (e,m),c in poly(row).items():
   assert e in [0,1] and (not e or i==60)
   expected[0,tuple(sorted(perm[j] for j in m+(247,)*e))]+=c
  expected={k:v for k,v in expected.items() if v}
  assert expected==poly(explicit[i]),('literal row differs',i+1)
 for i,expected in enumerate([
  {(0,()):F(149**5110),(0,(245,)):F(-1)},
  {(0,(245,245)):F(1),(0,(246,)):F(-1)},
  {(0,(246,246)):F(149),(0,(247,)):F(-1)}],216):
  assert expected==poly(explicit[i]),('literal ladder differs',i+1)
 # The previous ratio-based test would accept this multiplication; equality must not.
 actual=poly(explicit[0]);doubled={k:2*v for k,v in actual.items()}
 assert doubled!=actual
 return {'literal_row_equalities':219,'all_row_ratios_exactly_one':True,
         'scope':'Strengthened check of retained data; released Version20 files are untouched.'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
