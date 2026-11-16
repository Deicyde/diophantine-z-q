"""Finite checks for the standalone 198 record selector; never evaluates U or BB."""
import ast
import hashlib
import json
from pathlib import Path
from fractions import Fraction
import record_machine198 as m

base=Path(__file__).parent
source=base/'record_machine198.py'
data=source.read_bytes()
tree=ast.parse(data.decode('utf-8-sig'))
functions={n.name:n for n in tree.body if isinstance(n,ast.FunctionDef)}
calls={}
for name,fn in functions.items():
    calls[name]=set()
    for node in ast.walk(fn):
        if isinstance(node,ast.Call):
            assert isinstance(node.func,ast.Name)
            assert node.func.id in functions
            calls[name].add(node.func.id)
def depth(name,seen=()):
    assert name not in seen
    return 1+max([depth(c,seen+(name,)) for c in calls[name]] or [0])
nodes=sum(1 for _ in ast.walk(tree))
call_depth=max(map(depth,functions))
literals=[abs(n.value) for n in ast.walk(tree) if isinstance(n,ast.Constant) and isinstance(n.value,int)]
assert nodes<2**12 and call_depth<=12 and max(literals)<=1000
P=((57,-28,8),(-660,417,32))
assert m.multiple(2)==P
D=(11,-6,1)
for q in range(1,129):
    point=m.point_encoded(q)
    assert point is not None
    x,y=point
    assert m.field_mul(y,y)==m.field_sub(m.field_mul(m.field_mul(x,x),x),m.field_mul(D,x))
    doubled=m.point_add(point,point)
    assert doubled==m.multiple(2*(q//4))
assert [m.trace_height_bits(q,q,q,q) for q in (1,2,3,4,8)]==[3,4,1,4,7]
assert m.threshold_after_record(0,2)==2**32*3
# Verify coarse finite constants used by the proof without evaluating U.
assert 256<2**9
assert 21+17*76176==1295013
assert Fraction(7557,32)+Fraction(7,3)*1295013+1<4000000
assert 20+606+188<900<1000
# The independent constant coefficient bound implies crossover by N=53.
K0=31581660**28
H0=(5898050446009651968*K0)**2
assert H0<149**214
result={
 'status':'PASS_FINITE_CHECKS_ONLY',
 'record_program_sha256':hashlib.sha256(data).hexdigest(),
 'ast_nodes':nodes,'functions':len(functions),'call_depth':call_depth,
 'maximum_integer_literal':max(literals),'finite_point_cases':128,
 'trace_examples':{'all_(0,0)':7,'all_(d,0)':13,'all_(-d,0)':1,'all_R0':9,'all_P':'85/4'},
 'constant_coefficient_H0_digits':len(str(H0)),
 'H0_lt_149_pow_214':True,
 'claimed_machine_state_bound':'<2^900, by the inherited explicit counter compiler and the proof in TRANSFER198.md',
 'limits':['Does not execute the production record search, U, or BB.', 'Does not prove retained arithmetic premises.', 'Does not replace the mathematical no-translate, height, and compilation arguments.']
}
(base/'FINITE-CHECKS.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))

