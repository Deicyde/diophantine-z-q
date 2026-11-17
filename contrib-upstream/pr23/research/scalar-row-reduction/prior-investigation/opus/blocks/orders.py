import json,sys
from measure import measure
BASE=open('base_builder.cjs').read()
def variant(orders,beta,groups):
    s=BASE.replace('i===0?45:i===1?12:1',json.dumps(orders)+'[i]')
    s=s.replace('value:fsub(L[1],[beta,zero]),order:45','value:fsub(L[1],[beta,zero]),order:'+str(beta))
    start=s.index('const mixedTest1=squareTests[12][0]'); end=s.index("start('fixed_height_scales'",start)
    s=s[:start]+'''let coeffs={};for(let m of [1,12,45]){let sqtests=squareTests[m],sizes=GROUPS[m],pos=0;coeffs[m]=sizes.map((n,b)=>{let co=polyProduct('symmetric.'+m+'.group'+b,sqtests.slice(pos,pos+n));pos+=n;return co;});if(pos!==sqtests.length)throw Error('partition');}
'''.replace('GROUPS',json.dumps(dict(zip([1,12,45],groups))))+s[end:]
    start=s.index(' let mixedRaw=fadd('); end=s.index(' let pure=fmul(',start)
    s=s[:start]+" let mixed=evalSym('detector'+r+'.E12',coeffs[12],q12);\n"+s[end:]
    return s
cases={
 'probe_baseline':([45,12,1,1,1],45,[[4,4],[2],[3,3]]),
 'input_to_12':([45,12,1,1,1],12,[[4,4],[3],[3,2]]),
 'input_to_12_b':([45,12,1,1,1],12,[[4,4],[3],[5]]),
 'H_to_12':([12,12,1,1,1],45,[[4,4],[3],[3,2]]),
 'o45_6':([45,12,1,1,1],45,[[4,4],[2],[6]]),
 'o1_8':([45,12,1,1,1],45,[[8],[2],[3,3]]),
 'o1_53':([45,12,1,1,1],45,[[5,3],[2],[3,3]]),
}
if __name__=="__main__":
  for k in sys.argv[1:] or cases:
      print(k, measure(k, variant(*cases[k])), flush=True)
