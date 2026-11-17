from pathlib import Path
import json, subprocess, sys
ROOT=Path('/tmp/codex-glazer389-review-3j08z564/cube')
BASE=(ROOT/'build/final380/builder.cjs').read_text()
OUT=Path('/tmp/quartic-after13/grouping')
cases=[
 ('baseline',[45,12,1,1,1],45,[[4,4],[2],[3,3]]),
 ('demote_H_and_input',[12,12,1,1,1],12,[[4,4],[4],[4]]),
 ('promote_two_primary',[45,12,45,45,1],45,[[3,3],[2],[4,4]]),
 ('promote_three_primary',[45,12,45,45,45],45,[[2,3],[2],[3,3,3]]),
]
results=[]
for name,orders,beta,groups in cases:
    target=OUT/name
    target.mkdir(parents=True,exist_ok=False)
    s=BASE.replace('i===0?45:i===1?12:1',json.dumps(orders)+'[i]')
    s=s.replace('value:fsub(L[1],[beta,zero]),order:45','value:fsub(L[1],[beta,zero]),order:'+str(beta))
    start=s.index('const mixedTest1=squareTests[12][0]')
    end=s.index("start('fixed_height_scales'",start)
    s=s[:start]+'''let coeffs={};for(let m of [1,12,45]){let sqtests=squareTests[m],sizes=GROUPS[m],pos=0;coeffs[m]=sizes.map((n,b)=>{let co=polyProduct('symmetric.'+m+'.group'+b,sqtests.slice(pos,pos+n));pos+=n;return co;});if(pos!==sqtests.length)throw Error('partition');}
'''.replace('GROUPS',json.dumps(dict(zip([1,12,45],groups))))+s[end:]
    start=s.index(' let mixedRaw=fadd(')
    end=s.index(' let pure=fmul(',start)
    s=s[:start]+" let mixed=evalSym('detector'+r+'.E12',coeffs[12],q12);\n"+s[end:]
    (target/'builder.cjs').write_text(s)
    with (target/'run.log').open('w') as log:
        subprocess.run(['node',str(target/'builder.cjs')],check=True,stdout=log,stderr=subprocess.STDOUT)
        subprocess.run([sys.executable,'-B',str(ROOT/'research/conditional-quartic-reduction/construction/tools/compile_ir.py'),str(target/'raw-translated-ir.json'),str(target/'compiled')],check=True,stdout=log,stderr=subprocess.STDOUT)
    report=json.loads((target/'compiled/compiler-report.json').read_text())
    result={'name':name,'orders':orders,'inputOrder':beta,'partitions':groups,'compiledBeforeFactoredPoles':report['final']}
    results.append(result)
    print(name,report['final']['coordinates'],report['final']['residuals'],flush=True)
(OUT/'RESULTS.json').write_text(json.dumps(results,indent=2)+'\n')
