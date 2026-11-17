"""Bind the current dependency inventory to its proofs and generated artifact census.

This is a consistency/binding audit. It does not establish the proofs referenced
by the inventory or repeat the algebraic SOS/gate certificates.
"""
from pathlib import Path
from fractions import Fraction
from math import gcd
from functools import reduce
import argparse
import hashlib
import json
import re


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--package',type=Path,required=True)
    ap.add_argument('--inventory',type=Path)
    ap.add_argument('--markdown',type=Path)
    ap.add_argument('--report',type=Path,required=True)
    args=ap.parse_args()
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    pkg=args.package.resolve()
    inventory=args.inventory or pkg/'pr_dependency_inventory.json'
    markdown=args.markdown or inventory.parent/'PR_DEPENDENCIES.md'
    data=json.loads(inventory.read_text())
    s=data['selected'];checks=[]
    def check(label,value):
        assert value,label
        checks.append(label)
    check('selected census',(s['totalVariablesIncludingInput'],s['quadraticResiduals'],s['monomials'])==(389,357,26295))
    check('selected anchor and depth',(s['anchor'],s['anchorForcedThreeExponent'],s['balancedBase'])==('3^2364',1181,'3^394'))
    check('selected height exponent',Fraction(s['heightExponent'])==Fraction(577,32))
    check('selected height expression',s['heightConstant']=='3*2^106*(2^32*3^9)^6*46410^18+128')
    check('selected full order list',s['testOrders']==[45,12,1,1,1,1,1,1,1,1,12,45,45,45,45,45])
    check('unchanged scalar and exceptional set',s['scalarOrder']==28 and s['exceptionalSet']==[2,3,5,7,13,17])
    check('selected scalar target',s['scalarHeightTarget']=='h(beta)<|a-1|/4<=(|a|+1)/4')
    check('selected builder binding',s['builderSha256']==digest(pkg/s['builder']))
    ids=[e['id'] for e in data['transformations']]
    check('complete stable transformation identifiers',ids==['T'+str(i).zfill(2) for i in range(1,33)])
    catalog=data['proofCatalog']
    check('selected new proof catalog',all(k in catalog for k in ['P8_detector','P8_arithmetic','P8_diagonal']))
    for pid,proof in catalog.items():
        check('proof bytes '+pid,digest(pkg/proof['path'])==proof['sha256'])
    current={e['id']:e for e in data['transformations']}
    check('uniform pair current','(12,12)' in current['T08']['retainedStatement'])
    check('new primary order current','g(U_A) at order 12' in current['T07']['retainedStatement'])
    check('new anchor current','3^2364' in current['T21']['retainedStatement'] and '3^1181' in current['T21']['retainedStatement'])
    check('new scalar margin current','h(beta)<c/4' in current['T27']['retainedStatement'])
    check('new coefficient maximum current','28902*3^1576' in current['T31']['selectionNote'])
    check('Euler-genus argument explicit','577/192' in current['T32']['retainedStatement'] and 'T/6' in current['T32']['retainedStatement'])
    check('prior arithmetic classified',catalog['P7_arithmetic']['roleInSelectedConstruction'].startswith('Prior '))
    check('prior diagonal classified',catalog['P7_diagonal']['roleInSelectedConstruction'].startswith('Prior '))
    check('optional research classified',catalog['P7_optional']['roleInSelectedConstruction'].startswith('Optional '))
    b=pkg/'construction'
    raw=json.loads((b/'raw-ir.json').read_text())
    check('actual raw census',(len(raw['coordinates']),len(raw['residuals']),len(raw['gates']))==(400,368,339))
    check('actual fixed parameter',raw['fixedParameter']=={'name':'S','value':'3^2364','coordinate':False})
    compiler=json.loads((b/'compiled/compiler-report.json').read_text())
    check('actual compiled census',(compiler['final']['coordinates'],compiler['final']['residuals'])==(389,357))
    final=json.loads((b/'final/verification.json').read_text())
    check('no extra elimination',final['verified'] and final['eliminated']==0 and final['coordinates']==389 and final['residuals']==357)
    cert=json.loads((b/'balanced/diagonal-certificate.json').read_text())
    threes={int(k) for k,v in cert['threePowers'].items() if v}
    twos={int(k) for k,v in cert['twoPowers'].items() if v}
    check('actual diagonal coordinate counts',(len(threes),len(twos),len(threes|twos),len(threes&twos))==(12,2,13,1))
    check('actual anchor and base in diagonal certificate',(cert['anchorExponent'],cert['cExponent'])==(2364,394))
    check('input fixed',cert['threePowers']['0']==0 and cert['twoPowers']['0']==0)
    divisors=[Fraction(int(r['divisorNumerator']),int(r['divisorDenominator'])) for r in cert['rows']]
    check('all357 row divisors nonzero',len(divisors)==357 and all(divisors))
    check('five rational divisors',sorted(x.denominator for x in divisors if x.denominator!=1)==[2**13,2**21,2**21,2**21,2**42])
    poly=json.loads((b/'balanced/polynomial.json').read_text())
    coefficients=[int(t['coefficient']) for t in poly['terms']]
    check('actual monomial count',len(coefficients)==26295)
    check('actual degree and content',max(len(t['monomial']) for t in poly['terms'])==4 and reduce(gcd,coefficients)==1)
    check('actual coefficient maximum',max(map(abs,coefficients))==28902*3**1576)
    check('actual maximum bits and digits',max(map(abs,coefficients)).bit_length()==2513 and len(str(max(map(abs,coefficients))))==757)
    check('all coordinates active',set(x for t in poly['terms'] for x in t['monomial'])==set(range(389)))
    check('input fourth-power coefficient',next(t['coefficient'] for t in poly['terms'] if t['monomial']==[0,0,0,0])=='1')
    md=markdown.read_text()
    for label,path in re.findall(r'\[([^\]]+)\]\(([^)]+)\)',md):
        check('Markdown package link '+path,(pkg/path).is_file())
    current_table=None
    for line in md.splitlines():
        if not line.startswith('|'):
            current_table=None
            continue
        count=len(re.findall(r'(?<!\\)\|',line))
        if current_table is None:
            current_table=count
        check('Markdown table column count',count==current_table)
    report={'status':'PASS','assertions':len(checks),'checks':checks,'inventorySha256':digest(inventory),'markdownSha256':digest(markdown),'checkerSha256':digest(Path(__file__)),'builderSha256':s['builderSha256'],'proofTexts':len(catalog),'transformations':len(ids),'scope':'Current claims, paths and proof bindings matched to actual generated census/parameters/diagonal metadata/coefficient census. No theorem or algebraic derivation is newly certified by this inventory check.'}
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))


if __name__=='__main__':
    main()
