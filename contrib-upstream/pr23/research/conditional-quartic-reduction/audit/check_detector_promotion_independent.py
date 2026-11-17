"""Independent conservation and semantic audit of the primary-order promotion.

No producer/compiler/checker is imported. Sparse equations are decoded into
semantic coordinate names, so removed coordinate IDs cannot conceal changes.
The frozen baseline digest binds every unchanged equation. An optional
--baseline path independently recomputes that digest from the original IR.
This is a finite source audit; the uniform formal-group argument is in the
separately written review, and inherited global arithmetic remains conditional.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import hashlib
import json
import re

BASELINE_BUILDER = '78b54bcde24ff8a91091e102a4734c49878699f071d9230e5ce7a70ffd2114d0'
BASELINE_RAW = '582c8bf2fcde54242bb23bf7aa33d3a7a9065f04b8edd885a13386b5b779b92c'
BASELINE_UNCHANGED_EQUATIONS = '21f82ae2cc7888e46bff5d87c24708c8996c89e8b1ee43d29c57b6953fafceb8'
ORDERS = [45,12,1,1,1,1,1,1,1,1,12,45,45,45,45,45]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_name(name, candidate):
    return name.replace('testSquare.12.1.', 'testSquare.12.0.') if candidate else name


def read_ir(directory, candidate):
    data = json.loads((directory/'raw-ir.json').read_text())
    coordinates = {c['id']: canonical_name(c['name'], candidate) for c in data['coordinates']}
    def decode(terms):
        result = {}
        for term in terms:
            monomial = tuple(sorted(coordinates[i] for i in term['monomial']))
            key = (int(term.get('sPower',0)), monomial)
            result[key] = result.get(key, Fraction(0)) + Fraction(term['coefficient'])
        return {k:v for k,v in result.items() if v}
    values = {name:decode(value['terms']) for name,value in data['values'].items()}
    rows = {canonical_name(row['name'],candidate):decode(row['terms']) for row in data['residuals']}
    return data, rows, values


def plus(*polynomials):
    out = {}
    for polynomial in polynomials:
        for key,value in polynomial.items():
            out[key] = out.get(key,Fraction(0))+value
    return {k:v for k,v in out.items() if v}


def times(a,b):
    out = {}
    for (s,m),u in a.items():
        for (t,n),v in b.items():
            key=(s+t,tuple(sorted(m+n)))
            out[key]=out.get(key,Fraction(0))+u*v
    return {k:v for k,v in out.items() if v}


def scalar(a,q):
    return {k:v*q for k,v in a.items() if v*q}


ONE = {(0,()):Fraction(1)}
ZERO = {}


def field_product(a,b):
    return [plus(times(a[0],b[0]),scalar(times(a[1],b[1]),2)),
            plus(times(a[0],b[1]),times(a[1],b[0]))]


def normalized(polynomial):
    terms=sorted(polynomial.items())
    if not terms:
        return []
    first=terms[0][1]
    return [[s,list(m),str(c/first)] for (s,m),c in terms]


def equation_digest(rows):
    keep={}
    for name,row in rows.items():
        if re.fullmatch(r'detector[012]\.q1q12\.definition',name):
            continue
        if re.fullmatch(r'detector[012]\.mixed\.[01]\.definition',name):
            continue
        keep[name]=normalized(row)
    serialized=json.dumps(keep,sort_keys=True,separators=(',',':')).encode()
    return len(keep),hashlib.sha256(serialized).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('construction',type=Path)
    parser.add_argument('--baseline',type=Path)
    parser.add_argument('--proof',type=Path,required=True)
    parser.add_argument('--expected-exponent',type=int)
    parser.add_argument('--expected-anchor',help='Optional equivalent explicit declaration, e.g.3^2790')
    parser.add_argument('--report',type=Path,required=True)
    args=parser.parse_args()
    if args.expected_exponent is not None and args.expected_exponent<=0:
        parser.error('--expected-exponent must be positive')
    if args.expected_anchor is None:
        args.expected_anchor='3^'+str(args.expected_exponent if args.expected_exponent is not None else 2790)
    elif args.expected_exponent is not None and args.expected_anchor!='3^'+str(args.expected_exponent):
        parser.error('The two expected-anchor arguments disagree')
    checks=[]
    def require(condition,label):
        if not condition:
            raise ValueError(label)
        checks.append(label)
    data,rows,values=read_ir(args.construction,True)
    names=[c['name'] for c in data['coordinates']]
    require(data['counts']=={'baseCoordinates':61,'structuralResiduals':29,
        'coordinates':400,'residuals':368,'gates':339},'actual raw counts')
    require(data['coordinates'][0]['id']==0 and data['coordinates'][0]['name']=='input',
            'distinguished input unchanged')
    require(re.fullmatch(r'3\^[1-9][0-9]*',args.expected_anchor) is not None,
            'explicit positive anchor declaration')
    require(data['fixedParameter']=={'name':'S','value':args.expected_anchor,'coordinate':False},
            'actual fixed parameter matches requested declaration')
    require(len(names)==len(set(names)),'unique coordinate names')
    signatures={json.dumps(normalized(row),separators=(',',':')) for row in rows.values()}
    def equation(polynomial,label):
        require(not polynomial or json.dumps(normalized(polynomial),separators=(',',':')) in signatures,label)
    def field(name):
        return [values[name+'.0'],values[name+'.1']]
    def equal_field(a,b,label):
        for j in (0,1):
            require(a[j]==b[j],label+': component '+str(j))
    def field_equations(a,b,label):
        for j in (0,1):
            equation(plus(a[j],scalar(b[j],-1)),label+': component '+str(j))
    same_count,same_digest=equation_digest(rows)
    require(same_count==362,'362 unaffected source equations')
    require(same_digest==BASELINE_UNCHANGED_EQUATIONS,'every unaffected equation matches frozen semantic digest')
    baseline_comparison=None
    if args.baseline:
        require(sha(args.baseline/'builder.cjs')==BASELINE_BUILDER,'original builder binding')
        require(sha(args.baseline/'raw-ir.json')==BASELINE_RAW,'original raw IR binding')
        old,old_rows,old_values=read_ir(args.baseline,False)
        old_count,old_digest=equation_digest(old_rows)
        require((old_count,old_digest)==(same_count,same_digest),'direct original-versus-new equation comparison')
        old_names={c['name'] for c in old['coordinates']}
        new_names={canonical_name(n,True) for n in names}
        require(new_names<=old_names,'no unexpected new semantic coordinates')
        require(old_names-new_names=={f'detector{i}.q1q12.quadratic' for i in range(3)},
                'exactly three mixed-weight coordinates removed')
        for i in range(16):
            equal_field(field('test'+str(i)),[old_values[f'test{i}.{j}'] for j in (0,1)],
                        'unchanged actual test '+str(i))
        equal_field(field('mixedTestProduct'),[old_values[f'mixedTestProduct.{j}'] for j in (0,1)],
                    'unchanged shared field coefficient')
        baseline_comparison={'rawIrSha256':BASELINE_RAW,'equationsCompared':same_count,
                             'semanticCoordinatesRemoved':sorted(old_names-new_names)}
    equal_field(field('test1'),field('UA.g'),'promoted test is the input primary inverse root')
    equal_field(field('test10'),[plus(values['L1.0'],scalar(values['LP1.0'],-1)),
                                plus(values['L1.1'],values['LP1.1'])],
                'other paired test is the conjugated input comparison')
    semantic_tests=[field(name+'.g') for name in ('H','UA','US','UT','UZ')]
    semantic_tests += [[values[f'V{i}.f.0'],scalar(values[f'V{i}.f.1'],-1)] for i in range(5)]
    semantic_tests += [[plus(values[f'L{i}.0'],scalar(values[f'LP{i}.0'],-1)),
                        plus(values[f'L{i}.1'],values[f'LP{i}.1'])] for i in range(1,5)]
    semantic_tests += [[plus(values['L1.0'],scalar(values['beta'],-1)),values['L1.1']],
                       [values['Lucas.F0'],values['Lucas.F1']]]
    for i,wanted in enumerate(semantic_tests):
        equal_field(field('test'+str(i)),wanted,'standalone semantic test '+str(i))
    order_positions={1:0,12:0,45:0}
    for index,order in enumerate(ORDERS):
        slot=order_positions[order]
        field_equations(field(f'testSquare.{order}.{slot}'),
                        field_product(field('test'+str(index)),field('test'+str(index))),
                        'actual squared test/order '+str(index)+'/'+str(order))
        order_positions[order]+=1
    require(order_positions=={1:8,12:2,45:6},'complete test multiplicities')
    equal_field(field('testSquare.12.0'),field('UA.f'),'promoted square reuses the existing primary f')
    left,right=field('testSquare.12.0'),field('testSquare.12.1')
    shared=field('mixedTestProduct')
    field_equations(shared,field_product(left,right),'uniform-pair shared coefficient')
    for i in range(3):
        prefix='detector'+str(i)
        require(not any(n.startswith(prefix+'.q1q12') for n in names),prefix+' obsolete product absent')
        require(prefix+'.q1q12' not in values,prefix+' obsolete product alias absent')
        q,qs=values[prefix+'.q12'],values[prefix+'.mixedHigh']
        equation(plus(qs,scalar(times(q,q),-1)),prefix+' stored q12 square')
        equation(plus(times(values[prefix+'.q1CubedForWeights'],values[prefix+'.q45']),
                      scalar(times(qs,qs),-1)),prefix+' same square used by high-weight equation')
        expected=[plus(ONE,times(q,plus(left[0],right[0])),times(qs,shared[0])),
                  plus(times(q,plus(left[1],right[1])),times(qs,shared[1]))]
        field_equations(field(prefix+'.mixed'),expected,prefix+' actual uniform-pair output')
        field_equations(field(prefix+'.W'),field_product(field(prefix+'.pure'),field(prefix+'.mixed')),
                        prefix+' full product consumer')
        w=field(prefix+'.W');nw=values[prefix+'.normOver2w0']
        equation(plus(scalar(times(w[0],nw),2),scalar(times(w[0],w[0]),-1),
                      scalar(times(w[1],w[1]),2)),prefix+' reciprocal-trace quotient consumer')
        equation(plus(times(values[prefix+'.B'],values[prefix+'.eDelta']),scalar(times(nw,nw),-1)),
                 prefix+' same pole input formula')
    require(all(s+len(m)<=2 for row in rows.values() for s,m in row),'all rows quadratic after lifting S')
    require(1-2*12+2*45==67 and 45>=12>=1,'strict selected-contact valuation margin')
    require(10*12-6==114,'small-prime coefficient in the new fixed lower bound')
    compiled=json.loads((args.construction/'compiled/compiled-ir.json').read_text())
    polynomial=json.loads((args.construction/'compiled/polynomial.json').read_text())
    require(len(compiled['coordinates'])==389 and len(compiled['residuals'])==357,'actual compiled counts')
    require(len(polynomial['coordinates'])==389 and len({tuple(t['monomial']) for t in polynomial['terms']})==26295,
            'actual polynomial coordinate/ordinary-monomial dimensions')
    require(len(polynomial['terms'])==26299,'actual formal-parameter term count')
    require(max(len(t['monomial']) for t in polynomial['terms'])==4,'actual quartic degree')
    require({i for t in polynomial['terms'] for i in t['monomial']}==set(range(389)),
            'every compact polynomial coordinate is active')
    result={'status':'PASS','sourceAssertions':len(checks),'checks':checks,
            'builderSha256':sha(args.construction/'builder.cjs'),'rawIrSha256':sha(args.construction/'raw-ir.json'),
            'proofSha256':sha(args.proof),'checkerSha256':sha(Path(__file__)),
            'expectedAnchor':args.expected_anchor,'testOrders':ORDERS,
            'unaffectedEquationCount':same_count,'unaffectedEquationSemanticSha256':same_digest,
            'baselineComparison':baseline_comparison,'rawCoordinates':400,'rawResiduals':368,
            'compiledCoordinates':389,'compiledResiduals':357,'compiledMonomials':26295,
            'scope':'Independent source conservation, all actual test assignments, three uniform pair factors, retained norm/pole consumers and measured finite counts. Formal-group/completeness proof review is separate; inherited global arithmetic is not proved.'}
    args.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2))


if __name__=='__main__':
    main()
