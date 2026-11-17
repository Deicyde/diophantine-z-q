"""Separate exact audit of the round-eight core and its decimal variants.

This checker imports no construction or audit module, never executes the
builder, and does not modify the construction. It independently expands
every primitive quadratic residual by diagonal/off-diagonal pairs, checks
all requested constant-chain extensions and direct decimal specialization,
and parses every complete text table. The expected fixed exponent is a
mandatory command-line input, independently of every artifact's metadata.
"""
from pathlib import Path
from fractions import Fraction
from collections import defaultdict
from math import gcd,lcm
from itertools import combinations_with_replacement
import argparse,ast,hashlib,json,re,sys,subprocess,tempfile

if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):return json.loads(path.read_text())
def terms(entries):
    p=defaultdict(Fraction)
    for t in entries:
        m=tuple(t['monomial']);s=t.get('sPower',0)
        assert m==tuple(sorted(m)) and all(isinstance(i,int) and i>=0 for i in m)
        assert isinstance(s,int) and s>=0
        p[s,m]+=Fraction(t['coefficient'])
    return {k:v for k,v in p.items() if v}
def add(p,q):
    z=p.copy()
    for k,a in q.items():z[k]=z.get(k,Fraction(0))+a
    return {k:a for k,a in z.items() if a}
def multiply(p,q):
    out=defaultdict(Fraction)
    for (s,m),a in p.items():
        for (t,n),b in q.items():out[s+t,tuple(sorted(m+n))]+=a*b
    return {k:a for k,a in out.items() if a}
def constant(a):return {(0,()):Fraction(a)} if a else {}
def variable(i):return {(0,(i,)):Fraction(1)}
def scalar(p,a):return {k:v*a for k,v in p.items() if v*a}
def evaluate(p,S):
    out=defaultdict(Fraction)
    for (s,m),a in p.items():out[0,m]+=a*S**s
    return {k:a for k,a in out.items() if a}
def primitive(p):
    den=1
    for a in p.values():den=lcm(den,a.denominator)
    z={k:a.numerator*(den//a.denominator) for k,a in p.items()}
    common=0
    for a in z.values():common=gcd(common,abs(a))
    assert common
    first=min(z,key=lambda k:(k[1],k[0]))
    sign=1 if z[first]>0 else -1
    return {k:sign*a//common for k,a in z.items()}

def verify_anchor_translation(construction):
    raw=read(construction/'raw-ir.json');translated=read(construction/'raw-translated-ir.json')
    target=raw['anchor']['rowId'];ids=raw['anchor']['privateCoordinateIds'];assert len(ids)==3
    oldrows={r['id']:r for r in raw['residuals']};newrows={r['id']:r for r in translated['residuals']}
    assert oldrows.keys()==newrows.keys()
    for ri in oldrows:
        if ri!=target:assert oldrows[ri]==newrows[ri]
    U,V,W=map(variable,ids);S={(1,()):Fraction(1)}
    replacements={ids[0]:add(S,scalar(add(add(U,scalar(V,-3)),scalar(W,3)),Fraction(1,4))),
                  ids[1]:add(scalar(S,Fraction(1,2)),scalar(V,Fraction(1,4))),
                  ids[2]:add(scalar(S,Fraction(3,2)),scalar(W,Fraction(1,4)))}
    expanded={}
    for (s,m),a in terms(oldrows[target]['terms']).items():
        t={(s,()):a}
        for x in m:t=multiply(t,replacements.get(x,variable(x)))
        expanded=add(expanded,t)
    assert scalar(expanded,16)==terms(newrows[target]['terms'])
    assert all(len(m)+s<=2 for s,m in expanded)
    return {'identity':'translated row = 16 * old row after stated affine substitution','determinant':'1/64','verified':True}

def verify_protected_interface(construction,power):
    raw=read(construction/'raw-ir.json');small=read(construction/'final/integer-candidate-ir.json')
    assert raw['fixedParameter']==small['fixedParameter']=={'name':'S','value':f'3^{power}','coordinate':False}
    rawcoords={q['name']:q for q in raw['coordinates']};finalcoords={q['name']:q for q in small['coordinates']}
    assert rawcoords['input']['id']==finalcoords['input']['id']==0
    assert rawcoords['input']['protected'] and finalcoords['input']['protected']
    protected=['inputProduct.quadratic','heightProduct.scale0.quadratic','anchor.physicalA.quadratic']
    for name in protected:
        assert rawcoords[name]['protected'] and finalcoords[name]['protected']
        assert rawcoords[name]['id']==finalcoords[name]['id']
    Y=variable(rawcoords['inputProduct.quadratic']['id']);X=variable(0)
    rows={r['name']:terms(r['terms']) for r in raw['residuals']}
    assert rows['inputProduct.definition']==add(Y,scalar(add(multiply(X,X),X),-1))
    assert terms(raw['values']['inputSquare']['terms'])==add(Y,scalar(X,-1))
    degree=max(len(m)+s for r in small['residuals'] for s,m in terms(r['terms']))
    assert degree<=2
    assert not any('dx0Inverse' in n or 'w0Inverse' in n for n in rawcoords)
    return {'inputId':0,'inputProtected':True,'protectedCoordinates':protected,
            'inputProduct':'Y=X^2+X; X^2=Y-X','maximumDegreeWithSAsCoordinate':degree,
            'differenceGuards':0,'detectorTraceGuards':0}

def verify_chain(small,large,exponents,power):
    meta=large['constantChain'];chain=meta['coordinates']
    assert large['fixedParameter']==small['fixedParameter']=={'name':'S','value':f'3^{power}','coordinate':False}
    assert exponents and all(isinstance(e,int) and 0<=e<=100000 for e in exponents)
    assert meta=={'kind':'scaled-squaring-v1','coefficientExponents':exponents,'targetExponent':power,'coordinates':chain}
    assert len(chain)==len(exponents) and len(set(chain))==len(chain)
    # Closed form deliberately differs from the producer's recurrence.
    prefix=[sum(exponents[i]*2**(j-i) for i in range(j+1)) for j in range(len(exponents))]
    assert prefix[-1]==power
    oldcoords={c['id']:c for c in small['coordinates']};newcoords={c['id']:c for c in large['coordinates']}
    assert len(newcoords)==len(oldcoords)+len(chain)
    assert set(newcoords)==set(oldcoords)|set(chain) and set(oldcoords).isdisjoint(chain)
    for i,coord in oldcoords.items():assert coord==newcoords[i]
    for j,i in enumerate(chain):
        assert newcoords[i]['protected'] and newcoords[i]['name']==f'constant.3pow{prefix[j]}'
    remaining={r['id']:terms(r['terms']) for r in large['residuals']}
    for row in small['residuals']:
        expected=defaultdict(Fraction)
        for (s,m),a in terms(row['terms']).items():
            assert s in (0,1) and len(m)+s<=2
            expected[0,tuple(sorted(m+((chain[-1],) if s else ())))]+=a
        assert dict(expected)==remaining.pop(row['id'])
    for j,i in enumerate(chain):
        expected={(0,(i,)):Fraction(1),(0,() if j==0 else (chain[j-1],chain[j-1])):Fraction(-3**exponents[j])}
        assert remaining.pop('constant-chain-'+str(j))==expected
    assert not remaining
    return {'coefficientExponents':exponents,'targetExponent':power,'coordinateExponents':prefix,
            'coordinatesAdded':len(chain),'uniqueExtension':True,'lastValue':f'3^{power}',
            'allOldRowsExactlySpecialized':True}

def verify_text_table(path,expected,n,power):
    decoded={};monomials=set();linecount=0
    with path.open() as stream:
        header=False;comments=[]
        for line in stream:
            if line.startswith('#'):comments.append(line);continue
            if not header:assert line=='coefficient\tmonomial\n';header=True;continue
            expression,monomial=line.rstrip('\n').split('\t')
            m=() if monomial=='1' else tuple(int(x.removeprefix('x')) for x in monomial.split('*'))
            assert m==tuple(sorted(m)) and m not in monomials and len(m)<=4
            assert all(0<=x<n for x in m)
            monomials.add(m);expression=expression.replace(' ','');position=0
            for token in re.finditer(r'([+-]?\d+)(\*S(?:\^(\d+))?)?',expression):
                assert token.start()==position
                a=int(token[1]);s=(int(token[3]) if token[3] else 1) if token[2] else 0
                assert a and (s,m) not in decoded
                decoded[s,m]=a;position=token.end()
            assert position==len(expression);linecount+=1
    assert header and decoded==expected and path.stat().st_size>0,str(path)
    if any(s for s,m in expected):assert f'S = 3^{power} is a fixed integer coefficient, not a variable.' in ''.join(comments)
    else:assert 'Every coefficient is written explicitly in decimal. No symbolic coefficient parameter occurs.' in ''.join(comments)
    return {'rows':linecount,'bytes':path.stat().st_size,'sha256':digest(path),'allCoefficientsCompared':True}

def verify_sos(folder,source,table_path,text_path,expected_coordinates,expected_residuals,expected_monomials,power,already_specialized=False):
    inp=read(source);compiled=read(folder/'compiled-ir.json');table=read(table_path)
    expected_parameter={'name':'S','value':f'3^{power}','coordinate':False}
    assert inp['fixedParameter']==compiled['fixedParameter']==expected_parameter
    assert table['fixedParameter']=='S = '+expected_parameter['value']
    assert table['sosMultiplier']=='1'
    assert inp['coordinates']==compiled['coordinates']
    source_rows={r['id']:(terms(r['terms']) if already_specialized else primitive(terms(r['terms']))) for r in inp['residuals']}
    compiled_rows={r['id']:terms(r['terms']) for r in compiled['residuals']}
    assert source_rows==compiled_rows
    assert len(compiled_rows)==expected_residuals and len(compiled['coordinates'])==expected_coordinates
    active=set();sos=defaultdict(int)
    for p in source_rows.values():
        assert max(len(m) for s,m in p)<=2
        for s,m in p:active.update(m)
        items=list(p.items())
        for i,j in combinations_with_replacement(range(len(items)),2):
            (s,m),a=items[i];(t,n),b=items[j]
            sos[s+t,tuple(sorted(m+n))]+=(1 if i==j else 2)*a*b
    sos={k:a for k,a in sos.items() if a}
    assert active=={c['id'] for c in compiled['coordinates']}
    indices={q['sourceId']:q['id'] for q in table['coordinates']}
    assert set(indices)==active and list(indices.values())==list(range(expected_coordinates))
    assert list(indices)==sorted(active) and indices[0]==0
    by_id={q['id']:q for q in compiled['coordinates']}
    for q in table['coordinates']:assert by_id[q['sourceId']]['name']==q['name']
    expected={(s,tuple(indices[i] for i in m)):a for (s,m),a in sos.items()}
    actual=terms(table['terms']);assert expected==actual
    assert all(a.denominator==1 for a in actual.values())
    actual={k:a.numerator for k,a in actual.items()}
    assert actual[0,(0,0,0,0)]==1  # Explicit content-one and degree-four witness.
    assert max(len(m) for s,m in actual)==4
    monomials=defaultdict(dict)
    for (s,m),a in actual.items():monomials[m][s]=a
    if expected_monomials is not None:assert len(monomials)==expected_monomials
    # Every S-coefficient polynomial retains its sign/support at the fixed
    # value S0, using the independently supplied expected endpoint.
    for coeff in monomials.values():
        lead=max(coeff)
        if lead:
            bound=sum(abs(a) for s,a in coeff.items() if s<lead)
            assert (bound+1).bit_length()<=power
    symbolic=any(s for s,m in actual)
    if symbolic:
        def lexabs(coeff):
            sign=1 if coeff[max(coeff)]>0 else -1
            return tuple(sign*coeff.get(i,0) for i in (2,1,0))
        m,coeff=max(monomials.items(),key=lambda item:lexabs(item[1]));largest=lexabs(coeff)
        for other in monomials.values():
            difference=tuple(a-b for a,b in zip(largest,lexabs(other)))
            nonzero=next((a for a in difference if a),0)
            assert nonzero>=0
            assert (sum(abs(a) for a in difference)+1).bit_length()<=power
        maximum={'monomial':list(m),'coefficientBySPower':{str(2-i):str(a) for i,a in enumerate(largest) if a},'dominanceAtFixedSVerified':True}
    else:
        value=max(map(abs,actual.values()));maximum={'bits':value.bit_length(),'decimalDigits':len(str(value))}
    text=verify_text_table(text_path,actual,expected_coordinates,power)
    return {'coordinates':expected_coordinates,'residuals':expected_residuals,'degree':4,
            'monomials':len(monomials),'formalCoefficientTerms':len(actual),'content':1,
            'contentWitness':'coefficient of x0^4 equals 1','maximum':maximum,
            'sourceIrSha256':digest(source),'compiledIrSha256':digest(folder/'compiled-ir.json'),
            'polynomialSha256':digest(table_path),'textTable':text}

def verify_parameter_bindings(construction,power):
    expected={'name':'S','value':f'3^{power}','coordinate':False}
    paths=['raw-ir.json','raw-translated-ir.json','compiled/compiled-ir.json',
           'final/source-ir.json','final/candidate-ir.json','final/integer-candidate-ir.json',
           'final/polynomial/compiled-ir.json']
    for name in paths:assert read(construction/name)['fixedParameter']==expected,name
    tables=['compiled/polynomial.json','final/polynomial/polynomial.json']
    for name in tables:assert read(construction/name)['fixedParameter']=='S = '+expected['value'],name
    for prefix in ['compiled','final/polynomial']:
        certificate=read(construction/prefix/'specialization-certificate.json')
        assert certificate['fixedParameter']=='S = '+expected['value']
        assert certificate['universalParameterLowerBound']==f'S > 2^{power}'
        assert certificate['allComparisonBoundsSatisfied'] is True
        assert certificate['requiredPowerOfTwoLowerBound']<=power
    return {'expectedExponent':power,'expectedValue':expected['value'],
            'sourceAndIntermediateMetadataChecked':paths+tables,
            'specializationSignCertificatesUseExpectedExponent':True}

def verify_direct_specialization(construction,power):
    source=construction/'final/polynomial/compiled-ir.json'
    core=read(source);n=len(core['coordinates']);folder=construction/f'ordinary{n}'
    decimal=read(folder/'specialized-ir.json')
    expected={'name':'S','value':f'3^{power}','coordinate':False}
    assert core['fixedParameter']==decimal['fixedParameter']==expected
    assert core['coordinates']==decimal['coordinates']
    assert not (folder/'lifted-ir.json').exists()
    assert 'constantChain' not in decimal
    S=3**power
    oldrows={r['id']:r for r in core['residuals']};newrows={r['id']:r for r in decimal['residuals']}
    assert oldrows.keys()==newrows.keys()
    for ri,old in oldrows.items():
        assert {k:v for k,v in old.items() if k!='terms'}=={k:v for k,v in newrows[ri].items() if k!='terms'}
        assert evaluate(terms(old['terms']),S)==terms(newrows[ri]['terms'])
    oldtable=read(construction/'final/polynomial/polynomial.json')
    newtable=read(folder/'polynomial/polynomial.json')
    assert oldtable['coordinates']==newtable['coordinates']
    assert oldtable['fixedParameter']==newtable['fixedParameter']=='S = '+expected['value']
    assert evaluate(terms(oldtable['terms']),S)==terms(newtable['terms'])
    assert not any(s for s,m in terms(newtable['terms']))
    meta=decimal['directSpecialization']
    assert meta['fixedParameter']==expected and meta['expectedExponent']==power
    assert meta['sourceIrSha256']==digest(source)
    assert meta['sourcePolynomialSha256']==digest(construction/'final/polynomial/polynomial.json')
    assert newtable['directSpecialization']==meta
    return {'fixedValue':expected['value'],'fixedValueDecimalDigits':len(str(S)),
            'allResidualsExactlyEvaluated':True,'allSosCoefficientsExactlyEvaluated':True,
            'additionalCoordinates':0,'residualRenormalization':False,'coordinateMapUnchanged':True}

def verify_actual_detector_source(construction,checker,expected_assertions,high_order,expected_exponent):
    # Run the separate source-level reconstruction, never the builder or compiler.
    # Its source assertions check all actual groups and their products, including
    # the uniform order-(12,12) factor. A historical abstract grouping is insufficient.
    with tempfile.TemporaryDirectory(prefix='quartic-detector-audit-') as directory:
        report=Path(directory)/'source-check.json'
        completed=subprocess.run([sys.executable,str(checker),str(construction),'--report',str(report),'--anchor',f'3^{expected_exponent}','--high',str(high_order)],
                                 check=True,capture_output=True,text=True)
        data=read(report)
    assert data['status']=='PASS' and data['sourceAssertions']==expected_assertions
    assert data['abstractUniformPairIdentities']==2
    assert data['abstractLaurentIdentities']==7
    assert data['semanticNormalizationIdentities']==3
    assert data['highOrder']==high_order and data['anchor']==f'3^{expected_exponent}'
    assert data['builderSha256']==digest(construction/'builder.cjs')
    assert data['rawIrSha256']==digest(construction/'raw-ir.json')
    return {'status':'PASS','sourceAssertions':expected_assertions,'abstractUniformPairIdentities':2,'abstractLaurentIdentities':7,
            'expectedHighOrder':high_order,'expectedAnchor':f'3^{expected_exponent}',
            'actualGroups':{'uniformPairOrders':[12,12],'order1Blocks':[4,4],f'order{high_order}Blocks':[3,3]},
            'checkerSha256':digest(checker),'builderBindingMatches':True,'rawIrBindingMatches':True,
            'scope':data['scope']}

def inspect_scripts(construction,package_audit):
    names=['builder.cjs','finish_tables.py','verify_package.py','check_final.cjs','write_tables_text.py','specialize_core.py',
           'tools/compile_ir.py','tools/checker.cjs','tools/run_pipeline.py','tools/modulo_search.py','tools/affine_search.py',
           'tools/search.py','tools/verify.py','tools/verify_elimination.py']
    files=[construction/n for n in names]
    package=construction.parent
    if package_audit:
        files.append(construction/'reproduce.py')
        files.extend(sorted((package/'audit').glob('*.py')))
        assert (package/'audit/check_detector_source.py').is_file()
    assert all(p.is_file() and p.stat().st_size for p in files)
    local_python={'modulo_search','affine_search','verify','search'}
    for p in files:
        source=p.read_text();assert ('/'+'workspace'+'/') not in source,p
        if p.suffix=='.py':
            syntax=ast.parse(source)
            for node in ast.walk(syntax):
                if isinstance(node,ast.Import):mods=[q.name.split('.')[0] for q in node.names]
                elif isinstance(node,ast.ImportFrom):mods=[node.module.split('.')[0]] if node.module else []
                else:continue
                assert all(m in sys.stdlib_module_names or m in local_python for m in mods),(p,mods)
        if p.suffix=='.cjs':
            for m in re.findall(r"require\(['\"]([^'\"]+)",source):
                assert m.startswith('node:') or (m.startswith('./') and (p.parent/m).resolve().is_file()),(p,m)
    writer=(construction/'write_tables_text.py').read_text()
    assert 'os.fsync' in writer and 'os.replace' in writer
    specialize=(construction/'specialize_core.py').read_text()
    assert 'os.fsync' in specialize and 'os.replace' in specialize
    if package_audit:
        repro=(construction/'reproduce.py').read_text()
        assert 'specialize_core.py' in repro and 'check_detector_source.py' in repro
        assert 'check_delivered_quartics_round8.py' in repro
    return {'portable':True,'runtimeRequirements':['Python 3 standard library','Node.js standard library'],
            'externalNetworkRequired':False,'atomicTextAndDirectSpecializationPublication':True,
            'completionRecordScope':'The outer wrapper verifies structured completion after the final audit stage.',
            'scripts':[{'path':str(p.relative_to(package)),'sha256':digest(p)} for p in files]}

def report_bindings(paths,construction):
    out=[];bh=digest(construction/'builder.cjs');rh=digest(construction/'raw-ir.json')
    for p in paths:
        data=read(p);assert data['status']=='PASS'
        binding=data.get('sourceBinding') or data
        recorded=binding.get('builderSha256',binding.get('sourceBuilderSha256'))
        assert recorded==bh,(str(p),recorded,bh)
        if 'rawIrSha256' in binding:assert binding['rawIrSha256']==rh
        out.append({'name':p.name,'sha256':digest(p),'builderBindingMatches':True,
                    'rawIrBindingChecked':'rawIrSha256' in binding})
    return out

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('directory',type=Path,help='Construction directory or package containing construction/.')
    ap.add_argument('--expected-exponent',type=int,required=True)
    ap.add_argument('--expected-core',type=int,required=True)
    ap.add_argument('--expected-residuals',type=int,required=True)
    ap.add_argument('--expected-monomials',type=int,required=True)
    ap.add_argument('--chain',action='append',required=True)
    ap.add_argument('--expected-detector-assertions',type=int,required=True)
    ap.add_argument('--high-order',type=int,required=True)
    ap.add_argument('--detector-checker',type=Path)
    ap.add_argument('--source-report',action='append',type=Path,default=[])
    ap.add_argument('--package-audit',action='store_true')
    ap.add_argument('--report',type=Path,required=True)
    args=ap.parse_args();d=args.directory.resolve()
    construction=d/'construction' if (d/'construction').is_dir() else d
    assert 1<=args.expected_exponent<=100000
    chains=[[int(x) for x in text.split(',')] for text in args.chain]
    assert len({len(chain) for chain in chains})==len(chains)
    detector=args.detector_checker or construction.parent/'audit/check_detector_source.py'
    detector=detector.resolve();assert detector.is_file()
    n=args.expected_core;nr=args.expected_residuals;nm=args.expected_monomials;p=args.expected_exponent
    result={'status':'PASS','scope':'Independent full exact SOS/table/constant-chain/direct-specialization audit, source grouping reconstruction, parameter binding, and portable-script inspection. The inherited global arithmetic remains conditional on the separate reviewed proof inputs.',
            'builderSha256':digest(construction/'builder.cjs'),'rawIrSha256':digest(construction/'raw-ir.json'),
            'parameterBinding':verify_parameter_bindings(construction,p),
            'anchorTranslation':verify_anchor_translation(construction),
            'protectedInterface':verify_protected_interface(construction,p),
            'actualDetectorSource':verify_actual_detector_source(construction,detector,args.expected_detector_assertions,args.high_order,p),
            'scriptAudit':inspect_scripts(construction,args.package_audit),
            'auditReportBindings':report_bindings(args.source_report,construction)}
    small=read(construction/'final/integer-candidate-ir.json')
    result['symbolic']=verify_sos(construction/'final/polynomial',construction/'final/integer-candidate-ir.json',construction/'final/polynomial/polynomial.json',construction/f'quartic-{n}-symbolic.txt',n,nr,nm,p)
    direct=construction/f'ordinary{n}'
    result['directDecimal']={'specialization':verify_direct_specialization(construction,p),
        'table':verify_sos(direct/'polynomial',direct/'specialized-ir.json',direct/'polynomial/polynomial.json',construction/f'quartic-{n}-decimal.txt',n,nr,nm,p,True)}
    result['ordinary']={}
    expected_ordinary={f'ordinary{n}'}
    for exponents in chains:
        added=len(exponents);count=n+added;folder=construction/f'ordinary{count}'
        expected_ordinary.add(folder.name)
        result['ordinary'][str(count)]={'chain':verify_chain(small,read(folder/'lifted-ir.json'),exponents,p),
            'table':verify_sos(folder/'polynomial',folder/'lifted-ir.json',folder/'polynomial/polynomial.json',construction/f'quartic-{count}-decimal.txt',count,nr+added,None,p)}
    actual_ordinary={folder.name for folder in construction.glob('ordinary*') if (folder/'polynomial/polynomial.json').exists()}
    assert actual_ordinary==expected_ordinary,(actual_ordinary,expected_ordinary)
    result['checkerSha256']=digest(Path(__file__).resolve())
    args.report.parent.mkdir(parents=True,exist_ok=True)
    args.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in {'scriptAudit','auditReportBindings'}},indent=2))

if __name__=='__main__':main()

