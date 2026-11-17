"""Exact source delta, mixed-weight identities and finite height margins."""
from copy import deepcopy
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent/'scalar-chain-reduction'))
from check_chain import poly, add, scale, mul


def canonical(value):
    if isinstance(value, str):
        for a,b in [('.q46','.q45'),('.E46','.E45'),('symmetric.46.','symmetric.45.'),('testSquare.46.','testSquare.45.')]:
            value=value.replace(a,b)
        return value
    if isinstance(value, list):
        return [canonical(v) for v in value]
    if isinstance(value, dict):
        return {canonical(k):canonical(v) for k,v in value.items()}
    return value


def source_check(before, after):
    assert before['fixedParameter']=={'name':'S','value':'3^2118','coordinate':False}
    assert after['fixedParameter']=={'name':'S','value':'3^2010','coordinate':False}
    b=canonical(after)
    assert before.keys()==b.keys()
    for section in before.keys()-{'fixedParameter','variant','residuals','gates'}:
        assert before[section]==b[section], section
    arows={r['id']:r for r in before['residuals']}
    brows={r['id']:r for r in b['residuals']}
    assert arows.keys()==brows.keys()
    changed={i for i in arows if arows[i]!=brows[i]}
    assert {brows[i]['name'] for i in changed}=={f'detector{i}.q45.definition' for i in range(3)}
    ag={g['definitionResidualId']:g for g in before['gates']}
    bg={g['definitionResidualId']:g for g in b['gates']}
    assert ag.keys()==bg.keys()
    assert {i for i in ag if ag[i]!=bg[i]}==changed
    av={n:poly(p['terms']) for n,p in before['values'].items()}
    bv={n:poly(p['terms']) for n,p in after['values'].items()}
    rr={r['name']:poly(r['terms']) for r in after['residuals']}
    def eq(name,left,right):
        wanted=add(left,scale(right,-1)); actual=rr[name]
        pivot=min(wanted)
        assert pivot in actual and actual==scale(wanted,actual[pivot]/wanted[pivot]),name
    square=lambda x:mul(x,x)
    for i in range(3):
        p=f'detector{i}.'
        eq(p+'q46.definition',mul(bv[p+'q1'],bv[p+'q46']),square(bv[p+'mixedHigh']))
        eq(p+'mixedHigh.definition',bv[p+'mixedHigh'],square(bv[p+'q12']))
        eq(p+'q12.definition',mul(bv[p+'eDelta'],bv[p+'q12']),square(bv[p+'eTwelfth']))
        rid=next(r['id'] for r in after['residuals'] if r['name']==p+'q46.definition')
        assert poly(bg[rid]['denominator'])==bv[p+'q1']
        assert poly(ag[rid]['denominator'])==av[p+'q1CubedForWeights']
        assert ag[rid]['numerator']==bg[rid]['numerator']
        assert ag[rid]['coordinateId']==bg[rid]['coordinateId']
    return {'changedRows':[brows[i]['name'].replace('q45','q46') for i in sorted(changed)],
            'outsideRowsUnchanged':len(arows)-3,'allGuardsUnchanged':True,
            'allCoordinateSlotsRetained':True,'onlyOtherChange':'fixed parameter and descriptive variant metadata'}


def finite_checks():
    # Exponents in the explanatory pair (e, delta), never newly allocated.
    plus=lambda a,b:tuple(x+y for x,y in zip(a,b))
    minus=lambda a,b:tuple(x-y for x,y in zip(a,b))
    twice=lambda a:plus(a,a)
    q1=(1,-1); E=(1,1)
    e3=plus((3,-3),(0,3)); e6=twice(e3); e12=twice(e6)
    q12=minus(twice(e12),E); h=twice(q12); high=minus(twice(h),q1)
    assert q12==(23,-1) and high==(91,-3)
    # R*(D/delta^j/R^m)^2 has exponents (2m-1, 2m-1-2j).
    for m,j,weight in [(1,1,q1),(12,12,q12),(46,47,high)]:
        assert (2*m-1,2*m-1-2*j)==weight
    contacts=[F(0),F(1,49),F(1,50),F(1,2450),F(32,1225)]
    deltas=[98*x-1 for x in contacts]
    assert deltas==[F(-1),F(1),F(24,25),F(-24,25),F(39,25)]
    for d in deltas:
        for z in [abs(d.numerator),d.denominator]:
            for p in [2,3,5,7,13,17]:
                while z%p==0: z//=p
            assert z==1
    # v(e)=5s, v(delta)=s-nu; each weight gives a positive nu slope.
    local=[(-d,5*e+d) for e,d in [q1,q12,high]]
    assert local==[(1,4),(1,114),(3,452)]
    assert 1-2*46+2*46==1 and 2*46-1==91
    H=3*2**106*(2**32*3**9)**6*46410**18+128
    c=2*3**1004; b=c-1; p=2*b**4+6*b**3+5*b**2+1
    assert 8**992*c**415>(25*H)**992
    assert (2*(b*b-6))**1472>(3*H+14)**1472*p**577
    assert 64*46-2308==636 and 40*H<2**670 and b>67000 and b>=301
    assert F(384,19100)+F(577,191)*F(8,25)==F(4712,4775)
    assert F(4712,4775)*301+F(4616,4775)<301-3
    return {'weightExponents':{'q1':q1,'q12':q12,'high':high},
            'localNuAndS':local,'contactDeltaValues':list(map(str,deltas)),
            'highOrder':46,'anchorExponent':2010,'lucasRatioPower':636,
            'allThreeConsumerMargins':True}


def main():
    if not __debug__:
        raise RuntimeError('Run checks without Python optimization')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('before',type=Path);ap.add_argument('after',type=Path)
    ap.add_argument('--report',type=Path,required=True);args=ap.parse_args()
    before,after=[json.loads(p.read_text()) for p in [args.before,args.after]]
    delta=source_check(before,after); finite=finite_checks()
    probes=[]
    for name in ['detector0.q46.definition','scalar.N.definition']:
        changed=deepcopy(after);row=next(r for r in changed['residuals'] if r['name']==name)
        row['terms'][0]['coefficient']=str(F(row['terms'][0]['coefficient'])+1)
        probes.append((name,changed))
    changed=deepcopy(after);changed['guards']=[];probes.append(('drop guards',changed))
    changed=deepcopy(after);changed['fixedParameter']['value']='3^2004';probes.append(('wrong anchor',changed))
    changed=deepcopy(after);changed['coordinates'][0]['name']='other-input';probes.append(('rename input',changed))
    for name,changed in probes:
        try: source_check(before,changed)
        except (AssertionError,KeyError): pass
        else: raise AssertionError('Mutation accepted: '+name)
    result={'status':'PASS','independentAcceptance':False,'sourceDelta':delta,'finiteChecks':finite,
            'negativeControlsRejected':[n for n,_ in probes],
            'files':{n:hashlib.sha256(p.read_bytes()).hexdigest() for n,p in [('before',args.before),('after',args.after)]},
            'scope':'Exact source/equation/exponent and integer checks; uniform arithmetic arguments and inherited inputs require separate mathematical review.'}
    args.report.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: three mixed-weight gates, outside source identity, finite margins and five negative controls')


if __name__=='__main__': main()
