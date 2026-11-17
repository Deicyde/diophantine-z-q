"""Independent, exact rational-arithmetic checks of the delivered quartics.

Does not import the source builder or producer compiler.  The inherited arithmetic characterization is not checked. Changed-source
equations are verified separately by the four portable audit scripts.
"""
from pathlib import Path
from fractions import Fraction as Q
from functools import reduce
import argparse,hashlib,importlib.util,itertools,json,math,re,sys
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def poly(ts):
 p={}
 for t in ts:
  s=t.get('sPower',0);m=tuple(t['monomial']);assert s>=0 and m==tuple(sorted(m));k=s,m
  p[k]=p.get(k,Q(0))+Q(t['coefficient'])
 return {k:v for k,v in p.items() if v}
def add(p,q):
 r=p.copy()
 for k,v in q.items():r[k]=r.get(k,Q(0))+v
 return {k:v for k,v in r.items() if v}
def multiply(p,q):
 r={}
 for (s,m),a in p.items():
  for (t,n),b in q.items():
   k=s+t,tuple(sorted(m+n));r[k]=r.get(k,Q(0))+a*b
 return {k:v for k,v in r.items() if v}
def degree(p):return max((len(m) for s,m in p),default=0)
def vars(p):return {x for s,m in p for x in m}
def normalize(p):
 assert p
 den=reduce(math.lcm,(a.denominator for a in p.values()),1)
 g=reduce(math.gcd,(abs(a.numerator*(den//a.denominator)) for a in p.values()),0)
 scale=Q(den,g)
 if p[min(p,key=lambda k:(k[1],k[0]))]<0:scale=-scale
 return {k:a*scale for k,a in p.items()}
def check_table(directory,source):
 inp=read(source);ir=read(directory/'polynomial/compiled-ir.json');table=read(directory/'polynomial/polynomial.json')
 assert inp['coordinates']==ir['coordinates']
 assert {r['id']:normalize(poly(r['terms'])) for r in inp['residuals']}=={r['id']:poly(r['terms']) for r in ir['residuals']}
 active=set();sos={}
 for r in ir['residuals']:
  p=poly(r['terms']);assert p==normalize(p) and degree(p)<=2
  assert all(a.denominator==1 for a in p.values());active |= vars(p);sos=add(sos,multiply(p,p))
 coords={c['id']:c for c in ir['coordinates']};assert active==set(coords) and 0 in active
 ids={c['sourceId']:c['id'] for c in table['coordinates']}
 assert list(ids)==sorted(active) and list(ids.values())==list(range(len(ids))) and ids[0]==0
 assert all(c['name']==coords[c['sourceId']]['name'] for c in table['coordinates'])
 expected={(s,tuple(ids[v] for v in m)):a for (s,m),a in sos.items()};actual=poly(table['terms'])
 assert actual==expected and degree(actual)==4
 assert all(a.denominator==1 for a in actual.values())
 dependent={m for s,m in actual if s}
 independent=[abs(a.numerator) for (s,m),a in actual.items() if s==0 and m not in dependent]
 assert reduce(math.gcd,independent,0)==1
 parameter=any(s for s,m in actual)
 return {'coordinates':len(coords),'residuals':len(ir['residuals']),'degree':4,'monomials':len({m for s,m in actual}),'formalCoefficientTerms':len(actual),'content':1,'maximumCoefficientBits':None if parameter else max(abs(a.numerator).bit_length() for a in actual.values()),'polynomialSha256':sha(directory/'polynomial/polynomial.json')}
def check_lift(small,large):
 sc={c['id']:c for c in small['coordinates']};lc={c['id']:c for c in large['coordinates']}
 meta=large['constantChain'];chain=meta['coordinates'];exponents=meta['coefficientExponents']
 match=re.fullmatch(r'3\^([1-9]\d*)',small['fixedParameter']['value']);assert match
 target=int(match[1]);assert meta['kind']=='scaled-squaring-v1'
 assert meta['targetExponent']==target and len(chain)==len(exponents)>0
 assert all(isinstance(e,int) and 0<=e<=100000 for e in exponents)
 # Independent closed form, instead of the producer's recursive exponent update.
 assert sum(e*2**(len(exponents)-1-i) for i,e in enumerate(exponents))==target
 assert not (set(chain)&set(sc)) and set(lc)==set(sc)|set(chain)
 assert all(lc[x]==c for x,c in sc.items()) and all(lc[x]['protected'] for x in chain)
 rows={r['id']:poly(r['terms']) for r in large['residuals']}
 for r in small['residuals']:
  expected={}
  for (s,m),a in poly(r['terms']).items():
   assert s in (0,1) and len(m)+s<=2
   k=0,tuple(sorted(m+((chain[-1],) if s else ())))
   expected[k]=expected.get(k,Q(0))+a
  assert rows.pop(r['id'])==expected
 for k,v in enumerate(chain):
  expected={(0,(v,)):Q(1),(0,() if k==0 else (chain[k-1],chain[k-1])):Q(-3**exponents[k])}
  assert rows.pop(f'constant-chain-{k}')==expected
 assert not rows
 return {'coefficientExponents':exponents,'targetExponent':target,'additionalCoordinates':len(chain),'uniqueExtension':True,'valueOfLastCoordinate':small['fixedParameter']['value'],'allLiftedResidualDegreesAtMostTwo':True}
def check_grouping(d, expected_assertions):
 # Independent expansion by subset masks, in Z[Y_1,...,Y_n,q].
 out={}
 for n,blocks in [(8,[4,4]),(6,[3,3])]:
  p={0:1};offset=0
  for size in blocks:
   b={mask<<offset:1 for mask in range(1<<size)};q={}
   for m,a in p.items():
    for k,c in b.items():assert m&k==0;q[m|k]=q.get(m|k,0)+a*c
   p=q;offset+=size
  assert offset==n and p=={m:1 for m in range(1<<n)}
  out[str(n)]={'blocks':blocks,'expandedMonomials':len(p),'identityVerified':True}
 # Both members of the pair have order12 and share the same weight q.
 pair=multiply({(0,()):Q(1),(0,(0,1)):Q(1)},
               {(0,()):Q(1),(0,(0,2)):Q(1)})
 assert pair=={(0,()):Q(1),(0,(0,1)):Q(1),(0,(0,2)):Q(1),(0,(0,0,1,2)):Q(1)}
 out['uniformPair']={'orders':[12,12],'expandedMonomials':4,'identityVerified':True}
 # These abstract expansions alone do not certify that the source uses them.
 # Bind the separate full reconstruction of the actual tests and all products.
 source=read(d/'detector-source-check.json')
 assert source['status']=='PASS' and source['sourceAssertions']==expected_assertions and source['abstractUniformPairIdentities']==2
 assert source['highOrder']==45 and source['anchor']==read(d/'raw-ir.json')['fixedParameter']['value']
 assert source['abstractLaurentIdentities']==7
 assert source['semanticNormalizationIdentities']==3
 assert source['builderSha256']==sha(d/'builder.cjs') and source['rawIrSha256']==sha(d/'raw-ir.json')
 out['actualSourceReconstruction']={'sourceAssertions':expected_assertions,'abstractUniformPairIdentities':2,
  'builderBindingMatches':True,'rawIrBindingMatches':True,'reportSha256':sha(d/'detector-source-check.json')}
 return out

def check_combined_structure(d,small):
 # The four portable source checkers reconstruct the changed formulas.
 # This small structural check only checks the common interface and guards.
 raw=read(d/'raw-translated-ir.json')
 rc={c['name']:c for c in raw['coordinates']}
 assert rc['input']['id']==0 and rc['input']['protected']
 assert raw['counts']['baseCoordinates']==61
 assert {'lambda.positiveA','lambda.positiveB'} <= set(rc)
 assert not any('.dx0Inverse' in n or '.w0Inverse' in n for n in rc)
 protected={c['name'] for c in small['coordinates'] if c.get('protected')}
 assert {'input','inputProduct.quadratic','anchor.physicalA.quadratic'} <= protected
 assert any('heightProduct.scale0' in n for n in protected)
 return {'inputUnchanged':True,'baseCoordinates':61,'explicitDifferenceGuards':0,'explicitDetectorTraceGuards':0,'protectedInputProduct':True,'scope':'Interface only; complete changed-source equations are checked by the four scripts in audit/.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);ap.add_argument('--detector-assertions',type=int,required=True);a=ap.parse_args();d=a.directory.resolve()
 spec=importlib.util.spec_from_file_location('independent_elimination',d/'tools/verify_elimination.py');V=importlib.util.module_from_spec(spec);spec.loader.exec_module(V)
 V.SOURCE=d/'compiled/compiled-ir.json';V.HERE=d/'final';V.verify()
 small=read(d/'final/integer-candidate-ir.json');meta=small['fixedParameter']
 assert meta['name']=='S' and meta['coordinate'] is False and re.fullmatch(r'3\^([1-9]\d*)',meta['value'])
 weighted=max(len(m)+s for r in small['residuals'] for s,m in poly(r['terms']));assert weighted<=2
 protected=[c['name'] for c in small['coordinates'] if c.get('protected')];assert 'anchor.physicalA.quadratic' in protected and any('heightProduct.scale0' in n for n in protected)
 result={'scope':'Exact elimination, normalized full SOS expansion, coefficient content, current grouped polynomial identities with bound source reconstruction, and unique constant lifts. Arithmetic characterization and packed-anchor number theory are not established by this checker.','groupedPolynomialIdentities':check_grouping(d,a.detector_assertions),'combinedStructure':check_combined_structure(d,small),'eliminationVerified':True,'symbolic':check_table(d/'final',d/'final/integer-candidate-ir.json'),'maximumResidualDegreeAfterReplacingSByCoordinate':weighted,'lifts':{}}
 for folder in sorted(d.glob('ordinary*')):
  if not (folder/'lifted-ir.json').exists():continue
  result['lifts'][folder.name]={'chain':check_lift(small,read(folder/'lifted-ir.json')),'table':check_table(folder,folder/'lifted-ir.json')}
 (d/'independent-full-check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
