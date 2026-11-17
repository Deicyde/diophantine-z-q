from pathlib import Path
from fractions import Fraction
import argparse,json,sys,hashlib,os,tempfile
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
def sh(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def coefficient_string(co):
 out=''
 for s,a in sorted(co.items(),reverse=True):
  a=int(a);sign='-' if a<0 else '+';v=str(abs(a))
  if s:v+=('*S' if s==1 else '*S^'+str(s))
  if not out:out=('-' if a<0 else '')+v
  else:out+=' '+sign+' '+v
 return out

def write_one(d,folder):
 p=folder/'polynomial/polynomial.json';data=json.loads(p.read_text());n=len(data['coordinates']);groups={}
 for t in data['terms']:
  co=Fraction(t['coefficient']);assert co.denominator==1;m=tuple(t['monomial']);s=t.get('sPower',0)
  groups.setdefault(m,{})[s]=groups.setdefault(m,{}).get(s,0)+co.numerator
 symbolic=any(s for co in groups.values() for s in co)
 out=d/('quartic-'+str(n)+('-symbolic.txt' if symbolic else '-decimal.txt'))
 header=f'# Complete coefficient table for a quartic in {n} total rational variables.\n# x0 is the unchanged input. The polynomial is the sum of coefficient * monomial over all rows.\n'
 if symbolic:header+=f"# {data['fixedParameter']} is a fixed integer coefficient, not a variable.\n"
 else:header+='# Every coefficient is written explicitly in decimal. No symbolic coefficient parameter occurs.\n'
 header+='coefficient\tmonomial\n'
 # Publish only a complete table. The large decimal coefficient can take time
 # to convert; a partially written final path must never look like a deliverable.
 with tempfile.NamedTemporaryFile(mode='w',dir=d,prefix='.'+out.name+'.tmp.',delete=False) as f:
  temporary=Path(f.name)
  f.write(header)
  for m,co in sorted(groups.items()):f.write(coefficient_string(co)+'\t'+('*'.join('x'+str(i) for i in m) if m else '1')+'\n')
  f.flush();os.fsync(f.fileno())
 os.replace(temporary,out)
 # Independently parse this complete table back into numeric coefficient-polynomial terms.
 parsed={}
 import re
 lines=out.read_text().splitlines();lines=[l for l in lines if not l.startswith('#')];assert lines.pop(0)=='coefficient\tmonomial'
 for line in lines:
  a,m=line.split('\t');m=() if m=='1' else tuple(int(v[1:]) for v in m.split('*'))
  # A full token scanner prevents silently dropping malformed characters.
  expression=a.replace(' ','');idx=0
  pat=re.compile(r'([+-]?\d+)(\*S(?:\^(\d+))?)?')
  while idx<len(expression):
   match=pat.match(expression,idx);assert match,(expression,idx)
   c=int(match[1]);s=(int(match[3]) if match[3] else 1) if match[2] else 0
   parsed[(s,m)]=parsed.get((s,m),0)+c;idx=match.end()
 expected={(s,m):a for m,co in groups.items() for s,a in co.items()};assert parsed==expected
 largest=None if symbolic else max(abs(a) for co in groups.values() for a in co.values())
 return {'coordinates':n,'monomials':len(groups),'textBytes':out.stat().st_size,'textSha256':sh(out),'file':out.name,'maximumCoefficientBits':None if symbolic else largest.bit_length(),'maximumCoefficientDigits':None if symbolic else len(str(largest)),'constantCoefficient':str(groups.get((),{}).get(0,0)) if not symbolic and len(str(groups.get((),{}).get(0,0)))<2000 else 'See full table'}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);a=ap.parse_args();d=a.directory.resolve();out={'tables':[write_one(d,d/'final')]}
 for folder in sorted(d.glob('ordinary*')):
  if (folder/'polynomial/polynomial.json').exists():out['tables'].append(write_one(d,folder))
 (d/'text-table-summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
