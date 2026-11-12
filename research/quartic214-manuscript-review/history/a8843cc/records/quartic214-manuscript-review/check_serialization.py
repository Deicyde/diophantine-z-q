from pathlib import Path
import json,re,hashlib
root=Path.cwd()
texpath=root/'research/quartic214-manuscript/quartic214.tex'
tex=texpath.read_text().splitlines(); m=json.loads((root/'research/quartic214-manuscript/SOURCE_SPANS.json').read_text())
assert hashlib.sha256(texpath.read_bytes()).hexdigest()==m['output_sha256']
retained=0
for s in m['spans']:
 if s['method']=='exact-retained-body-LF':
  a,b=s['source_lines'];c,d=s['tex_lines']
  assert (root/s['source']).read_text().splitlines()[a-1:b]==tex[c-1:d]
  retained+=b-a+1
ir=json.loads((root/'research/quartic214/construction/artifacts/candidate214-brox/candidate214-ir.json').read_text())
names=[r['name'] for r in ir['coordinates']+ir['residuals']]
for name in names: assert r'\nolinkurl{'+name+'}' in '\n'.join(tex),name
checked=0;terms=0
for s in m['spans']:
 ptr=s.get('source_json_pointer') or ''
 if not ptr.startswith('/residuals/'):continue
 row=ir['residuals'][int(ptr.split('/')[-1])]
 a,b=s['tex_lines']; lines=tex[a-1:b]
 assert str(row['id']) in lines[0]
 termlines=lines[2:-1]
 assert len(termlines)==len(row['terms']),(row['id'],len(termlines),len(row['terms']))
 for line,t in zip(termlines,row['terms']):
  line=line.removesuffix('\\\\ &').strip()
  sign=-1 if line.startswith('-') else 1
  line=line.lstrip('+- ').strip()
  coef=1
  if line.startswith('\\left('):
   end=line.index('\\end{gathered}\\right)')+len('\\end{gathered}\\right)')
   expression=line[:end];line=line[end:].lstrip('\\,')
   blocks=expression[len('\\left(\\begin{gathered}'): -len('\\end{gathered}\\right)')].split('\\\\{}+{}')
   coef=0
   for block in blocks:
    match=re.fullmatch(r'(\d+)(?:\\cdot10\^\{(\d+)\})?',block);assert match,block
    coef+=int(match[1])*10**int(match[2] or 0)
  elif re.match(r'\d',line):
   match=re.match(r'(\d+)',line);coef=int(match[1]);line=line[match.end():].lstrip('\\,')
  assert sign*coef==int(t['coefficient']),(row['id'],sign*coef,t)
  parameter=re.search(r'A_N(?:\^\{(\d+)\})?',line)
  assert (int(parameter[1] or 1) if parameter else 0)==t['parameterPower']
  mon=[]
  for match in re.finditer(r'X_\{(\d+)\}(?:\^\{(\d+)\})?',line):mon += [int(match[1])]*int(match[2] or 1)
  assert sorted(mon)==sorted(t['monomial']),(row['id'],line,t)
  rem=re.sub(r'A_N(?:\^\{\d+\})?|X_\{\d+\}(?:\^\{\d+\})?|\\,','',line)
  assert not rem.strip(),rem
  terms+=1
 checked+=1
assert checked==188
print(json.dumps({'tex_sha256':m['output_sha256'],'retained_foundation_lines_equal':retained,'rows_independently_parsed':checked,'row_terms_parsed':terms,'literal_coordinate_and_row_names':len(names),'scope':'Inverse parse of all displayed row terms and exact LF-retained current foundation transport, not arithmetic theorem validation.'},indent=2))
