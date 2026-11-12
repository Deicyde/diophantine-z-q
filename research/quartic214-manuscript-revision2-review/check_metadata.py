from pathlib import Path
import json,re,hashlib
R=Path('/tmp/quartic214-manuscript-20261112');O=Path(__file__).parent
M=json.loads((R/'research/quartic214-manuscript-revision2/SOURCE_SPANS.json').read_text());T=(R/'research/quartic214-manuscript-revision2/quartic214.tex').read_text().splitlines();S=next(x for x in M['spans']if x['method']=='complete-recursive-primary-source-catalogue');j=json.loads((R/S['source']).read_text());source=[]
def walk(a):
 if isinstance(a,dict):
  for k,v in a.items():
   if isinstance(v,(dict,list)):walk(v)
   else:source.append((k,v))
 elif isinstance(a,list):
  for v in a:
   if isinstance(v,(dict,list)):walk(v)
   else:source.append((None,v))
walk(j)
def decode(s):
 s=s.replace('\\allowbreak{}','')
 for cmd,ch in [('\\pi ','π'),('\\to ','→'),('\\mapsto ','↦'),('\\Longrightarrow ','⇒')]:s=s.replace('\\ensuremath{'+cmd+'}',ch)
 s=re.sub(r'\\(?:url|nolinkurl)\{(.*)\}',r'\1',s)
 for a,b in [('\\S{}','§'),('\\textbackslash{}','\\'),('\\textasciicircum{}','^'),('\\textasciitilde{}','~')]:s=s.replace(a,b)
 for ch in '{}$&#%_^':s=s.replace('\\'+ch,ch)
 return s.replace('---','-').replace('--','-').replace('–','-').replace('−','-')
actual=[]
for s in T[S['tex_lines'][0]-1:S['tex_lines'][1]]:
 z=re.fullmatch(r'\\noindent\\textbf\{(.*?)\}: (.*)\\par',s)
 if z:actual.append((decode(z[1]),decode(z[2])))
 else:
  z=re.fullmatch(r'\\noindent \$\\bullet\$ (.*)\\par',s)
  if z:actual.append((None,decode(z[1])))
expected=[(k,decode('true'if v is True else'false'if v is False else'null'if v is None else str(v)))for k,v in source]
assert actual==expected,[(a,b)for a,b in zip(actual,expected)if a!=b][:3]
out={'source':S['source'],'source_sha256':hashlib.sha256((R/S['source']).read_bytes()).hexdigest(),'metadata_scalar_entries_in_original_order':len(source),'all_keys_values_preserved':True,'normalization':'TeX text escapes, invisible allowbreak, Unicode math glyphs; en-dash/minus/hyphen normalized for displayed-text comparison','scope':'Literal metadata transport only; old inspection statements remain attributed historical evidence, not fresh reviewer reading of publications.'}
(O/'METADATA_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
