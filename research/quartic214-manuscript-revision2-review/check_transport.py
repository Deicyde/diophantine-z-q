from pathlib import Path
import json,re,hashlib
R=Path('/tmp/quartic214-manuscript-20261112');O=Path(__file__).parent
rev=R/'research/quartic214-manuscript-revision2';t=(rev/'quartic214.tex').read_text().splitlines();m=json.loads((rev/'SOURCE_SPANS.json').read_text());h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Read and reuse the prior independent exact inverse parser, with only its receiving-directory changed.
s=(R/'research/quartic214-manuscript-review/check_serialization.py').read_text().replace("root=Path.cwd()",'root=R').replace('research/quartic214-manuscript/','research/quartic214-manuscript-revision2/')
ns={'R':R};exec(compile(s,'prior-independent-inverse-parser','exec'),ns)
sp=m['spans'];ir=json.loads((R/'research/quartic214/construction/artifacts/candidate214-brox/candidate214-ir.json').read_text());cs=next(x for x in sp if x['method']=='complete-coordinate-dictionary');a,b=cs['tex_lines'];cr=[]
for l in t[a-1:b]:
 z=re.fullmatch(r'(\d+) & \\nolinkurl\{([^}]+)\} & (\d+)\\\\',l)
 if z:cr.append((int(z[1]),z[2],int(z[3])))
assert cr==[(x['id'],x['name'],x['parent224Id'])for x in ir['coordinates']]
assert len(cr)==214
fr=[]
for x in sp:
 if not x['method'].startswith('retained-tex;'):continue
 original=(R/x['source']).read_text();a,b=x['tex_lines'];actual='\n'.join(t[a-1:b]);prefix='q214brox:'if'evaluation-'in x['source']else'q214factor:'
 # Discover the declared namespace from the first local label and verify that ONE prefix applies to every label/ref.
 label=re.search(r'\\label\{([^}]+)\}',original)
 if label:
  al=re.search(r'\\label\{([^}]+)\}',actual);assert al[1].endswith(label[1]);prefix=al[1][:-len(label[1])]
 expect=re.sub(r'\\(label|ref|eqref)\{([^}]+)\}',lambda z:'\\'+z[1]+'{'+prefix+z[2]+'}',original).replace('\\section{','\\subsection{')
 for key in ['Javanpeykar','vonKaenel','Stacks','Serre']:expect=expect.replace('{'+key+'}','{v15-height-'+key+'}')
 expect=expect.replace('~\\cite{Logs}','~Section~\\ref{v15:logs}')
 
 assert expect.rstrip('\n').splitlines()==actual.rstrip('\n').splitlines(),x['source']
 fr.append({'path':x['source'],'sha256':h(R/x['source']),'lines':len(original.splitlines()),'label_prefix':prefix,'exact_except_declared_aliases':True})
init=json.loads((O/'INITIAL_TRANSFORMS.json').read_text());cov=[]
for x in init['converted_proof_sources']:
 p=x['path'];sl=(R/p).read_text().splitlines();covered=[]
 for z in sp:
  if z.get('source')==p and 'source_lines'in z:covered+=list(range(z['source_lines'][0],z['source_lines'][1]+1))
 assert covered==list(range(1,len(sl)+1)),(p,sorted(set(range(1,len(sl)+1))-set(covered)))
 cov.append({'path':p,'sha256':h(R/p),'source_lines':len(sl),'all_lines_mapped_exactly_once':True})
x=next(x for x in sp if x['method']=='authored-introduction-verbatim');a,b=x['tex_lines'];assert(R/x['source']).read_text().splitlines()==t[a-1:b]
natives=[x for x in sp if x['method']=='exact-retained-body-LF'];ranges=sum((list(range(x['source_lines'][0],x['source_lines'][1]+1))for x in natives),[]);assert ranges==[i for i in range(58,39932)if i!=73]
source=(R/'manuscripts/quartic_v16.tex').read_text().splitlines();assert source[72]=='\\tableofcontents';assert source[-1]=='\\end{document}'
result={'tex_sha256':h(rev/'quartic214.tex'),'map_sha256':h(rev/'SOURCE_SPANS.json'),'reused_inverse_parser_source_sha256':h(R/'research/quartic214-manuscript-review/check_serialization.py'),'coordinates_exact_id_name_parent':len(cr),'rows_exact_inverse_parsed':ns['checked'],'terms_exact_inverse_parsed':ns['terms'],'retained_native_lines_exact':ns['retained'],'native_body_unmapped_lines':'title/preamble before58, tableofcontents73, final end-document; only declared wrapper/anchors/operative note are inserted','retained_fragments':fr,'converted_source_line_accounting':cov,'introduction_exact':True,'scope':'Exact transport of listed objects only; no polynomial expansion, source theorem acceptance or rendering claim.'}
(O/'TRANSPORT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in['converted_source_line_accounting','retained_fragments']},indent=2))
