from pathlib import Path
import json,re,hashlib,difflib,unicodedata
ROOT=Path('/tmp/quartic214-manuscript-20261112');OUT=Path(__file__).parent
m=json.loads((ROOT/'research/quartic214-manuscript-revision2/SOURCE_SPANS.json').read_text());tl=(ROOT/'research/quartic214-manuscript-revision2/quartic214.tex').read_text().splitlines()
corr={(c['source'],c['source_line']):c['corrected_line']for c in json.loads((ROOT/'research/quartic214-manuscript/SOURCE_CORRECTIONS_V1.json').read_text())['corrections']};ov=json.loads((ROOT/'research/quartic214-manuscript-revision2/RECEIVING_OVERLAY.json').read_text());corr[ov['f6']['source'],57]=ov['f6']['corrected_source_line']
symbol={'α':'alpha','β':'beta','γ':'gamma','δ':'delta','ε':'epsilon','η':'eta','θ':'theta','κ':'kappa','λ':'lambda','μ':'mu','ν':'nu','π':'pi','ρ':'rho','σ':'sigma','τ':'tau','φ':'phi','χ':'chi','ω':'omega','Γ':'Gamma','Δ':'Delta','Θ':'Theta','Σ':'Sigma','Ω':'Omega','ℓ':'ell','𝒳':'X','ĥ':'h','²':'^2','³':'^3','⁴':'^4','¹':'^1','−':'-','–':'-','—':'-','′':"'",'’':"'",'‘':"'",'“':'"','”':'"','…':'...','§':'section','→':'->','↦':'mapsto','≠':'!=','≤':'<=','≥':'>=','∈':'in','⊂':'subset','⊃':'supset','⊗':'tensor','⊕':'directsum','∩':'intersection','∪':'union','∞':'infinity','≅':'cong','±':'+-','×':'times','∏':'product','∑':'sum','∧':'wedge','∫':'integral','∖':'setminus','⇔':'iff','⇒':'implies','∣':'|','·':'*','⌊':'floor','⌋':'floor'}
macro={'to':'->','mapsto':'mapsto','ne':'!=','le':'<=','ge':'>=','in':'in','subset':'subset','supset':'supset','otimes':'tensor','oplus':'directsum','cap':'intersection','cup':'union','infty':'infinity','cong':'cong','pm':'+-','times':'times','prod':'product','sum':'sum','wedge':'wedge','int':'integral','setminus':'setminus','Longleftrightarrow':'iff','Longrightarrow':'implies','mid':'|','cdot':'*','lfloor':'floor','rfloor':'floor','S':'section','ldots':'...','textbackslash':'','textasciicircum':'^','textasciitilde':'~','sim':'~'}
fmt=r'(?:operatorname|text|mathrm|mathbf|mathbb|mathcal|mathfrak|widehat|bar|overline|ensuremath|textbf|emph|footnotesize|small|noindent|par|medskip|clearpage|section|subsection|subsubsection|paragraph|item|endhead|toprule|midrule|bottomrule|raggedright|begingroup|endgroup|nolinkurl|url)'
def canon(s,is_tex=False):
 if not is_tex:
  s=re.sub(r'\[([^\]]+)\]\(([^\s]+)\)',r'\1',s)
  s=re.sub(r'<(https?://[^>]+)>',r'\1',s)
  s=s.replace('**','');s=re.sub(r'(?<!\w)\*([^*]+)\*(?!\w)',r'\1',s)
  s=s.replace('`','');s=re.sub(r'^\s*(?:#+|[-*])\s*','',s,flags=re.M)
  s=s.replace('direct-sum','directsum')
 else:
  s=re.sub(r'\\href\{[^{}]*\}\{([^{}]*)\}',r'\1',s)
  s=re.sub(r'\\(?:begin|end)\{(?:gather\*|quote|itemize|longtable)\}(?:\{[^\n]*\})?','',s)
  s=re.sub(r'\\label\{[^}]*\}','',s)
  s=re.sub(r'\\tag\{([^}]*)\}',r'(\1)',s)
  s=re.sub(r'\\'+fmt+r'\b','',s)
  s=re.sub(r'\\([A-Za-z]+)',lambda z:macro.get(z[1],z[1]),s)
  s=s.replace(r'\(', '').replace(r'\)','').replace(r'\[','').replace(r'\]','').replace(r'\\','')
  s=s.replace(r'\,','').replace(r'\;','').replace(r'\!','').replace(r'\#','#').replace(r'\&','&')
 for a,b in symbol.items():s=s.replace(a,b)
 s=s.replace('sqrt','ROOT').replace('√','ROOT')
 # Content-only comparison: grouping/script scope is deliberately reviewed separately.
 s=re.sub(r'[\s{}()\[\]_$`".,;:#&\\]','',s)
 s=s.replace('--','-')
 return s
rows=[]
for sp in m['spans']:
 src=sp.get('source','');method=sp['method']
 if src not in {x['path']for x in json.loads((OUT/'INITIAL_TRANSFORMS.json').read_text())['converted_proof_sources']}:continue
 if method in ['paragraph-break']:continue
 if 'source_lines'not in sp:continue
 a,b=sp['source_lines'];lines=(ROOT/src).read_text().splitlines();ss='\n'.join(corr.get((src,n),lines[n-1])for n in range(a,b+1));c,d=sp['tex_lines'];tt='\n'.join(tl[c-1:d])
 if Path(src).name in ['height-different.md','height-metric.md','aggregate-bridge.md']:ss=ss.replace('Σ','∑')
 if Path(src).name in ['aggregate-bridge.md','uniform-existence.md']:ss=ss.replace('F+','F_{+}')
 if Path(src).name=='uniform-existence.md':ss=ss.replace('mathfrak_b',r'\mathfrak{b}')
 if Path(src).name=='height-averaging.md'and'J_0 = C_1 x ... x C_r x E'in ss:ss=ss.replace(' x ',' × ')
 if Path(src).name=='height-metric.md':ss=ss.replace('p*ω','p_*ω').replace('barη',r'\overline{η}').replace('dbar t',r'd\overline{t}').replace('P1_t','P^1_t')
 if Path(src).name in ['height-evaluation.md','height-different.md']:ss=re.sub(r'\bP1\b','P^1',ss)
 ss=re.sub(r'\bH0\(','H^0(',ss)
 aa,bb=canon(ss),canon(tt,True);diff=[]
 if aa!=bb:
  for tag,i,j,k,l in difflib.SequenceMatcher(None,aa,bb,autojunk=False).get_opcodes():
   if tag!='equal':diff.append({'source':aa[max(0,i-25):min(len(aa),j+25)],'target':bb[max(0,k-25):min(len(bb),l+25)]})
 rows.append({'source':src,'source_lines':[a,b],'tex_lines':[c,d],'method':method,'content_equal':aa==bb,'diff':diff})
(OUT/'LEXICAL_COMPARISON.json').write_text(json.dumps({'scope':'Independent content-skeleton comparison only. Grouping, scripts and mathematical semantics require separate inspection. Differences are candidates, not established defects.','rows':rows},indent=2)+'\n')
print('rows',len(rows),'equal',sum(x['content_equal']for x in rows),'different',sum(not x['content_equal']for x in rows))
for x in rows:
 if x['diff']:print(Path(x['source']).name,x['source_lines'],x['diff'])
