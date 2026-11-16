"""Print the frozen unbalanced 198 table as standalone, readable TeX."""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
WORK=HERE.parents[2]
SOURCE=WORK/'v18-198-dependency-inventory-20261114/package/H10-quartic198/circuits/inverse198'
source=SOURCE/'quadratic.json';poly=SOURCE/'polynomial.json'
d=json.loads(source.read_text())
assert sha256(source.read_bytes()).hexdigest()=='c55d7eefe41f62fee88b467e3ea8f6be8ba1e66f6a94b30eb74b39f6f6e7efad'
large=sorted({abs(int(t['coefficient'])) for r in d['residuals'] for t in r['terms'] if len(str(abs(int(t['coefficient']))))>8})
aliases={v:i+1 for i,v in enumerate(large)}
def esc(name):
    assert set(name)<=set('abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._-')
    return name.replace('_',r'\_').replace('.',r'.\allowbreak{}')
def coefficient(v):
    v=abs(v)
    return (r'\mathsf{k}_{'+str(aliases[v])+'}') if v in aliases else str(v)
def term(t):
    c=int(t['coefficient']);parts=[];width=0
    a=int(t['parameterPower']);powers=Counter(t['monomial'])
    if abs(c)!=1 or (not powers and not a):
        parts.append(coefficient(c));width+=8 if abs(c) in aliases else len(str(abs(c)))
    if a:parts.append('A' if a==1 else 'A^{'+str(a)+'}');width+=2
    for i,e in sorted(powers.items()):
        parts.append('Y_{'+str(i-1)+'}'+('^{'+str(e)+'}' if e!=1 else ''))
        width+=5+(2 if e!=1 else 0)
    return ('-' if c<0 else '+'),''.join(parts),width+2
def blocks(integer):
    # Base-10 expansion into at most 30-digit integers. Every term is explicit.
    digits=str(integer);parts=[]
    for end in range(len(digits),0,-30):
        start=max(0,end-30);value=int(digits[start:end]);power=len(digits)-end
        if value:parts.append(str(value)+(r'\cdot 10^{'+str(power)+'}' if power else ''))
    return list(reversed(parts))

out=[r'% Generated only from the frozen unbalanced Conant 198 table.',
     r'% Root supplies the surrounding heading and label q198:rows.',
     r'% Required packages: amsmath, longtable. No preamble or document class.',
     '% Source quadratic SHA-256: '+sha256(source.read_bytes()).hexdigest(),
     '% Source quartic SHA-256: '+sha256(poly.read_bytes()).hexdigest(),
     r'\begingroup',r'\allowdisplaybreaks[1]',
     r'This is the unbalanced 198-coordinate specification of Gabriel Conant,',
     r"obtained from Jos\'e Brox's 204-coordinate family through the affine",
     r'odd-fourth-label intermediate.  The source quadratic table has SHA-256',
     r'\begin{center}\small\ttfamily',sha256(source.read_bytes()).hexdigest(),r'\end{center}',
     r'The variables are $\mathbf Y=(Y_0,\ldots,Y_{197})$, with $Y_0=x$ the input.',
     r'The integer $A$ is a fixed coefficient, not a coordinate; the designated',
     r'family uses $A=149^{2N+1}$ for an integer $N\geq1$.  Each residual below',
     r'is an integral quadratic polynomial in $\mathbf Y$.  The polynomial',
     r'specified by this table is',
     r'\[',r'\mathcal P_{198,A}(\mathbf Y)=',
     r'\sum_{i=1}^{184}\bigl(q_i^{[198]}(\mathbf Y;A)\bigr)^2.',r'\]',
     r'Every displayed coordinate is quantified except the distinguished input',
     r'$Y_0$; the named integer coefficients below introduce no further variables.',
     r'\paragraph{Coordinate dictionary.}',
     r'The formal identifier $j$ and exponent $e$ record the source convention',
     r'$\xi_j=R^eY_i$, with $R=Y_{115}$.  Names are retained verbatim as source',
     r'identifiers.  The displayed residuals, rather than these names, define',
     r'the polynomial.  The dictionary lists all 198 coordinates.',
     r'{\small',r'\setlength{\tabcolsep}{4pt}',
     r'\begin{longtable}{@{}r r r p{0.64\linewidth}@{}}',
     r'\caption{Complete coordinate dictionary for the unbalanced 198 table.}',
     r'\label{q198:coordinates}\\',r'\hline',
     r'Variable & Formal $j$ & $e$ & Source name \\',r'\hline',r'\endfirsthead',
     r'\multicolumn{4}{l}{\emph{Coordinate dictionary, continued.}}\\',
     r'\hline',r'Variable & Formal $j$ & $e$ & Source name \\',r'\hline',r'\endhead',
     r'\hline\multicolumn{4}{r}{\emph{Continued on the next page.}}\\',r'\endfoot',
     r'\hline',r'\endlastfoot']
for co in d['coordinates']:
    out.append(r'\(Y_{'+str(co['id']-1)+r'}\) & '+str(co['formalId'])+' & '+str(co['rescalingExponent'])+r' & \texttt{'+esc(co['name'])+r'} \\')
out += [r'\end{longtable}',r'}',r'\paragraph{Explicit integer coefficients.}',
        r'The following positive integers abbreviate long coefficients.  Powers',
        r'of ten are part of their explicit integer definitions.  No coefficient',
        r'is defined recursively and none depends on $A$ or on a coordinate.']
for value,index in aliases.items():
    bb=blocks(value)
    out += [r'\[',r'\begin{aligned}',r'\mathsf{k}_{'+str(index)+r'} &={} '+bb[0]+(r'\\' if len(bb)>1 else '')]
    for j,b in enumerate(bb[1:]):out.append(r'&{}+ '+b+(r'\\' if j<len(bb)-2 else ''))
    out += [r'\end{aligned}',r'\]']
out += [r'\paragraph{The 184 quadratic residuals.}',
        r'Write $q_i^{[198]}$ for $q_i^{[198]}(\mathbf Y;A)$.  The equations',
        r'of the system are $q_i^{[198]}=0$ for $1\leq i\leq184$.']
for row in d['residuals']:
    i=row['id'];lines=[];line='';width=0
    for t in row['terms']:
        sign,value,tw=term(t)
        if line and width+tw>65:
            lines.append(line);line='';width=0
        if not line and not lines and sign=='+':line=value
        else:line+=((' '+sign+' ') if line else (sign+' '))+value
        width+=tw
    if line:lines.append(line)
    out += ['% Source residual '+str(i)+': '+row['name'],
            r'\begin{equation}\label{q198:row:'+str(i).zfill(3)+'}',r'\begin{aligned}',
            r'q_{'+str(i)+r'}^{[198]} &={} '+lines[0]+(r'\\' if len(lines)>1 else '')]
    for j,ln in enumerate(lines[1:]):out.append(r'&{} '+ln+(r'\\' if j<len(lines)-2 else ''))
    out += [r'\end{aligned}',r'\end{equation}']
out += [r'\endgroup','']
component=HERE/'q198-rows.tex'
component.write_text('\n'.join(out),encoding='utf-8',newline='\n')
wrapper=r'''\documentclass[10pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage[margin=22mm]{geometry}
\usepackage{amsmath,longtable}
\setlength{\emergencystretch}{2em}
\begin{document}
\section{Exact unbalanced 198-variable row specification}\label{q198:rows}
\input{q198-rows.tex}
\end{document}
'''
(HERE/'preview.tex').write_text(wrapper,encoding='utf-8',newline='\n')
print(json.dumps({'component_sha256':sha256(component.read_bytes()).hexdigest(),
    'rows':len(d['residuals']),'coordinates':len(d['coordinates']),'integer_aliases':len(aliases),
    'root_owned_label':'q198:rows','defined_labels':['q198:coordinates','q198:row:001 through q198:row:184']},indent=2))
