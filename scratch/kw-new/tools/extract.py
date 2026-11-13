"""extract.py NOV01_MODULE NAME... : print the nov01 declaration blocks (docstring+attrs+body)
of the given short names. Each block is preceded by '-- namespace: NS' and followed by the
'variable'/'open' commands in scope ('-- scope:' lines)."""
import sys,re,os
mod=sys.argv[1]; names=sys.argv[2:]
path=os.path.expanduser('~/tc-nov01/')+mod.replace('.','/')+'.lean'
L=open(path,encoding='utf-8').read().split('\n')
KW=r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)'
scopes=[['file','',[]]]
def block_start(i):
    j=i
    while j>0 and L[j-1].strip()!='' and (L[j-1].rstrip().endswith(' in') or not re.match(r'^\s*(end|namespace|section|variable|open|noncomputable section|public)\b',L[j-1])):
        j-=1
    return j
def cmd_end(i):
    e=i+1
    while e<len(L) and L[e][:1] in (' ','\t') and L[e].strip(): e+=1
    return e
out=[]; i=0; incomment=False
while i<len(L):
    line=L[i]
    if line.startswith('/-') and not line.startswith('/--') and '-/' not in line:
        while i<len(L) and '-/' not in L[i]: i+=1
        i+=1; continue
    m=re.match(r'^namespace\s+(\S+)',line)
    if m: scopes.append(['ns',m.group(1),[]]); i+=1; continue
    m=re.match(r'^(?:public\s+)?(?:noncomputable\s+)?section\b\s*(\S*)',line)
    if m: scopes.append(['sec',m.group(1),[]]); i+=1; continue
    m=re.match(r'^end\b',line)
    if m and len(scopes)>1: scopes.pop(); i+=1; continue
    if re.match(r'^(variable|open|universe|attribute \[local|local notation|scoped|set_option)\b',line) and not L[cmd_end(i)-1].rstrip().endswith(' in'):
        e=cmd_end(i); scopes[-1][2].append('\n'.join(L[i:e])); i=e; continue
    m=re.match(r'^\s*(?:(?:private|protected|noncomputable|nonrec)\s+)*'+KW+r'\s+([^\s:({\[]+)',line)
    if m and (m.group(1) in names or m.group(1).split('.')[-1] in names):
        s=block_start(i); e=i+1
        while e<len(L) and not (L[e].strip()=='' and (e+1>=len(L) or (L[e+1][:1] not in (' ','')))): e+=1
        ns='.'.join(x[1] for x in scopes if x[0]=='ns')
        out.append(f'-- namespace: {ns}  (nov01 line {s+1})')
        for sc in scopes:
            for c in sc[2]: out.append('-- scope: '+c.replace('\n','\n-- scope: '))
        out.extend(L[s:e]); out.append('')
        i=e; continue
    i+=1
print('\n'.join(out))
