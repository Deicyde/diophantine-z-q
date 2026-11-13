# Generates Bundle5.lean: import TailF + g0-assemble3's olean/TailD.lean body + CPtsTransport.lean + BCUnique.lean
# (minus imports/#check) + GluePieces5 (GluePieces4 of parts/z95_bundle4.lean minus two fields).
import re
taild=open('/home/jackmccarthy/dzq-wt/g0-assemble3/scratch/g0-assemble3/olean/TailD.lean').read()
assert taild.startswith('import TailF\n')
body=taild[len('import TailF\n'):]
def strip(s):
    return '\n'.join(l for l in s.split('\n') if not (l.startswith('import ') or l.startswith('#check')
                     or l.startswith('#print GlueAssembly')))
t1=strip(open('CPtsTransport.lean').read()); t2=strip(open('BCUnique.lean').read())
lines=open('../g0-assemble3/parts/z95_bundle4.lean').read().split('\n')
i=next(k for k,l in enumerate(lines) if l.startswith('structure GluePieces4'))
j=next(k for k in range(i,len(lines)) if lines[k]=='')
st=lines[i+1:j]
fpat=re.compile(r'^  (?:/--.*-/\s*)?([A-Za-z0-9_]+) : ')
chunks=[]; cur=[]; curf=None
for l in st:
    if (l.startswith('  /--') or l.startswith('  --')) and curf is not None:
        chunks.append((curf,cur)); cur=[]; curf=None
    cur.append(l)
    m=fpat.match(l)
    if m: curf=m.group(1)
chunks.append((curf,cur))
fields=[f for f,_ in chunks]
assert len(fields)==46 and None not in fields, fields
drop={'baseChangeClassUnique','cPtsTransport'}
kept=[f for f in fields if f not in drop]
gp5='structure GluePieces5 : Prop where\n'+'\n'.join(l for f,c in chunks if f not in drop for l in c)
assign=',\n    '.join(f'{f} := gp.{f}' for f in kept)
bundle=open('bundle5_tail.lean.in').read().replace('@GP5@',gp5).replace('@ASSIGN@',assign)
hdr=open('bundle5_head.lean.in').read()
open('Bundle5.lean','w').write(hdr+body+'\nsection CPtsTransportSec\n'+t1+'\nend\n\nend CPtsTransportSec\n\nsection BCUniqueSec\n'+t2+'\nend\n\nend BCUniqueSec\n'+bundle)
print(len(kept),'fields kept')
