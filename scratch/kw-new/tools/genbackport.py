"""genbackport.py TRANS_TXT : generate draft Backport helper files from transitive.py output."""
import sys,os,re,subprocess
sys.path.insert(0,os.path.dirname(__file__))
H=os.path.expanduser('~')
groups={}; cur=None
for line in open(sys.argv[1]):
    if line.startswith('TauCeti.'): cur=line.split()[0]; groups[cur]=[]
    elif line.startswith('    ') and cur: groups[cur].append(line.strip())
HDR='''/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- {m}), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.{m}`.
module

public import ZInQKernel.Contrib.{m}
'''
for m,names in groups.items():
    src=open(H+'/tc-nov01/'+m.replace('.','/')+'.lean',encoding='utf-8').read()
    opens=[l for l in src.split('\n') if re.match(r'^open\b',l)]
    short=[n.split('.')[-1] for n in names]
    ex=subprocess.run(['python3',os.path.dirname(__file__)+'/extract.py',m]+short,capture_output=True,text=True).stdout
    # group blocks by namespace
    sec=(re.search(r'^((?:@\[expose\] )?public (?:noncomputable )?section)',src,re.M) or [None,'public section'])[1]
    if 'noncomputable' not in sec and re.search(r'^noncomputable section\s*$',src,re.M): sec+='\nnoncomputable section'
    out=HDR.replace('{m}',m)+'\n'+sec+'\n\n'
    for blk in ex.split('-- namespace: ')[1:]:
        ns=blk.split('  (')[0].strip(); body=blk.split('\n',1)[1].rstrip()+'\n'
        sc=[l[len('-- scope: '):] for l in body.split('\n') if l.startswith('-- scope: ')]
        body='\n'.join(l for l in body.split('\n') if not l.startswith('-- scope: '))
        scs='\n'.join(sc)+'\n\n' if sc else ''
        out+=(f'namespace {ns}\n\n{scs}{body}\nend {ns}\n\n' if ns else f'section\n\n{scs}{body}\nend\n\n')
    out+='end\n'*(2 if sec.count('section')==2 else 1)
    d='ZInQKernel/Contrib/TauCeti/Backport/'+'/'.join(m.split('.')[1:])+'.lean'
    os.makedirs(os.path.dirname(d),exist_ok=True)
    if os.path.exists(d) and '--force' not in sys.argv: print('exists',d); continue
    open(d,'w').write(out); print('wrote',d)
