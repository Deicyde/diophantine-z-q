# Assembles scratch/h-decomposition/Leaves.lean from the reports' compiled drafts.
root='/home/jackmccarthy/dzq-wt/hsyn/'
def body(path, ren=None):
    L=open(root+path).read().split('\n')
    last=max(i for i,l in enumerate(L) if l.startswith('import '))
    out=[l for l in L[last+1:] if not l.startswith('#print')]
    if sum(l.strip()=='noncomputable section' for l in out) > sum(l.strip()=='end' for l in out): out.append('end')
    if ren:
        out=[l.replace(ren[0],ren[1]) for l in out]
    return '\n'.join(out)
parts=[open(root+'scratch/hsyn/head.lean').read()]
srcs=[('PkgI1','scratch/pkg-I1/I1.lean'),('PkgI2','scratch/pkg-I2/I2.lean'),
      ('PkgI3','scratch/pkg-I3/I3.lean'),('PkgI4','scratch/pkg-I4/I4.lean'),('PkgI6','scratch/pkg-I6/I6.lean'),
      ('CondBreaks','scratch/glue-conductor/Breaks.lean'),('CondDyadic','scratch/glue-conductor/Dyadic.lean'),
      ('CondLevel','scratch/glue-conductor/Level.lean'),('Assembly','scratch/glue-assembly/GlueAssembly.lean'),('AsmC8','scratch/glue-assembly/C8.lean'),('AsmE1','scratch/glue-assembly/E1Lin.lean'),('AsmE2','scratch/glue-assembly/E2Index.lean'),('AsmF3','scratch/glue-assembly/F3Glue.lean')]
srcs+=[('Desc'+f,'scratch/glue-descent/%s.lean'%f) for f in ['ProjRep','B1Quat','Cochain','Constants','Chi','B2Glue','B2Assembly','B3Assembly']]
srcs+=[('Repo'+f,'scratch/glue-repo/%s.lean'%f) for f in ['A1Quaternion','TorsionFree','PRArith','Numerics']]
for tag,f in srcs:
    ren=('PkgI3','PkgI4.I3') if tag=='PkgI4' else None
    note=' The copy of pkg-I3 inside it is renamed `PkgI4.I3`.' if ren else ''
    parts.append('section %sSec\n/-! ### Copied from `%s` (compiled there).%s -/\n'%(tag,f,note)+body(f,ren)+'\nend %sSec\n'%tag)
fa=open(root+'scratch/hdec-faithful/Leaves.lean').read()
s=fa.index('noncomputable section'); e=fa.index('/-! ## §2.')
core=fa[s:e].replace('namespace HDec','namespace HSyn')
core=core.replace('/-! ## §1. Leaves statable today (not proved here) -/','/-! ## §1. Leaves statable today over the cheap definitions (not proved here; copied from the\nhdec-faithful draft). Numbering of the note: T13 Skolem–Noether, T14 HasseBrauerQ, T17\nKronecker–Weber, T18 FrobeniusDense, T19 Brauer–Nesbitt, R14 EigenformRepExists, R15\nDeligneSerreConseq, T24 EigenformTwist. -/')
parts.append(core)
parts.append(open(root+'scratch/hsyn/tail.lean').read())
open(root+'scratch/h-decomposition/Leaves.lean','w').write('\n'.join(parts))
