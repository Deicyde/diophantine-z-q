"""Generate FoldCheck.lean: the H chain from TailZ23 to TailZ45 re-run with the research field
`sga3_VIB_3_10` / `sga3_VIB_3_10_Nbhd` replaced by `SGA3Nbhd.SGA3_VIB_3_10_NeronOL` (copies in namespace
HDec.HSyn.NOL; unqualified names resolve to the copies first)."""
import re, sys
H='ZInQKernel/OneProof/H/'
KEY=re.compile(r'^(/--|structure |theorem |def |noncomputable |open .* in$|@\[)')
def hsyn_blocks(path):
    L=open(path).read().split('\n')
    try:
        a=L.index('namespace HSyn'); b=len(L)-1-L[::-1].index('end HSyn')
    except ValueError:
        return []
    body=L[a+1:b]
    blocks=[]; cur=[]; pending=False
    for ln in body:
        if KEY.match(ln):
            if cur and not pending:
                blocks.append('\n'.join(cur)); cur=[]
            pending = ln.startswith('/--') or (ln.startswith('open ') and ln.endswith(' in'))
            if ln.startswith('/--') and not ln.rstrip().endswith('-/'):
                pending=True
            cur.append(ln)
            if ln.startswith('/--') and ln.rstrip().endswith('-/'):
                pending=True
        else:
            cur.append(ln)
            if pending and (ln.rstrip().endswith('-/')):
                pending=True
            elif pending and cur and not cur[0].startswith('/--') and not cur[0].startswith('open '):
                pending=False
        # a docstring chunk stays pending until a declaration keyword line arrives
        if cur and KEY.match(ln) and not (ln.startswith('/--') or (ln.startswith('open ') and ln.endswith(' in'))):
            pending=False
    if cur: blocks.append('\n'.join(cur))
    return blocks
def name_of(b):
    if b.startswith('namespace SGRFold'): return 'SGRFold'
    m=re.search(r'^(structure|theorem|def) (\S+)',b,re.M)
    return m.group(2) if m else None
def sgr_blocks():
    L=open('ZInQKernel/Contrib/OneProof/SGRFold.lean').read().split('\n')
    a=L.index('namespace SGRFold'); b=L.index('end SGRFold')
    return ['namespace SGRFold\n\n'+'\n'.join(L[a+1:b])+'\nend SGRFold']
blocks=[]
for k in range(23,46):
    for b in hsyn_blocks(f'{H}TailZ{k}.lean'):
        if b.strip(): blocks.append((k,b))
    if k==35:
        for b in sgr_blocks(): blocks.append(('SGRFold',b))
copied={f'OpenResearchLeaves{k}' for k in range(14,29)}
sel=set()
changed=True
while changed:
    changed=False
    for i,(k,b) in enumerate(blocks):
        n=name_of(b)
        if i in sel or n is None: continue
        if n in copied or any(re.search(r'(?<![\w.])'+re.escape(c)+r'(?![\w])',b) for c in copied):
            sel.add(i); copied.add(n); changed=True
MODE = sys.argv[2] if len(sys.argv) > 2 else 'remove'
RN=[
 ("  sga3_VIB_3_10 : _root_.CToPrinted.SGA3_VIB_3_10","  sga3_VIB_3_10_NeronOL : _root_.SGA3Nbhd.SGA3_VIB_3_10_NeronOL"),
 ("  sga3_VIB_3_10_Nbhd : _root_.SGA3IdComp.SGA3_VIB_3_10_Nbhd","  sga3_VIB_3_10_NeronOL : _root_.SGA3Nbhd.SGA3_VIB_3_10_NeronOL"),
 ("  sga3_VIB_3_10 := n.sga3_VIB_3_10\n","  sga3_VIB_3_10_NeronOL := n.sga3_VIB_3_10_NeronOL\n"),
 ("  sga3_VIB_3_10_Nbhd := n.sga3_VIB_3_10_Nbhd\n","  sga3_VIB_3_10_NeronOL := n.sga3_VIB_3_10_NeronOL\n"),
 ("  sga3_VIB_3_10 := _root_.SGA3IdComp.sga3_VIB_3_10_of_nbhd n.sga3_VIB_3_10_Nbhd _root_.geomConnOfRationalPoint_proof\n","  sga3_VIB_3_10_NeronOL := n.sga3_VIB_3_10_NeronOL\n"),
 ("_root_.CToPrinted.semistableNeronBaseChange_of_printed_full r.blr_1_2_4\n    r.sga3_VIB_3_10 r.sga7_IX_3_3","_root_.SGA3Nbhd.semistableNeronBaseChange_of_NeronOL r.blr_1_2_4\n    r.sga3_VIB_3_10_NeronOL r.sga7_IX_3_3"),
 ("_root_.SGA7PersistsNF.sga7_IX_3_3_of_SH n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization n.sga3_VIB_3_10 t.geomConnOfRationalPoint","_root_.SGA3Nbhd.NF.sga7_IX_3_3_of_SH' n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint"),
 ("_root_.GapPersists.semistablePersistsSHcp_of_SH n.sga3_VIB_3_10 n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint","_root_.SGA3Nbhd.Persists.semistablePersistsSHcp_of_SH' n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint"),
 ("_root_.DictModels.SGA7Pre.sga7_IX_3_3_SH_of_pre n.sga7_IX_3_3_SHpre (_root_.SGA3IdComp.sga3_VIB_3_10_of_nbhd n.sga3_VIB_3_10_Nbhd _root_.geomConnOfRationalPoint_proof) _root_.geomConnOfRationalPoint_proof","_root_.SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre' n.sga7_IX_3_3_SHpre _root_.geomConnOfRationalPoint_proof"),
]
RR=[
 ("  /-- gt-sga3, narrowed: SGA 3 VI_B 3.10 in neighbourhood form: for a smooth group scheme G over any S and every s in S, some open neighbourhood of e(s) lies in the identity component G^0 (numbers UNVERIFIED). With GeomConnOfRationalPoint (proved) gives SGA3_VIB_3_10 (SGA3IdComp.sga3_VIB_3_10_of_nbhd). -/\n",""),
 ("  sga3_VIB_3_10 : _root_.CToPrinted.SGA3_VIB_3_10\n",""),
 ("  sga3_VIB_3_10_Nbhd : _root_.SGA3IdComp.SGA3_VIB_3_10_Nbhd\n",""),
 ("  sga3_VIB_3_10 := n.sga3_VIB_3_10\n",""),
 ("  sga3_VIB_3_10_Nbhd := n.sga3_VIB_3_10_Nbhd\n",""),
 ("  sga3_VIB_3_10 := _root_.SGA3IdComp.sga3_VIB_3_10_of_nbhd n.sga3_VIB_3_10_Nbhd _root_.geomConnOfRationalPoint_proof\n",""),
 ("_root_.CToPrinted.semistableNeronBaseChange_of_printed_full r.blr_1_2_4\n    r.sga3_VIB_3_10 r.sga7_IX_3_3 r.egaIV_8_10_5_openImm t.geomConnOfRationalPoint","_root_.SGA3Nbhd.semistableNeronBaseChange_noSGA3 r.blr_1_2_4\n    r.sga7_IX_3_3 t.geomConnOfRationalPoint"),
 RN[6], RN[7], RN[8],
]
if MODE == 'narrow':
    sys.exit('narrow mode superseded: SGA3NbhdOL.lean (narrowed leaf) was removed; see log.md')
R = RR
IMPORT = 'import ZInQKernel.Contrib.OneProof.SemistableNeronBaseChangeNoSGA3'
out=[('import ZInQKernel.OneProof.H.TailZ45' if MODE=='module' else 'import ZInQKernel.OneProof.Main'),IMPORT,'',
 '/-! # sga3-nbhd manual fold check: the research chain TailZ23–TailZ45 with `sga3_VIB_3_10(_Nbhd)` replaced by',
 '`SGA3Nbhd.SGA3_VIB_3_10_NeronOL` (narrow mode) or removed (remove mode); generated by scratch/sga3-nbhd/fold/gen_fold.py. -/','',
 'set_option linter.style.longLine false','set_option linter.unusedVariables false','',
 'namespace HDec','','namespace HSyn','','namespace NOL','']
counts={a:0 for a,_ in R}
for i,(k,b) in enumerate(blocks):
    if i not in sel: continue
    if MODE in ('remove', 'module'):
        b, nd = re.subn(r'  /--(?:(?!-/).)*?SGA 3 VI_B 3\.10(?:(?!-/).)*-/\n(?=  sga3_VIB_3_10(?:_Nbhd)? :)', '', b, flags=re.S)
        counts.setdefault('docstrings', 0); counts['docstrings'] += nd
    for a,c in R:
        if a in b: counts[a]+=b.count(a); b=b.replace(a,c)
    out.append(f'-- copied from TailZ{k}')
    out.append(b.rstrip()+'\n')
M=open('ZInQKernel/OneProof/Main.lean').read()
ma=M.index('namespace ZInQ.Contrib.TYZChain'); mb=M.index('end ZInQ.Contrib.TYZChain')
main=M[ma:mb+len('end ZInQ.Contrib.TYZChain')]
main=main.replace('theorem _root_.ZInQ.OneProof.frozenTarget\n','theorem _root_.ZInQ.OneProof.frozenTargetNOL\n')
main=main.replace('(r : HDec.HSyn.OpenResearchLeaves28)','(r : HDec.HSyn.OpenResearchLeaves29)')
main=main.replace('(HDec.HSyn.sixContactMin_of_open38 r t l)','(HDec.HSyn.sixContactMin_of_open39 r t l)')
assert 'frozenTargetNOL' in main and 'open39' in main and 'Leaves29' in main
out+=['end NOL','',
 ('/-- The new top research bundle: `OpenResearchLeaves28` without `sga3_VIB_3_10_Nbhd` (sga3-nbhd). -/' if MODE=='remove' else
  '/-- The new top research bundle: `OpenResearchLeaves28` with `sga3_VIB_3_10_Nbhd` replaced by `sga3_VIB_3_10_NeronOL` (sga3-nbhd). -/'),
 'abbrev OpenResearchLeaves29 : Prop := NOL.OpenResearchLeaves28','',
 '/-- **G0 with only the open leaves** (sga3-nbhd manual fold). -/',
 'theorem sixContactMin_of_open39 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves13) (l : OpenAddedLeaves19) :',
 '    ZInQ.SixContactMin :=','  NOL.sixContactMin_of_open38 r t l','',
 'end HSyn','','end HDec','']
if MODE == 'module':
    out += ['#print axioms HDec.HSyn.sixContactMin_of_open39']
else:
  out += [main, '',
 '#print axioms ZInQ.OneProof.frozenTargetNOL',
 '#print axioms HDec.HSyn.NOL.sixContactMin_of_open38', '',
 'open Lean Elab Command in',
 'partial def nolClosure (env : Environment) (root : Name) : Std.HashSet Name := Id.run do',
 '  let mut seen : Std.HashSet Name := {}',
 '  let mut stack : Array Name := #[root]',
 '  while !stack.isEmpty do',
 '    let n := stack.back!',
 '    stack := stack.pop',
 '    if seen.contains n then continue',
 '    seen := seen.insert n',
 '    if let some ci := env.find? n then',
 '      for c in ci.getUsedConstantsAsSet do',
 '        if !seen.contains c then stack := stack.push c',
 '  return seen',
 '',
 'open Lean Elab Command in',
 'elab "#nolcheck" : command => do',
 '  let env ← getEnv',
 '  let cl := nolClosure env ``ZInQ.OneProof.frozenTargetNOL',
 '  IO.println s!"closure size {cl.size}"',
 '  for t in [``CToPrinted.SGA3_VIB_3_10, ``SGA3IdComp.SGA3_VIB_3_10_Nbhd, ``SGA3IdComp.sga3_VIB_3_10_of_nbhd,',
 '      ``CToPrinted.idComp_baseChange, ``CToPrinted.semistableNeronBaseChange_of_printed_full] do',
 '    IO.println s!"{t} in closure: {cl.contains t}"',
 '  let old := getStructureFields env ``HDec.HSyn.OpenResearchLeaves28',
 '  let new := getStructureFields env ``HDec.HSyn.NOL.OpenResearchLeaves28',
 '  IO.println s!"fields old {old.size}, new {new.size}; removed {old.filter (fun f => !new.contains f)}; added {new.filter (fun f => !old.contains f)}"',
 '',
 '#nolcheck']
open(sys.argv[1],'w').write('\n'.join(out)+'\n')
for a,n in counts.items(): print(n, a[:70].replace('\n',' '), file=sys.stderr)
print('copied', len(sel), 'blocks:', ' '.join(name_of(blocks[i][1]) for i in sorted(sel)), file=sys.stderr)
