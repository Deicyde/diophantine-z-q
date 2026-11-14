"""Generate parts/d40_abvarbc.lean and d45_r10.lean from ZInQKernel/Contrib/{AbVarBC,R10} (repo root, python3 -I)."""
def body(p):
    L=open(p).read().split('\n')
    return '\n'.join(l for l in L if not l.startswith('import ') and not l.startswith('#print'))
EDITS=[('ZInQ.Contrib.G9.PkgI3.AbVar','_root_.PkgI3.AbVar'),('ZInQ.Contrib.G9.PkgI4.I3.AbVar','_root_.PkgI4.I3.AbVar'),
  ('ZInQ.Contrib.G9.G0Galois.G9Glue','_root_.G0Galois.G9Glue'),
  ('open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.G9.G0Galois Module','open ZInQ.Contrib.G9 _root_.PkgI4 ZInQ.Contrib.G9.PkgI4 _root_.G0Galois Module'),
  ('open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4\n','open ZInQ.Contrib.G9 _root_.PkgI4 ZInQ.Contrib.G9.PkgI4\n')]
def wrap(p,name):
    b=body(p)
    for a,c in EDITS: b=b.replace(a,c)
    L=b.split('\n'); extra=L.count('noncomputable section')-L.count('end')
    return f'section G0A3file_{name}\n-- (file {p}, verbatim minus imports and #print lines; g0-assemble3 edits listed in the part header)\n'+b+'\nend\n'*max(extra,0)+f'\nend G0A3file_{name}\n'
D='ZInQKernel/Contrib/AbVarBC/'
files=['Dim','Points','Tate','Torsion','Mul','G9Instance','G9Mul']
hdr='''/-! ## g0-assemble3: g9-abvarbc (ZInQKernel/Contrib/AbVarBC/{Dim,Points,Tate,Torsion,Mul,G9Instance,G9Mul}.lean, in
import order, verbatim minus imports and `#print` lines; each in its own section). Edits (g9-derham's layer copies
`ZInQ.Contrib.G9.{PkgI3, PkgI4.I3}.AbVar` and `G0Galois` are not in this file, as for part a95: names resolve to
Leaves.lean's): `ZInQ.Contrib.G9.PkgI3.AbVar` → `_root_.PkgI3.AbVar`, `ZInQ.Contrib.G9.PkgI4.I3.AbVar` →
`_root_.PkgI4.I3.AbVar`, `ZInQ.Contrib.G9.G0Galois.G9Glue` → `_root_.G0Galois.G9Glue`; an `end` is appended where a
file leaves its `noncomputable section` open at end of file. `KerUnit`, `Tangent` and `Main`
(its own proof of `MulIsogeny`) are not copied: `MulIsogeny` is infra-stalks' `MulRigidity.mulIsogeny` (part b10),
applied through `G9Mul`'s `abVarBaseChange_of_mulIsogeny` in part d45. -/
'''
open('scratch/assemble-port/parts/d40_abvarbc.lean','w').write(hdr+'\n'.join(wrap(D+f+'.lean',f) for f in files))
R='ZInQKernel/Contrib/R10/'
hdr2='''/-! ## g0-assemble3: r10-amend (ZInQKernel/Contrib/R10/Amend.lean and Glue.lean, verbatim minus imports and `#print`
lines; the `open` lines name `_root_.PkgI4` and `_root_.G0Galois` in place of g9-derham's omitted layer copies, as
for part a95), then the closing theorems of Final.lean with g9-abvarbc's `abVarBaseChange` replaced by
`abVarBaseChange_of_mulIsogeny` applied to the `MulIsogeny` of infra-stalks (`G0FibreSimple.MulIsogeny` of part 40 and
g9-abvarbc's namespaced copy `ZInQ.Contrib.AbVarBC.G0FibreSimple.MulIsogeny` have the same text). -/
'''
tail='''
namespace ZInQ.Contrib.R10

open ZInQ.Contrib.G9 _root_.G0Galois

/-- (g0-assemble3) g9-abvarbc's `AbVarBaseChange`, from infra-stalks' `MulIsogeny`. -/
theorem abVarBaseChange_g0a3 : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  ZInQ.Contrib.AbVarBC.abVarBaseChange_of_mulIsogeny MulRigidity.mulIsogeny

/-- g0-mod-galois's `G9Glue` (verbatim) from the amended R10 (Final.lean's theorem, with
`abVarBaseChange_g0a3`). -/
theorem g9Glue_of_deRhamComparisonHT (h : DeRhamComparisonHT) : G9Glue :=
  g9Glue_of_HT abVarBaseChange_g0a3 h

end ZInQ.Contrib.R10
'''
open('scratch/assemble-port/parts/d45_r10.lean','w').write(hdr2+wrap(R+'Amend.lean','Amend')+wrap(R+'Glue.lean','Glue')+tail)
