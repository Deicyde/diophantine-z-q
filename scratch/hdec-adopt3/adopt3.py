# Generate the hdec-adopt3 modules of ZInQKernel/HDecomp/ from the scratch drafts (run from the
# worktree root). Verbatim copies of existing HDecomp code become imports.
import re, os, subprocess, sys
sys.path.insert(0, 'scratch/hdec-adopt2')
from blocks import block
S = 'scratch/'; D = 'ZInQKernel/HDecomp/'; H = 'ZInQKernel.HDecomp.'
DOC = ('/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from\n'
       '`scratch/{src}`{part}.\n'
       'The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/\n')
made = []
def emit(dst, src, lines, imports, part=''):
    body = [l for l in lines if not l.startswith('import ')]
    body = [l for l in body if not re.match(r'#(print|check|eval|exit)', l)]
    while body and not body[-1].strip(): body.pop()
    seen = []; [seen.append(i) for i in imports if i not in seen]
    out = (['import ' + i + '\n' for i in seen] + ['\n', DOC.format(src=src, part=part), '\n']
           + body)
    os.makedirs(os.path.dirname(D + dst), exist_ok=True)
    open(D + dst, 'w').write(''.join(out)); made.append(D + dst)
def rd(p): return open(S + p).read().splitlines(keepends=True)
def imps(lines): return [l.split()[1] for l in lines if l.startswith('import ')]
def idx(L, pred, start=0): return next(i for i in range(start, len(L)) if pred(L[i]))
def at(L, prefix, start=0): return idx(L, lambda l: l.startswith(prefix), start)
KINDS = ('def', 'abbrev', 'theorem', 'lemma', 'noncomputable def', 'instance', 'structure')
def cut_blocks(L, names):
    c = set()
    for n in names:
        s, e = block(L, n, KINDS); c |= set(range(s, e))
    return c
def drop(L, cut): return [l for k, l in enumerate(L) if k not in cut]
def opening(L, prefix, extra):
    """Insert the lines `extra` after the first line starting with `prefix`."""
    i = at(L, prefix); return L[:i + 1] + extra + L[i + 1:]

# ---- B3 (v) with no leaf: glue-t32a's T32a.lean minus its copy of glue-b3b's B3b.lean.
L = rd('glue-t32a/T32a.lean')
t = at(L, '# glue-t32a: proof of T32(a)') - 1
assert L[t].startswith('/-!')
B2O = ['\n', '/-! `GQ`, `cyc`, `galChar`, `UnramifiedAt`, … are glue-descent\'s, as in `B3Unram.B3b`. -/\n',
       'open GlueDescent.B2Q (GQ act toRingAut cyc galChar isLocallyConstant_of_openSubgroup\n',
       '  cyc_eq_of_agree cyc_isLocallyConstant galChar_isLocallyConstant UnramifiedAt)\n']
NOTE = ['/-! The draft\'s first 1816 lines are a verbatim copy of glue-b3b\'s `B3b.lean`; here they are\n',
        'imported from `ZInQKernel.HDecomp.B3Unram.B3b`. -/\n', '\n']
emit('B3Unram/T32a.lean', 'glue-t32a/T32a.lean',
     NOTE + opening(L[t:], 'namespace GlueB3Unram', B2O), [H + 'B3Unram.B3b'])

# ---- Modular curves: leaf-modcurves' ModCurveLeaves.lean, split into Genus (§A), Defs (§B-§E),
# Leaves (§F-§H), Glue (§I-§J).
L = rd('leaf-modcurves/ModCurveLeaves.lean')
src = 'leaf-modcurves/ModCurveLeaves.lean'
iB = at(L, '/-! ## §B.'); iF = at(L, '/-! ## §F.'); iI = at(L, '/-! ## §I.')
iend = max(i for i, l in enumerate(L) if l.startswith('end LeafModCurves'))
# §A: GlueAssembly's copies (Assembly/E2Index.lean) opened.
A = L[:iB]
A = drop(A, cut_blocks(A, 'firstColMod firstCol_algebra firstColMod_eq_iff index_Gamma1_le'.split()))
A = opening(A, 'section Genus', [
    '\n', '/-! `firstColMod`, `firstCol_algebra`, `firstColMod_eq_iff`, `index_Gamma1_le` (copied in\n',
    'the draft) are `GlueAssembly`\'s, from `ZInQKernel.HDecomp.Assembly.E2Index`. -/\n',
    'open GlueAssembly (firstColMod firstCol_algebra firstColMod_eq_iff index_Gamma1_le)\n'])
emit('ModCurves/Genus.lean', src, A, imps(L) + [H + 'Assembly.E2Index'], ', §A')
P4 = 'Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH oldSpace IsNewform'
P4O = ['open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH\n',
       '  oldSpace IsNewform)\n']
B = L[iB:iF]
B = drop(B, cut_blocks(B, P4.split()))
B = opening(B, 'open scoped MatrixGroups ModularForm', [
    '\n', '/-! `ℚ̄`, `G_ℚ`, `LiesOver`, `IsArithFrob` and the cusp-form definitions (copied in the\n',
    'draft from `Leaves.lean`) are `PkgI4`\'s, from `ZInQKernel.HDecomp.Conductor.LadicCond`. -/\n']
    + P4O)
HDR = (['noncomputable section\n', '\n', 'namespace LeafModCurves\n', '\n',
        'open scoped MatrixGroups ModularForm\n'] + P4O +
       ['open WeierstrassCurve AlgebraicGeometry\n',
        'open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj\n',
        'open PkgI3 PkgI3.AbVar\n', '\n'])
END = ['\n', 'end LeafModCurves\n']
emit('ModCurves/Defs.lean', src, ['noncomputable section\n', '\n'] + B + END,
     [H + 'Objects', H + 'C10.C10', H + 'Conductor.LadicCond'], ', §B-§E')
emit('ModCurves/Leaves.lean', src, HDR + L[iF:iI] + END,
     [H + 'ModCurves.Genus', H + 'ModCurves.Defs'], ', §F-§H')
emit('ModCurves/Glue.lean', src, HDR + L[iI:iend + 1], [H + 'ModCurves.Leaves'], ', §I-§J')

# ---- QM: leaf-qm-fp's QMLeaves.lean, split into Structures (§0-§3), Pairs (§4-§7), Leaves (§8).
L = rd('leaf-qm-fp/QMLeaves.lean')
src = 'leaf-qm-fp/QMLeaves.lean'
i4 = at(L, '/-! ## §4'); i8 = at(L, '/-! ## §8')
iend = max(i for i, l in enumerate(L) if l.startswith('end LeafQM'))
HDR = ['noncomputable section\n', '\n', 'namespace LeafQM\n', '\n', 'namespace AV\n', '\n',
       'open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj\n',
       'open PkgI3\n', '\n', 'variable {K : Type} [Field K]\n', '\n']
END = ['\n', 'end AV\n', '\n', 'end LeafQM\n']
emit('QM/Structures.lean', src, L[:i4] + END, imps(L), ', §0-§3')
emit('QM/Pairs.lean', src, HDR + L[i4:i8] + END, [H + 'QM.Structures'], ', §4-§7')
emit('QM/Leaves.lean', src, HDR + L[i8:iend + 1], [H + 'QM.Pairs'], ', §8')

# ---- The stable Faltings height: def-faltings' Faltings.lean, split into HodgeData (§1-§6),
# IdealLines (§7-§14), Models (§15-§17), Height (§18-§20), Leaves (§21-§22). The draft's copy of
# `PkgI3.AbVar` (structure, `baseChange`, `dim`) is replaced by `open PkgI3 (AbVar)`; its new
# `AbVar.structMapOn`, `AbVar.origin` are declared in `PkgI3.AbVar` so that `A.origin` still
# elaborates.
L = rd('def-faltings/Faltings.lean')
src = 'def-faltings/Faltings.lean'
s = {k: at(L, f'/-! ## {k}.') for k in (7, 15, 18, 21)}
iend = max(i for i, l in enumerate(L) if l.startswith('end ZInQ.DefFaltings'))
c = cut_blocks(L, ['AbVar', 'AbVar.baseChange', 'AbVar.dim'])
c.add(at(L, 'attribute [instance] AbVar.grp'))
L = [l for k, l in enumerate(L)] ; L2 = [('' if k in c else l) for k, l in enumerate(L)]
L2 = [l.replace('noncomputable def AbVar.structMapOn', 'noncomputable def _root_.PkgI3.AbVar.structMapOn')
       .replace('noncomputable def AbVar.origin', 'noncomputable def _root_.PkgI3.AbVar.origin')
      for l in L2]
def sl(a, b):
    out = [l for l in L2[a:b] if l != '']
    # collapse runs of blank lines left by the cut
    res = []
    for l in out:
        if not l.strip() and res and not res[-1].strip(): continue
        res.append(l)
    return res
NS = ['namespace ZInQ.DefFaltings\n', '\n', 'open NumberField MeasureTheory\n', '\n']
MS = ['section ModelsSec\n', '\n',
      'open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj\n',
      'open scoped TensorProduct\n', 'open ExteriorAlgebra\n', 'open PkgI3 (AbVar)\n', '\n']
NSE = ['\n', 'end ZInQ.DefFaltings\n']; MSE = ['\n', 'end ModelsSec\n']
emit('Faltings/HodgeData.lean', src, sl(0, s[7]) + NSE, imps(L), ', §1-§6')
emit('Faltings/IdealLines.lean', src, NS + sl(s[7], s[15]) + NSE, [H + 'Faltings.HodgeData'],
     ', §7-§14')
M = sl(s[15], s[18])
M = opening(M, 'open ExteriorAlgebra', [
    '\n', '/-! `AbVar`, `AbVar.baseChange`, `AbVar.dim` (copied in the draft from `Objects.lean`) are\n',
    '`PkgI3`\'s, from `ZInQKernel.HDecomp.Objects`. -/\n', 'open PkgI3 (AbVar)\n'])
emit('Faltings/Models.lean', src, NS + M + MSE + NSE,
     [H + 'Faltings.IdealLines', H + 'Objects'], ', §15-§17')
emit('Faltings/Height.lean', src, NS + MS + sl(s[18], s[21]) + MSE + NSE,
     [H + 'Faltings.Models'], ', §18-§20')
emit('Faltings/Leaves.lean', src, NS + MS + sl(s[21], iend + 1), [H + 'Faltings.Height'],
     ', §21-§22')
subprocess.run(['python3', '-I', 'scratch/hdec-adopt/wrap.py'] + made)
print('\n'.join(made))
