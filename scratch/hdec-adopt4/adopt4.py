# Generate the hdec-adopt4 modules of ZInQKernel/HDecomp/ from the scratch drafts (run from the
# worktree root: python3 -I scratch/hdec-adopt4/adopt4.py). Verbatim copies of existing HDecomp
# code become imports; nothing else in the drafts changes.
import re, os, subprocess, sys
sys.path.insert(0, 'scratch/hdec-adopt2')
from blocks import block
S = 'scratch/'; D = 'ZInQKernel/HDecomp/'; H = 'ZInQKernel.HDecomp.'
DOC = ('/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from\n'
       '`scratch/{src}`{part}.\n'
       'The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/\n')
made = []
def emit(dst, src, lines, imports, part=''):
    body = [l for l in lines if not l.startswith('import ')]
    body = [l for l in body if not re.match(r'#(print|check|eval|exit)', l)]
    while body and not body[-1].strip(): body.pop()
    res = []
    for l in body:  # collapse runs of blank lines left by the cuts
        if not l.strip() and res and not res[-1].strip(): continue
        res.append(l)
    seen = []; [seen.append(i) for i in imports if i not in seen]
    out = (['import ' + i + '\n' for i in seen] + ['\n', DOC.format(src=src, part=part), '\n']
           + res)
    os.makedirs(os.path.dirname(D + dst), exist_ok=True)
    open(D + dst, 'w').write(''.join(out)); made.append(D + dst)
def rd(p): return open(S + p).read().splitlines(keepends=True)
def imps(lines): return [l.split()[1] for l in lines if l.startswith('import ')]
def idx(L, pred, start=0): return next(i for i in range(start, len(L)) if pred(L[i]))
def at(L, prefix, start=0): return idx(L, lambda l: l.startswith(prefix), start)
KINDS = ('def', 'abbrev', 'theorem', 'lemma', 'noncomputable def', 'instance', 'structure',
         'class')
def cut_blocks(L, names):
    c = set()
    for n in names:
        s, e = block(L, n, KINDS); c |= set(range(s, e))
    return c
def drop(L, cut): return [l for k, l in enumerate(L) if k not in cut]

# ---- leaf-push2: Part I (lines up to `end ModelsSec`) is a copy of def-faltings §§1-18 + H5,
# adopted by hdec-adopt3 as Faltings.{HodgeData,IdealLines,Models,Height}: imported, opened.
# Part II's IsCurve, IsJacobian, JacobianExists, IsBelyiFunction are LeafModCurves'; R3's order
# (B … O) is LeafQM's, its QMStr is LeafQM.AV's (same structure, binders written differently);
# T's IsComplexConj is PkgI4's (same body; PkgI4.GQ is an abbrev of the same type).
L = rd('leaf-push2/LeafPush2.lean')
src = 'leaf-push2/LeafPush2.lean'
iI = at(L, 'end ModelsSec')
iC = at(L, 'section CurvesSec'); i18 = at(L, 'section R18Sec'); i22 = at(L, 'section R22Sec')
i3 = at(L, 'section R3Sec'); iT = at(L, 'section TSec'); iend = at(L, 'end ZInQ.LeafPush2')
doc = L[at(L, '/-!'):at(L, 'namespace ZInQ.LeafPush2')]
hdr = lambda extra: (['namespace ZInQ.LeafPush2\n', '\n', 'open NumberField MeasureTheory\n', '\n',
    '/-! Part I of the draft (def-faltings §§1-18 and H5, a verbatim copy) is imported from\n',
    '`ZInQKernel.HDecomp.Faltings.Height`, namespace `ZInQ.DefFaltings`; the copies of\n',
    'leaf-modcurves\' curve definitions are `LeafModCurves`\'s, from\n',
    '`ZInQKernel.HDecomp.ModCurves.Leaves`. -/\n',
    'open ZInQ.DefFaltings\n',
    'open LeafModCurves (IsCurve IsJacobian JacobianExists IsBelyiFunction)\n'] + extra + ['\n'])
QMO = ['/-! The order `𝒪` and `QMStr` (copied in the draft from leaf-qm-fp) are `LeafQM`\'s, from\n',
       '`ZInQKernel.HDecomp.QM.Structures`. -/\n',
       'open LeafQM (B ofInt InO mulCoord ofInt_mul ofInt_add ofInt_neg ofInt_zero ofInt_one O)\n',
       'open LeafQM.AV (QMStr)\n']
CCO = ['/-! `IsComplexConj` (a duplicate in the draft) is `PkgI4`\'s, from\n',
       '`ZInQKernel.HDecomp.Conductor.LadicCond` (same body; `PkgI4.GQ` is an abbrev of\n',
       '`AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`). -/\n', 'open PkgI4 (IsComplexConj)\n']
END = ['\n', 'end ZInQ.LeafPush2\n']
C = L[iC:i18]
C = drop(C, cut_blocks(C, 'IsCurve IsJacobian JacobianExists IsBelyiFunction'.split()))
emit('LeafPush2/R18.lean', src, doc + hdr([]) + L[iI + 1:iC] + C + L[i18:i22] + END,
     [H + 'Faltings.Height', H + 'ModCurves.Leaves'], ', Part II and R18')
emit('LeafPush2/R22.lean', src, hdr([]) + L[i22:i3] + END, [H + 'LeafPush2.R18'], ', R22')
R = L[i3:iT]
R = drop(R, cut_blocks(R, ('B ofInt InO mulCoord ofInt_mul ofInt_add ofInt_neg ofInt_zero '
                           'ofInt_one O QMStr').split()))
emit('LeafPush2/R3.lean', src, hdr(QMO) + R + END, [H + 'LeafPush2.R22', H + 'QM.Structures'],
     ', R3')
T = L[iT:iend]
T = drop(T, cut_blocks(T, ['IsComplexConj']))
emit('LeafPush2/T.lean', src, hdr(CCO) + T + END,
     [H + 'LeafPush2.R3', H + 'Conductor.LadicCond'], ', T10-T12')

# ---- bp-analytic: Torus.lean split at its section boundaries; §10's copy of `PkgI3.AbVar`
# (structure, instances, `ptObj`, `Pt`) is replaced by `open PkgI3 (AbVar)`.
L = rd('bp-analytic/Torus.lean')
src = 'bp-analytic/Torus.lean'
s7 = at(L, '/-! ## §7.'); s8 = at(L, '/-! ## §8.'); s10 = at(L, '/-! ## §10.')
eB = at(L, 'end BPAnalytic')
TOP = ['open scoped Manifold ContDiff Topology\n', 'open Set Filter\n', '\n',
       'set_option linter.unusedSectionVars false\n', '\n', 'noncomputable section\n', '\n']
NSV = (['namespace BPAnalytic\n', '\n',
        'variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]\n', '\n',
        'variable (Λ : Submodule ℤ E) [DiscreteTopology Λ]\n', '\n']
       + L[at(L, 'variable {F : Type*}'):at(L, 'variable {F : Type*}') + 2] + ['\n'])
NSE = ['\n', 'end BPAnalytic\n']
emit('Analytic/Torus.lean', src, L[:s7] + NSE, imps(L), ', §1-§6')
emit('Analytic/QMLattice.lean', src, TOP + NSV + L[s7:s8] + NSE, [H + 'Analytic.Torus'], ', §7')
emit('Analytic/Hom.lean', src, TOP + NSV + L[s8:eB + 1], [H + 'Analytic.Torus'], ', §8-§9')
U = L[s10:]
a = at(U, '/-- (copied from Objects.lean, `PkgI3.AbVar`)'); b = at(U, 'end AbVar')
U = U[:a] + ['/-! `AbVar`, `AbVar.ptObj`, `AbVar.Pt` (copied in the draft from `Objects.lean`) are\n',
             '`PkgI3`\'s, from `ZInQKernel.HDecomp.Objects`. -/\n', 'open PkgI3 (AbVar)\n'] + U[b + 1:]
emit('Analytic/Uniformization.lean', src, TOP + U, [H + 'Analytic.Hom', H + 'Objects'], ', §10')

# ---- rv-qm-polar: QMPolar.lean; its copy of leaf-qm-fp's order (B … O) is LeafQM's.
L = rd('rv-qm-polar/QMPolar.lean')
src = 'rv-qm-polar/QMPolar.lean'
names = 'B ofInt InO mulCoord ofInt_mul ofInt_add ofInt_neg ofInt_zero ofInt_one O'
L = drop(L, cut_blocks(L, names.split()))
i = at(L, 'namespace RvQMPolar')
L = L[:i + 1] + ['\n', '/-! `B`, `ofInt`, `InO`, `mulCoord`, `ofInt_mul`, … and `O` (copied in the draft) are\n',
                 '`LeafQM`\'s, from `ZInQKernel.HDecomp.QM.Structures` (identical code). -/\n',
                 'open LeafQM (' + names + ')\n'] + L[i + 1:]
emit('QM/Polar.lean', src, L, imps(L) + [H + 'QM.Structures'])
subprocess.run(['python3', '-I', 'scratch/hdec-adopt/wrap.py'] + made)
print('\n'.join(made))
