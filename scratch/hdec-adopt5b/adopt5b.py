# Generate the hdec-adopt5b modules of ZInQKernel/HDecomp/Textbook/ from the scratch drafts (run
# from the worktree root: python3 -I scratch/hdec-adopt5b/adopt5b.py T10SRC). Verbatim copies of
# existing HDecomp code become imports (plus a selective `open`); nothing else changes.
# T10SRC is scratch/t10-etale/T10Etale.lean of origin/wip/t10-etale (9610b943), extracted with
# `git show` (that branch is not merged into this one).
import re, os, sys
sys.path.insert(0, 'scratch/hdec-adopt2')
from blocks import block
S = 'scratch/'; D = 'ZInQKernel/HDecomp/Textbook/'; H = 'ZInQKernel.HDecomp.'
DOC = ('/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt5b from\n'
       '`scratch/{src}`{part}.\n'
       'The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/\n')
made = []
def emit(dst, src, lines, imports, part=''):
    body = [l for l in lines if not l.startswith('import ')]
    body = [l for l in body if not re.match(r'#(print|check|eval|exit)', l)]
    body = [l for l in body if not l.startswith('-- =====')]
    while body and not body[-1].strip(): body.pop()
    while body and not body[0].strip(): body.pop(0)
    res = []
    for l in body:  # collapse runs of blank lines left by the cuts
        if not l.strip() and res and not res[-1].strip(): continue
        res.append(l)
    seen = []; [seen.append(i) for i in imports if i not in seen]
    out = (['import ' + i + '\n' for i in seen] + ['\n', DOC.format(src=src, part=part), '\n']
           + res)
    if not out[-1].endswith('\n'): out[-1] += '\n'
    os.makedirs(os.path.dirname(D + dst), exist_ok=True)
    open(D + dst, 'w').write(''.join(out)); made.append(D + dst)
def rd(p): return open(p if p.startswith('/') else S + p).read().splitlines(keepends=True)
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
def before(L, prefix, new):  # insert the lines `new` before the first line starting with prefix
    i = at(L, prefix); return L[:i] + new + L[i:]
def note(text): return ['/-! ' + text + ' -/\n']

# ---- t-different: All.lean (the deduplicated union of the three proof files). Its copy of
# pkg-I6's ramification definitions (first `namespace PkgI6` … `end PkgI6`) and of the four leaf
# statements are `ZInQKernel.HDecomp.Conductor.I6Base`'s (namespace `PkgI6`, same text).
src = 't-different/All.lean'; L = rd(src)
i0 = at(L, 'namespace PkgI6'); i1 = at(L, 'end PkgI6')
L = L[:i0] + note('The definitions `PkgI6.lowerRam`, `lowerRamR`, `herbrandPhi`, `upperRam` (and\n'
    '`mem_lowerRam`, `lowerRam_tower`), copied verbatim in the draft, are imported from\n'
    '`ZInQKernel.HDecomp.Conductor.I6Base`.') + L[i1 + 1:]
L = drop(L, cut_blocks(L, ['HilbertDifferentFormula', 'DifferentBound', 'HerbrandTransitivity',
                           'HerbrandQuotient']))
i = max(k for k, l in enumerate(L) if l.startswith('namespace PkgI6'))
L = L[:i + 1] + ['\n'] + note('The leaf statements `HilbertDifferentFormula`, `DifferentBound`,\n'
    '`HerbrandQuotient`, `HerbrandTransitivity` (verbatim copies in the draft) are\n'
    '`ZInQKernel.HDecomp.Conductor.I6Base`\'s.') + L[i + 1:]
emit('Different.lean', src, L, ['Mathlib', H + 'Conductor.I6Base'], ' (T20-T22, local forms)')

# ---- t-skolem-kw
src = 't-skolem-kw/SkolemNoether.lean'; L = rd(src)
L = drop(L, cut_blocks(L, ['SkolemNoether', 'LeafSkolemNoether']))
L = before(L, 'namespace TSkolemKW', note('`SkolemNoether` and `LeafSkolemNoether` (verbatim copies\n'
    'in the draft) are `PkgI6.SkolemNoether` (`Conductor.I6Base`) and\n'
    '`GlueDescent.LeafSkolemNoether` (`Descent.B1Quat`).') +
    ['open PkgI6 (SkolemNoether)\n', 'open GlueDescent (LeafSkolemNoether)\n', '\n'])
emit('SkolemNoether.lean', src, L, ['Mathlib', H + 'Conductor.I6Base', H + 'Descent.B1Quat'],
     ' (T13)')

src = 't-skolem-kw/BrauerNesbitt.lean'; L = rd(src)
L = drop(L, cut_blocks(L, ['BrauerNesbittChar0']))
L = before(L, 'namespace TSkolemKW', note('`BrauerNesbittChar0` (a verbatim copy in the draft) is\n'
    '`PkgI6.BrauerNesbittChar0` (`Conductor.I6Base`).') +
    ['open PkgI6 (BrauerNesbittChar0)\n', '\n'])
emit('BrauerNesbitt.lean', src, L, ['Mathlib', H + 'Conductor.I6Base'], ' (T19)')

src = 't-skolem-kw/C10Closed.lean'; L = rd(src)
i0 = max(k for k, l in enumerate(L) if l.startswith('namespace TSkolemKW.C10'))
L = [
    '/-!\n', '# t-skolem-kw: C10 from Chebotarev alone\n', '\n',
    'The draft `C10Closed.lean` is `BrauerNesbitt.lean` (adopted as\n',
    '`ZInQKernel.HDecomp.Textbook.BrauerNesbitt`), then glue-c10\'s namespace `GlueC10` verbatim\n',
    '(adopted as `ZInQKernel.HDecomp.C10.C10`), then the part below.\n', '-/\n', '\n',
    'open NumberField\n', 'open GlueC10\n', '\n'] + L[i0:]
emit('C10Closed.lean', src, L, [H + 'Textbook.BrauerNesbitt', H + 'C10.C10'], ' (its last part)')

src = 't-skolem-kw/FrobeniusDense.lean'; L = rd(src)
i0 = at(L, 'namespace TSkolemKW.C10'); i1 = at(L, 'end TSkolemKW.C10')
L = L[:i0] + note('Part C10 of the draft (glue-c10\'s Frobenius lift, a verbatim copy in namespace\n'
    '`TSkolemKW.C10`) is `GlueC10`\'s, from `ZInQKernel.HDecomp.C10.C10`.') + L[i1 + 1:]
k = at(L, 'open TSkolemKW.C10 (')
L[k] = L[k].replace('open TSkolemKW.C10 (', 'open GlueC10 (')
L = drop(L, cut_blocks(L, ['Qbar', 'GQ', 'LiesOver', 'IsArithFrob']))
k = at(L, 'open GlueC10 (')
L = L[:k + 1] + note('`Qbar`, `GQ`, `LiesOver`, `IsArithFrob` (verbatim copies of `HSyn`\'s in the\n'
    'draft) are `PkgI4`\'s, from `ZInQKernel.HDecomp.Conductor.LadicCond`.') + \
    ['open PkgI4 (Qbar GQ LiesOver IsArithFrob)\n'] + L[k + 1:]
emit('FrobeniusDense.lean', src, L, ['Mathlib', H + 'C10.C10', H + 'Conductor.LadicCond'],
     ' (T18 from `ChebotarevExists`)')

src = 't-skolem-kw/KroneckerWeberUse.lean'; L = rd(src)
L = drop(L, cut_blocks(L, ['Qbar', 'GQ']))
L = before(L, 'namespace TSkolemKW.KW', note('`Qbar` and `GQ` (verbatim copies in the draft) are\n'
    '`PkgI4`\'s, from `ZInQKernel.HDecomp.Conductor.LadicCond`.') +
    ['open PkgI4 (Qbar GQ)\n', '\n'])
emit('KroneckerWeberUse.lean', src, L, ['Mathlib', H + 'Conductor.LadicCond'],
     ' (the C8 use of T17)')

src = 't-skolem-kw/ChebotarevCyclotomic.lean'; L = rd(src)
L = drop(L, cut_blocks(L, ['card_quot']))
L = before(L, 'namespace TSkolemKW.ChebCyc', note('`card_quot` (a verbatim copy in the draft) is\n'
    '`GlueC10.card_quot`, from `ZInQKernel.HDecomp.C10.C10`.') +
    ['open GlueC10 (card_quot)\n', '\n'])
emit('ChebotarevCyclotomic.lean', src, L, ['Mathlib', H + 'C10.C10'],
     ' (`ChebotarevExists` for cyclotomic fields)')

# ---- t30-adelic: no copies.
for f, dst, part in [('SqrtCrit', 'T30SqrtCrit', ' (T30)'), ('Adelic', 'G1Adelic', ' (G1-adelic)'),
                     ('G1Count', 'G1Count', ' (G1-adelic, the count)')]:
    src = 't30-adelic/' + f + '.lean'; L = rd(src)
    imps = [l.split()[1] for l in L if l.startswith('import ')]
    emit(dst + '.lean', src, L, imps, part)

# ---- t10-etale: `T10_groupIso` is leaf-push2's (`ZInQ.LeafPush2.T10_groupIso`, LeafPush2.T).
L = rd(sys.argv[1]); src = 't10-etale/T10Etale.lean'
imps = [l.split()[1] for l in L if l.startswith('import ')]
L = drop(L, cut_blocks(L, ['T10_groupIso']))
L = before(L, 'namespace T10Etale', note('leaf-push2\'s group form `T10_groupIso` (a verbatim copy in\n'
    'the draft) is `ZInQ.LeafPush2.T10_groupIso`, from `ZInQKernel.HDecomp.LeafPush2.T`.') +
    ['open ZInQ.LeafPush2 (T10_groupIso)\n', '\n'])
emit('T10Etale.lean', src, L, imps + [H + 'LeafPush2.T'], ' (branch `wip/t10-etale`)')

# ---- t28-igusa: Igusa.lean split at its part boundaries (one `noncomputable section` in the
# draft; each module reopens it). The second batch of `ring` proofs of M3 (G23, G33, a112, about
# 7 minutes in the draft) is not adopted.
src = 't28-igusa/Igusa.lean'; L = rd(src)
iSO3 = at(L, 'namespace T28SO3'); iSO3 = idx(L, lambda l: l.startswith('/-!'), iSO3 - 20)
iM = at(L, '/-! ## Mestre')
iG = at(L, '/-! ## The generic case')
iA = at(L, '/-! ## M3 identities proved by `ring`')
iB = at(L, '/-! ## M3 identities proved by `ring`', iA + 1)
iEnd = max(k for k, l in enumerate(L) if l.rstrip() == 'end')
HD = ['open Matrix\n', '\n', 'noncomputable section\n', '\n']
END = ['\n', 'end\n']
emit('Igusa/Forward.lean', src, L[:iSO3] + END, ['Mathlib'], ', definitions, `⇒` and the `iff`')
emit('Igusa/SO3.lean', src, HD + L[iSO3:iM] + END, [H + 'Textbook.Igusa.Forward'],
     ', the `SO(3) = PGL(2)` lemma')
emit('Igusa/Generic.lean', src, HD + L[iM:iA] + END, [H + 'Textbook.Igusa.SO3'],
     ', Mestre\'s step, the generic case and the reduction')
emit('Igusa/M3a.lean', src, HD + L[iA:iB] + END, [H + 'Textbook.Igusa.Generic'],
     ', the first batch of `ring` proofs of M3')
print('\n'.join(made))
