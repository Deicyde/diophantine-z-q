"""raynaud-narrow: generate ZInQKernel/Contrib/OneProof/RaynaudNarrowChain.lean.

Copies, verbatim, every declaration of the H chain from `sixContactMin_of_open17` (TailZ23) to
`sixContactMin_of_open38` (TailZ45) whose type mentions a research bundle `OpenResearchLeaves14` ... `28` (the
bundles carrying `raynaudSemistableSH` / `raynaudSemistableSHOr`), into the namespace `HDec.HSyn.RNarrow`, with the
following changes only:

* in each research bundle the field `raynaudSemistableSH : ReductGlue.RaynaudSemistableSH` (generation 28:
  `raynaudSemistableSHOr : DictModels.RaynaudOr.RaynaudSemistableSHOr`) is replaced by
  `raynaudSemistableSHcp : ReductB.RaynaudSemistableSHcp`, and each pass-through line by
  `raynaudSemistableSHcp := n.raynaudSemistableSHcp`;
* the two readers `raynaudCriterionNF_of14` and `ss1_ss3_of14NF` (TailZ26) are re-proved from the cp field by
  raynaud-proof's `RaynaudCP.raynaudCriterion_leavesNF_cp` and neron-dvr's `GapNeron.ss1_ss3_of_cp_fullNF`, with every
  other input the term the original uses; `raynaudSemistable_of14` and `semistableReductionDVR_of14` are not copied.

Unqualified names inside `HDec.HSyn.RNarrow` resolve to the copies first, then to `HDec.HSyn` (textbook, added, glue
bundles and everything else stay the originals).

Usage (repository root): python3 scratch/raynaud-narrow/gen_chain.py
"""
import re

H = 'ZInQKernel/OneProof/H/'
OUT = 'ZInQKernel/Contrib/OneProof/RaynaudNarrowChain.lean'
STOP = re.compile(r'^(/--|/-!|theorem |structure |def |lemma |abbrev |end |#print|namespace |section |open )')
DECL = re.compile(r'^(theorem|structure|def|lemma|abbrev) (\S+)')


def decls(path):
    L = open(path).read().split('\n')
    out = {}
    i = 0
    doc = None
    while i < len(L):
        l = L[i]
        if l.startswith('/--'):
            doc = i
            # skip to end of docstring
            while '-/' not in L[i]:
                i += 1
            i += 1
            continue
        m = DECL.match(l)
        if m:
            start = doc if doc is not None else i
            j = i + 1
            while j < len(L) and not STOP.match(L[j]):
                j += 1
            block = L[start:j]
            while block and block[-1].strip() == '':
                block.pop()
            out[m.group(2)] = block
            doc = None
            i = j
            continue
        if l.strip() and not l.startswith('/-'):
            doc = None
        i += 1
    return out


NEWDOC = ('  /-- raynaud-narrow: Raynaud\'s criterion (SGA 7 I, Exp. IX, Prop. 4.7; number UNVERIFIED) over a strictly\n'
          '  henselian DVR of a field of characteristic `0` with perfect (hence algebraically closed) residue field\n'
          '  (`ReductB.RaynaudSemistableSHcp`, TailZ23), the only generality the chain reads; replaces\n'
          '  `raynaudSemistableSH` (generation 28: `raynaudSemistableSHOr`). -/')
NEWFIELD = '  raynaudSemistableSHcp : _root_.ReductB.RaynaudSemistableSHcp'
FIELD = re.compile(r'^  (raynaudSemistableSH|raynaudSemistableSHOr) : ')
ASSIGN = re.compile(r'^  (raynaudSemistableSH|raynaudSemistableSHcp) := ')


def fix_struct(block):
    out = list(block)
    idx = [k for k, l in enumerate(out) if FIELD.match(l)]
    assert len(idx) == 1, (block[0], idx)
    k = idx[0]
    s = k
    if not out[k - 1].lstrip().startswith('/--') and not out[k - 1].rstrip().endswith('-/'):
        pass
    if out[k - 1].rstrip().endswith('-/'):
        s = k - 1
        while not out[s].lstrip().startswith('/--'):
            s -= 1
    out[s:k + 1] = [NEWDOC, NEWFIELD]
    return out


def fix_map(block):
    out = []
    n = 0
    for l in block:
        if ASSIGN.match(l):
            out.append('  raynaudSemistableSHcp := n.raynaudSemistableSHcp')
            n += 1
        else:
            out.append(l)
    assert n == 1, block[0]
    return out


RAY_NF = '''/-- **r6 at number fields** (raynaud-narrow re-version of `raynaudCriterionNF_of14`, TailZ26): raynaud-proof's
`RaynaudCP.raynaudCriterion_leavesNF_cp` from the cp field, with every other input the original's term. -/
theorem raynaudCriterionNF_of14 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) :
    PkgI2.RaynaudCriterionNF.{0} :=
  _root_.RaynaudCP.raynaudCriterion_leavesNF_cp r.raynaudSemistableSHcp r.strictHenselizationPair
    r.semistableUnipotent (_root_.GapNeron.neronSchemeModelExistsNF t.neronSchemeExtensionExists)
    t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme'''

SS_NF = '''/-- **SS1 and SS3** (raynaud-narrow re-version of `ss1_ss3_of14NF`, TailZ26): neron-dvr's
`GapNeron.ss1_ss3_of_cp_fullNF` from the cp field, with every other input the original's term. -/
theorem ss1_ss3_of14NF (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) :
    _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists :=
  _root_.GapNeron.ss1_ss3_of_cp_fullNF r.raynaudSemistableSHcp r.semistablePersistsSHcp r.strictHenselizationPair
    t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme
    (_root_.GapNeron.neronSchemeModelExistsNF t.neronSchemeExtensionExists)
    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed r.blr_1_2_4))
    (semistableAlmostAll_of10 (addedLeaves9_of_open14 r t l))'''

# (file, [(name, kind)]) in dependency order; kind: s = research bundle, m = pass-through map, c = copy verbatim
PLAN = [
    ('TailZ23', [('OpenResearchLeaves14', 's'), ('x6Rows_of_open14', 'c'), ('addedLeaves9_of_open14', 'c'),
                 ('researchLeaves9_of_open14', 'c'), ('sixContactMin_of_open17', 'c')]),
    ('TailZ24', [('sixContactMin_of_open18', 'c')]),
    ('TailZ25', [('OpenResearchLeaves15', 's'), ('openResearchLeaves14_of_OpenResearchLeaves15', 'm'),
                 ('sixContactMin_of_open19', 'c')]),
    ('TailZ26', [('OpenResearchLeaves16', 's'), ('openResearchLeaves15_of_OpenResearchLeaves16', 'm'),
                 (RAY_NF, 'raw'), (SS_NF, 'raw'), ('sixContactMin_of_open20', 'c')]),
]
for k, (a, b) in {27: (17, 16), 28: (18, 17), 29: (19, 18)}.items():
    PLAN.append((f'TailZ{k}', [(f'OpenResearchLeaves{a}', 's'), (f'openResearchLeaves{b}_of_OpenResearchLeaves{a}', 'm'),
                               (f'sixContactMin_of_open{k - 6}', 'c')]))
PLAN += [('TailZ30', [('sixContactMin_of_open24', 'c')]), ('TailZ31', [('sixContactMin_of_open25', 'c')]),
         ('TailZ32', [('sixContactMin_of_open26', 'c')])]
for k, (a, b) in {33: (20, 19), 34: (21, 20), 35: (22, 21)}.items():
    PLAN.append((f'TailZ{k}', [(f'OpenResearchLeaves{a}', 's'), (f'openResearchLeaves{b}_of_OpenResearchLeaves{a}', 'm'),
                               (f'sixContactMin_of_open{k - 6}', 'c')]))
PLAN.append(('../../Contrib/OneProof/SGRFold', [('namespace SGRFold', 'raw'), ('research14_of_open29', 'c'),
                                                ('added12_of_open29', 'c'), ('heckeSqrtBranchAny_of_open29', 'c'),
                                                ('end SGRFold', 'raw')]))
for k, (a, b) in {36: (23, 22), 37: (24, 23), 38: (25, 24)}.items():
    PLAN.append((f'TailZ{k}', [(f'OpenResearchLeaves{a}', 's'), (f'openResearchLeaves{b}_of_OpenResearchLeaves{a}', 'm'),
                               (f'sixContactMin_of_open{k - 6}', 'c')]))
PLAN += [('TailZ39', [('openGlue7_of_OpenGlue8', 'c'), ('sixContactMin_of_open33', 'c')]),
         ('TailZ41', [('OpenResearchLeaves26', 's'), ('openResearchLeaves25_of_OpenResearchLeaves26', 'm'),
                      ('sixContactMin_of_open34', 'c')]),
         ('TailZ42', [('sixContactMin_of_open35', 'c')]),
         ('TailZ43', [('sixContactMin_of_open36', 'c')]),
         ('TailZ44', [('OpenResearchLeaves27', 's'), ('openResearchLeaves26_of_OpenResearchLeaves27', 'm'),
                      ('sixContactMin_of_open37', 'c')]),
         ('TailZ45', [('OpenResearchLeaves28', 's'), ('openResearchLeaves27_of_OpenResearchLeaves28', 'm'),
                      ('sixContactMin_of_open38', 'c')])]

HEADER = '''import ZInQKernel.OneProof.H.TailZ45
import ZInQKernel.Contrib.OneProof.RaynaudSemistableCP
import ZInQKernel.Contrib.OneProof.RaynaudSemistableSHcpOr

/-! # raynaud-narrow: the H chain with Raynaud's criterion in the form it consumes (generated)

Generated by `scratch/raynaud-narrow/gen_chain.py`; do not edit by hand. Task raynaud-narrow
(docs/research/raynaud-narrow.md).

The research field `raynaudSemistableSHOr` (TailZ45; before dict-models `raynaudSemistableSH`, TailZ23) is read by
the chain only through `raynaudSemistable_of14` (TailZ23), whose readers `raynaudCriterionNF_of14` and
`ss1_ss3_of14NF` (TailZ26) use it at number fields (closure probe, `scratch/raynaud-narrow/fielduse-output.txt`). This
module re-versions every declaration from `sixContactMin_of_open17` to `sixContactMin_of_open38` whose type mentions
a research bundle of generation 14 to 28, in the namespace `HDec.HSyn.RNarrow`: each research bundle carries
`raynaudSemistableSHcp : ReductB.RaynaudSemistableSHcp` in place of `raynaudSemistableSH` (generation 28: in place of
`raynaudSemistableSHOr`), and the two readers are re-proved from it (raynaud-proof's
`RaynaudCP.raynaudCriterion_leavesNF_cp`, neron-dvr's `GapNeron.ss1_ss3_of_cp_fullNF`). Every other line is the
original's, verbatim. The top theorem is `HDec.HSyn.RNarrow.sixContactMin_of_open38`, with the textbook, added and
glue bundles of the original top (`OpenTextbookLeaves13`, `OpenAddedLeaves19`). `narrowed_of_current` maps the
current top research bundle to the narrowed one (the narrowed bundle is no stronger)
(through the printed leaf `RaynaudNarrow.RaynaudSemistableSHcpOr`). No `sorry`, no `axiom`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)

namespace HDec

namespace HSyn

namespace RNarrow
'''

def field_names(block):
    return [m.group(1) for l in block for m in [re.match(r"^  ([A-Za-z_][\w']*) :", l)] if m]


TAIL = '''
/-! ### The narrowed top from the current one -/

/-- **The narrowed research bundle from the current top one** (`HDec.HSyn.OpenResearchLeaves28`, TailZ45): the cp
field from `raynaudSemistableSHOr` by `RaynaudNarrow.cpOr_of_or` and `raynaudSemistableSHcp_of_cpOr'`; every other
field passed through. So `sixContactMin_of_open38` here needs no more than the current top. -/
theorem narrowed_of_current (n : HDec.HSyn.OpenResearchLeaves28) : OpenResearchLeaves28 where
{assigns}

/-- The current top theorem's conclusion through the narrowed chain. -/
theorem sixContactMin_of_current (r : HDec.HSyn.OpenResearchLeaves28) (t : OpenTextbookLeaves13)
    (l : OpenAddedLeaves19) : ZInQ.SixContactMin :=
  sixContactMin_of_open38 (narrowed_of_current r) t l
'''

FOOTER = '''
end RNarrow

end HSyn

end HDec

#print axioms HDec.HSyn.RNarrow.sixContactMin_of_open38
#print axioms HDec.HSyn.RNarrow.sixContactMin_of_current
'''


def main():
    out = [HEADER]
    cache = {}
    for fn, items in PLAN:
        path = H + fn + '.lean'
        if path not in cache:
            cache[path] = decls(path)
        D = cache[path]
        out.append(f'/-! ### from `{fn.split("/")[-1]}` -/\n')
        for name, kind in items:
            if kind == 'raw':
                out.append(name + '\n')
                continue
            block = D[name]
            if kind == 's':
                block = fix_struct(block)
            elif kind == 'm':
                block = fix_map(block)
            else:
                assert not any(FIELD.match(l) or ASSIGN.match(l) for l in block), name
            out.append('\n'.join(block) + '\n')
    names = field_names(fix_struct(cache[H + 'TailZ45.lean']['OpenResearchLeaves28']))
    assigns = '\n'.join(
        '  raynaudSemistableSHcp := _root_.RaynaudNarrow.raynaudSemistableSHcp_of_cpOr' + "'" +
        ' (_root_.RaynaudNarrow.cpOr_of_or n.raynaudSemistableSHOr)' if f == 'raynaudSemistableSHcp' else f'  {f} := n.{f}'
        for f in names)
    out.append(TAIL.replace('{assigns}', assigns).replace('{{', '{').replace('}}', '}'))
    src = '\n'.join(out) + FOOTER
    assert 'raynaudSemistableSH ' not in src.replace('`raynaudSemistableSH`', '')
    open(OUT, 'w').write(src)
    print(f'wrote {OUT}: {src.count(chr(10))} lines')


if __name__ == '__main__':
    main()
