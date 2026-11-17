"""fold-b112 fold 1 (bost-gr9 on the fold-b112 line): the research field `bostLowerBoundAnSS` (Bost's bound over the
printed semistability) replaced by Gaudron-Remond section 9 over the printed semistability, `gaudronRemondSec9LowerAnSS`
(ZInQ.BostGR9.GaudronRemondSec9LowerAnSS, Contrib/OneProof/GaudronRemondSection9SS.lean). Weaker-leaf bypass, regenerated
from bost-gr9's generator (scratch/bost-gr9/gen_bypass.py) on the current head.

The new leaf is strictly weaker than the field (ZInQ.BostGR9.sec9_bound_lt_bost), so no proof of the field exists and
autofold.py cannot be used. As in bost-gr9, every declaration reachable from Main's top theorem whose type mentions a
bundle carrying the Bost field (in any of its forms) is copied VERBATIM into the sub-namespace HDec.HSyn.GR9, with only:
  * field types in the copied structures: SemistabAssembly.BostLowerBoundAnSS / R3Residual.BostLowerBoundAn /
    HeightFix.BostLowerBoundPrinted / HeightSplit.BostLowerBound -> BostGR9.GaudronRemondSec9LowerAnSS /
    GaudronRemondSec9LowerAn / GaudronRemondSec9LowerPrinted / HeightSplit.GRBostBound;
  * the field `bostLowerBoundAnSS` renamed `gaudronRemondSec9LowerAnSS` (new doc comment), `.bostLowerBoundAnSS` likewise;
  * the conversions of the field replaced by their GR section 9 analogues, same argument shapes:
      SemistabAssembly.bostLowerBoundAn_of_ss          -> BostGR9.gaudronRemondSec9LowerAn_of_ss
      R3Residual.bostLowerBoundPrinted_of_an            -> BostGR9.sec9Printed_of_an
      ChevFree.bostLowerBound_of_printed_free X Y Z     -> BostGR9.grBostBound_of_sec9Printed X Y Z ChevFree.semiAbelianDescendsPerfect_proof
      SemiAbDescend.bostLowerBound_of_printed_chevalley -> BostGR9.grBostBound_of_sec9Printed_chevalley
      HeightSplit.r21_of_leaves'                        -> BostGR9.r21_of_grBost'
  * the top research bundle (Main's binder `r`) is emitted in HDec.HSyn under the next free OpenResearchLeaves number
    (with the javanpeykarThm111An field doc's semistability phrase corrected, inbox 62), and every copy names it.
The new top theorem `HDec.HSyn.sixContactMin_of_open<N+1>` calls the copied top theorem. No existing declaration changes.
Main.lean is switched; kinds.tsv: the bostLowerBoundAnSS row is replaced by the new leaf's row; claims.tsv rows dropped.

Usage (repository root), two steps, one Lean process:
  python3 scratch/fold-b112/gen_gr9_fold.py closure      # writes scratch/fold-b112/GR9Closure.lean for Main's top
  lake env lean scratch/fold-b112/GR9Closure.lean        # writes scratch/fold-b112/gr9-closure.tsv (~2.5 min)
  python3 scratch/fold-b112/gen_gr9_fold.py [--dry-run]  # writes ZInQKernel/OneProof/H/TailZ<j>.lean, Main, kinds, claims
"""
import csv, os, re, sys

sys.path.insert(0, 'scripts/one_proof')
import autofold as af  # noqa: E402
import render_open  # noqa: E402

D = 'scratch/fold-b112/'
H = 'ZInQKernel/OneProof/H/'
CONTRIB = 'ZInQKernel.Contrib.OneProof.GaudronRemondSection9SS'
OLDF, NEWF = 'bostLowerBoundAnSS', 'gaudronRemondSec9LowerAnSS'
NEWT = '_root_.ZInQ.BostGR9.GaudronRemondSec9LowerAnSS'
NS = 'GR9'

FIELD_TYPES = [
    ('_root_.ZInQ.SemistabAssembly.BostLowerBoundAnSS', NEWT),
    ('_root_.ZInQ.R3Residual.BostLowerBoundAn', '_root_.ZInQ.BostGR9.GaudronRemondSec9LowerAn'),
    ('_root_.ZInQ.HeightFix.BostLowerBoundPrinted', '_root_.ZInQ.BostGR9.GaudronRemondSec9LowerPrinted'),
    ('_root_.ZInQ.HeightSplit.BostLowerBound', '_root_.ZInQ.HeightSplit.GRBostBound'),
]
CONVS = [
    ('_root_.ZInQ.SemistabAssembly.bostLowerBoundAn_of_ss ', '_root_.ZInQ.BostGR9.gaudronRemondSec9LowerAn_of_ss '),
    ('_root_.ZInQ.R3Residual.bostLowerBoundPrinted_of_an ', '_root_.ZInQ.BostGR9.sec9Printed_of_an '),
    ('_root_.ZInQ.SemiAbDescend.bostLowerBound_of_printed_chevalley ',
     '_root_.ZInQ.BostGR9.grBostBound_of_sec9Printed_chevalley '),
    ("_root_.ZInQ.HeightSplit.r21_of_leaves' ", "_root_.ZInQ.BostGR9.r21_of_grBost' "),
]
FREE = '_root_.ZInQ.ChevFree.bostLowerBound_of_printed_free '
SGR_SIBLINGS = ['added12_of_open29_hf_pz']

NEWDOC = ('  /-- bost-gr9 (fold-b112), printed form over the printed semistability: Gaudron-Remond, Polarisations et '
          'isogenies, Duke Math. J. 163 (2014), 2057-2108, section 9, proof of Lemme 9.1, p. 2098 (read by the locator '
          'audit, locators R21; cited by the manuscript at diophantine_zq.tex L894-895, step E4): h_F(A) >= -(3/2) dim A '
          'for every abelian variety over a number field, Faltings\' original normalization, over '
          'ZInQ.SemistabAssembly.IsAnStableHeightSS (semistable reduction as printed, as gaudronRemondThm14AnSS). '
          'Replaces bostLowerBoundAnSS (strictly stronger: -(g/2) log(2 pi^2), BostGR9.sec9_bound_lt_bost; it implies '
          'the leaf, BostGR9.gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS); consumed through '
          'BostGR9.gaudronRemondSec9LowerAn_of_ss, BostGR9.sec9Printed_of_an, BostGR9.grBostBound_of_sec9Printed and '
          'BostGR9.r21_of_grBost\' (R21). -/')
JP_OLD = 'semistable reduction as printed, semistab-assembly)'
JP_NEW = ('semistability: semi-abelian reduction of the Jacobian\'s Neron model, IsSemistablePrinted, semistab-assembly; '
          'not the print\'s curve-model semistability, Def. 2.2.1)')

ROW = dict(
    kind='published',
    flag=('pending reading (GR p. 2098 normalization): new printed leaf, the GR14 section 9 inequality h(A) >= -(3/2) dim A '
          '(p. 2098, AUDIT-READ in locators R21, no statement check recorded; the normalization warning on that page is '
          'unread, and a Deligne reading would be weaker, bost-gr9 K3); cited inside a proof (Lemme 9.1; GR refer to Bost '
          '1996 and GR CMH 2014 Cor. 8.4, bost-gr9 K2); R3\' (etale coordinates are holomorphic charts, inside '
          'IsAnMetricSq) remains a step, as for gaudronRemondThm14AnSS; semistability as printed (IsAnStableHeightSS, '
          'fold-b112, as semistab-assembly); provenance cited'),
    source=('Gaudron-Remond, Polarisations et isogenies, Duke Math. J. 163 (2014), 2057-2108, section 9, proof of Lemme '
            '9.1, p. 2098 (locators.md R21); cited by diophantine_zq.tex L894-895 (step E4); over the stable height with '
            'the metric on A_tau(C)^an (r3-residual), semistability as printed (IsAnStableHeightSS; semistab-assembly); '
            'replaces Bost, Sem. Bourbaki 795 (not in the manuscript\'s bibliography; strictly stronger, bost-gr9)'),
    rated_by='bost-gr9 (fold-b112); pending review',
)


def closure_file():
    _, binders, top, N, last_mod, k = af.main_state()
    src = open('scratch/bost-gr9/Closure.lean').read()
    src = src.replace('TailZ74', last_mod).replace('sixContactMin_of_open67', top)
    src = src.replace('scratch/bost-gr9/closure.tsv', D + 'gr9-closure.tsv')
    src = src.replace('#[`ZInQ.R3Residual.BostLowerBoundAn,',
                      '#[`ZInQ.SemistabAssembly.BostLowerBoundAnSS, `ZInQ.R3Residual.BostLowerBoundAn,')
    assert 'BostLowerBoundAnSS' in src and D + 'gr9-closure.tsv' in src
    open(D + 'GR9Closure.lean', 'w').write(src)
    print(f'wrote {D}GR9Closure.lean (root HDec.HSyn.{top}, import {last_mod}); now: lake env lean {D}GR9Closure.lean')


cache = {}


def lines_of(mod):
    if mod not in cache:
        cache[mod] = open(mod.replace('.', '/') + '.lean', encoding='utf-8').read().split('\n')
    return cache[mod]


def context(lines, upto):
    """Scope stack before line `upto` (1-based): [kind, name, [open/set_option lines]] (bost-gr9's)."""
    stack = [['root', '', []]]
    for l in lines[:upto - 1]:
        s = l.strip()
        m = re.match(r'^namespace (\S+)$', s)
        if m:
            stack.append(['namespace', m.group(1), []]); continue
        m = re.match(r'^(noncomputable )?section( (\S+))?$', s)
        if m:
            stack.append(['section', m.group(3) or '', []]); continue
        if re.match(r'^end( (\S+))?$', s):
            stack.pop(); continue
        if (s.startswith('open ') and not s.endswith(' in')) or s.startswith('set_option '):
            if l.startswith(' '):
                continue
            stack[-1][2].append(s)
    return stack


def replace_free(text):
    """ChevFree.bostLowerBound_of_printed_free X Y Z -> BostGR9.grBostBound_of_sec9Printed X Y Z <descent proof>."""
    while FREE in text:
        i = text.index(FREE)
        j = i + len(FREE)
        args = []
        while len(args) < 3:
            while text[j] == ' ':
                j += 1
            if text[j] == '(':
                d, s0 = 0, j
                while True:
                    if text[j] == '(':
                        d += 1
                    elif text[j] == ')':
                        d -= 1
                        if d == 0:
                            j += 1
                            break
                    j += 1
                while j < len(text) and text[j] not in ' \n()':  # a projection after the parenthesis
                    j += 1
                args.append(text[s0:j])
            else:
                s0 = j
                while j < len(text) and text[j] not in ' \n)':
                    j += 1
                args.append(text[s0:j])
        text = (text[:i] + '(_root_.ZInQ.BostGR9.grBostBound_of_sec9Printed ' + ' '.join(args)
                + ' _root_.ZInQ.ChevFree.semiAbelianDescendsPerfect_proof)' + text[j:])
    return text


def main():
    if 'closure' in sys.argv[1:]:
        return closure_file()
    dry = '--dry-run' in sys.argv
    main_src, binders, top, N, last_mod, k = af.main_state()
    R0 = dict((v, s) for v, s in binders)['r']
    m = re.match(r'^OpenResearchLeaves(\d+)$', R0)
    assert m, R0
    newR = f'OpenResearchLeaves{int(m.group(1)) + 1}'
    if af.os.system(f"grep -q 'structure {newR} ' {H}*.lean") == 0:
        af.die(f'{newR} exists already')
    j = k + 1
    while os.path.exists(os.path.join(H, f'TailZ{j}.lean')):
        j += 1
    new_mod = f'TailZ{j}'
    rows = [l.rstrip('\n').split('\t') for l in open(D + 'gr9-closure.tsv', encoding='utf-8') if l.strip()]
    names = [r[0] for r in rows]
    if f'HDec.HSyn.{top}' not in names or f'HDec.HSyn.{R0}' not in names:
        af.die('gr9-closure.tsv is stale: rerun the closure step for the current top ' + top)
    out = []
    top_struct = None
    for name, mod, s, e, kind in rows:
        s, e = int(s), int(e)
        L = lines_of(mod)
        st = context(L, s)
        ns = [x[1] for x in st if x[0] == 'namespace']
        assert '.'.join(ns).startswith('HDec.HSyn'), name
        pre = []
        q = s - 2
        while q >= 0 and L[q].strip().endswith(' in') and L[q].strip().startswith('open '):
            pre.insert(0, L[q]); q -= 1
        text = '\n'.join(pre + L[s - 1:e])
        if kind == 'structure':
            for a, b in FIELD_TYPES:
                text = re.sub(re.escape(a) + r'\b', b, text)
            tl = text.split('\n')
            idx = [i for i, x in enumerate(tl) if x.strip().startswith(OLDF + ' :')]
            if idx:
                i = idx[0]
                dd = i - 1
                assert tl[dd].rstrip().endswith('-/'), name
                while not tl[dd].lstrip().startswith('/--'):
                    dd -= 1
                tl[dd:i + 1] = [NEWDOC, f'  {NEWF} : {NEWT}']
            text = '\n'.join(tl)
            for bad in ('BostLowerBound ', 'BostLowerBoundAn', 'BostLowerBoundPrinted', 'BostLowerBound\n'):
                assert bad not in text, (name, bad)
        else:
            text = text.replace('.' + OLDF, '.' + NEWF)
            for a, b in CONVS:
                text = text.replace(a, b)
            text = replace_free(text)
            for a, _ in CONVS + [(FREE, None)]:
                assert a not in text, (name, a)
            assert OLDF not in text, name
        if '.SGRFold.' in name:
            for x in SGR_SIBLINGS:
                text = re.sub(r'(?<![.\w])' + x + r'\b', '_root_.HDec.HSyn.SGRFold.' + x, text)
        if name == f'HDec.HSyn.{R0}':
            # the new top bundle, in HDec.HSyn
            assert kind == 'structure' and len(st) == 3 and [x[1] for x in st[1:]] == ['HDec', 'HSyn'], st
            tl = text.split('\n')
            si = [i for i, x in enumerate(tl) if x.startswith(f'structure {R0} : Prop where')]
            assert len(si) == 1
            tl = tl[si[0] + 1:]
            body = '\n'.join(tl)
            assert body.count(JP_OLD) == 1, 'javanpeykarThm111An doc phrase'
            body = body.replace(JP_OLD, JP_NEW)
            top_struct = body
            continue
        text = re.sub(r'(?<![.\w])' + R0 + r'\b', newR, text)
        blk = ['-- copied from %s:%d (%s)' % (mod.replace('.', '/') + '.lean', s, name)]
        closers, seen = [], False
        for kind_, nm, opens in st[1:]:
            if kind_ == 'namespace':
                parts, newparts = nm.split('.'), []
                for p in parts:
                    newparts.append(p)
                    if p == 'HSyn' and not seen:
                        newparts.append(NS); seen = True
                blk.append('namespace ' + '.'.join(newparts))
                closers.insert(0, 'end ' + '.'.join(newparts))
            else:
                blk.append('section')
                closers.insert(0, 'end')
            blk += opens
        assert seen, name
        blk.append(text)
        blk += closers
        out.append('\n'.join(blk))
    assert top_struct is not None
    nfields = len(re.findall(r'^  [A-Za-z_][\w\']* :', top_struct, re.M))
    tvar = [(v, s) for v, s in binders]
    params = ' '.join(f'({v} : {newR if s == R0 else s})' for v, s in tvar)
    args = ' '.join(v for v, _ in tvar)
    hdr = f'''import ZInQKernel.OneProof.H.{last_mod}
import {CONTRIB}

/-! # OneProof H, bost-gr9 (fold-b112): `sixContactMin_of_open{N + 1}` (generated by scratch/fold-b112/gen_gr9_fold.py)

Field replaced: the research field `{OLDF}` (Bost's bound `h_F >= -(g/2) log(2 pi^2)` over the printed semistability,
not cited by the manuscript) by `{NEWF}` (`ZInQ.BostGR9.GaudronRemondSec9LowerAnSS`: Gaudron-Remond, Duke Math. J. 163
(2014), section 9, `h_F >= -(3/2) dim`, as the manuscript cites it at diophantine_zq.tex L894-895; over the printed
semistability). The new leaf is strictly weaker than the field (`ZInQ.BostGR9.sec9_bound_lt_bost`), so the next
generation cannot map to `{R0}`: this is bost-gr9's weaker-leaf bypass, regenerated on this head. The {len(rows) - 1}
declarations of the live path that carry the field (the research bundles from `{R0}` down to `OpenResearchLeaves8EB`, their
conversions, the height-row consumer and the `sixContactMin_of_open*` chain; `scratch/fold-b112/gr9-closure.tsv`) are
copied verbatim into `HDec.HSyn.{NS}` with the field's type weakened at each generation and its conversions replaced by
the GR section 9 ones (`BostGR9.gaudronRemondSec9LowerAn_of_ss`, `sec9Printed_of_an`, `grBostBound_of_sec9Printed` with
the proved descent glue `ChevFree.semiAbelianDescendsPerfect_proof`, `r21_of_grBost'`). `{newR}` is `{R0}` with the
field replaced. Every existing declaration is unchanged. -/

set_option linter.style.longLine false

namespace HDec

namespace HSyn

/-- `{R0}` with `{OLDF}` replaced by `{NEWF}` (bost-gr9, fold-b112: Gaudron-Remond section 9 over the printed
semistability, the manuscript's citation for step E4). {nfields} fields. -/
structure {newR} : Prop where
{top_struct}

end HSyn

end HDec

'''
    ftr = f'''

namespace HDec

namespace HSyn

/-- **G0 with only the open leaves and the open glue** (bost-gr9, fold-b112): `{top}` with Gaudron-Remond section 9
over the printed semistability in place of `{OLDF}`, through the copied chain `HDec.HSyn.{NS}`. -/
theorem sixContactMin_of_open{N + 1} {params} : ZInQ.SixContactMin :=
  {NS}.{top} {args}

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open{N + 1}
'''
    text = hdr + '\n\n'.join(out) + ftr
    # Main.lean
    ms = main_src.replace(f'import ZInQKernel.OneProof.H.{last_mod}', f'import ZInQKernel.OneProof.H.{new_mod}', 1)
    ms = ms.replace(f'HDec.HSyn.{R0})', f'HDec.HSyn.{newR})', 1)
    ms = ms.replace(f'HDec.HSyn.{top} ', f'HDec.HSyn.sixContactMin_of_open{N + 1} ', 1)
    anchor = 'The hypotheses of `frozenTarget` are therefore exactly the open statements.'
    if anchor not in ms:
        af.die('Main.lean docstring anchor not found')
    para = (f'bost-gr9 (folded by fold-b112) replaced the research field `{OLDF}` (Bost\'s bound, not cited by the manuscript and\n'
            f'strictly stronger than its citation) by `{NEWF}` (Gaudron-Remond, Duke 2014, section 9, `h_F >= -(3/2) dim`, the\n'
            'manuscript\'s citation at L894-895, over the printed semistability; `Contrib/OneProof/GaudronRemondSection9.lean`\n'
            f'and `GaudronRemondSection9SS.lean`). `{newR}` (`{new_mod}`) is `{R0}` with the field replaced, and\n'
            f'`HDec.HSyn.sixContactMin_of_open{N + 1}` goes through a copy of the {len(rows) - 1} declarations of the chain that carry\n'
            f'the field (namespace `HDec.HSyn.{NS}`, weaker-leaf bypass, generated by `scratch/fold-b112/gen_gr9_fold.py`); no\n'
            'existing declaration is changed.\n\n')
    ms = ms.replace(anchor, para + anchor, 1)
    _, binders2, top2, _, mod2, _ = af.main_state(ms)
    assert top2 == f'sixContactMin_of_open{N + 1}' and mod2 == new_mod, (top2, mod2)
    # kinds.tsv
    krows, cols = af.load_kinds()
    before = af.counts(krows)
    old = next(r for r in krows if r['field'] == OLDF)
    new = dict(old)
    new.update(field=NEWF, **ROW)
    new['strict'] = 'LEAF' if new['kind'] == 'published' and not render_open.must_be_glue(new['flag']) else 'GLUE'
    new['strictest'] = new['strict']
    new['flag_class'] = af.flag_class(new['flag'], new['strict'], new['strictest'], '')
    kept = [r for r in krows if r['field'] != OLDF] + [new]
    with open(af.CLAIMS, newline='') as fh:
        held = {r['field'] for r in csv.DictReader(fh, delimiter='\t') if r.get('hold') == 'held'}
    probs = render_open.kinds_row_problems(new, {r['field'] for r in kept}, held)
    if probs:
        af.die('new row problems: ' + '; '.join(probs))
    after = af.counts(kept)
    print(f'strict count: {before[1]}/{before[2]} on {before[0]} -> {after[1]}/{after[2]} on {after[0]}; '
          f'strictest {before[3]}/{before[4]} -> {after[3]}/{after[4]}')
    print(f'copied {len(rows) - 1} declarations; {R0} -> {newR} ({nfields} fields); module {new_mod}; '
          f'new row flag_class {new["flag_class"]}, {new["strict"]}/{new["strictest"]}')
    if after[2] > before[2] or after[4] > before[4]:
        af.die('a GLUE count rises')
    if dry:
        print(text)
        return
    open(H + new_mod + '.lean', 'w').write(text)
    open(af.MAIN, 'w').write(ms)
    order = {'research': 0, 'textbook': 1, 'added': 2, 'glue': 3}
    pos = {r['field']: i for i, r in enumerate(krows)}
    pos[NEWF] = pos[OLDF]
    kept.sort(key=lambda r: (order.get(r['bundle'], 9), r['field'].lower() if r['bundle'] in order else pos[r['field']]))
    with open(af.KINDS, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter='\t', lineterminator='\n', extrasaction='ignore')
        w.writeheader()
        w.writerows(kept)
    with open(af.CLAIMS, newline='') as fh:
        rd = csv.DictReader(fh, delimiter='\t')
        crows, ccols = list(rd), rd.fieldnames
    with open(af.CLAIMS, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=ccols, delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(r for r in crows if r['field'] != OLDF)
    print(f'wrote {H}{new_mod}.lean, switched {af.MAIN} to sixContactMin_of_open{N + 1}, updated {af.KINDS}, {af.CLAIMS}')


if __name__ == '__main__':
    main()
