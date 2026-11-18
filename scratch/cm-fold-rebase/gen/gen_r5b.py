"""cm-fold-rebase: the R5ptProps prune copies (weak-row bypass) for the CM-branch route on main's bost-gr9 chain.

cm-branch2's gen_r5.py (scratch/cm-branch2/gen/gen_r5.py) made namespace-aware and incremental:

Input: scratch/cm-fold-rebase/dirty3.tsv (output of scratch/cm-fold-rebase/Dirty3.lean, rooted at
HDec.HSyn.GR9.sixContactMin_of_open48_eb_k954_cm2): name, module, idx, range, TYPE|value, and `ALL <name>` lines
(the ZInQKernel closure of the root). Every non-generated dirty declaration that cm-branch2 has NOT already copied
(cm-branch2's dirty set scratch/cm-branch2/dirty.tsv; its copies are in CMBranch/R5Prune*.lean and are reused) is
copied verbatim from its source file, in import/line order, into ZInQKernel/Contrib/OneProof/CMFoldRebase/R5GR9*.lean,
in its own namespace and context, with
  * every reference to a dirty declaration renamed `<last>_r5` (same namespace; S.x members of a dirty structure S
    become S_r5.x), the referent resolved as Lean does: innermost enclosing namespace first, then opened namespaces,
  * every `R5ptProps a b` replaced by `True`,
  * cm-branch2's hand patches (PATCHES) at the producers that built R5ptProps from Gonzalez-Rotger.
"""
import re, sys, os
sys.path.insert(0, os.path.dirname(__file__))
import leanctx

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..'))
GEN_SUFFIXES = ('.mk', '.rec', '.recOn', '.casesOn', '.noConfusion', '.noConfusionType', '.ctorIdx',
                '.sizeOf_spec', '.injEq', '.inj', '.mk.injEq', '.mk.inj', '.mk.sizeOf_spec', '.mk.noConfusion',
                '.ext', '.ext_iff', '.congr_simp')
SKIP = {'HDec.HSyn.r5fp_of_rep', 'ShimuraSplit.r5fp_of_point', 'ShimuraSplit.point_of_r5fp',
        'GRDict.r5ptProps_of_thm512', 'GRDict.gonzalezRotgerX6Ab_of_witness',
        'GRX6AbPrint.gonzalezRotgerX6Ab_of_coarse', 'GRX6AbPrint.gonzalezRotgerX6Ab_of_print'}
SEEDS = {'LeafQM.AV.R5ptProps'}


def read_rows(p):
    rows, allnames = [], set()
    for line in open(p):
        parts = line.rstrip('\n').split('\t')
        if len(parts) == 2 and parts[0] == 'ALL':
            allnames.add(parts[1]); continue
        if len(parts) < 5: continue
        name, mod, idx, rng, kind = parts[:5]
        rows.append((name, mod, int(idx), rng, kind))
    return rows, allnames


def copy_set(rows):
    """cm-branch2's selection: the declarations a weak copy is needed for, and the dirty structures."""
    names = {r[0] for r in rows}
    structs = {n[:-3] for n in names if n.endswith('.mk')}
    srange = {}
    for (name, mod, idx, rng, kind) in rows:
        if name in structs and rng != '-':
            a, b = map(int, rng.split('-'))
            srange[name] = (mod, a, b)
    rowmap = {r[0]: r for r in rows}

    def generated(n):
        if n in SEEDS or n in SKIP: return True
        if any(n.endswith(s) for s in GEN_SUFFIXES): return True
        if re.search(r'\._proof_\d+$|\.match_\d+|\._simp_\d+|\.eq_\d+$|\._sunfold$|\._unsafe_rec$|_def$', n): return True
        for s in structs:
            if n.startswith(s + '.') and n.count('.') == s.count('.') + 1:
                r = rowmap.get(n)
                if s in srange and r is not None and r[3] != '-':
                    a = int(r[3].split('-')[0])
                    m, sa, sb = srange[s]
                    if not (r[1] == m and sa <= a <= sb):
                        return False
                return True
        return False

    copies = [r for r in rows if not generated(r[0]) and r[3] != '-']
    for (name, mod, idx, rng, kind) in rows:
        if name.endswith('.mk') and name[:-3] in structs:
            S = name[:-3]
            path = os.path.join(ROOT, mod.replace('.', '/') + '.lean')
            Ls = leanctx.lines_of(path)
            last = S.split('.')[-1]
            hits = [i for i, l in enumerate(Ls) if re.match(r'^structure\s+' + re.escape(last) + r'\b', l)]
            if len(hits) != 1:
                # several structures with this last name in one file (GR9 copies): pick by namespace
                hits = [i for i in hits if leanctx.context(path, i + 1)[0] == '.'.join(S.split('.')[:-1])]
            if len(hits) != 1:
                print('STRUCT?', S, len(hits)); continue
            a = hits[0]
            s0 = a
            if s0 > 0 and Ls[s0 - 1].rstrip().endswith('-/'):
                while s0 > 0 and not Ls[s0 - 1].startswith('/--'):
                    s0 -= 1
                s0 -= 1
            b = a + 1
            while b < len(Ls) and (Ls[b].startswith(' ') or Ls[b].strip() == '' and b + 1 < len(Ls) and Ls[b + 1].startswith(' ')):
                b += 1
            if not any(c[0] == S for c in copies):
                copies.append((S, mod, idx, f'{s0 + 1}-{b}', 'TYPE'))
    copies.sort(key=lambda r: (r[2], int(r[3].split('-')[0])))
    return copies, structs


rows, ALL = read_rows(os.path.join(ROOT, 'scratch/cm-fold-rebase/dirty3.tsv'))
OLD_ROWS, _ = read_rows(os.path.join(ROOT, 'scratch/cm-branch2/dirty.tsv'))
copies, structs = copy_set(rows)
old_copies, old_structs = copy_set(OLD_ROWS)
OLD = {r[0] for r in old_copies}
rename = {r[0] for r in copies} | OLD
dstructs = {r[0] for r in copies if r[0] in structs} | {r[0] for r in old_copies if r[0] in old_structs}
new_copies = [r for r in copies if r[0] not in OLD]
missing_old = sorted(OLD - {r[0] for r in copies})


def newname(full):
    c = full.split('.')
    for k in range(1, len(c)):
        if '.'.join(c[:k]) in dstructs:
            return '.'.join(c[:k - 1] + [c[k - 1] + '_r5'] + c[k:])
    return '.'.join(c[:-1] + [c[-1] + '_r5'])


by_last = {}
for n in rename:
    by_last.setdefault(n.split('.')[-1], []).append(n.split('.'))

TOK = re.compile(r"(?<![\w'.!?])((?:_root_\.)?[^\W\d][\w'!?]*(?:\.[\w'!?]+)*)")
CUR_NS = ['']


def ren_token(m):
    t = m.group(1)
    root = t.startswith('_root_.')
    comps = (t[len('_root_.'):] if root else t).split('.')
    ns = CUR_NS[0].split('.') if CUR_NS[0] else []
    for k in range(len(comps), 0, -1):
        head = comps[:k]
        # Lean's resolution: the innermost enclosing namespace first
        prefixes = [[]] if root else [ns[:j] for j in range(len(ns), -1, -1)]
        for p in prefixes:
            full = '.'.join(p + head)
            if full in ALL or full in rename:
                if full in rename:
                    return '_root_.' + '.'.join([newname(full)] + comps[k:])
                return t
        # opened namespaces / dot notation: cm-branch2's suffix match
        cands = by_last.get(head[-1], [])
        for c in cands:
            if k == 1 and any('.'.join(c[:j]) in dstructs for j in range(1, len(c))):
                continue
            if (root and c == head) or (not root and c[-k:] == head):
                return '_root_.' + '.'.join([newname('.'.join(c))] + comps[k:])
    return t


R5RE = re.compile(r"(?:_root_\.)?(?:LeafQM\.AV\.)?R5ptProps\s+(\([^()]*\)|[^\s()]+)\s+(\([^()]*\)|[^\s()]+)")


def transform(text, ns):
    CUR_NS[0] = ns
    text = R5RE.sub('True', text)
    return TOK.sub(ren_token, text)


PATCHES = [
 ("  r5 : LeafQM.AV.R5fp\n", "  r5 : True\n"),
 ("  r5 := r5fp_of_rep r.r1r2", "  r5 := trivial"),
 ("gonzalezRotgerX6Ab := _root_.GRX6AbPrint.gonzalezRotgerX6Ab_of_print n.gonzalezRotgerThm512X6 n.shimuraMainThmIDeligneY3AbU n.x6CoarseModuli t.gagaMorphism t.mumfordTorsionAlgClosed",
  "gonzalezRotgerX6Ab := _root_.HDec.QMSplit.Moduli.gonzalezRotgerX6Ab_r5_of_coarse n.shimuraMainThmIDeligneY3AbU n.x6CoarseModuli"),
]


def main():
    print(len(copies), 'dirty copies in the new closure;', len(OLD), 'already copied by cm-branch2;',
          len(new_copies), 'new')
    print('cm-branch2 copies not dirty here (unused):', len(missing_old))
    hdr = ['import ZInQKernel.Contrib.OneProof.CMFoldRebase.Top3', '',
           '/-! # cm-fold-rebase: the weak-row bypass (R5ptProps carried as `True`) on the bost-gr9 chain, generated by',
           '`scratch/cm-fold-rebase/gen/gen_r5b.py` from the dirty set `scratch/cm-fold-rebase/dirty3.tsv`. Every declaration',
           'is a verbatim copy of the named original with dirty references renamed `_r5` and `R5ptProps X Ψ` replaced by',
           '`True` (cm-branch2\'s hand patches); the dirty declarations cm-branch2 already copied (CMBranch/R5Prune*.lean)',
           'are reused. -/', '', 'set_option maxHeartbeats 1000000', 'set_option autoImplicit false',
           'set_option linter.style.longLine false', '']
    out = []
    for name, mod, idx, rng, kind in new_copies:
        path = os.path.join(ROOT, mod.replace('.', '/') + '.lean')
        a, b = map(int, rng.split('-'))
        ns, ctx = leanctx.context(path, a)
        blk = leanctx.block(path, a, b)
        if 'SGRDirect' in mod:
            blk = re.sub(r"(?<![\w.\[])X(?![\w'\]])(?!\s*:=)", 'Polynomial.X', blk)
        out.append(f'-- copied from {mod} {a}-{b} ({name}, {kind})')
        out.append('noncomputable section')
        if ns: out.append(f'namespace {ns}')
        out.extend(ctx)
        out.append(transform(blk, ns))
        if ns: out.append(f'end {ns}')
        out.append('end')
        out.append('')
    txt = '\n'.join(out)
    for pat, rep in PATCHES:
        k = txt.count(pat)
        print('PATCH', k, 'x:', pat[:70])
        txt = txt.replace(pat, rep)
    blocks = ['-- copied from' + b for b in txt.split('-- copied from')[1:]]
    parts, cur = [], ''
    for b in blocks:
        if len((cur + b).encode()) > 140000 and cur:
            parts.append(cur); cur = ''
        cur += b
    parts.append(cur)
    n = len(parts)
    names = [f'R5GR9_{i + 1}' for i in range(n - 1)] + ['R5GR9']
    base = os.path.join(ROOT, 'ZInQKernel/Contrib/OneProof/CMFoldRebase/')
    header = '\n'.join(hdr) + '\n'
    for i, (nm, body) in enumerate(zip(names, parts)):
        imp = 'import ZInQKernel.Contrib.OneProof.CMFoldRebase.Top3' if i == 0 else f'import ZInQKernel.Contrib.OneProof.CMFoldRebase.{names[i - 1]}'
        h = header.replace('import ZInQKernel.Contrib.OneProof.CMFoldRebase.Top3', imp)
        h = h.replace('-/', f'Part {i + 1} of {n}. -/', 1)
        open(base + nm + '.lean', 'w').write(h + body)
    print('parts:', names, len(txt.splitlines()), 'lines')
    with open(os.path.join(ROOT, 'scratch/cm-fold-rebase/new-copies.tsv'), 'w') as f:
        for r in new_copies:
            f.write('\t'.join(map(str, r)) + '\n')


if __name__ == '__main__':
    main()
