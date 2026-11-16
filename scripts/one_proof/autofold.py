"""Fold contributions into the single proof: the next bundle generation, its conversion, the next top theorem.

A contribution proves an open hypothesis of `ZInQ.OneProof.frozenTarget` that is a field of one of its bundles
(docs/one-proof/OPEN.md), outright or from new published-form leaves; `#discharges` has checked it. This script
writes the fold that removes the field:

* a new module `ZInQKernel/OneProof/H/TailZ<j>.lean` (the first free number after the top) importing the current last module and the contributions,
  with the next generation of each affected bundle (the old fields minus the discharged ones, plus the new
  leaves), a theorem mapping it to the old generation that fills each discharged field with its proof, and the
  next top theorem `sixContactMin_of_open<N+1>`;
* `ZInQKernel/OneProof/Main.lean` switched to it;
* `docs/one-proof/kinds.tsv` (discharged rows removed, leaf rows added) and `claims.tsv` (rows of discharged
  fields removed). A leaf row takes the bundle, area_issue, packet, label and tier of the field it replaces. A published leaf with no
  flag gets the flag "unread: new printed leaf, no reading recorded" (it counts LEAF until a reading says
  otherwise; a plausible weaker reading is flagged "pending reading: ..." and counts GLUE). Its flag_class comes
  from the flag's prefix, as in the existing rows: pending reading, pending review, reading risk, restricted,
  unread, strictest reading, "locator UNVERIFIED" anywhere, else note. A leaf may give its own flag_class,
  area_issue, packet, label and tier instead. Every new row passes render_open.py's row checks before anything is written.

It refuses a fold that raises either GLUE count of kinds.tsv (the strict and the strictest column) unless
`--allow-rise` is given.

Spec (JSON):

    {"name": "leaf-fold15",
     "imports": ["ZInQKernel.Contrib.OneProof.IgusaCM24"],
     "discharges": [
       {"field": "igusaCMValue24", "proof": "_root_.CM24.igusaCMValue24_field"},
       {"field": "t09SymmIsogenyExists",
        "proof": "_root_.T09Pic.t09_of_leaves {n}.picZeroAbVar {n}.weilPairingMumford",
        "leaves": [{"name": "picZeroAbVar", "type": "_root_.T09Pic.PicZeroAbVar",
                    "doc": "Mumford, Abelian varieties, 13 (printed form)", "kind": "published", "flag": "",
                    "source": "Mumford, Abelian varieties, section 13"}]}]}

In "proof", `{n}` stands for the new bundle (so a leaf is `{n}.<leaf>`), and `{r}`, `{t}`, `{l}`, `{g}` (frozenTarget's
variable names) for the other bundles' new values, so a proof may use their fields (`{t}.gagaMorphism`); write types and proofs fully qualified
(`_root_.` for names outside `HDec`), since the new module opens nothing. Leaves go into the bundle of the field
they replace.

Usage, from the repository root:

    python3 scripts/one_proof/autofold.py SPEC.json [--allow-rise] [--dry-run]

Then build and check (the same checks as every fold): `lake build +ZInQKernel.OneProof.Main`;
`#print axioms ZInQ.OneProof.frozenTarget` standard; `scratch/one-proof/DumpCompact.lean` with `cmp_hashes.py` against the
base (no existing constant changed except `frozenTarget`); `lake env lean scripts/one_proof/OpenStatements.lean`;
`python3 scripts/one_proof/render_open.py`, then `render_open.py --check`.
"""
import csv, glob, json, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import render_open  # noqa: E402  (its row checks)

H = 'ZInQKernel/OneProof/H/'
MAIN = 'ZInQKernel/OneProof/Main.lean'
KINDS = 'docs/one-proof/kinds.tsv'
CLAIMS = 'docs/one-proof/claims.tsv'
NL = '\n'


def die(msg):
    print('autofold: ' + msg)
    sys.exit(1)


def main_state():
    s = open(MAIN).read()
    m = re.search(r'theorem _root_\.ZInQ\.OneProof\.frozenTarget\s*\n(.*?)\)\s*:\s*\n\s*ZInQ\.FrozenTarget', s, re.S)
    if not m:
        die('cannot find frozenTarget in Main.lean')
    sig = m.group(1)
    binders = re.findall(r'\((\w+) : HDec\.HSyn\.(\w+)\)', sig)
    top = re.search(r'HDec\.HSyn\.(sixContactMin_of_open(\d+)) (\w+(?: \w+)*)\)', s)
    imp = re.search(r'^import ZInQKernel\.OneProof\.H\.(TailZ(\d+))$', s, re.M)
    if not (binders and top and imp):
        die('cannot parse Main.lean (bundles, top theorem or last module)')
    return s, binders, top.group(1), int(top.group(2)), imp.group(1), int(imp.group(2))


def find_struct(name):
    for fn in sorted(glob.glob(H + '*.lean')):
        L = open(fn).read().split(NL)
        for i, l in enumerate(L):
            if l.startswith(f'structure {name} : Prop where'):
                j = i + 1
                while j < len(L) and L[j].strip() != '' and not L[j].startswith(('theorem', 'def', 'structure', '/-', 'end')):
                    j += 1
                return fn, L[i + 1:j]
    die(f'structure {name} not found under {H}')


def field_groups(block):
    """[(field name, lines including its docstring)] in order."""
    groups, cur = [], []
    for l in block:
        # a continuation line of the previous field's type
        if not cur and groups and l.startswith('    ') and not l.lstrip().startswith('/--'):
            groups[-1][1].append(l)
            continue
        cur.append(l)
        m = re.match(r'^  ([A-Za-z_][\w\']*) :', l)
        if m and not l.lstrip().startswith('/--'):
            groups.append((m.group(1), cur))
            cur = []
    if any(x.strip() for x in cur):
        die('unparsed trailing lines in a structure block: ' + repr(cur[:2]))
    return groups


def bump(name):
    m = re.match(r'^(.*?)(\d+)$', name)
    if not m:
        die(f'bundle name without a generation number: {name}')
    return f'{m.group(1)}{int(m.group(2)) + 1}'


def load_kinds():
    rows = list(csv.DictReader(open(KINDS), delimiter='\t'))
    return rows, list(rows[0].keys())


NEW_LEAF_FLAG = 'unread: new printed leaf, no reading recorded'
FLAG_PREFIXES = [('pending reading', 'pending-reading'), ('pending review', 'pending-review'),
                 ('reading risk', 'reading-risk'), ('restricted', 'restricted'), ('unread', 'unread')]


def flag_class(flag, strict, strictest, given=''):
    """The flag_class of a new row: the spec's, else from the flag's prefix; 'strictest' exactly when the strict
    and strictest columns differ."""
    classes = [c for c in given.split(',') if c and c != 'strictest']
    if not classes:
        classes = [c for pre, c in FLAG_PREFIXES if flag.startswith(pre)]
        if 'locator UNVERIFIED' in flag:
            classes.append('unverified-locator')
    if strict != strictest:
        classes.append('strictest')
    if flag and not classes:
        classes = ['note']
    return ','.join(classes)


def counts(rows):
    rows = [r for r in rows if r['bundle'] != 'frozenTarget']  # the H fields only, as OPEN.md counts them
    n = len(rows)
    L = sum(r['strict'] == 'LEAF' for r in rows)
    Ls = sum(r['strictest'] == 'LEAF' for r in rows)
    return n, L, n - L, Ls, n - Ls


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    if len(args) != 1:
        die('usage: autofold.py SPEC.json [--allow-rise] [--dry-run]')
    spec = json.load(open(args[0]))
    name = spec.get('name', 'autofold')
    main_src, binders, top, N, last_mod, k = main_state()
    by_field = {d['field']: d for d in spec['discharges']}

    # a contribution importing Main would make an import cycle once Main imports the fold
    for m in spec.get('imports', []):
        path = m.replace('.', '/') + '.lean'
        try:
            src = open(path).read()
        except OSError:
            die(f'import {m}: no file {path}')
        if re.search(r'^import ZInQKernel\.OneProof\.Main\s*$', src, re.M):
            die(f'{path} imports ZInQKernel.OneProof.Main: import the module that defines the statement instead')

    # which bundle holds each discharged field
    bundles = {}
    for var, sname in binders:
        fn, block = find_struct(sname)
        bundles[sname] = (var, fn, field_groups(block))
    owner = {}
    for sname, (_, _, groups) in bundles.items():
        for f, _ in groups:
            if f in by_field:
                owner[f] = sname
    missing = sorted(set(by_field) - set(owner))
    if missing:
        die(f'not a field of the current bundles: {missing}')

    # kinds.tsv: before and after
    rows, cols = load_kinds()
    before = counts(rows)
    kept = [r for r in rows if r['field'] not in by_field]
    new_rows = []
    for d in spec['discharges']:
        for lf in d.get('leaves', []):
            kind = lf.get('kind', 'published')
            flag = lf.get('flag', '')
            if not flag and lf.get('flag_class'):
                die(f"leaf {lf['name']}: a flag_class needs the flag text it classifies")
            if not flag and kind == 'published':
                flag = NEW_LEAF_FLAG
            strict = 'LEAF' if kind == 'published' and not flag.startswith('pending reading') else 'GLUE'
            strictest = 'GLUE' if flag.startswith('strictest') else strict
            old = next(r for r in rows if r['field'] == d['field'])
            new_rows.append(dict(bundle=old['bundle'], field=lf['name'],
                                 kind=kind, flag=flag, strict=strict, strictest=strictest,
                                 source=lf.get('source', ''), rated_by=f'{name}; pending review',
                                 packet=lf.get('packet', old.get('packet', '')), label=lf.get('label', old.get('label', '')),
                                 tier=lf.get('tier', old.get('tier', '')),
                                 flag_class=flag_class(flag, strict, strictest, lf.get('flag_class', '')),
                                 area_issue=lf.get('area_issue', old.get('area_issue', ''))))
    kept += new_rows
    open_after = {r['field'] for r in kept}
    with open(CLAIMS, newline='') as fh:
        held = {r['field'] for r in csv.DictReader(fh, delimiter='\t') if r.get('hold') == 'held'}
    problems = [p for r in new_rows for p in render_open.kinds_row_problems(r, open_after, held)]
    if problems:
        die('the new kinds.tsv rows would fail render_open.py --check:\n  ' + '\n  '.join(problems))
    after = counts(kept)
    print(f'strict count: {before[1]}/{before[2]} on {before[0]} -> {after[1]}/{after[2]} on {after[0]}; '
          f'strictest {before[3]}/{before[4]} -> {after[3]}/{after[4]}')
    if (after[2] > before[2] or after[4] > before[4]) and '--allow-rise' not in sys.argv:
        die('a GLUE count (strict or strictest) rises; not folding (pass --allow-rise to override)')

    # the new module
    # the first free module number after the current top (an existing module is never overwritten: some
    # hand folds use numbers above the top, e.g. rigid-prune's TailZ40)
    j = k + 1
    while os.path.exists(os.path.join(H, f'TailZ{j}.lean')):
        j += 1
    new_mod = f'TailZ{j}'
    out = [f'import ZInQKernel.OneProof.H.{last_mod}'] + [f'import {m}' for m in spec.get('imports', [])]
    out += ['', f'/-! # OneProof H, {name}: `sixContactMin_of_open{N + 1}` (generated by scripts/one_proof/autofold.py)', '',
            'Fields removed (each proved by a contribution): ' + ', '.join(f'`{f}`' for f in by_field) + '.',
            'Fields added (new leaves): ' + (', '.join(f"`{lf['name']}`" for d in spec['discharges']
                                                       for lf in d.get('leaves', [])) or 'none') + '. -/',
            '', 'namespace HDec', '', 'namespace HSyn', '']
    newname = {s: bump(s) for s in bundles if any(owner[f] == s for f in by_field)}
    for sname, (var, fn, groups) in bundles.items():
        mine = [f for f in by_field if owner[f] == sname]
        if not mine:
            continue
        nn = newname[sname]
        # other bundles the proofs name as {r}, {t}, {l}, {g} (frozenTarget's variable names): their new values
        extra = [(v, newname.get(s, s)) for v, s in binders
                 if s != sname and any('{' + v + '}' in by_field[f]['proof'] for f in mine)]
        leaves = [lf for f in mine for lf in by_field[f].get('leaves', [])]
        out.append(f'/-- `{sname}` without ' + ', '.join(f'`{f}`' for f in mine)
                   + (', with the leaves ' + ', '.join(f"`{lf['name']}`" for lf in leaves) if leaves else '')
                   + f' ({name}). -/')
        out.append(f'structure {nn} : Prop where')
        for f, lines in groups:
            if f not in by_field:
                out.extend(lines)
        for lf in leaves:
            if lf.get('doc'):
                out.append(f"  /-- {lf['doc']} -/")
            out.append(f"  {lf['name']} : {lf['type']}")
        out.append('')
        conv = f'{sname[0].lower()}{sname[1:]}_of_{nn}'
        out.append(f'/-- `{sname}` from `{nn}`: ' + ', '.join(f'`{f}`' for f in mine) + ' by the contributions. -/')
        params = ''.join(f' ({v} : {t})' for v, t in extra)
        out.append(f'theorem {conv} (n : {nn}){params} : {sname} where')
        for f, _ in groups:
            if f in by_field:
                proof = by_field[f]['proof'].replace('{n}', 'n')
                for v, _ in extra:
                    proof = proof.replace('{' + v + '}', v)
                out.append(f"  {f} := {proof}")
            else:
                out.append(f'  {f} := n.{f}')
        out.append('')
        bundles[sname] = (var, fn, groups, conv, [v for v, _ in extra])
    new_binders = ' '.join(f'({v} : {newname.get(s, s)})' for v, s in binders)
    call = ' '.join('(' + ' '.join([bundles[s][3], v] + bundles[s][4]) + ')' if s in newname else v
                    for v, s in binders)
    out += [f'/-- **G0 with only the open leaves and the open glue** ({name}; generated). -/',
            f'theorem sixContactMin_of_open{N + 1} {new_binders} : ZInQ.SixContactMin :=',
            f'  {top} {call}', '', 'end HSyn', '', 'end HDec', '',
            f'#print axioms HDec.HSyn.sixContactMin_of_open{N + 1}', '']

    # Main.lean
    ms = main_src.replace(f'import ZInQKernel.OneProof.H.{last_mod}', f'import ZInQKernel.OneProof.H.{new_mod}', 1)
    for old, nn in newname.items():
        ms = ms.replace(f'HDec.HSyn.{old})', f'HDec.HSyn.{nn})')
    ms = ms.replace(f'HDec.HSyn.{top} ', f'HDec.HSyn.sixContactMin_of_open{N + 1} ', 1)

    if '--dry-run' in sys.argv:
        print(NL.join(out))
        return
    open(H + new_mod + '.lean', 'w').write(NL.join(out))
    open(MAIN, 'w').write(ms)
    order = {'research': 0, 'textbook': 1, 'added': 2, 'glue': 3}
    pos = {r['field']: i for i, r in enumerate(rows)}  # other rows (frozenTarget's) keep their order
    kept.sort(key=lambda r: (order.get(r['bundle'], 9), r['field'].lower() if r['bundle'] in order else pos[r['field']]))
    with open(KINDS, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter='\t', lineterminator='\n', extrasaction='ignore')
        w.writeheader()
        w.writerows(kept)
    with open(CLAIMS, newline='') as fh:
        rd = csv.DictReader(fh, delimiter='\t')
        crows, ccols = list(rd), rd.fieldnames
    with open(CLAIMS, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=ccols, delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(r for r in crows if r['field'] not in by_field)
    print(f'wrote {H}{new_mod}.lean, switched {MAIN} to sixContactMin_of_open{N + 1}, updated {KINDS} and {CLAIMS}')
    print('next: lake build +ZInQKernel.OneProof.Main, the hash guard, OpenStatements.lean, render_open.py, '
          'render_open.py --check')


if __name__ == '__main__':
    main()
