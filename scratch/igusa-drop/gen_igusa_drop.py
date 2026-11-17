#!/usr/bin/env python3
"""igusa-drop (adapted from scratch/fold-b105/gen_chev_bypass.py): remove the research field `igusaGL2DSGalSome`
(Diamond-Shurman Thm 7.6.3, printed form; igusa-gal) by a bypass, with no new leaf.

The chain reads the field once: in the composite conversion of fold-b105 (pb-p1, TailZ77 on 97247ce1;
fold-chev's TailZ75 on older heads), as
    r16CoreY := (AfTateLam.r16CoreY_of_ds965 a b c (X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome X.igusaGL2DSGalSome) d)
and `AfTateLam.r16CoreY_of_ds965_x0 a b c d` (igusa-drop, ZInQKernel/Contrib/OneProof/IgusaDrop.lean) proves the same
`R16Split.R16CoreY` without the Igusa argument (the argument was used only as `X1PointsConjugate`, which is proved:
`Iff.rfl` to `IgusaTransitive`, `ZInQ.RLeaf.igusaTransitive_iff_x0Transitive` (T40.lean), `FltCqj2.x0Transitive_proof`).

The script follows Main.lean's current top theorem down its chain (let-steps and nested conversion composites as in
fold-b105), composes the conversions field by field with the reader replaced, and stops at the first conversion whose
result bundle has no `igusaGL2DSGalSome` (on 97247ce1: `openResearchLeaves36EBCF_of_OpenResearchLeaves51`, bundle
`OpenResearchLeaves36EBCF`).  It writes `ZInQKernel/OneProof/H/TailZ<j>.lean` (first free number), switches Main.lean
and drops the field's rows from kinds.tsv and claims.tsv.  No existing declaration is changed.  Usage, from the
repository root, on a head that has IgusaDrop.lean and whose top research bundle still carries the field:

    python3 scratch/igusa-drop/gen_igusa_drop.py [--dry-run]
"""
import csv, glob, os, re, sys

sys.path.insert(0, 'scripts/one_proof')
import autofold as af  # noqa: E402  (its parsers and writers)

FIELD = 'igusaGL2DSGalSome'
CONTRIB = 'ZInQKernel.Contrib.OneProof.IgusaDrop'
H = af.H
NL = '\n'


def die(m):
    print('gen_igusa_drop: ' + m)
    sys.exit(1)


# ---------------------------------------------------------------- Lean source helpers
_SRC = {fn: open(fn).read() for fn in sorted(glob.glob(H + '*.lean'))}


def find_theorem(name):
    """(params [(var, type)], result type, body lines) of `theorem name ...`, single definition under H."""
    hits = []
    for fn, s in _SRC.items():
        for m in re.finditer(r'^theorem ' + re.escape(name) + r'((?: \([^()]*\))*) :\s*(.*?)(?: where| :=)\s*$', s, re.M):
            hits.append((fn, m))
    if len(hits) != 1:
        die(f'theorem {name}: {len(hits)} definitions')
    fn, m = hits[0]
    params = re.findall(r'\((\w+) : ([^()]*)\)', m.group(1))
    L = _SRC[fn][m.end():].split(NL)[1:]
    body = []
    for l in L:
        if l.strip() == '' or not l.startswith('  '):
            break
        body.append(l)
    return params, m.group(2).strip(), body, m.group(0).endswith('where')


def split_args(s):
    """top-level whitespace-separated arguments of an application (parentheses respected)."""
    out, depth, cur = [], 0, ''
    for c in s.strip():
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        if c.isspace() and depth == 0:
            if cur:
                out.append(cur)
            cur = ''
        else:
            cur += c
    if cur:
        out.append(cur)
    return out


def strip_parens(s):
    s = s.strip()
    while s.startswith('(') and s.endswith(')'):
        d = 0
        for i, c in enumerate(s):
            d += c == '('
            d -= c == ')'
            if d == 0 and i < len(s) - 1:
                return s
        s = s[1:-1].strip()
    return s


def paren(e):
    return e if re.fullmatch(r"[\w.'_]+", e) or (e.startswith('(') and strip_parens(e) != e) else f'({e})'


def subst(expr, env):
    """replace the variables of env (name -> expr) in expr; `v.f` with env[v] a dict -> env[v][f]."""
    def rep(m):
        v, f = m.group(1), m.group(2)
        val = env[v]
        if isinstance(val, dict):
            if f is None:
                die(f'bundle variable {v} used whole in: {expr}')
            if f not in val:
                die(f'field {f} missing (needed in: {expr})')
            if val[f] is None:
                die(f'field {f} is the removed field (needed in: {expr})')
            return paren(val[f])
        return paren(val) + ('.' + f if f else '')
    pat = r"(?<![\w.'])(" + '|'.join(map(re.escape, env)) + r")(?![\w'])(?:\.([\w']+))?"
    return re.sub(pat, rep, expr)


def fields_of(body):
    """[(field, expr)] of a `where` body."""
    out = []
    for l in body:
        m = re.match(r"^  ([\w']+) := (.*)$", l)
        if m:
            out.append([m.group(1), m.group(2)])
        elif l.startswith('    ') and out:
            out[-1][1] += ' ' + l.strip()
        else:
            die('unparsed conversion line: ' + l)
    return out


READERS = [
    (re.compile(r"_root_\.AfTateLam\.r16CoreY_of_ds965 (\S+) (\S+) (\S+) "
                r"\(_root_\.X1Igusa\.igusaGL2DS_of_igusaGL2DSGalSome (\w+)\.igusaGL2DSGalSome\) "),
     lambda m: f'_root_.AfTateLam.r16CoreY_of_ds965_x0 {m.group(1)} {m.group(2)} {m.group(3)} '),
]


def reroute(expr):
    for pat, f in READERS:
        expr = pat.sub(f, expr)
    return expr


def apply_conv(name, args_vals):
    params, res, body, is_where = find_theorem(name)
    if not is_where or len(params) != len(args_vals):
        die(f'{name}: not a `where` conversion with {len(args_vals)} arguments')
    env = {v: a for (v, _), a in zip(params, args_vals)}
    out = {}
    for f, e in fields_of(body):
        if f == FIELD:
            out[f] = None  # the field itself; must not be read below
            continue
        out[f] = subst(reroute(e), env)
    return res, out


def eval_bundle(expr, env):
    """value (dict) of a research-bundle argument expression."""
    e = strip_parens(expr)
    if re.fullmatch(r'\w+', e):
        if not isinstance(env.get(e), dict):
            die(f'research argument {e} is not the bundle variable')
        return env[e]
    parts = split_args(e)
    head, args = parts[0], parts[1:]
    vals = [eval_bundle(args[0], env)] + [subst(a, {k: v for k, v in env.items() if not isinstance(v, dict)})
                                         for a in args[1:]]
    return apply_conv(head, vals)[1]


def struct_fields(sname):
    fn, block = af.find_struct(sname)
    return af.field_groups(block)



# ---------------------------------------------------------------- the fold (fold-b105: let-steps, nested composites)
def parse_step(name):
    params, res, body, is_where = find_theorem(name)
    if is_where or res != 'ZInQ.SixContactMin' or len(params) != 3:
        die(f'{name}: not a sixContactMin step')
    lets, rest = [], []
    for l in body:
        m = re.match(r"^  let ([\w']+) := (.*)$", l)
        if m and not rest:
            lets.append((m.group(1), m.group(2)))
        else:
            rest.append(l.strip())
    return params, lets, ' '.join(rest)


def decompose(expr, base):
    """`c1 (c2 (... (ck base) ...) a) a` -> [(c1, [a..]), ..., (ck, [..])] (outermost first)."""
    out = []
    e = strip_parens(expr)
    while e != base:
        parts = split_args(e)
        if len(parts) < 2:
            die(f'cannot decompose research argument at: {e}')
        out.append((parts[0], parts[2:]))
        e = strip_parens(parts[1])
    return out


def conv_result(name):
    return find_theorem(name)[1]


def main():
    dry = '--dry-run' in sys.argv
    main_src, binders, top, N, last_mod, k = af.main_state()
    if len(binders) != 3:
        die(f'expected frozenTarget bundles (r, t, l), got {binders}')
    (rv, R0), (tv, T0), (lv, L0) = binders
    groups = struct_fields(R0)
    names = [f for f, _ in groups]
    if FIELD not in names:
        die(f'{R0} has no field {FIELD}: nothing to do')
    newR = af.bump(R0)
    value = {f: (None if f == FIELD else f'n.{f}') for f in names}
    scal_t, scal_l = 't', 'l'          # current textbook / added arguments, as expressions in the top t, l
    cur = top
    walked = []
    while True:
        params, lets, call = parse_step(cur)
        (pr, PR), (pt, _), (pl, _) = params
        loc = {pt: scal_t, pl: scal_l}
        for v, e in lets:
            loc[v] = subst(e, loc)
        parts = split_args(call)
        callee, cargs = parts[0], parts[1:]
        if len(cargs) != 3:
            die(f'{cur}: final call {callee} without (r t l)')
        convs = decompose(cargs[0], pr)
        rem = list(convs)
        stop = None
        while rem:
            conv, extra = rem.pop()
            res, value = apply_conv(conv, [value] + [subst(a, loc) for a in extra])
            walked.append(conv)
            if FIELD not in [f for f, _ in struct_fields(res)]:
                stop = res
                break
        if stop is None:
            RSc = find_theorem(callee)[0][0][1]
            if FIELD not in [f for f, _ in struct_fields(RSc)]:
                stop = RSc
        if stop is not None:
            RS = stop
            # re-emit the step's lets (values in the top t, l); outer arguments keep the let names
            loc2 = {pt: scal_t, pl: scal_l}
            top_lets = []
            for v, e in lets:
                top_lets.append((v, subst(e, loc2)))
                loc2[v] = v
            outer = [(c, [subst(a, loc2) for a in ex]) for c, ex in rem]  # outermost first
            final_callee = callee
            targ, larg = subst(cargs[1], loc2), subst(cargs[2], loc2)
            stop_step = cur
            break
        walked.append(callee)
        scal_t, scal_l = subst(cargs[1], loc), subst(cargs[2], loc)
        cur = callee
    RSf = [f for f, _ in struct_fields(RS)]
    vals = value
    if set(vals) - {FIELD} != set(RSf):
        die(f'conversion fields differ from {RS}: {sorted(set(vals) ^ set(RSf))}')
    for f in RSf:
        if vals[f] is None or FIELD in vals[f] or 'IgusaGL2DS' in vals[f] or 'igusaGL2DS' in vals[f]:
            die(f'{RS}.{f} still reads the removed field: {vals[f]}')
    body_used = ' '.join(vals[f] for f in RSf)
    use_t = re.search(rf"(?<![\w.']){tv}(?![\w'])", body_used) is not None
    use_l = re.search(rf"(?<![\w.']){lv}(?![\w'])", body_used) is not None
    convname = f'openResearchLeaves{RS[len("OpenResearchLeaves"):]}_of_{newR}'
    cparams_s = f'(n : {newR})' + (f' ({tv} : {T0})' if use_t else '') + (f' ({lv} : {L0})' if use_l else '')
    cargs_s = ' '.join(['r'] + ([tv] if use_t else []) + ([lv] if use_l else []))
    j = k + 1
    while os.path.exists(os.path.join(H, f'TailZ{j}.lean')):
        j += 1
    new_mod = f'TailZ{j}'
    readers = sorted(f for f in RSf if 'r16CoreY_of_ds965_x0' in vals[f])
    rexpr = f'({convname} {cargs_s})'
    for c, ex in reversed(outer):
        rexpr = '(' + ' '.join([c, rexpr] + [paren(a) for a in ex]) + ')'
    out = [f'import ZInQKernel.OneProof.H.{last_mod}', f'import {CONTRIB}', '',
           f'/-! # OneProof H, igusa-drop: `sixContactMin_of_open{N + 1}` (generated by scratch/igusa-drop/gen_igusa_drop.py)',
           '',
           f'Field removed: the research field `{FIELD}` (`X1Igusa.IgusaGL2DSGalSome`, Diamond-Shurman Thm 7.6.3 in its',
           'printed form; igusa-gal). Fields added: none. The chain read the field once, as',
           '`X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome` passed to `AfTateLam.r16CoreY_of_ds965`, which uses it only as',
           '`R16IsJ1Dict.X1PointsConjugate`; that Prop is proved (`AfTateLam.x1PointsConjugate_proof`: `Iff.rfl` to',
           '`ZInQ.RLeaf.IgusaTransitive`, `ZInQ.RLeaf.igusaTransitive_iff_x0Transitive` with the proved `tateMuN`, and',
           '`FltCqj2.x0Transitive_proof`), so `AfTateLam.r16CoreY_of_ds965_x0` (`Contrib/OneProof/IgusaDrop.lean`) gives',
           f'`r16CoreY` without it. A proof of `{FIELD}` itself is not available, so this is a bypass, not an autofold',
           f'(fold-b105\'s pattern): `{newR}` is `{R0}` without the field, and `{convname}` composes, field by field,',
           f'the conversions from `{R0}` down to `{RS}` (the first bundle of the chain without `{FIELD}`), with',
           'the reader ' + ', '.join(f'`{f}`' for f in readers) + ' taking `r16CoreY_of_ds965_x0`.',
           f'`sixContactMin_of_open{N + 1}` re-enters the chain of `{stop_step}` below that bundle.',
           'Every existing declaration is unchanged. -/', '', 'namespace HDec', '', 'namespace HSyn', '',
           f'/-- `{R0}` without `{FIELD}` (igusa-drop; `X1PointsConjugate` is proved from `X0Transitive`, no',
           f'replacement field). {len(names) - 1} fields. -/',
           f'structure {newR} : Prop where']
    for f, lines in groups:
        if f != FIELD:
            out.extend(lines)
    out += ['', f'/-- `{RS}` from `{newR}`: the conversions ' + ', '.join(f'`{c}`' for c in walked) + ' composed, with',
            '`AfTateLam.r16CoreY_of_ds965_x0` (no Igusa argument) where they read `igusaGL2DSGalSome`. -/',
            f'theorem {convname} {cparams_s} : {RS} where']
    out += [f'  {f} := {vals[f]}' for f in RSf]
    out += ['', f'/-- **G0 with only the open leaves and the open glue** (igusa-drop; `{FIELD}` removed with no new leaf). -/',
            f'theorem sixContactMin_of_open{N + 1} (r : {newR}) ({tv} : {T0}) ({lv} : {L0}) : ZInQ.SixContactMin :=',
            *[f'  let {v} := {e}' for v, e in top_lets],
            f'  {final_callee} {rexpr} {paren(targ)} {paren(larg)}',
            '', 'end HSyn', '', 'end HDec', '', f'#print axioms HDec.HSyn.sixContactMin_of_open{N + 1}', '']
    text = NL.join(out)
    if re.search(r'n\.igusaGL2DSGalSome|igusaGL2DSGalSome :', text):
        die('the module still mentions the field')
    ms = main_src.replace(f'import ZInQKernel.OneProof.H.{last_mod}', f'import ZInQKernel.OneProof.H.{new_mod}', 1)
    ms = ms.replace(f'HDec.HSyn.{R0})', f'HDec.HSyn.{newR})', 1)
    ms = ms.replace(f'HDec.HSyn.{top} ', f'HDec.HSyn.sixContactMin_of_open{N + 1} ', 1)
    anchor = 'The hypotheses of `frozenTarget` are therefore exactly the open statements.'
    if anchor not in ms:
        die('Main.lean docstring anchor not found')
    para = (f'igusa-drop removed the research field `{FIELD}` (Diamond-Shurman Thm 7.6.3, printed form) with no new\n'
            'leaf: the chain read it only through `AfTateLam.r16CoreY_of_ds965`, which uses it as `X1PointsConjugate`,\n'
            'proved from `X0Transitive` (`AfTateLam.r16CoreY_of_ds965_x0`, `Contrib/OneProof/IgusaDrop.lean`).\n'
            f'`{newR}` (`{new_mod}`) is `{R0}` without it, and `HDec.HSyn.sixContactMin_of_open{N + 1}` enters the\n'
            f'chain at `{RS}` through the composite conversion `{convname}` (bypass, generated by\n'
            '`scratch/igusa-drop/gen_igusa_drop.py`); no declaration is copied or changed.\n\n')
    ms = ms.replace(anchor, para + anchor, 1)
    rows, cols = af.load_kinds()
    before = af.counts(rows)
    kept = [r for r in rows if r['field'] != FIELD]
    after = af.counts(kept)
    print(f'walk: {top}: ' + ' -> '.join(walked) + f'; stop at {RS}; outer {[c for c, _ in outer]}; final {final_callee}')
    print(f'{R0} ({len(names)} fields) -> {newR} ({len(names) - 1}); stop bundle {RS} ({len(RSf)} fields); readers {readers}')
    print(f'strict count: {before[1]}/{before[2]} on {before[0]} -> {after[1]}/{after[2]} on {after[0]}; '
          f'strictest {before[3]}/{before[4]} -> {after[3]}/{after[4]}')
    if after[2] > before[2] or after[4] > before[4]:
        die('a GLUE count rises')
    if dry:
        print(text)
        return
    open(H + new_mod + '.lean', 'w').write(text)
    open(af.MAIN, 'w').write(ms)
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
        w.writerows(r for r in crows if r['field'] != FIELD)
    print(f'wrote {H}{new_mod}.lean, switched {af.MAIN} to sixContactMin_of_open{N + 1}, updated {af.KINDS} and {af.CLAIMS}')


if __name__ == '__main__':
    main()
