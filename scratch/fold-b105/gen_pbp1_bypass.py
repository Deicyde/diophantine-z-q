#!/usr/bin/env python3
"""fold-b105 step 3 (pb-p1): replace the research fields `panPrintedP` and `bergerPrintedVT` by pb-p1's leaves
`panPrintedF` (Pan Thm 1.0.4 over Fontaine's B_st) and `bergerSurveyF` (Berger's survey IV.5.1 over Fontaine's B_st),
by a bypass (regenerates pb-p1's manual `scratch/pb-p1/BypassFold.lean` on the current head).

`HDec.PkgI4.PanDict.panBerger_of_F` (Contrib/OneProof/PanBergerFontaine.lean) proves `r11r12 : PanBerger` from the two
new leaves and the same DS inputs as `panBerger_of_printedPV`; the old field `panPrintedP` is not derivable from
`PanPrintedF` (pb-p1 section 5), so autofold cannot be used. The chain reads the two old fields only in the `r11r12`
line `panBerger_of_printedPV X.panPrintedP (bergerPrintedV_of_T X.bergerPrintedVT) ...` (on fb0885a8: in the composite
conversion `openResearchLeaves36EBCF_of_OpenResearchLeaves49`, TailZ75), elsewhere only passed through.

Like `gen_chev_bypass.py` (whose helpers it imports): follow Main's top theorem down its chain (let-steps and nested
composites allowed), composing the research-bundle conversions field by field with the `r11r12` reader rewritten to
`panBerger_of_F X.panPrintedF X.bergerSurveyF ...`, the two new fields carried along, until the first bundle without
either old field; write `TailZ<j>.lean` with the next research generation (the top one with the two fields replaced
in place, docstrings below), the composite conversion and `sixContactMin_of_open<N+1>`; switch Main; drop the old
kinds/claims rows and add the two new kinds rows (KINDS_ROWS below).  Usage (repository root):

    python3 scratch/fold-b105/gen_pbp1_bypass.py [--dry-run]

No existing declaration is changed. On a later head with further autofolds this works unchanged as long as the reader
line keeps this form (the walk dies with a message otherwise).
"""
import csv, importlib.util, os, re, sys

_spec = importlib.util.spec_from_file_location('gcb', os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                                  'gen_chev_bypass.py'))
g = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(g)
af, H, NL, die = g.af, g.H, g.NL, g.die

OLD = ('panPrintedP', 'bergerPrintedVT')
NEW = [('panPrintedF', '_root_.HDec.PkgI4.PanDict.PanPrintedF',
        '  /-- R12 (pb-p1, fold-b105). Pan, J. Amer. Math. Soc. 35 (2022), Theorem 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 '
        'p. 5 with Conj. 1.0.1 p. 2; the manuscript cites this arXiv version), p >= 5, printed form with "potentially '
        "semi-stable in the sense of Fontaine\" over Fontaine's B_st = B_cris[log p~] inside B_dR (Berger, "
        'arXiv:math/0210184v1, II.3.1 and II.3.3), basis form, on a model V = E^n; otherwise as pb-fix3\'s PanPrintedP. '
        'Replaces panPrintedP (with bergerSurveyF: r11r12 by HDec.PkgI4.PanDict.panBerger_of_F). -/'),
       ('bergerSurveyF', '_root_.HDec.PkgI4.PanDict.BergerSurveyF',
        "  /-- R11 (pb-p1, fold-b105). Berger's theorem (Invent. Math. 148 (2002), Theoreme 0.6 = Theoreme 5.19 of "
        'arXiv:math/0102179v3; Theoreme 0.7 there is Sen\'s theorem) in the printed form of Berger, An introduction to the '
        'theory of p-adic representations (arXiv:math/0210184v1, IV.5.1 p. 30, IV.5.3 p. 31): a de Rham p-adic '
        "representation V = E^n of G_Qp is potentially semistable over Fontaine's B_st = B_cris[log p~] (II.3.1, II.3.3), "
        'basis form (I.2.3). Replaces bergerPrintedVT. -/')]
NEWF = [f for f, _, _ in NEW]
CONTRIB = 'ZInQKernel.Contrib.OneProof.PanBergerFontaine'
READER = re.compile(r"_root_\.HDec\.PkgI4\.PanDict\.panBerger_of_printedPV (\w+)\.panPrintedP "
                    r"\(_root_\.HDec\.PkgI4\.PanDict\.bergerPrintedV_of_T \1\.bergerPrintedVT\)")
KINDS_ROWS = [
    dict(bundle='research', field='panPrintedF', kind='published',
         flag="pending review; unread: new printed leaf (pb-p1; fold-b105); Pan arXiv:1901.07166v2 Conj. 1.0.1 p. 2 and "
              "Thm 1.0.4 p. 5 read by pb-p1 (the manuscript cites this arXiv version; JAMS numbering not checked); "
              "'potentially semi-stable in the sense of Fontaine' over Fontaine's B_st = B_cris[log p~] as Berger prints it "
              "(arXiv:math/0210184v1 II.3.1, II.3.3; a_n -> 0 read p-adically, as for A_max), basis form of admissibility "
              "(stronger hypothesis than the dimension form: isAdmissible_of_pstF, B_st G-stable bstF_stable); other "
              "readings as pb-fix3's panPrintedP (eigenform in its weakest sense, rho_g pinned by geometric-Frobenius traces)",
         strict='GLUE', strictest='GLUE',
         source="Pan, The Fontaine-Mazur conjecture in the residually reducible case, J. Amer. Math. Soc. 35 (2022), "
                "1031-1169, Thm 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1); Fontaine's B_st as BstFOf, pst as "
                "LocalIsPstF in Contrib/OneProof/PanBergerFontaine.lean",
         flag_class='pending-review,unread'),
    dict(bundle='research', field='bergerSurveyF', kind='published',
         flag="pending review (pb-p1; fold-b105): cited print; Berger 2004 survey read by pb-p1 on arXiv:math/0210184v1 "
              "(pages are the arXiv pages; de Gruyter pagination not checked); a reader checked it against Invent. Math. "
              "148 (2002) Theoreme 0.6 = Theoreme 5.19 (arXiv:math/0102179v3), the same theorem (0.7 there is Sen's "
              "theorem); readings: a_n -> 0 in B~^+ read p-adically with coefficients in A_inf and B_cris^+ the Q_p-algebra "
              "they generate (as bst-construct reads A_max); admissibility in its basis form, which the survey prints as "
              "equivalent to the dimension form (I.2.3, p. 6)",
         strict='GLUE', strictest='GLUE',
         source="Berger, An introduction to the theory of p-adic representations (2004), arXiv:math/0210184v1, IV.5.1 and "
                "IV.5.3, with II.2.3, II.3.1, II.3.3, II.5.2, I.2.3; = Berger, Invent. Math. 148 (2002), Theoreme 0.6 "
                "(= Theoreme 5.19 of arXiv:math/0102179v3); B_st (Fontaine) as BstFOf, admissibility (basis form) as "
                "IsAdmissibleT in Contrib/OneProof/PanBergerFontaine.lean and PanBergerPst.lean",
         flag_class='pending-review'),
]


def has_old(bundle):
    return any(f in OLD for f, _ in g.struct_fields(bundle))


def apply_conv(name, args_vals):
    params, res, body, is_where = g.find_theorem(name)
    if not is_where or len(params) != len(args_vals):
        die(f'{name}: not a `where` conversion with {len(args_vals)} arguments')
    env = {v: a for (v, _), a in zip(params, args_vals)}
    out = {}
    for f, e in g.fields_of(body):
        if f in OLD:
            out[f] = None
            continue
        e2 = READER.sub(lambda m: f'_root_.HDec.PkgI4.PanDict.panBerger_of_F {m.group(1)}.panPrintedF '
                                  f'{m.group(1)}.bergerSurveyF', e)
        out[f] = g.subst(e2, env)
    for f in NEWF:  # carried along
        out[f] = args_vals[0][f]
    return res, out


def main():
    dry = '--dry-run' in sys.argv
    main_src, binders, top, N, last_mod, k = af.main_state()
    (rv, R0), (tv, T0), (lv, L0) = binders
    groups = g.struct_fields(R0)
    names = [f for f, _ in groups]
    if not all(f in names for f in OLD):
        die(f'{R0} lacks {OLD}')
    newR = af.bump(R0)
    value = {f: (None if f in OLD else f'n.{f}') for f in names}
    value.update({f: f'n.{f}' for f in NEWF})
    scal_t, scal_l = 't', 'l'
    cur, walked = top, []
    while True:
        params, lets, call = g.parse_step(cur)
        (pr, PR), (pt, _), (pl, _) = params
        loc = {pt: scal_t, pl: scal_l}
        for v, e in lets:
            loc[v] = g.subst(e, loc)
        parts = g.split_args(call)
        callee, cargs = parts[0], parts[1:]
        convs = g.decompose(cargs[0], pr)
        rem, stop = list(convs), None
        while rem:
            conv, extra = rem.pop()
            res, value = apply_conv(conv, [value] + [g.subst(a, loc) for a in extra])
            walked.append(conv)
            if not has_old(res):
                stop = res
                break
        if stop is None and not has_old(g.find_theorem(callee)[0][0][1]):
            stop = g.find_theorem(callee)[0][0][1]
        if stop is not None:
            RS = stop
            loc2 = {pt: scal_t, pl: scal_l}
            top_lets = []
            for v, e in lets:
                top_lets.append((v, g.subst(e, loc2)))
                loc2[v] = v
            outer = [(c, [g.subst(a, loc2) for a in ex]) for c, ex in rem]
            final_callee, stop_step = callee, cur
            targ, larg = g.subst(cargs[1], loc2), g.subst(cargs[2], loc2)
            break
        walked.append(callee)
        scal_t, scal_l = g.subst(cargs[1], loc), g.subst(cargs[2], loc)
        cur = callee
    RSf = [f for f, _ in g.struct_fields(RS)]
    vals = value
    if set(vals) - set(OLD) - set(NEWF) != set(RSf):
        die(f'conversion fields differ from {RS}: {sorted((set(vals) - set(OLD) - set(NEWF)) ^ set(RSf))}')
    for f in RSf:
        if vals[f] is None or re.search(r'\.(panPrintedP|bergerPrintedVT)\b', vals[f]):
            die(f'{RS}.{f} still reads an old field: {vals[f]}')
    readers = sorted(f for f in RSf if 'panBerger_of_F' in vals[f])
    if not readers:
        die('no reader rewritten')
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
    rexpr = f'({convname} {cargs_s})'
    for c, ex in reversed(outer):
        rexpr = '(' + ' '.join([c, rexpr] + [g.paren(a) for a in ex]) + ')'
    out = [f'import ZInQKernel.OneProof.H.{last_mod}', f'import {CONTRIB}', '',
           f'/-! # OneProof H, fold-b105 (pb-p1): `sixContactMin_of_open{N + 1}` (generated by scratch/fold-b105/gen_pbp1_bypass.py)',
           '',
           'Fields removed: `panPrintedP` (Pan Thm 1.0.4 with pst over the tree\'s `B_max[log p~]`) and `bergerPrintedVT`',
           '(Berger\'s theorem over the tree\'s `B_st`). Fields added: `panPrintedF` and `bergerSurveyF`, the same theorems',
           'over Fontaine\'s `B_st = B_cris[log p~]` as printed (pb-p1, `Contrib/OneProof/PanBergerFontaine.lean`).',
           '`r11r12 : PanBerger` follows from them by `HDec.PkgI4.PanDict.panBerger_of_F` (no comparison of period rings;',
           'the old `panPrintedP` is not derivable from `PanPrintedF`, so this is a bypass, not an autofold, as pb-p1\'s',
           f'`scratch/pb-p1/BypassFold.lean`): `{newR}` is `{R0}` with the two fields replaced in place, and',
           f'`{convname}` composes, field by field, the conversions from `{R0}` down to `{RS}` (the first bundle',
           'of the chain without either old field), with ' + ', '.join(f'`{f}`' for f in readers) + ' from `panBerger_of_F`.',
           f'`sixContactMin_of_open{N + 1}` re-enters the chain of `{stop_step}` below that bundle.',
           'Every existing declaration is unchanged. -/', '', 'namespace HDec', '', 'namespace HSyn', '',
           f'/-- `{R0}` with `panPrintedP`, `bergerPrintedVT` replaced by pb-p1\'s `panPrintedF`, `bergerSurveyF`',
           f'(fold-b105). {len(names)} fields. -/',
           f'structure {newR} : Prop where']
    for f, lines in groups:
        if f in OLD:
            nf, ty, doc = NEW[OLD.index(f)]
            out += [doc, f'  {nf} : {ty}']
        else:
            out.extend(lines)
    out += ['', f'/-- `{RS}` from `{newR}`: the conversions ' + ', '.join(f'`{c}`' for c in walked) + ' composed, with',
            '`r11r12` from `HDec.PkgI4.PanDict.panBerger_of_F` (pb-p1) where they read `panPrintedP` and `bergerPrintedVT`. -/',
            f'theorem {convname} {cparams_s} : {RS} where']
    out += [f'  {f} := {vals[f]}' for f in RSf]
    out += ['', '/-- **G0 with only the open leaves and the open glue** (fold-b105, pb-p1: Pan and Berger over Fontaine\'s',
            '`B_st` as printed). -/',
            f'theorem sixContactMin_of_open{N + 1} (r : {newR}) ({tv} : {T0}) ({lv} : {L0}) : ZInQ.SixContactMin :=',
            *[f'  let {v} := {e}' for v, e in top_lets],
            f'  {final_callee} {rexpr} {g.paren(targ)} {g.paren(larg)}',
            '', 'end HSyn', '', 'end HDec', '', f'#print axioms HDec.HSyn.sixContactMin_of_open{N + 1}', '']
    text = NL.join(out)
    if re.search(r'panPrintedP :|bergerPrintedVT :|n\.panPrintedP\b|n\.bergerPrintedVT\b', text):
        die('the module still mentions an old field')
    ms = main_src.replace(f'import ZInQKernel.OneProof.H.{last_mod}', f'import ZInQKernel.OneProof.H.{new_mod}', 1)
    ms = ms.replace(f'HDec.HSyn.{R0})', f'HDec.HSyn.{newR})', 1)
    ms = ms.replace(f'HDec.HSyn.{top} ', f'HDec.HSyn.sixContactMin_of_open{N + 1} ', 1)
    anchor = 'The hypotheses of `frozenTarget` are therefore exactly the open statements.'
    if anchor not in ms:
        die('Main.lean docstring anchor not found')
    para = ('fold-b105 (pb-p1) replaced the research fields `panPrintedP` and `bergerPrintedVT` by `panPrintedF` (Pan,\n'
            'arXiv:1901.07166v2 Thm 1.0.4) and `bergerSurveyF` (Berger\'s survey IV.5.1), both over Fontaine\'s `B_st` as\n'
            'printed (`Contrib/OneProof/PanBergerFontaine.lean`); `r11r12` follows by `HDec.PkgI4.PanDict.panBerger_of_F`.\n'
            f'`{newR}` (`{new_mod}`) enters the chain at `{RS}` through the composite conversion `{convname}`\n'
            '(bypass, generated by `scratch/fold-b105/gen_pbp1_bypass.py`); no declaration is copied or changed.\n\n')
    ms = ms.replace(anchor, para + anchor, 1)
    rows, cols = af.load_kinds()
    before = af.counts(rows)
    old_rows = {r['field']: r for r in rows if r['field'] in OLD}
    if set(old_rows) != set(OLD):
        die(f'kinds rows missing for {set(OLD) - set(old_rows)}')
    kept = []
    for r in rows:
        if r['field'] in OLD:
            o = r
            nr = dict(KINDS_ROWS[OLD.index(r['field'])])
            full = {c: o.get(c, '') for c in cols}
            full.update({c: nr[c] for c in nr})
            full['rated_by'] = 'pb-p1 (unreviewed)'
            kept.append(full)
        else:
            kept.append(r)
    after = af.counts(kept)
    import render_open
    held = set()
    open_after = {f for f in names if f not in OLD} | set(NEWF)
    probs = [p for r in kept if r['field'] in NEWF for p in render_open.kinds_row_problems(r, open_after, held)]
    print(f'walk: {top}: ' + ' -> '.join(walked) + f'; stop at {RS}; outer {[c for c, _ in outer]}; final {final_callee}')
    print(f'{R0} ({len(names)} fields) -> {newR} ({len(names)}); stop bundle {RS} ({len(RSf)} fields); readers {readers}')
    print(f'strict count: {before[1]}/{before[2]} on {before[0]} -> {after[1]}/{after[2]} on {after[0]}; '
          f'strictest {before[3]}/{before[4]} -> {after[3]}/{after[4]}')
    if probs:
        print('row problems (render_open):', probs)
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
        w.writerows(r for r in crows if r['field'] not in OLD)
    print(f'wrote {H}{new_mod}.lean, switched {af.MAIN} to sixContactMin_of_open{N + 1}, updated {af.KINDS} and {af.CLAIMS}')


if __name__ == '__main__':
    main()
