#!/usr/bin/env python3
"""fold-b116: d2a6b's generator retargeted on the post-ss-faltings chain (CHAIN_R/CHAIN_TOP are SSFChain's copies;
the chain is OneProof/H/D2A6Chain.lean; outputs in scratch/fold-b116/gen-d2a6b/).

d2a6b: the bypass fold that removes `sga7_IX_3_5_ForwardGeom_Def34` (SGA 7 IX 3.5) from the top research bundle,
with A6 on the manuscript's `Y₃` leaf `Y3RouteA.Y3FullThreeRepZ30` (y3-route-a) instead of sgr-split's
`ShimuraIntegralModelRep` (d2a6-reroute's first version, scratch/d2a6-reroute/gen/gen_bypass.py).

The chain (`Contrib/OneProof/D2A6Chain.lean`, gen_chain.py) proves `sixContactMin_of_open73_u` from
`OpenResearchLeaves54U` = `OpenResearchLeaves54` (TailZ80; on f3402e89) with the IX 3.5 field replaced by `r6u : D2A6.R6U`, where now
`R6U = SZRaynaud.RaynaudWildNF ∧ Y3RouteA.Y3FullThreeRepZ30` (`Contrib/OneProof/D2A6Wrap.lean`). This script writes the
next research bundle from the current top one, `R0`, field by field:

* `sga7_IX_3_5_ForwardGeom_Def34` -> `elliotWildInertiaTrivial` (ELLIOT, L817-818);
* `raynaudSemistableSHOr` -> `silverbergZarhinThm35` (SZ Thm 3.5, L816) if `R0` still has it; if sz-raynaud's autofold
  was folded first, `R0` already has `silverbergZarhinThm35` and it is mapped, not replaced (d2a6-reroute's Known
  issue 5);
* `y3FullThreeRepZ30`: if `R0` already has it (y3-route-a's autofold folded first, `--mode post`) it is mapped;
  otherwise `--mode absorb` (default) replaces `y3FineModuliAbP` by it (y3-route-a's autofold done in the same module:
  `y3FineModuliAbP := Y3RouteA.y3FineModuliAbP_of_z30 n.y3FullThreeRepZ30`), and `--mode add` keeps
  `y3FineModuliAbP` and adds `y3FullThreeRepZ30` (this base alone without y3-route-a's discharge);

then the conversion to `OpenResearchLeaves54U` and the next top theorem. On fork main f3402e89 (sz-raynaud and
y3-route-a folded, TailZ81/TailZ82) only `--mode post` applies; `absorb`/`add` were for the TailZ79 base (their
outputs are archived in scratch/d2a6b/tailz79/). Options:

    python3 scratch/d2a6b/gen/gen_bypass.py [--mode absorb|add|post] [--base FILE] [--out FILE] [--rows FILE]

`--base FILE` (with `--mode post`) reads `R0` and the top theorem from FILE (e.g. y3-route-a's autofold dry-run module,
scratch/d2a6b/y3-dryrun.txt) instead of ZInQKernel/OneProof/H/; the script then also writes FILE's module followed by
the bypass as one compilable test module (`--test FILE`). It changes nothing under ZInQKernel/ or docs/.
"""
import argparse, csv, importlib.util, os, re, sys

ROOT = os.getcwd()
_spec = importlib.util.spec_from_file_location('af', os.path.join(ROOT, 'scripts/one_proof/autofold.py'))
af = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(af)
import render_open  # noqa: E402 (autofold put scripts/one_proof on sys.path)

CHAIN_R = 'OpenResearchLeaves54SF'  # fold-b116: ss-faltings' copy (SSFChain) of TailZ80's bundle
CHAIN_R_OLD = 'OpenResearchLeaves54'          # the bundle the generated chain copies (its `...U` is the chain's top; d2a6b on f3402e89: TailZ80)
CHAIN_TOP = 'sixContactMin_of_open73_sf'  # fold-b116
CHAIN_TOP_OLD = 'sixContactMin_of_open73'     # the chain's top theorem (its `_u` copy)
Y3_SPEC = 'scratch/y3-route-a/autofold.json'
Y3_ROW = 'scratch/y3-route-a/kinds-row.tsv'

SZ_DOC = ("  /-- Silverberg-Zarhin, Semistable reduction and torsion subgroups of abelian varieties, Ann. Inst. Fourier 45 "
          "(1995), 403-420, Theorem 3.5, p. 406 (Raynaud's criterion as diophantine_zq.tex L816 cites it; bibliography "
          "L11077): over any field with a discrete valuation, n >= 3 not divisible by the residue characteristic, the "
          "n-torsion rational, then semistable reduction in Silverberg-Zarhin's sense (p. 405; torus not necessarily split). "
          "Replaces raynaudSemistableSHOr (SGA 7 IX 4.7; recovered by SZRaynaud.raynaudSemistableSHOr_of_sz35) and, with "
          "elliotWildInertiaTrivial, gives L814-818 (SZRaynaud.raynaudWildNF_of_leaves) in place of SGA 7 IX 3.5 "
          "(sz-raynaud; d2a6-reroute). -/")
EL_DOC = ("  /-- ELLIOT (provenance (a): the uncited sentence of diophantine_zq.tex L817-818, 'Its wild inertia acts trivially "
          "on each V_l(A) with l != p'), stated at a finite place of a number field (SZRaynaud.ElliotWildInertiaTrivial): "
          "semistable reduction in Silverberg-Zarhin's sense implies every wild inertia element acts trivially on T_l(A), "
          "l invertible. True and standard (SGA 7 IX 3.5 with wild inertia pro-p; SZRaynaud.elliot_of_semistableUnipotent), "
          "but the manuscript cites nothing. With silverbergZarhinThm35 it gives D2 (d2a6-reroute: "
          "Contrib/OneProof/D2WildNF.lean) and replaces sga7_IX_3_5_ForwardGeom_Def34. -/")

SZ_ROW = dict(field='silverbergZarhinThm35', kind='published',
              flag="reading 11-17 (the fleet's print reader, page image of Ann. Inst. Fourier 45 (1995) p. 406, relayed by "
                   "the lead; notes scratch/sz-raynaud/sz-thm35-reading.md): the hypothesis line is n >= 3 (numdam's OCR "
                   "shows '>'); any field with a discrete valuation; semistable as on p. 405 (torus not necessarily split); "
                   "the n = 3 flag of locators R6 cleared",
              source="Silverberg-Zarhin, Ann. Inst. Fourier 45 (1995), Theorem 3.5, p. 406 (proof: SGA 7 IX Prop. 4.7), "
                     "semistable reduction section 3, p. 405; cited by diophantine_zq.tex L816; sz-raynaud; d2a6-reroute",
              replaces='raynaudSemistableSHOr', rated_by='d2a6-reroute; pending review')
EL_ROW = dict(field='elliotWildInertiaTrivial', kind='consequence',
              flag="ELLIOT: uncited manuscript sentence (diophantine_zq.tex:817-818), provenance (a); true and standard "
                   "(SGA 7 I Exp. IX Prop. 3.5 with wild inertia pro-p; SZRaynaud.elliot_of_semistableUnipotent proves it "
                   "from those and the on-the-spot glue WildPeriodCoprime); the manuscript cites nothing for it (sz-raynaud "
                   "section 4)",
              source="diophantine_zq.tex L817-818 (uncited); suggested citation SGA 7 I Exp. IX Prop. 3.5 (number "
                     "UNVERIFIED) with wild inertia pro-p; SZRaynaud.ElliotWildInertiaTrivial; sz-raynaud; d2a6-reroute",
              replaces='sga7_IX_3_5_ForwardGeom_Def34', rated_by='d2a6-reroute, d2a6b; pending review')

R6U_VALUE = ('  r6u := ⟨_root_.SZRaynaud.raynaudWildNF_of_leaves n.silverbergZarhinThm35 n.elliotWildInertiaTrivial\n'
             '      (_root_.GapNeron.neronSchemeModelExistsNF\n'
             '        (_root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind n.neronSchemeExtensionDedekind)),\n'
             '    n.y3FullThreeRepZ30⟩')


def struct_in_text(text, name):
    L = text.split('\n')
    for i, l in enumerate(L):
        if l.startswith(f'structure {name} : Prop where'):
            j = i + 1
            while j < len(L) and L[j].strip() != '' and not L[j].startswith(('theorem', 'def', 'structure', '/-', 'end')):
                j += 1
            return L[i + 1:j]
    af.die(f'structure {name} not found')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['absorb', 'add', 'post'], default='absorb')
    ap.add_argument('--base')
    ap.add_argument('--out')
    ap.add_argument('--rows')
    ap.add_argument('--test')
    a = ap.parse_args()
    mode = a.mode
    out_path = a.out or f'scratch/fold-b116/gen-d2a6b/BypassFold-{mode}.lean'
    rows_path = a.rows or f'scratch/fold-b116/gen-d2a6b/kinds-rows-{mode}.tsv'

    # the current top: R0, its top theorem, its module, the other bundles
    if a.base:
        base_text = open(a.base).read()
        lines = base_text.split('\n')
        if lines and lines[0].startswith('strict count'):
            lines = lines[1:]
        base_text = '\n'.join(lines)
        m = re.search(r'^theorem (sixContactMin_of_open(\d+)) \(r : (\w+)\) \(t : (\w+)\) \(l : (\w+)\)', base_text, re.M)
        if not m:
            af.die('no top theorem in ' + a.base)
        top, topn, R0, T0, A0 = m.group(1), int(m.group(2)), m.group(3), m.group(4), m.group(5)
        r0_block = struct_in_text(base_text, R0)
        base_imports = [l for l in lines if l.startswith('import ')]
        base_body = '\n'.join(l for l in lines if not l.startswith('import ') and not l.startswith('#print axioms'))
        top_mod = None
    else:
        _, binders, top, topn, top_mod, _ = af.main_state()
        bmap = {v: s for v, s in binders}
        R0, T0, A0 = bmap['r'], bmap['t'], bmap['l']
        _, r0_block = af.find_struct(R0)
    groups = af.field_groups(r0_block)
    names = [f for f, _ in groups]
    _, chain_block = af.find_struct(CHAIN_R)
    chain_names = [f for f, _ in af.field_groups(chain_block)]

    has_sz = 'silverbergZarhinThm35' in names
    has_y3 = 'y3FullThreeRepZ30' in names
    if 'sga7_IX_3_5_ForwardGeom_Def34' not in names:
        af.die(f'{R0} lacks sga7_IX_3_5_ForwardGeom_Def34')
    if not has_sz and 'raynaudSemistableSHOr' not in names:
        af.die(f'{R0} has neither raynaudSemistableSHOr nor silverbergZarhinThm35')
    if mode == 'post' and not has_y3:
        af.die(f'--mode post: {R0} lacks y3FullThreeRepZ30 (fold y3-route-a first, or use --mode absorb/add)')
    if mode != 'post' and has_y3:
        af.die(f'{R0} already has y3FullThreeRepZ30: use --mode post')
    if mode in ('absorb', 'add') and 'y3FineModuliAbP' not in names:
        af.die(f'{R0} lacks y3FineModuliAbP')
    y3spec = __import__('json').load(open(Y3_SPEC))
    y3leaf = y3spec['discharges'][0]['leaves'][0]
    Y3_FIELD = [f"  /-- {y3leaf['doc']} Also gives A6 and the kernel field's good reduction (L529-530; d2a6b: "
                "Contrib/OneProof/A6Z30.lean, D2A6.hasGoodReduction_of_z30) in place of R6. -/",
                '  y3FullThreeRepZ30 : _root_.Y3RouteA.Y3FullThreeRepZ30']

    NEWR = af.bump(R0)
    NEWTOP = f'sixContactMin_of_open{topn + 1}'
    out_fields = []
    for f, lines in groups:
        if f == 'raynaudSemistableSHOr':
            out_fields += [SZ_DOC, '  silverbergZarhinThm35 : _root_.SZRaynaud.SilverbergZarhinThm35']
        elif f == 'sga7_IX_3_5_ForwardGeom_Def34':
            out_fields += [EL_DOC, '  elliotWildInertiaTrivial : _root_.SZRaynaud.ElliotWildInertiaTrivial']
            if mode == 'add':
                out_fields += Y3_FIELD
        elif f == 'y3FineModuliAbP' and mode == 'absorb':
            out_fields += Y3_FIELD
        else:
            out_fields += lines
    new_names = [re.match(r'^  (\w+) :', l).group(1) for l in out_fields if re.match(r'^  (\w+) :', l)]

    # the conversion to the chain's bundle, field by field
    conv = []
    for f in chain_names:
        if f == 'sga7_IX_3_5_ForwardGeom_Def34':
            conv.append(R6U_VALUE)
        elif f == 'raynaudSemistableSHOr':
            conv.append('  raynaudSemistableSHOr := _root_.SZRaynaud.raynaudSemistableSHOr_of_sz35 n.silverbergZarhinThm35')
        elif f == 'y3FineModuliAbP' and 'y3FineModuliAbP' not in new_names:
            conv.append('  y3FineModuliAbP := _root_.Y3RouteA.y3FineModuliAbP_of_z30 n.y3FullThreeRepZ30')
        elif f == 'carayolThmAIrr' and 'carayolThmAIrr' not in new_names:
            # carirr-refold (TailZ83), as in its conversion `openResearchLeaves56_of_OpenResearchLeaves57`
            conv.append('  carayolThmAIrr := _root_.CarayolRefold.carayolThmAIrr_of_frob n.carayolThmAFrob')
        elif f in new_names:
            conv.append(f'  {f} := n.{f}')
        else:
            af.die(f'{CHAIN_R} field {f}: no value from {NEWR} (regenerate the chain on this base)')
    unused = [f for f in new_names if f not in chain_names and f not in
              ('silverbergZarhinThm35', 'elliotWildInertiaTrivial', 'y3FullThreeRepZ30', 'carayolThmAFrob')]
    if unused:
        af.die(f'{NEWR} fields not read by the conversion: {unused}')

    removed = ['sga7_IX_3_5_ForwardGeom_Def34'] + ([] if has_sz else ['raynaudSemistableSHOr']) + \
        (['y3FineModuliAbP'] if mode == 'absorb' else [])
    added = ([] if has_sz else ['silverbergZarhinThm35']) + ['elliotWildInertiaTrivial'] + \
        (['y3FullThreeRepZ30'] if mode in ('absorb', 'add') else [])
    nf = len(new_names)
    imports = ([f'import ZInQKernel.OneProof.H.{top_mod}'] if top_mod else ['import ZInQKernel.OneProof.H.TailZ<y3>']) + \
        ['import ZInQKernel.OneProof.H.D2A6Chain']
    body = [
        '',
        f'/-! # OneProof H, d2a6b: `{NEWTOP}` (generated by scratch/fold-b116/gen-d2a6b/gen_bypass.py --mode {mode}, d2a6b\'s generator retargeted on the post-ss-faltings chain)',
        '',
        'Fields removed: ' + ', '.join(f'`{f}`' for f in removed) + '. Fields added: ' +
        ', '.join(f'`{f}`' for f in added) + '. Fields mapped: ' +
        ', '.join(f'`{f}`' for f in ['silverbergZarhinThm35'] * has_sz + ['y3FullThreeRepZ30'] * has_y3) + '.',
        'The removed IX 3.5 field fed only R6 (`PkgI2.RaynaudCriterionNF`), whose three readers (D2, A6, the kernel',
        'field) take on the manuscript\'s route `D2A6.R6U` = `SZRaynaud.RaynaudWildNF` (L814-818) ∧',
        '`Y3RouteA.Y3FullThreeRepZ30` (the proper model of L443-477 over ℤ[1/30], used at L529-530;',
        '`Contrib/OneProof/D2A6Wrap.lean`, `A6Z30.lean`); `OneProof/H/D2A6Chain.lean` is the chain of',
        f'`{CHAIN_TOP}` (ss-faltings\' chain `OneProof/H/SSFChain.lean`) on `R6U` (generated, gen_chain.py). A bypass, not an autofold (fold-b105\'s pattern): the old',
        'field is not derivable from the new leaves. Every existing declaration is unchanged. -/',
        '',
        'namespace HDec',
        '',
        'namespace HSyn',
        '',
        f'/-- `{R0}` with ' + '; '.join(
            [f'`{x}` replaced by `{y}`' for x, y in [('sga7_IX_3_5_ForwardGeom_Def34', 'elliotWildInertiaTrivial')]
             + ([] if has_sz else [('raynaudSemistableSHOr', 'silverbergZarhinThm35')])
             + ([('y3FineModuliAbP', 'y3FullThreeRepZ30')] if mode == 'absorb' else [])]
            + (['`y3FullThreeRepZ30` added'] if mode == 'add' else [])) + f' (d2a6b). {nf} fields. -/',
        f'structure {NEWR} : Prop where',
        *out_fields,
        '',
        f'/-- `{CHAIN_R}U` (`D2A6Chain.lean`: `{CHAIN_R}` with `r6u : D2A6.R6U`) from `{NEWR}`: `faltingsSemistableHeightBC` mapped; `r6u` from',
        '`SZRaynaud.raynaudWildNF_of_leaves` (L814-818; the Néron input from `neronSchemeExtensionDedekind`) and',
        '`y3FullThreeRepZ30` (L443-477); `raynaudSemistableSHOr` from `silverbergZarhinThm35`; `y3FineModuliAbP` from',
        '`y3FullThreeRepZ30` (y3-route-a\'s `y3FineModuliAbP_of_z30`) where it is not a field. -/',
        f'theorem {CHAIN_R[0].lower() + CHAIN_R[1:]}U_of_{NEWR} (n : {NEWR}) : {CHAIN_R}U where',
        *conv,
        '',
        '/-- **G0 with only the open leaves and the open glue** (d2a6b: D2 through L814-818, A6 and the kernel field',
        'through the manuscript\'s model of `Y₃` over ℤ[1/30], L443-477; SGA 7 IX 3.5 removed' +
        ('; IX 4.7 was removed by sz-raynaud\'s fold). -/' if has_sz else ' and 4.7 removed). -/'),
        f'theorem {NEWTOP} (r : {NEWR}) (t : {T0}) (l : {A0}) :',
        '    ZInQ.SixContactMin :=',
        f'  {CHAIN_TOP}_u ({CHAIN_R[0].lower() + CHAIN_R[1:]}U_of_{NEWR} r) t l',
        '',
        'end HSyn',
        '',
        'end HDec',
        '',
        f'#print axioms HDec.HSyn.{NEWTOP}',
        '']
    if T0 != 'OpenTextbookLeaves18' or A0 != 'OpenAddedLeaves27':
        af.die(f'the chain takes OpenTextbookLeaves18/OpenAddedLeaves27, the top has {T0}/{A0}: regenerate the chain')
    open(out_path, 'w').write('\n'.join(imports + body))
    if a.base and a.test:
        imps = sorted(set(base_imports + ['import ZInQKernel.OneProof.H.D2A6Chain']))
        open(a.test, 'w').write('\n'.join(imps) + '\n' + base_body + '\n' + '\n'.join(body))

    # kinds rows and counts
    rows, cols = af.load_kinds()
    base_counts = af.counts(rows)
    y3row = list(csv.DictReader(open(Y3_ROW), delimiter='\t'))[0]
    if mode == 'post':
        # the y3-route-a fold first (its exact row), when this base's kinds.tsv does not have it yet
        if not any(r['field'] == 'y3FullThreeRepZ30' for r in rows):
            rows = [r for r in rows if r['field'] != 'y3FineModuliAbP'] + [y3row]
    before = af.counts(rows)
    by = {r['field']: r for r in rows}
    new_rows = []
    for d in ([] if has_sz else [SZ_ROW]) + [EL_ROW]:
        old = by[d['replaces']]
        strict = 'LEAF' if d['kind'] == 'published' and not render_open.must_be_glue(d['flag']) else 'GLUE'
        row = {c: '' for c in cols}
        row.update(bundle=old['bundle'], field=d['field'], kind=d['kind'], flag=d['flag'], strict=strict,
                   strictest=strict, source=d['source'], rated_by=d['rated_by'],
                   packet=old.get('packet', ''), label=old.get('label', ''), tier=old.get('tier', ''),
                   flag_class=af.flag_class(d['flag'], strict, strict), area_issue=old.get('area_issue', ''))
        new_rows.append(row)
    if mode in ('absorb', 'add'):
        new_rows.append(dict(y3row))
    kept = [r for r in rows if r['field'] not in removed]
    after = af.counts(kept + new_rows)
    with open(rows_path, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter='\t', lineterminator='\n', extrasaction='ignore')
        w.writeheader()
        w.writerows(new_rows)
    print(f'mode {mode}: {R0} ({len(names)} fields) -> {NEWR} ({nf}); top {NEWTOP}; wrote {out_path}, {rows_path}'
          + (f', {a.test}' if a.base and a.test else ''))
    print(f'  removed {removed}; added {added}; mapped ' + str(['silverbergZarhinThm35'] * has_sz + ['y3FullThreeRepZ30'] * has_y3))
    if mode == 'post':
        print(f'  this base (kinds.tsv): {base_counts[1]}/{base_counts[2]} on {base_counts[0]}; after y3-route-a\'s '
              f'fold: {before[1]}/{before[2]} on {before[0]}')
    print(f'  strict count: {before[1]}/{before[2]} on {before[0]} -> {after[1]}/{after[2]} on {after[0]}; '
          f'strictest {before[3]}/{before[4]} -> {after[3]}/{after[4]}')
    for r in new_rows:
        print(f"  new row {r['field']}: {r['kind']} {r['strict']}/{r['strictest']} ({r['flag_class']})")
    for r in new_rows:
        probs = render_open.kinds_row_problems(r, {x['field'] for x in kept + new_rows}, set())
        if probs:
            print(f"  ROW PROBLEM {r['field']}: {probs}")


if __name__ == '__main__':
    main()
