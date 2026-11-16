"""W13 normalization pipeline (offline tool): port-command translation, notation inlining, notices.

  python3 pipeline.py --cone-json work/cone_core.json [--write]
  python3 pipeline.py --modules M1 M2 ... [--write]

Order: translate (topological, publishing aliases), write, inline notations (Lean-parser located),
append a per-file normalization notice.  Writes work/manifest/<module>.json.
"""
import os, sys, json, argparse, collections, re, datetime
sys.path.insert(0, os.path.dirname(__file__))
from translate import Translator, topo_order, FQ_PREFIX, WORK
from sim import Graph
from graph import ROOT, path_of
import cmdparse
import notation_inline as ni

NOTICE_TAG = 'Normalization notice (W13 source normalization)'


def notice_text(counts, nrep):
    items = []
    def c(k):
        return counts.get(k, 0)
    if c('import-portutilext'):
        items.append('the import of the omitted `CloudB3W13Shared.R2NOS.PortUtilExt` command module was removed '
                     '(replaced by the existing `CloudW03NeronSurj.PortUtil` import where it was the only one)')
    shims = [(k[5:], v) for k, v in sorted(counts.items()) if k.startswith('shim-')]
    if shims:
        items.append('port scope commands rewritten as ordinary Lean (`open _root_.…`, `open scoped _root_.…`, '
                     '`export _root_.… (…)`, `attribute [-instance]/[-simp] …`), reproducing their effect on '
                     'open declarations, active scoped namespaces, aliases and erased attributes: ' +
                     ', '.join('%s ×%d' % (k, v) for k, v in shims))
    syncs = sum(v for k, v in counts.items() if k.startswith('sync-after-'))
    if syncs:
        items.append('%d `open` line(s) inserted where a namespace opened earlier by a port command came into '
                     'existence (same scope effect as the port command)' % syncs)
    if c('typeeq-removed'):
        items.append('%d `#r2nos_type_eq_warn` diagnostic(s) removed' % c('typeeq-removed'))
    sk = c('erase-skip-unknown') + c('erase-skip-ambiguous') + c('erase-skip-already')
    if sk:
        items.append('%d erase-guard name(s) the port command would have skipped (not declared in this '
                     'import closure) omitted' % sk)
    if c('alias-redundant'):
        items.append('%d redundant alias(es) dropped (name resolution unchanged)' % c('alias-redundant'))
    if nrep:
        items.append('%d file-local notation(s) inlined at %d use(s) (right-hand side substituted, '
                     'parenthesised)' % (nrep['defs'], nrep['uses']))
    if not items:
        return None
    body = ('/- %s, 2026-11-16, Cloud Batch 3 Worker 13 with Metamate/agentcloud assistance\n'
            '(modification under Apache-2.0 §4(b)): ' % NOTICE_TAG) + '; '.join(items) + (
        '. Mechanical, tool-generated (offline translator, see CloudB3W13/NORMALIZATION.md); no statement, '
        'hypothesis, definition or proof was changed. -/\n')
    # wrap at ~110 columns
    out = []
    line = ''
    for w in body.split(' '):
        if '\n' in w:
            a, b = w.split('\n', 1)
            line = (line + ' ' + a) if line else a
            out.append(line)
            line = b
            continue
        if len(line) + 1 + len(w) > 110 and line:
            out.append(line)
            line = w
        else:
            line = (line + ' ' + w) if line else w
    if line:
        out.append(line)
    return '\n'.join(out).rstrip() + '\n'


def insert_notice(src, text):
    """insert after the leading comment block(s) before the first import / module line"""
    if NOTICE_TAG in src:
        return src
    m = re.search(r'^(?:module|public import|import)\b', src, re.M)
    pos = m.start() if m else 0
    return src[:pos] + text + src[pos:]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cone-json')
    ap.add_argument('--modules', nargs='*', default=[])
    ap.add_argument('--write', action='store_true')
    ap.add_argument('--no-notation', action='store_true')
    args = ap.parse_args()
    G = Graph()
    mods = list(args.modules)
    if args.cone_json:
        mods += json.load(open(args.cone_json))
    order = topo_order(G, mods)
    os.makedirs(os.path.join(WORK, 'manifest'), exist_ok=True)
    tot = collections.Counter()
    res_tot = collections.Counter()
    texts = {}
    meta = {}
    for m in order:
        if m.startswith(FQ_PREFIX):
            tot['skipped-finitequotient'] += 1
            continue
        tr = Translator(G, m).run()
        for a, ts in tr.S.aliases.items():
            for t in ts:
                G.add_alias(m, a, t)
        texts[m] = tr.output()
        meta[m] = {'counts': dict(tr.counts), 'residuals': tr.res, 'decisions': tr.decisions, 'orig': tr.src}
        tot.update(tr.counts)
        for r in tr.res:
            res_tot[r['kind']] += 1
    # notation inlining on the translated texts
    nreports = {}
    notation_files = [m for m in texts if re.search(r'^(?:local |scoped )?(?:notation|infixl?|infixr|prefix|postfix|macro)\b',
                                                     texts[m], re.M)]
    if notation_files and not args.no_notation:
        # the Lean locator reads files from disk: write the translated texts to a scratch mirror
        scratch = os.path.join(WORK, 'scratch_mirror')
        rels = []
        for m in notation_files:
            rel = path_of(m)
            dst = os.path.join(scratch, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            open(dst, 'w', encoding='utf-8').write(texts[m])
            rels.append(dst)
        info = ni.run_lean_tool(rels, os.path.join(WORK, 'mods_mathlib.txt'), os.path.join(WORK, 'nuses.jsonl'))
        for m, dst in zip(notation_files, rels):
            d = info[dst]
            new, rep = ni.inline_file(path_of(m), d, src=texts[m])
            if d['errors']:
                rep['tool_errors'] = d['errors']
            nreports[m] = {k: v for k, v in rep.items() if k != 'unmatched'}
            nreports[m]['unmatched'] = len(rep['unmatched'])
            texts[m] = new
            tot['notation-defs'] += rep['defs']
            tot['notation-uses'] += rep['uses']
    changed = 0
    for m, t in texts.items():
        nt = notice_text(meta[m]['counts'], nreports.get(m))
        if nt and t != meta[m]['orig']:
            t = insert_notice(t, nt)
        texts[m] = t
        man = {'module': m, 'counts': meta[m]['counts'], 'residuals': meta[m]['residuals'],
               'decisions': meta[m]['decisions'], 'notation': nreports.get(m), 'changed': t != meta[m]['orig']}
        json.dump(man, open(os.path.join(WORK, 'manifest', m + '.json'), 'w'), indent=1, default=str, ensure_ascii=False)
        if t != meta[m]['orig']:
            changed += 1
            if args.write:
                open(os.path.join(ROOT, path_of(m)), 'w', encoding='utf-8').write(t)
    print(json.dumps({'modules': len(order), 'changed': changed, 'counts': tot, 'residuals': res_tot,
                      'notation_files': len(notation_files),
                      'notation_risks': sum(len(r.get('risks', [])) for r in nreports.values()),
                      'notation_unmatched': sum(r.get('unmatched', 0) for r in nreports.values()),
                      'notation_tool_errors': sum(len(r.get('tool_errors', [])) for r in nreports.values())},
                     indent=1, default=str))


if __name__ == '__main__':
    main()
