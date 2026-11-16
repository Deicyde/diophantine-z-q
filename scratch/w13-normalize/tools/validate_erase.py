"""Cross-check erase-guard decisions against the old compile receipts (diagnostic only).

For staged files whose latest old receipt compiled (rc 0), the receipt's
`r2nos_erase_attr: … skipped, unknown constant X` warnings say which names the port command skipped in
the old environment; every other listed name was erased.  Compares with the translator's decisions
(work/full_manifest/<module>.json).  Line numbers: staged = old + 5 (the staging header).
"""
import os, sys, json, re, collections
sys.path.insert(0, os.path.dirname(__file__))
from graph import ROOT, staged_files, mod_of

REC = '/home/jackmccarthy/cloud-b3/w13/recovery/extracted/1472158738352531/receipts'
WORK = '/home/jackmccarthy/cloud-b3/w13/normalize/work'
REMAP = {'ZInQKernel/Contrib/CloudB2Shimura/': 'ZInQKernel/Contrib/CloudB3W13/',
         'ZInQKernel/Contrib/CloudR2NOS/Source/': 'ZInQKernel/Contrib/CloudB3W13Shared/R2NOS/',
         'ZInQKernel/Contrib/CloudB2TateCp/': 'ZInQKernel/Contrib/CloudB3W13Shared/TateCp/'}


def old2new(p):
    for o, n in REMAP.items():
        if p.startswith(o):
            return n + p[len(o):]
    return None


def load_receipts():
    latest = {}
    for d in os.listdir(REC):
        p = os.path.join(REC, d, 'result.json')
        if not os.path.exists(p):
            continue
        r = json.load(open(p))
        f = next((a for a in r.get('argv', []) if a.endswith('.lean')), None)
        if not f:
            continue
        m = re.search(r'ZInQKernel/.*', f)
        if not m:
            continue
        new = old2new(m.group(0))
        if not new:
            continue
        key = r.get('finished_ns') or 0
        if new not in latest or key > latest[new][0]:
            latest[new] = (key, r.get('returncode'), d)
    return latest


def receipt_skips(d):
    skips = collections.defaultdict(set)   # line -> names
    p = os.path.join(REC, d, 'stdout.log')
    for line in open(p, errors='replace'):
        line = line.strip()
        if not line.startswith('{'):
            continue
        try:
            m = json.loads(line)
        except Exception:
            continue
        data = m.get('data', '')
        mm = re.match(r'r2nos_erase_attr: \[-(\w+)\] skipped, unknown constant (\S+)', data)
        if mm:
            skips[(m['pos']['line'] + 5, mm.group(1))].add(mm.group(2))
    return skips


def main():
    latest = load_receipts()
    stats = collections.Counter()
    mism = []
    for f, (k, rc, d) in sorted(latest.items()):
        if rc != 0:
            continue
        mod = mod_of(f)
        mp = os.path.join(WORK, 'full_manifest', mod + '.json')
        if not os.path.exists(mp):
            continue
        man = json.load(open(mp))
        decs = [x for x in man['decisions'] if 'attr' in x]
        if not decs:
            continue
        skips = receipt_skips(d)
        lines_with_dec = set((x['line'], x['attr']) for x in decs)
        # line alignment check: every receipt skip line must be a decision line
        if any(key not in lines_with_dec for key in skips):
            stats['files-misaligned'] += 1
            continue
        stats['files-compared'] += 1
        for x in decs:
            actual_erase = x['name'] not in skips.get((x['line'], x['attr']), set())
            if actual_erase == x['erase']:
                stats['agree-' + ('erase' if actual_erase else 'skip')] += 1
            else:
                stats['DISAGREE-pred-%s-actual-%s' % ('erase' if x['erase'] else 'skip', 'erase' if actual_erase else 'skip')] += 1
                mism.append({'module': mod, 'line': x['line'], 'attr': x['attr'], 'name': x['name'],
                             'pred': x['erase'], 'actual': actual_erase, 'res': x.get('res')})
    json.dump({'stats': stats, 'mismatches': mism}, open(os.path.join(WORK, 'erase_validation.json'), 'w'), indent=1)
    print(json.dumps(stats, indent=1))
    byname = collections.Counter((m['name'], m['pred'], m['actual']) for m in mism)
    for k, v in byname.most_common(40):
        print(v, k)


if __name__ == '__main__':
    main()
