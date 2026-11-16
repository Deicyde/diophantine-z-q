"""Bounded canonical-provider import retarget (offline tool, W13 integration repair, 2026-11-16).

Replaces exactly the import lines
  import ZInQKernel.Contrib.CloudB3W13Shared.TateCp.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_X
by
  import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_X
(X in FreyPackage, GaloisRep, Ramification) in the explicitly listed files only, verifies the expected
number of replacements, and adds a modification notice.  Nothing else in the files is touched.
Usage: python3 retarget_tatecp.py FILELIST EXPECTED_TOTAL [--write]
"""
import os, sys, re, json
sys.path.insert(0, os.path.dirname(__file__))
from graph import ROOT
from leanlex import lex

OLD = 'ZInQKernel.Contrib.CloudB3W13Shared.TateCp.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_'
NEW = 'ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_'
NAMES = ('FreyPackage', 'GaloisRep', 'Ramification')


def notice(names):
    lst = ', '.join('`Def_FLTPrelim_%s`' % n for n in names)
    return ('/- Import notice (W13 normalization, canonical-provider integration repair), 2026-11-16, Cloud Batch 3\n'
            'Worker 13 with Metamate/agentcloud assistance (modification under Apache-2.0 §4(b)): the import(s) of %s\n'
            'from `ZInQKernel.Contrib.CloudB3W13Shared.TateCp.Vendor.AnthropicFLT.Definitions` now name main\'s canonical\n'
            'providers of the same name in `ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions`. Their code\n'
            'is token-identical apart from four file-local `set_option`s; the staged duplicate declared the same root names and\n'
            'collided with main\'s copy. No other change. -/\n') % lst


def main():
    lst, expected = sys.argv[1], int(sys.argv[2])
    write = '--write' in sys.argv
    files = [l.strip() for l in open(lst) if l.strip()]
    total = 0
    report = []
    for f in files:
        p = os.path.join(ROOT, f)
        src = open(p, encoding='utf-8').read()
        lines = src.split('\n')
        hit = []
        for i, l in enumerate(lines):
            m = re.fullmatch(r'import ' + re.escape(OLD) + r'(\w+)', l)
            if m:
                if m.group(1) not in NAMES:
                    raise SystemExit('unexpected module %s in %s' % (m.group(1), f))
                lines[i] = 'import ' + NEW + m.group(1)
                hit.append(m.group(1))
        if not hit:
            raise SystemExit('no import line to retarget in %s' % f)
        if OLD in '\n'.join(lines):
            raise SystemExit('residual reference to the TateCp copy in %s' % f)
        new = '\n'.join(lines)
        # insertion point: the first code token (comments/strings excluded) of the header
        k = next(a for kind, a, b in lex(new) if kind not in ('ws', 'comment', 'doc', 'moddoc'))
        if new[k:k + 6] not in ('import', 'module', 'public'):
            raise SystemExit('unexpected first code token in %s: %r' % (f, new[k:k + 20]))
        new = new[:k] + notice(hit) + new[k:]
        total += len(hit)
        report.append({'file': f, 'retargeted': hit})
        if write:
            open(p, 'w', encoding='utf-8').write(new)
    if total != expected:
        raise SystemExit('expected %d replacements, found %d' % (expected, total))
    print(json.dumps({'files': len(files), 'lines': total, 'write': write}, indent=1))
    json.dump(report, open('/home/jackmccarthy/cloud-b3/w13/normalize/work/retarget_tatecp_report.json', 'w'), indent=1)


if __name__ == '__main__':
    main()
