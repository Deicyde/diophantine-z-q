"""Assign the 82 audit records (docs/theorem-application-audit/applications.json) to the
roles of the construction, using the manuscript line ranges of their anchors.

Line ranges (diophantine_zq.tex, sha256 cb1148cd...):
  254-376   G   elliptic model and generator
  377-972   H   six-contact height (with the appendix 10936-11250)
  973-1122  PC  pole predicate, PC from RC
  1123-1759 M   multiplication and 22P
  1760-5744, 6825-10935  RC  restricted converse
  5745-6093 C   compiler
  6094-6271 V   value relation
  6272-6442 S   cutoff and size (CAT)
  6443-6590 X   corollaries
"""
import json, collections, sys, os
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.abspath(os.path.join(here, '..', '..'))
apps = json.load(open(os.path.join(root, 'docs/theorem-application-audit/applications.json')))

def role(l):
    if 254 <= l < 377: return 'G'
    if 377 <= l < 973 or 10936 <= l <= 11250: return 'H'
    if 973 <= l < 1123: return 'PC'
    if 1123 <= l < 1760: return 'M'
    if 1760 <= l < 5745 or 6825 <= l < 10936: return 'RC'
    if 5745 <= l < 6094: return 'C'
    if 6094 <= l < 6272: return 'V'
    if 6272 <= l < 6443: return 'S'
    if 6443 <= l < 6591: return 'X'
    return 'other'

assert len(apps) == 82
sha = {a['manuscript_sha256'] for a in apps}
print('manuscript sha256 in audit:', sha)
groups = collections.defaultdict(list)
for a in apps:
    rs = sorted({role(x['line_start']) for x in a['manuscript_anchors'] if 'line_start' in x})
    groups['+'.join(rs)].append((a['id'], a['title']))
for k in sorted(groups, key=lambda k: (-len(groups[k]), k)):
    print('%-14s %2d  %s' % (k, len(groups[k]), ' '.join(i for i, _ in groups[k])))
# records touching each role at all
touch = collections.Counter()
for k, v in groups.items():
    for r in k.split('+'):
        touch[r] += len(v)
print('records touching each role:', dict(touch))
