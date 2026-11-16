"""raynaud-narrow: the integrator's hand step (proposed H module) and the patched Main / kinds.tsv for testing.

Writes scratch/raynaud-narrow/TailZ46.lean: the proposed `ZInQKernel/OneProof/H/TailZ46.lean` (hand fold
raynaud-narrow): `OpenResearchLeaves29` = `OpenResearchLeaves28` with `raynaudSemistableSHOr` replaced by
`raynaudSemistableSHcp`, its conversion to `RNarrow.OpenResearchLeaves28` (RaynaudNarrowChain.lean, field for field),
and `sixContactMin_of_open39`. With `--tree DIR` also writes DIR/ZInQKernel/OneProof/Main.lean switched to it and
DIR/docs/one-proof/kinds.tsv with the row `raynaudSemistableSHOr` renamed (for the autofold dry run).

Usage (repository root): python3 scratch/raynaud-narrow/gen_fold.py [--tree DIR]
"""
import csv, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_chain import decls, field_names  # noqa: E402

CHAIN = 'ZInQKernel/Contrib/OneProof/RaynaudNarrowChain.lean'
OUT = 'scratch/raynaud-narrow/TailZ46.lean'

D = decls(CHAIN)
block = D['OpenResearchLeaves28']
assert block[0].startswith('/--') or block[0].startswith('structure')
body = block[block.index('structure OpenResearchLeaves28 : Prop where') + 1:]
names = field_names(body)

src = ['import ZInQKernel.OneProof.H.TailZ45', 'import ZInQKernel.Contrib.OneProof.RaynaudNarrowChain', '',
       '/-! # OneProof H, raynaud-narrow (hand fold): `sixContactMin_of_open39`', '',
       'The research field `raynaudSemistableSHOr` (TailZ45) is read by the chain only at number fields, through',
       '`raynaudSemistable_of14` (TailZ23); raynaud-narrow re-versioned every declaration from `sixContactMin_of_open17`',
       'to `sixContactMin_of_open38` that carries it (`ZInQKernel/Contrib/OneProof/RaynaudNarrowChain.lean`, namespace',
       '`HDec.HSyn.RNarrow`) so that the chain reads `ReductB.RaynaudSemistableSHcp` instead (characteristic `0`,',
       'algebraically closed residue field). This module is the next generation over that chain: `OpenResearchLeaves29`',
       'is `OpenResearchLeaves28` with `raynaudSemistableSHOr` replaced by `raynaudSemistableSHcp`. The field is then',
       'discharged by autofold (`scratch/raynaud-narrow/autofold.json`) from the printed leaf',
       '`RaynaudNarrow.RaynaudSemistableSHcpOr`. -/', '', 'namespace HDec', '', 'namespace HSyn', '',
       '/-- `OpenResearchLeaves28` with `raynaudSemistableSHOr` replaced by `raynaudSemistableSHcp`, the generality the',
       'chain reads (raynaud-narrow). -/',
       'structure OpenResearchLeaves29 : Prop where'] + body + ['',
       '/-- raynaud-narrow\'s chain bundle `RNarrow.OpenResearchLeaves28` from `OpenResearchLeaves29` (field for field). -/',
       'theorem rNarrowLeaves28_of_OpenResearchLeaves29 (n : OpenResearchLeaves29) : RNarrow.OpenResearchLeaves28 where'] + \
      [f'  {f} := n.{f}' for f in names] + ['',
       '/-- **G0 with only the open leaves and the open glue** (raynaud-narrow; hand fold over the re-versioned chain). -/',
       'theorem sixContactMin_of_open39 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves13) (l : OpenAddedLeaves19) : ZInQ.SixContactMin :=',
       '  RNarrow.sixContactMin_of_open38 (rNarrowLeaves28_of_OpenResearchLeaves29 r) t l', '',
       'end HSyn', '', 'end HDec', '', '#print axioms HDec.HSyn.sixContactMin_of_open39', '']
open(OUT, 'w').write('\n'.join(src))
print(f'wrote {OUT}')

ROW_FLAG = ('reading risk: the print may require m > 3 (locators.md R6; the chain uses m = 3); the k(s)/kbar reading '
            'of semistable is moot (residue field algebraically closed); locator UNVERIFIED')
ROW_SOURCE = ('SGA 7 I (LNM 288) Exp. IX Prop. 4.7 (number UNVERIFIED), restricted to strictly henselian DVRs of '
              'characteristic 0 with perfect (so algebraically closed) residue field; geometric-fibre conclusion')

if '--tree' in sys.argv:
    d = sys.argv[sys.argv.index('--tree') + 1]
    m = open('ZInQKernel/OneProof/Main.lean').read()
    m2 = m.replace('import ZInQKernel.OneProof.H.TailZ45', 'import ZInQKernel.OneProof.H.TailZ46', 1)
    m2 = m2.replace('(r : HDec.HSyn.OpenResearchLeaves28)', '(r : HDec.HSyn.OpenResearchLeaves29)', 1)
    m2 = m2.replace('HDec.HSyn.sixContactMin_of_open38 ', 'HDec.HSyn.sixContactMin_of_open39 ', 1)
    assert m2.count('TailZ46') == 1 and 'OpenResearchLeaves29' in m2 and 'sixContactMin_of_open39' in m2
    os.makedirs(f'{d}/ZInQKernel/OneProof/H', exist_ok=True)
    open(f'{d}/ZInQKernel/OneProof/Main.lean', 'w').write(m2)
    open(f'{d}/ZInQKernel/OneProof/H/TailZ46.lean', 'w').write('\n'.join(src))
    rows = list(csv.DictReader(open('docs/one-proof/kinds.tsv'), delimiter='\t'))
    cols = list(rows[0].keys())
    for r in rows:
        if r['field'] == 'raynaudSemistableSHOr':
            r['field'] = 'raynaudSemistableSHcp'
            r['flag'] = ROW_FLAG
            r['source'] = ROW_SOURCE
            r['rated_by'] = 'raynaud-narrow; pending review'
            r['flag_class'] = 'reading-risk,unverified-locator'
    os.makedirs(f'{d}/docs/one-proof', exist_ok=True)
    with open(f'{d}/docs/one-proof/kinds.tsv', 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(rows)
    print(f'wrote {d}/ZInQKernel/OneProof/Main.lean, H/TailZ46.lean, docs/one-proof/kinds.tsv')
