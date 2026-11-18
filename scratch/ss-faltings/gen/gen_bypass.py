#!/usr/bin/env python3
"""ss-faltings: the bypass fold that removes the research field `sga7_IX_Cor3_3_Def34` (SGA 7 IX Cor. 3.3, the last SGA 7
row) from the top bundle, in fold-b105's and d2a6-reroute's way.

The field's only readers are height-split's SS1/SS2/SS3, read by the height rows; on Faltings' route these need
`ZInQ.SSFaltings.FaltingsSemistableHeightBC` (Faltings 1983, invariance of the semistable height; the manuscript's
uncited L596-598) and `SemistableReductionThmIF` (proved from Raynaud's criterion). The chain of the top theorem on
these is the generated module `Contrib/OneProof/SSFChain.lean` (gen_chain.py), whose top bundle `<R0>SF` is `<R0>` with
the field replaced by `faltingsSemistableHeightBC`. This script writes the next generation `<NEWR>`: `<R0>` with
`sga7_IX_Cor3_3_Def34` replaced by `faltingsSemistableHeightBC` (docstring with the provenance), the conversion
`<lower R0>SF_of_<NEWR>` and the new top theorem. It writes the module to scratch/ss-faltings/BypassFold.lean (the
integrator's next `TailZ<j>.lean`), the proposed kinds row to scratch/ss-faltings/kinds-rows.tsv, and prints the strict
counts. It stops with an error if an edit target is missing. It changes nothing under ZInQKernel/ or docs/.

Usage (repository root):
    python3 scratch/ss-faltings/gen/gen_bypass.py [TOP_MODULE R0 OLD_TOP NEWR NEW_TOP TEXTBOOK ADDED]
defaults: ZInQKernel.OneProof.H.TailZ83 OpenResearchLeaves57 sixContactMin_of_open76 OpenResearchLeaves58SF
          sixContactMin_of_open77sf OpenTextbookLeaves18 OpenAddedLeaves27
"""
import csv, importlib.util, os, sys

ROOT = os.getcwd()
ARGS = sys.argv[1:]
sys.argv = sys.argv[:1]
_spec = importlib.util.spec_from_file_location('af', os.path.join(ROOT, 'scripts/one_proof/autofold.py'))
af = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(af)
import render_open  # noqa: E402 (autofold put scripts/one_proof on sys.path)

D = ['ZInQKernel.OneProof.H.TailZ83', 'OpenResearchLeaves57', 'sixContactMin_of_open76', 'OpenResearchLeaves58SF',
     'sixContactMin_of_open77sf', 'OpenTextbookLeaves18', 'OpenAddedLeaves27']
TOPMOD, R0, OLD_TOP, NEWR, NEW_TOP, TB, AD = (ARGS + D[len(ARGS):]) if len(ARGS) <= len(D) else af.die('too many args')
OUT = 'scratch/ss-faltings/BypassFold.lean'
ROWS = 'scratch/ss-faltings/kinds-rows.tsv'
OLDF = 'sga7_IX_Cor3_3_Def34'
NEWF = 'faltingsSemistableHeightBC'

F_DOC = ("  /-- Faltings, Endlichkeitssaetze fuer abelsche Varietaeten ueber Zahlkoerpern, Invent. Math. 73 (1983), 349-366 "
         "(bibliography faltings1983, diophantine_zq.tex L11084-11086), section 1 (locator UNVERIFIED, pending reading): "
         "the height of an abelian variety with semistable reduction everywhere does not change under finite extension of "
         "the ground field. Stated over the kernel's objects (ZInQ.SSFaltings.FaltingsSemistableHeightBC): if the Neron "
         "model N of A_L over O_L is semistable (height-split's IsSemistable), the Neron model N' of A_{L'} for L'/L "
         "finite has N'.height = N.height (metrized Hodge line, Faltings' normalization (i/2)^g, degree normalized). "
         "The manuscript uses it uncited at L596-598 ('This extension does not change its stable Faltings height') and "
         "throughout through the stable height (L598, L876). A consequence of SS2 (faltingsSemistableHeightBC_of_ss2). "
         "With Raynaud's criterion (SemistableReductionThmIF, proved) it gives the height rows R18, R19, R21, R22, "
         "StableHeightFinite and R20's lower half (Contrib/OneProof/SSFaltings.lean) in place of SGA 7 IX Cor. 3.3 "
         "(ss-faltings). -/")

KINDS_ROW = dict(
    field=NEWF, kind='published',
    flag="pending reading: Faltings 1983 section 1 not read by this task (no network access): the statement 'the height of a "
         "semistable abelian variety is invariant under finite extension' is recalled, with the locator (section 1, "
         "page) UNVERIFIED; the print gives it with SGA 7 IX 3.3 as the reason; stated over the kernel's GroupModel.height "
         "and height-split's IsSemistable",
    source="Faltings, Invent. Math. 73 (1983), 349-366, section 1 (locator UNVERIFIED; bibliography faltings1983, "
           "diophantine_zq.tex L11084-11086; the manuscript cites the paper at L621 and L733, and uses this statement "
           "uncited at L596-598); ZInQ.SSFaltings.FaltingsSemistableHeightBC; ss-faltings",
    replaces=OLDF)


def lower1(s):
    return s[0].lower() + s[1:]


def main():
    fn, block = af.find_struct(R0)
    groups = af.field_groups(block)
    names = [f for f, _ in groups]
    if OLDF not in names:
        af.die(f'{R0} lacks {OLDF}')
    if NEWF in names:
        af.die(f'{R0} already has {NEWF}')
    out_fields = []
    for f, lines in groups:
        if f == OLDF:
            out_fields += [F_DOC, f'  {NEWF} : _root_.ZInQ.SSFaltings.FaltingsSemistableHeightBC']
        else:
            out_fields += lines
    conv = [f'  {NEWF if f == OLDF else f} := n.{NEWF if f == OLDF else f}' for f in names]
    nf = len(names)
    conv_name = f'{lower1(R0)}SF_of_{NEWR}'
    text = '\n'.join([
        f'import {TOPMOD}',
        'import ZInQKernel.Contrib.OneProof.SSFChain',
        '',
        f'/-! # OneProof H, ss-faltings: `{NEW_TOP}` (generated by scratch/ss-faltings/gen/gen_bypass.py)',
        '',
        f'Field removed: `{OLDF}` (SGA 7 IX Cor. 3.3, not in the manuscript\'s bibliography; SGA 7 IX 4.7 left with',
        'sz-raynaud, so with d2a6b\'s removal of IX 3.5 this is the last SGA 7 row). Field added: `faltingsSemistableHeightBC` (Faltings 1983:',
        'the height of a semistable abelian variety is invariant under finite extension; the manuscript\'s uncited',
        'L596-598). The removed field fed only height-split\'s SS1-SS3, read only by the height rows; on Faltings\' route',
        'they take `FaltingsSemistableHeightBC` and `SemistableReductionThmIF` (proved from Raynaud\'s criterion from the',
        'same bundle fields as before), `Contrib/OneProof/SSFaltings.lean`; `Contrib/OneProof/SSFChain.lean` is the chain',
        f'of `{OLD_TOP}` on these (generated, gen_chain.py). This is a bypass, not an autofold (fold-b105\'s pattern): the',
        'old field is not derivable from the new leaf. Every existing declaration is unchanged. -/',
        '',
        'namespace HDec',
        '',
        'namespace HSyn',
        '',
        f'/-- `{R0}` with `{OLDF}` replaced by `{NEWF}` (ss-faltings). {nf} fields. -/',
        f'structure {NEWR} : Prop where',
        *out_fields,
        '',
        f'/-- `{R0}SF` (`SSFChain.lean`: `{R0}` with `{NEWF}` in place of `{OLDF}`) from `{NEWR}` (field by field). -/',
        f'theorem {conv_name} (n : {NEWR}) : {R0}SF where',
        *conv,
        '',
        '/-- **G0 with only the open leaves and the open glue** (ss-faltings: the height rows through Faltings 1983 and',
        'Raynaud\'s criterion; SGA 7 IX Cor. 3.3 removed). -/',
        f'theorem {NEW_TOP} (r : {NEWR}) (t : {TB}) (l : {AD}) :',
        '    ZInQ.SixContactMin :=',
        f'  {OLD_TOP}_sf ({conv_name} r) t l',
        '',
        'end HSyn',
        '',
        'end HDec',
        '',
        f'#print axioms HDec.HSyn.{NEW_TOP}',
        ''])
    open(OUT, 'w').write(text)
    rows, cols = af.load_kinds()
    if not any(r['field'] == OLDF for r in rows):
        af.die(f'kinds.tsv lacks {OLDF}')
    before = af.counts(rows)
    by = {r['field']: r for r in rows}
    kept = [r for r in rows if r['field'] != OLDF]
    d = KINDS_ROW
    old = by[d['replaces']]
    strict = 'LEAF' if d['kind'] == 'published' and not render_open.must_be_glue(d['flag']) else 'GLUE'
    row = {c: '' for c in cols}
    row.update(bundle=old['bundle'], field=d['field'], kind=d['kind'], flag=d['flag'], strict=strict,
               strictest=strict, source=d['source'], rated_by='ss-faltings; pending review',
               packet=old.get('packet', ''), label=old.get('label', ''), tier=old.get('tier', ''),
               flag_class=af.flag_class(d['flag'], strict, strict), area_issue=old.get('area_issue', ''))
    after = af.counts(kept + [row])
    with open(ROWS, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter='\t', lineterminator='\n', extrasaction='ignore')
        w.writeheader()
        w.writerow(row)
    print(f'{R0} ({len(names)} fields) -> {NEWR} ({nf}); wrote {OUT}, {ROWS}')
    print(f'strict count: {before[1]}/{before[2]} on {before[0]} -> {after[1]}/{after[2]} on {after[0]}; '
          f'strictest {before[3]}/{before[4]} -> {after[3]}/{after[4]}')
    print(f"  new row {row['field']}: {row['kind']} {row['strict']}/{row['strictest']} ({row['flag_class']})")


if __name__ == '__main__':
    main()
