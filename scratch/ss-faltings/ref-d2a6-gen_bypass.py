#!/usr/bin/env python3
"""d2a6-reroute: the bypass fold that removes the research field `sga7_IX_3_5_ForwardGeom_Def34` (SGA 7 IX 3.5) from
the top bundle, in fold-b105's way (scratch/fold-b105/gen_pbp1_bypass.py; pb-p1's BypassFold.lean).

On the manuscript's route the field's only use, R6 (`PkgI2.RaynaudCriterionNF`), is replaced by `D2A6.R6U` =
`SZRaynaud.RaynaudWildNF` (diophantine_zq.tex L814-818) ∧ `SGRSplit.ShimuraIntegralModelRep` (L443-477, L529-530);
the chain of `sixContactMin_of_open72` on `R6U` is the generated module `Contrib/OneProof/D2A6Chain.lean`
(gen_chain.py), whose top bundle `OpenResearchLeaves53U` is `OpenResearchLeaves53` with the field replaced by
`r6u : D2A6.R6U`. This script writes the next generation `OpenResearchLeaves54`:

* `sga7_IX_3_5_ForwardGeom_Def34` -> `elliotWildInertiaTrivial` (ELLIOT, L817-818) and `shimuraIntegralModelRep`
  (the integral model, sgr-split's statement);
* `raynaudSemistableSHOr` -> `silverbergZarhinThm35` (Silverberg-Zarhin Thm 3.5, L816; sz-raynaud's autofold, included
  because `RaynaudWildNF` needs SZ35 itself; `raynaudSemistableSHOr` is recovered by `raynaudSemistableSHOr_of_sz35`);

the conversion `openResearchLeaves53U_of_OpenResearchLeaves54` (`r6u := ⟨raynaudWildNF_of_leaves .., ..⟩`) and
`sixContactMin_of_open73`. It writes the module to scratch/d2a6-reroute/BypassFold.lean (the integrator's next
`TailZ<j>.lean`), the proposed kinds rows to scratch/d2a6-reroute/kinds-rows.tsv, and prints the strict counts.
It changes nothing under ZInQKernel/ or docs/. Usage (repository root):

    python3 scratch/d2a6-reroute/gen/gen_bypass.py
"""
import csv, importlib.util, os, re, sys

ROOT = os.getcwd()
_spec = importlib.util.spec_from_file_location('af', os.path.join(ROOT, 'scripts/one_proof/autofold.py'))
af = importlib.util.module_from_spec(_spec)
sys.argv_saved = sys.argv
_spec.loader.exec_module(af)
import render_open  # noqa: E402 (autofold put scripts/one_proof on sys.path)

R0 = 'OpenResearchLeaves53'
NEWR = 'OpenResearchLeaves54'
OLD_TOP = 'sixContactMin_of_open72'
OUT = 'scratch/d2a6-reroute/BypassFold.lean'
ROWS = 'scratch/d2a6-reroute/kinds-rows.tsv'

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
IM_DOC = ("  /-- The proper model of diophantine_zq.tex L443-477 with its universal abelian scheme, used at L529-530 ('The "
          "proper model and its universal abelian scheme give good reduction outside the places over S'), in sgr-split's "
          "form (SGRSplit.ShimuraIntegralModelRep): for every prime p > 324 a proper smooth curve over Z_(p) with a "
          "QMAbScheme representing the full-three QM moduli problem on locally noetherian Z_(p)-schemes. The manuscript "
          "builds it from Buzzard, Duke Math. J. 87 (1997), Thm 2.1 and Cor. 2.3 at V_1(5) over Z[1/30] (full five-marking, "
          "Isom_O(O/3, A[3]), free quotient by (O/5O)^*); sgr-split's literature: Kottwitz 1992 section 5, Buzzard 1997, "
          "Morita 1981 (pending reading). Gives A6 and the kernel field's good reduction (d2a6-reroute: "
          "Contrib/OneProof/A6IntModel.lean, D2A6.hasGoodReduction_of_intModel) in place of R6. -/")

KINDS_ROWS = [
    dict(field='silverbergZarhinThm35', kind='published',
         flag="reading 11-17 (the fleet's print reader, page image of Ann. Inst. Fourier 45 (1995) p. 406, relayed by the "
              "lead; notes scratch/sz-raynaud/sz-thm35-reading.md): the hypothesis line is n >= 3 (numdam's OCR shows '>'); "
              "any field with a discrete valuation; semistable as on p. 405 (torus not necessarily split); the n = 3 flag of "
              "locators R6 cleared",
         source="Silverberg-Zarhin, Ann. Inst. Fourier 45 (1995), Theorem 3.5, p. 406 (proof: SGA 7 IX Prop. 4.7), "
                "semistable reduction section 3, p. 405; cited by diophantine_zq.tex L816; sz-raynaud; d2a6-reroute",
         replaces='raynaudSemistableSHOr'),
    dict(field='elliotWildInertiaTrivial', kind='consequence',
         flag="ELLIOT: uncited manuscript sentence (diophantine_zq.tex:817-818), provenance (a); true and standard "
              "(SGA 7 I Exp. IX Prop. 3.5 with wild inertia pro-p; SZRaynaud.elliot_of_semistableUnipotent proves it from "
              "those and the on-the-spot glue WildPeriodCoprime); the manuscript cites nothing for it (sz-raynaud section 4)",
         source="diophantine_zq.tex L817-818 (uncited); suggested citation SGA 7 I Exp. IX Prop. 3.5 (number UNVERIFIED) "
                "with wild inertia pro-p; SZRaynaud.ElliotWildInertiaTrivial; sz-raynaud; d2a6-reroute",
         replaces='sga7_IX_3_5_ForwardGeom_Def34'),
    dict(field='shimuraIntegralModelRep', kind='consequence',
         flag="pending reading: the manuscript's construction (diophantine_zq.tex L443-477: Buzzard Thm 2.1 and Cor. 2.3 at "
              "V_1(5) over Z[1/30], full five-marking, Isom_O(O/3, A[3]), free G_5-quotient, descent) is not formalized; "
              "sgr-split's literature reading is pending (Kottwitz 1992 section 5 is the PEL functor: the polarization-free "
              "integral form needs a relative Lemma P and the rational-to-integral level comparison; Buzzard and Morita may "
              "require level prime to D); restricted to p > 324 (the manuscript's model is over Z[1/30]); locators UNVERIFIED",
         source="diophantine_zq.tex L443-477 (from Buzzard, Duke Math. J. 87 (1997), Thm 2.1, Cor. 2.3), used at L529-530; "
                "Kottwitz, J. AMS 5 (1992) section 5; Buzzard 1997 sections 1-4; Morita, Hokkaido Math. J. 10 (1981) "
                "(locators UNVERIFIED); SGRSplit.ShimuraIntegralModelRep (sgr-split); d2a6-reroute",
         replaces='sga7_IX_3_5_ForwardGeom_Def34'),
]


def main():
    fn, block = af.find_struct(R0)
    groups = af.field_groups(block)
    names = [f for f, _ in groups]
    for need in ('sga7_IX_3_5_ForwardGeom_Def34', 'raynaudSemistableSHOr', 'neronSchemeExtensionDedekind'):
        if need not in names:
            af.die(f'{R0} lacks {need}')
    out_fields = []
    for f, lines in groups:
        if f == 'raynaudSemistableSHOr':
            out_fields += [SZ_DOC, '  silverbergZarhinThm35 : _root_.SZRaynaud.SilverbergZarhinThm35']
        elif f == 'sga7_IX_3_5_ForwardGeom_Def34':
            out_fields += [EL_DOC, '  elliotWildInertiaTrivial : _root_.SZRaynaud.ElliotWildInertiaTrivial',
                           IM_DOC, '  shimuraIntegralModelRep : _root_.SGRSplit.ShimuraIntegralModelRep']
        else:
            out_fields += lines
    conv = []
    for f in names:
        if f == 'raynaudSemistableSHOr':
            conv.append('  raynaudSemistableSHOr := _root_.SZRaynaud.raynaudSemistableSHOr_of_sz35 n.silverbergZarhinThm35')
        elif f == 'sga7_IX_3_5_ForwardGeom_Def34':
            conv.append('  r6u := ⟨_root_.SZRaynaud.raynaudWildNF_of_leaves n.silverbergZarhinThm35 n.elliotWildInertiaTrivial\n'
                        '      (_root_.GapNeron.neronSchemeModelExistsNF\n'
                        '        (_root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind n.neronSchemeExtensionDedekind)),\n'
                        '    n.shimuraIntegralModelRep⟩')
        else:
            conv.append(f'  {f} := n.{f}')
    nf = len(names) + 1
    text = '\n'.join([
        'import ZInQKernel.OneProof.H.TailZ79',
        'import ZInQKernel.Contrib.OneProof.D2A6Chain',
        '',
        '/-! # OneProof H, d2a6-reroute: `sixContactMin_of_open73` (generated by scratch/d2a6-reroute/gen/gen_bypass.py)',
        '',
        'Fields removed: `sga7_IX_3_5_ForwardGeom_Def34` (SGA 7 IX 3.5, not in the manuscript) and `raynaudSemistableSHOr`',
        '(SGA 7 IX 4.7). Fields added: `silverbergZarhinThm35` (Silverberg-Zarhin Thm 3.5, L816), `elliotWildInertiaTrivial`',
        '(ELLIOT, the uncited sentence at L817-818) and `shimuraIntegralModelRep` (the proper model of L443-477 with its',
        'universal abelian scheme, L529-530). The removed IX 3.5 field fed only R6 (`PkgI2.RaynaudCriterionNF`), whose',
        'three readers (D2, A6, the kernel field) take on the manuscript\'s route `D2A6.R6U` = `RaynaudWildNF` ∧',
        '`ShimuraIntegralModelRep` (`Contrib/OneProof/D2A6Wrap.lean`); `Contrib/OneProof/D2A6Chain.lean` is the chain of',
        f'`{OLD_TOP}` on `R6U` (generated, gen_chain.py). This is a bypass, not an autofold (fold-b105\'s pattern): the old',
        'field is not derivable from the new leaves. `raynaudSemistableSHOr` is discharged outright by sz-raynaud\'s',
        '`raynaudSemistableSHOr_of_sz35` (its autofold, scratch/sz-raynaud/autofold.json). Every existing declaration is',
        'unchanged. -/',
        '',
        'namespace HDec',
        '',
        'namespace HSyn',
        '',
        f'/-- `{R0}` with `sga7_IX_3_5_ForwardGeom_Def34` replaced by `elliotWildInertiaTrivial` and',
        f'`shimuraIntegralModelRep`, and `raynaudSemistableSHOr` by `silverbergZarhinThm35` (d2a6-reroute). {nf} fields. -/',
        f'structure {NEWR} : Prop where',
        *out_fields,
        '',
        f'/-- `{R0}U` (`D2A6Chain.lean`: `{R0}` with `r6u : D2A6.R6U`) from `{NEWR}`: `r6u` from',
        '`SZRaynaud.raynaudWildNF_of_leaves` (L814-818; the Néron input from `neronSchemeExtensionDedekind`) and the integral',
        'model; `raynaudSemistableSHOr` from `silverbergZarhinThm35`. -/',
        f'theorem openResearchLeaves53U_of_{NEWR} (n : {NEWR}) : {R0}U where',
        *conv,
        '',
        '/-- **G0 with only the open leaves and the open glue** (d2a6-reroute: D2 through L814-818, A6 and the kernel field',
        'through the proper model of L443-477; SGA 7 IX 3.5 and 4.7 removed). -/',
        f'theorem sixContactMin_of_open73 (r : {NEWR}) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27) :',
        '    ZInQ.SixContactMin :=',
        f'  {OLD_TOP}_u (openResearchLeaves53U_of_{NEWR} r) t l',
        '',
        'end HSyn',
        '',
        'end HDec',
        '',
        '#print axioms HDec.HSyn.sixContactMin_of_open73',
        ''])
    open(OUT, 'w').write(text)
    rows, cols = af.load_kinds()
    before = af.counts(rows)
    by = {r['field']: r for r in rows}
    kept = []
    new_rows = []
    for r in rows:
        if r['field'] in ('raynaudSemistableSHOr', 'sga7_IX_3_5_ForwardGeom_Def34'):
            continue
        kept.append(r)
    for d in KINDS_ROWS:
        old = by[d['replaces']]
        strict = 'LEAF' if d['kind'] == 'published' and not render_open.must_be_glue(d['flag']) else 'GLUE'
        row = {c: '' for c in cols}
        row.update(bundle=old['bundle'], field=d['field'], kind=d['kind'], flag=d['flag'], strict=strict,
                   strictest=strict, source=d['source'], rated_by='d2a6-reroute; pending review',
                   packet=old.get('packet', ''), label=old.get('label', ''), tier=old.get('tier', ''),
                   flag_class=af.flag_class(d['flag'], strict, strict), area_issue=old.get('area_issue', ''))
        new_rows.append(row)
    after = af.counts(kept + new_rows)
    with open(ROWS, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter='\t', lineterminator='\n', extrasaction='ignore')
        w.writeheader()
        w.writerows(new_rows)
    print(f'{R0} ({len(names)} fields) -> {NEWR} ({nf}); wrote {OUT}, {ROWS}')
    print(f'strict count: {before[1]}/{before[2]} on {before[0]} -> {after[1]}/{after[2]} on {after[0]}; '
          f'strictest {before[3]}/{before[4]} -> {after[3]}/{after[4]}')
    for r in new_rows:
        print(f"  new row {r['field']}: {r['kind']} {r['strict']}/{r['strictest']} ({r['flag_class']})")


if __name__ == '__main__':
    main()
