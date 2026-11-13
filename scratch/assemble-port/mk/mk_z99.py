"""assemble-port: parts/z99_bundle5.lean (GluePieces5 = g0-assemble3's GluePieces4 minus 5 fields; sixContactMin_of_leaves5).
Run from scratch/assemble-port."""
import re
src = open('parts/z95_bundle4.lean').read()
a = src.index('/-- **The named Props left after g0-assemble3.** -/'); b = src.index('/-- `MobiusGlue` from T5 alone (image-plane). -/')
lines = src[a:b].split('\n'); out = []; i = 0
KUM = ['kummerAbhyankarFinGlue', 'kummerOtherBranchFin', 'kummerVerticalFin', 'kummerAbhyankarInfGlue',
       'kummerOtherBranchInf', 'kummerVerticalInf']                  # proved by ts-kummer (part e12)
DROP1 = ('verticalResidueSeparable :', 'snSpecialize :') + tuple(k + ' :' for k in KUM)  # one-line fields
DROP_DOC = ('g0-mod-galois, LEAF (R14 with its determinant', 'R17 concretely, LEAF (Carayol')  # doc line + field line
while i < len(lines):
    l = lines[i]
    if any(d in l for d in DROP1): i += 1; continue
    if any(d in l for d in DROP_DOC): i += 2; continue
    if 'fibre-qm-period, LEAF (R1(b) in family form' in l: i += 5; continue  # doc + 4-line field r1bFamily
    if 'metrization (via unif-dims), LEAF (the uniformization theorem' in l: i += 3; continue  # doc (2 lines) + field
    if 'period-map, GLUE (base change of QM classes is unique)' in l or 'fibre-qm-period, GLUE (transport of complex points' in l:
        i += 2; continue  # doc + field (proved by cpts-transport)
    out.append(l); i += 1
blk = '\n'.join(out)
assert all(k not in blk for k in KUM) and 'cPtsTransport' not in blk and 'baseChangeClassUnique' not in blk and 'analyticUniformizationOfDim' not in blk and 'r1bFamily' not in blk and 'carayolR17' not in blk and 'r14Det :' not in blk
blk = blk.replace('/-- **The named Props left after g0-assemble3.** -/', '''/-- **The named Props left after assemble-port** (32 fields): g0-assemble3's `GluePieces4` without
* `verticalResidueSeparable`, `snSpecialize`: proved by prop-ts-glue (`verticalResidueDegree`, `snSpecializeUnram`;
  together `PropTSGlue.specNonMeeting`);
* `r14Det`, `r1bFamily`, `carayolR17`: these leaves are fields of leaf-fold2's research bundle `OpenResearchLeaves2`
  (`r14`, `r1b`, `r17`), the same Props;
* `analyticUniformizationOfDim`: follows from the textbook leaf T35 (`t35 : UniformizationExists`) by metrization2's
  transport (leaf-fold2's `analyticUniformizationOfDim_of_uniformizationExists`, part e40);
* `cPtsTransport`, `baseChangeClassUnique`: proved by cpts-transport (part e45);
* the six Kummer pieces `kummerAbhyankarFinGlue`, `kummerOtherBranchFin`, `kummerVerticalFin`, `kummerAbhyankarInfGlue`,
  `kummerOtherBranchInf`, `kummerVerticalInf`: proved by ts-kummer (part e12). -/''').replace('structure GluePieces5', 'X').replace('structure GluePieces4', 'structure GluePieces5')
fields = [f for f in re.findall(r'^\s*(?:/--.*?-/\s*)?([a-zA-Z0-9]+) : ', blk, re.M) if f != 'h']
assert len(fields) == 32, len(fields)
rf = ['r1r2','r1rec','r3','r4','r5','r5count','r6','r7a','r7b','r8','r9a','r9b','r10','r11r12','r13','r14','r15','r16',
      'r18','r19','r20','r21','r22','h5fin']
def assign(lst, src, special={}):
    return ',\n    '.join('%s := %s' % (f, special.get(f, src + '.' + f)) for f in lst)
hdr = '''/-! ## assemble-port: `GluePieces5`, `sixContactMin_of_leaves5`

Task assemble-port, 2026-11-13. g0-assemble3's `sixContactMin_of_leaves4` (part z95), ported onto leaf-fold2's base
(`scratch/h-decomposition/Leaves.lean` with the ten unused `TextbookLeaves` fields deleted, every part in `namespace
HDec`; leaf-fold2's bundles `OpenResearchLeaves2`, `OpenTextbookLeaves2`, part z98), with prop-ts-glue's final results
(part e10 regenerated from `scratch/prop-ts-glue/PropTSGlue.lean` at 3d41b3d5): `VerticalResidueSeparable` and
`SNSpecialize` are theorems (so is `SpecNonMeeting`). -/

noncomputable section

namespace HSyn

/-- leaf-fold2's research bundle gives g0-assemble3's `ResearchLeaves4`: R14 without its determinant clause
(`eigenformRepExists_of_r14Det`); R10 amended in leaf-fold's form `PkgI4.DeRhamComparisonHT` is r10-amend's
`ZInQ.Contrib.R10.DeRhamComparisonHT` (the same statement, two copies; accepted by unfolding). -/
theorem researchLeaves4_of_open2 (r : OpenResearchLeaves2) : ResearchLeaves4 :=
  { %s }

''' % assign(rf, 'r', {'r14': 'eigenformRepExists_of_r14Det r.r14', 'r10': 'r.r10'})
mid = '''

/-- **`GluePieces4` from `GluePieces5`** and leaf-fold2's research and textbook bundles. -/
theorem gluePieces4_of_gluePieces5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5) :\n    GluePieces4 :=
  { %s }

/-- **G0 after assemble-port** (no `sorry`, standard axioms): leaf-fold2's open research leaves (`OpenResearchLeaves2`,
26 fields) and open textbook leaves (`OpenTextbookLeaves2`, 18 fields) and `GluePieces5` (32 fields: 13 LEAF, 3 LEAF?,
24 GLUE; table in docs/research/assemble-port.md) imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves5 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2) (gp : GluePieces5) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves4 (researchLeaves4_of_open2 r) (textbookLeaves_of_open2 t) (gluePieces4_of_gluePieces5 r t gp)

end HSyn

end

#print axioms HSyn.researchLeaves4_of_open2
#print axioms HSyn.gluePieces4_of_gluePieces5
#print axioms HSyn.sixContactMin_of_leaves5
#print axioms HSyn.textbookLeaves_of_open2
#print axioms HSyn.t14a_proved
#print axioms HSyn.t14b_proved
#print axioms HSyn.t36_proved
#print axioms HSyn.t37_proved
#print axioms HSyn.t39_of_t40
#print axioms PropTSGlue.specNonMeeting
#print axioms TsKummer.kummerAbhyankarFinGlue
#print axioms TsKummer.kummerOtherBranchFin
#print axioms TsKummer.kummerVerticalFin
#print axioms TsKummer.kummerAbhyankarInfGlue
#print axioms TsKummer.kummerOtherBranchInf
#print axioms TsKummer.kummerVerticalInf
#print axioms HSyn.G0Split.FibreQM.cPtsTransport_proof
#print axioms HSyn.G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof
#print axioms ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists
#print axioms PropTSGlue.verticalResidueDegree
#print axioms PropTSGlue.snSpecializeUnram
#print axioms PropTSGlue.propTSAll_final''
''' % assign(['verticalResidueSeparable', 'snSpecialize', 'r14Det', 'r1bFamily', 'carayolR17', 'analyticUniformizationOfDim', 'cPtsTransport', 'baseChangeClassUnique'] + KUM + fields, 'gp', {
    'verticalResidueSeparable': 'PropTSGlue.verticalResidueSeparable_of_degree PropTSGlue.verticalResidueDegree',
    'snSpecialize': 'PropTSGlue.snSpecialize_of_unram PropTSGlue.snSpecializeUnram',
    'r14Det': 'r.r14', 'r1bFamily': 'r.r1b', 'carayolR17': 'r.r17',
    'analyticUniformizationOfDim': 'ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists t.t35',
    'cPtsTransport': 'G0Split.FibreQM.cPtsTransport_proof',
    'baseChangeClassUnique': 'G0Split.FibreQM.PeriodMapH.baseChangeClassUnique_proof',
    **{k: 'TsKummer.' + k for k in KUM}})
open('parts/z99_bundle5.lean', 'w').write(hdr + blk.rstrip() + '\n' + mid)
open('fields5.txt', 'w').write('\n'.join(fields) + '\n')
print('ok', len(fields))
