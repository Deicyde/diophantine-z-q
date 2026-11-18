"""y3-x6b (adapted from y3-x6's gen_y3.py to the cm-fold-rebase base): generate the Y3-row copies of the CM-branch route (no X6 witness).

Input: cm-branch2's weak-row copies ZInQKernel/Contrib/OneProof/CMBranch/R5Prune{1,2,3,}.lean (every declaration
that mentions the moduli row, copied with suffix `_r5`) and CMBranch/Open73.lean (the top bundle generation).
Output: ZInQKernel/Contrib/OneProof/Y3X6/Copy{1..n}.lean and Y3X6/Top.lean, where
  * every `_r5` name is renamed `_y3` (the copies are verbatim otherwise);
  * the row `R1R2fpRepW_y3` and `R1R2fp_y3` are `Y3X6.R1R2fpY3` (the row over Y3, `Y3X6/Row.lean`);
  * the readers of the X6 clauses are replaced by the proofs of `Y3X6/Row.lean` (REPLACE below);
  * the producers of the X6 row and of the X6 conic are deleted (DELETE) and `X6ConicModel_y3 := True`
    (read by nothing on the CM-branch route; cm-branch2 section 5.1);
  * in every bundle generation the carried fields `gonzalezRotgerX6Ab` (the X6 witness) become `y3row : Y3ToP1j`,
    the Elkies fields (`elkiesX6StarFunctionField`, `elkiesX6StarPrinted`, `elkiesEquationsX6Ab`) become
    `heckeSqrtY3 : HeckeSqrtBranchAny`, and `babaGranathRationalAb` is dropped;
  * the top bundle drops `x6CoarseModuliIdeal`, `elkiesX6StarEveryIdeal` and adds `y3ToP1j`, `heckeSqrtBranchAny`.
"""
import re, os

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..'))
SRC = os.path.join(ROOT, 'ZInQKernel/Contrib/OneProof/')
OUT = os.path.join(ROOT, 'ZInQKernel/Contrib/OneProof/Y3X6/')

def rd(p): return open(p).read()

DELETE = {
 'HDec.FS5NoCM.R1R2fpFullProps',
 'HDec.QMSplit.Moduli.ResidueOfX6', 'HDec.QMSplit.Moduli.ConicOfWitness', 'HDec.QMSplit.Moduli.x6ConicModel_of',
 'HDec.QMSplit.Moduli.GonzalezRotgerX6', 'HDec.QMSplit.Moduli.coarseFactor_of_rep',
 'HDec.QMSplit.Moduli.coarseFactor_of_rep\'', 'HDec.QMSplit.Moduli.residueOfX6_of_r5fp',
 'HDec.QMSplit.Moduli.conicOfWitness_of_elkies', 'HDec.QMSplit.Moduli.x6ConicModel_of_elkies',
 'HDec.QMSplit.Moduli.x6ConicModel_of_elkies_t5', 'HDec.QMSplit.Moduli.r1r2fpRep_ofW',
 'HDec.QMSplit.Moduli.r1r2fpRep_of\'W', 'HDec.QMSplit.Moduli.r1r2fpRep_of_splitW',
 'HDec.QMSplit.Moduli.geomConnX6W_of_gr', 'HDec.QMSplit.Moduli.r1r2fpRep_of_split5W',
 'HDec.QMSplit.Moduli.r1r2fpRep_of_split6W', 'HDec.QMSplit.Moduli.r1r2fpRep_of_printedW',
 'HDec.QMSplit.Moduli.r1r2fpRep_of_printed_t5W', 'HDec.QMSplit.Moduli.r1r2_of_publishedW',
 'HDec.QMSplit.Moduli.x6ConicModel_of_publishedW', 'HDec.QMSplit.Moduli.X6LeavesW',
 'HDec.QMSplit.Moduli.x6Rows_of_leavesW', 'HDec.QMSplit.Moduli.GonzalezRotgerX6Ab',
 'LeafQM.AV.R1UnivRigid.gonzalezRotgerX6_iff_ab_gl', 'SGRDirect.elkies_coordinate',
 'SGRDirect.heckeSqrtBranchAny_of_elkies', 'HDec.HSyn.SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb',
 'HDec.HSyn.openResearchLeaves34_of_OpenResearchLeaves35_eb_cf', 'HDec.HSyn.sixContactMin_of_open72_cm2',
 # y3-x6b: the GR9 copy of the Elkies-based producer of HeckeSqrtBranchAny (bost-gr9's TailZ80 chain)
 'HDec.HSyn.GR9.SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb',
 # y3-x6b: the GR9 conversion 35 -> 34 (the top conversion of Open77 replaces it)
 'HDec.HSyn.GR9.openResearchLeaves34_of_OpenResearchLeaves35_eb_cf',
}

# hand-written replacements (the block after the context lines); the copied block's namespace/opens are kept
REPLACE = {
 'LeafQM.AV.R1R2fp': '''/-- y3-x6: the moduli row over `Y₃` (`Y3X6.R1R2fpY3`); the `X₆` witness and its clauses are gone. -/
def _root_.LeafQM.AV.R1R2fp_y3 : Prop := _root_.Y3X6.R1R2fpY3''',
 'LeafQM.AV.R1R2fp_Y': '''/-- y3-x6: `R1R2fp_Y` on the row over `Y₃` (`Y3X6.r1r2fp_Y`). -/
theorem _root_.LeafQM.AV.R1R2fp_Y_y3 (h : _root_.LeafQM.AV.R1R2fp_y3) : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (π : ToP1 Y.left), R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ R2fpProps Y Φ π :=
  _root_.Y3X6.r1r2fp_Y h''',
 'LeafQM.AV.residue_unramified_over_branch': '''/-- y3-x6: Lemma NV step 2 on the row over `Y₃` (`Y3X6.residue_unramified_over_branch`). -/
theorem _root_.LeafQM.AV.residue_unramified_over_branch_y3 (h : _root_.LeafQM.AV.R1R2fp_y3) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ (y : fieldPt Qbar ⟶ Y),
        (π.val (K := Qbar) y.left = OnePoint.some 0 ∨
          π.val (K := Qbar) y.left = OnePoint.infty ∨
          π.val (K := Qbar) y.left = OnePoint.some (-16 / 27)) →
        UnramifiedAbove5 (residueImage (X := Y.left) y.left) :=
  _root_.Y3X6.residue_unramified_over_branch h''',
 'LeafQM.AV.exists_fibre_object': '''/-- y3-x6: A4 on the row over `Y₃` (`Y3X6.exists_fibre_object`). -/
theorem _root_.LeafQM.AV.exists_fibre_object_y3 (h : _root_.LeafQM.AV.R1R2fp_y3) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ t : OnePoint Qbar, ∃ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
        Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = t :=
  _root_.Y3X6.exists_fibre_object h''',
 'LeafQM.AV.Pin.cm_objects_of_R1R2fp': '''/-- y3-x6: CM objects from the row over `Y₃` (`Y3X6.cm_objects`). -/
theorem _root_.LeafQM.AV.Pin.cm_objects_of_R1R2fp_y3 (h : _root_.LeafQM.AV.R1R2fp_y3) :
    (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q) :=
  _root_.Y3X6.cm_objects h''',
 'HDec.LeafAdopt.R1R2fpRepW': '''/-- y3-x6: the weak row is the row over `Y₃` (`Y3X6.R1R2fpY3`). -/
def _root_.HDec.LeafAdopt.R1R2fpRepW_y3 : Prop := _root_.Y3X6.R1R2fpY3''',
 'HDec.LeafAdopt.R1R2fp_of_rep': '''/-- y3-x6: both rows are `Y3X6.R1R2fpY3`. -/
theorem _root_.HDec.LeafAdopt.R1R2fp_of_rep_y3 (h : _root_.HDec.LeafAdopt.R1R2fpRepW_y3) : _root_.LeafQM.AV.R1R2fp_y3 := h''',
 'HDec.HSyn.r1rec_of_rep': '''/-- y3-x6: `R1rec` from the row over `Y₃` (`Y3X6.r1rec_of_row`). -/
theorem _root_.HDec.HSyn.r1rec_of_rep_y3 (h : _root_.HDec.LeafAdopt.R1R2fpRepW_y3) : LeafQM.AV.R1rec :=
  _root_.Y3X6.r1rec_of_row h''',
 'HDec.QMSplit.Moduli.pairsLift_of_rep': '''/-- y3-x6: `PairsLift` does not need the row: it is `pairsLift_of_t5` with T5 from the proved
`mumfordTorsionAlgClosed_proof`. -/
theorem _root_.HDec.QMSplit.Moduli.pairsLift_of_rep_y3 (h : _root_.HDec.LeafAdopt.R1R2fpRepW_y3) : PairsLift :=
  pairsLift_of_t5 (_root_.AvSplit.torsionStructure_of_mumford _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof)''',
 'HDec.X6Kummer.X6ConicModel': '''/-- y3-x6: the conic model of `X₆` (row H-43) is read by no theorem of the CM-branch route (cm-branch2 §5.1:
`X6ConicModel` used in 0 constants); it is carried as `True`. -/
def _root_.HDec.X6Kummer.X6ConicModel_y3 : Prop := True''',
}

# text patches inside copied blocks (after renaming): (block name, old, new)
PATCH = [
 ('HDec.HSyn.G0Split.FibreQM.PeriodMapH.LeafQCheck.descend_main',
  '''  obtain ⟨Y, Φ, X, Ψ, fY, π₆, hR1, -⟩ := hRep''',
  '''  obtain ⟨Y, Φ, π, hR1, -⟩ := hRep'''),
 ('GapST.cm_pointW',
  '''  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5⟩ := hRep''',
  '''  obtain ⟨Y, Φ, π, h1, hh, hat, hr⟩ := hRep'''),
 ('GapST.cm_pointW',
  '''  obtain ⟨x, hx⟩ := hs.1 (OnePoint.some 1)
  obtain ⟨y₁, hy₁⟩ := hs.2 x
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : QML3 Qbar, Φ Qbar y₁ = M3.mk P₀ :=
    ⟨(Φ Qbar y₁).out, (Quotient.out_eq _).symm⟩
  have hΨ : Ψ x = Quotient.mk _ P₀.forget := by rw [← hy₁]; exact h6.2.2.2.2.2 y₁ P₀ hP₀
  obtain ⟨-, h4, h3, h24⟩ := h2 x x P₀.forget P₀.forget hΨ hΨ''',
  '''  obtain ⟨y₁, hx⟩ := hat.2.1 (OnePoint.some 1)
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : QML3 Qbar, Φ Qbar y₁ = M3.mk P₀ :=
    ⟨(Φ Qbar y₁).out, (Quotient.out_eq _).symm⟩
  obtain ⟨-, h4, h3, h24⟩ := hat.1 y₁ y₁ P₀ P₀ hP₀ hP₀'''),
 ('HDec.HSyn.x6Rows_of_open14_hf_gm_pz_eb',
  '''  have hR := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw
  _root_.HDec.QMSplit.Moduli.x6Rows_of_leavesW_y3
    { t5 := _root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed
      babaGranathR := (_root_.LeafQM.AV.R1UnivRigid.babaGranathRational_iff_ab_gl hR).mpr r.babaGranathRationalAb
      rayClass := (_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab_gl hR).mpr r.rayClassCMAb
      gonzalezRotger := (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerX6_iff_ab_gl_y3 hR).mpr r.gonzalezRotgerX6Ab
      elkiesEq := (_root_.LeafQM.AV.R1UnivRigid.elkiesEquationsX6_iff_ab_gl hR).mpr r.elkiesEquationsX6Ab }''',
  '''  have hR := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw
  ⟨_root_.Y3X6.r1r2fpY3_of r.y3row ((_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab_gl hR).mpr r.rayClassCMAb), trivial⟩'''),
 ('HDec.HSyn.openGlue7_of_OpenGlue8_hf_gm_pz_eb',
  '''  heckeSqrtBranchAny := _root_.HDec.HSyn.SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb_y3
    (_root_.HDec.HSyn.openResearchLeaves22_of_OpenResearchLeaves23_gm_eb_y3
      (_root_.HDec.HSyn.openResearchLeaves23_of_OpenResearchLeaves24_hf_gm_eb_y3 (_root_.HDec.HSyn.openResearchLeaves24_of_OpenResearchLeaves25_gm_eb_y3 r) t)) t l''',
  '''  heckeSqrtBranchAny := r.heckeSqrtY3'''),
]


# y3-x6b: the same two patches in bost-gr9's GR9 copies of the chain (TailZ80)
PATCH += [
 ('HDec.HSyn.GR9.x6Rows_of_open14_hf_gm_pz_eb', PATCH[3][1], PATCH[3][2]),
 ('HDec.HSyn.GR9.openGlue7_of_OpenGlue8_hf_gm_pz_eb',
  '''  heckeSqrtBranchAny := _root_.HDec.HSyn.GR9.SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb_y3
    (_root_.HDec.HSyn.GR9.openResearchLeaves22_of_OpenResearchLeaves23_gm_eb_y3
      (_root_.HDec.HSyn.GR9.openResearchLeaves23_of_OpenResearchLeaves24_hf_gm_eb_y3 (_root_.HDec.HSyn.GR9.openResearchLeaves24_of_OpenResearchLeaves25_gm_eb_y3 r) t)) t l''',
  '''  heckeSqrtBranchAny := r.heckeSqrtY3'''),
]

ELK = ('elkiesX6StarFunctionField', 'elkiesX6StarPrinted', 'elkiesEquationsX6Ab')

def field_ops(text):
    """Structure fields and `where` assignments of the carried X6 fields."""
    L = text.split('\n')
    out = []
    i = 0
    def drop_doc():
        # drop a field docstring directly above (lines starting '  /--' ... ending '-/')
        if out and out[-1].rstrip().endswith('-/') and out[-1].startswith('  '):
            while out and not out[-1].startswith('  /--'):
                out.pop()
            if out: out.pop()
    while i < len(L):
        l = L[i]
        m = re.match(r'^  (\w+) (:=?) (.*)$', l)
        if m and (m.group(1) in ('gonzalezRotgerX6Ab', 'babaGranathRationalAb') + ELK):
            f, op, rhs = m.groups()
            j = i + 1
            while j < len(L) and L[j].startswith('    '):
                rhs += ' ' + L[j].strip(); j += 1
            i = j
            if op == ':':
                drop_doc()
                if f == 'gonzalezRotgerX6Ab':
                    out.append('  /-- y3-x6 (carried leaf): the manuscript\'s map `Y₃ → P¹_j` (diophantine_zq.tex L420-440), in place of the `X₆` witness. -/')
                    out.append('  y3row : _root_.Y3P1j.Y3ToP1j')
                elif f in ELK:
                    out.append('  /-- y3-x6 (carried glue): the quadratic subfield ramified over `−16/27` and `∞` (`HeckeSqrtBranchAny`), in place of Elkies\' model. -/')
                    out.append('  heckeSqrtY3 : SGRDirect.HeckeSqrtBranchAny')
                # babaGranathRationalAb: dropped
            else:
                if f == 'gonzalezRotgerX6Ab':
                    v = re.match(r'^(\w+)\.gonzalezRotgerX6Ab$', rhs.strip())
                    assert v, ('GR rhs', rhs)
                    out.append(f'  y3row := {v.group(1)}.y3row')
                elif f in ELK:
                    v = re.search(r'\b(\w+)\.(' + '|'.join(ELK) + r')\b', rhs)
                    assert v, ('ELK rhs', rhs)
                    out.append(f'  heckeSqrtY3 := {v.group(1)}.heckeSqrtY3')
            continue
        out.append(l); i += 1
    return '\n'.join(out)

R5 = re.compile(r'_r5(?![A-Za-z0-9])')

def blocks_of(path):
    t = rd(path)
    k = t.index('-- copied from')
    return [('-- copied from' + b) for b in t[k:].split('-- copied from')[1:]]

def name_of(b):
    m = re.match(r'-- copied from \S+ \S+ \((.*), (TYPE|value)\)', b)
    return m.group(1)

def replace_block(b, new):
    """keep the block's context lines (up to the first docstring/decl), replace the declaration by `new`."""
    L = b.split('\n')
    k = next(i for i, l in enumerate(L) if l.startswith('/--') or re.match(r'^(@\[|theorem|def|structure|lemma|abbrev)', l))
    e = max(i for i, l in enumerate(L) if l.startswith('end'))
    # the block ends with `end <ns>` and `end` lines; keep them
    tail_start = k
    for i in range(k, len(L)):
        if L[i].startswith('end'):
            tail_start = i; break
    return '\n'.join(L[:k] + [new] + L[tail_start:])

def main():
    files = ['CMBranch/R5Prune1', 'CMBranch/R5Prune2', 'CMBranch/R5Prune3', 'CMBranch/R5Prune', 'CMFoldRebase/R5GR9_1', 'CMFoldRebase/R5GR9']
    allb = []
    for f in files:
        allb += blocks_of(SRC + f + '.lean')
    used_patch = set()
    out = []
    for b in allb:
        n = name_of(b)
        if n in DELETE:
            continue
        b = R5.sub('_y3', b)
        b = b.replace('-- cm-branch2 (hand-written)', '-- (cm-branch2 hand-written block)')
        if n in REPLACE:
            b = replace_block(b, REPLACE[n])
        for (pn, old, new) in PATCH:
            if pn == n:
                assert old in b, ('PATCH', pn, old[:60])
                b = b.replace(old, new); used_patch.add((pn, old))
        b = field_ops(b)
        out.append(b)
    assert len(used_patch) == len(PATCH), 'unused patches'
    for d in DELETE:
        assert any(name_of(b) == d for b in allb), ('DELETE not found', d)
    for r in REPLACE:
        assert any(name_of(b) == r for b in allb), ('REPLACE not found', r)
    header = ('/-! # y3-x6b: the CM-branch route with the moduli row over `Y₃` (no `X₆`), generated by\n'
              '`scratch/y3-x6b/gen/gen_y3b.py` (y3-x6\'s generator on the cm-fold-rebase base) from the weak-row copies\n'
              '`CMBranch/R5Prune*.lean` and `CMFoldRebase/R5GR9*.lean`: every declaration is a\n'
              'verbatim copy with `_r5` renamed `_y3`, except the hand-written replacements and deletions listed in the\n'
              'generator (the row is `Y3X6.R1R2fpY3`; the carried `X₆` fields become `y3row` and `heckeSqrtY3`). -/\n\n'
              'set_option maxHeartbeats 1000000\nset_option autoImplicit false\n\n')
    parts, cur = [], ''
    for b in out:
        if len((cur + b).encode()) > 140000 and cur:
            parts.append(cur); cur = ''
        cur += b
    parts.append(cur)
    os.makedirs(OUT, exist_ok=True)
    names = [f'Copy{i + 1}' for i in range(len(parts))]
    for i, (nm, body) in enumerate(zip(names, parts)):
        imp = 'import ZInQKernel.Contrib.OneProof.Y3X6.Row' if i == 0 else f'import ZInQKernel.Contrib.OneProof.Y3X6.{names[i - 1]}'
        open(OUT + nm + '.lean', 'w').write(imp + '\n\n' + header.replace('-/', f'Part {i + 1} of {len(parts)}. -/', 1) + body)
    print('parts', names, len(out), 'blocks')
    # leftover references to the dropped fields / deleted names
    txt = ''.join(out)
    for w in ['gonzalezRotgerX6Ab', 'babaGranathRationalAb', 'elkiesX6StarPrinted', 'elkiesX6StarFunctionField',
              'elkiesEquationsX6Ab', 'x6Rows_of_leavesW', 'X6LeavesW']:
        for m in re.finditer(r'.*\b' + w + r'\b.*', txt):
            print('LEFT', w, '|', m.group(0)[:160])

if __name__ == '__main__':
    main()
