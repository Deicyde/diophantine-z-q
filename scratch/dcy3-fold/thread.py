"""dcy3-fold step 1: thread `hY3 : TSHecke.Y3Connected` from `addedLeaves8_of_open9` (TailZ13, where generation 8's
`y3Connected` is produced) up to `sixContactMin_of_open27` (TailZ33), and supply it in `sixContactMin_of_open28`
(TailZ34) by dcy3-used's `DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU`.
Every edit is an exact-text replacement that must match once. Run from the repository root."""
H = 'ZInQKernel/OneProof/H/'
B = '(hY3 : TSHecke.Y3Connected)'
edits = {
'TailZ13': [
 ("theorem addedLeaves8_of_open9 (l : OpenAddedLeaves9) : OpenAddedLeaves8 where",
  "theorem addedLeaves8_of_open9 (l : OpenAddedLeaves9) " + B + " : OpenAddedLeaves8 where"),
 ("  y3Connected := _root_.ShimuraSplit.y3Connected_of_deligne\n"
  "    (_root_.ShimuraGlue.deligneComponentsY3_of_printed l.deligneComponentsY3Printed)\n",
  "  y3Connected := hY3\n"),
 ("    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open10 r t (addedLeaves8_of_open9 l) g hF5 hYu",
  "    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)\n"
  "    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open10 r t (addedLeaves8_of_open9 l hY3) g hF5 hYu"),
],
'TailZ15': [
 ("    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open11 (researchLeaves9_of_open10 r t l) t l g\n"
  "    (_root_.ZInQ.HeightSplit.faltingsLemma5BCLower_of_BC r.faltingsLemma5BC) hYu\n",
  "    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open11 (researchLeaves9_of_open10 r t l) t l g\n"
  "    (_root_.ZInQ.HeightSplit.faltingsLemma5BCLower_of_BC r.faltingsLemma5BC) hYu hY3\n"),
],
'TailZ17': [
 ("    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open12 (researchLeaves10_of_open11 r) t (addedLeaves9_of_open10 r l) g hYu\n",
  "    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open12 (researchLeaves10_of_open11 r) t (addedLeaves9_of_open10 r l) g hYu hY3\n"),
],
'TailZ18': [
 ("    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open13 r t (addedLeaves10_of_open11 l) g hYu\n",
  "    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open13 r t (addedLeaves10_of_open11 l) g hYu hY3\n"),
],
'TailZ19': [
 ("    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open14 (researchLeaves11_of_open12 r t) t l g hYu\n",
  "    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open14 (researchLeaves11_of_open12 r t) t l g hYu hY3\n"),
],
'TailZ22': [
 ("    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open15 (researchLeaves12_of_open13 r t l) t (addedLeaves11_of_open12 r t l) g hYu\n",
  "    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open15 (researchLeaves12_of_open13 r t l) t (addedLeaves11_of_open12 r t l) g hYu hY3\n"),
],
'TailZ23': [
 ("    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists) :\n"
  "    ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open11 (researchLeaves9_of_open14 r t l h6 hSS) t (addedLeaves9_of_open14 r t l) g\n"
  "    (_root_.ReductSplit.faltingsLemma5BCLower_final _root_.GapHeight.faltingsLemma5Lower) hYu\n",
  "    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists)\n"
  "    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open11 (researchLeaves9_of_open14 r t l h6 hSS) t (addedLeaves9_of_open14 r t l) g\n"
  "    (_root_.ReductSplit.faltingsLemma5BCLower_final _root_.GapHeight.faltingsLemma5Lower) hYu hY3\n"),
],
'TailZ24': [
 ("    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists) :\n"
  "    ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open17 r t (addedLeaves12_of_open13 l) g hYu h6 hSS\n",
  "    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists)\n"
  "    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open17 r t (addedLeaves12_of_open13 l) g hYu h6 hSS hY3\n"),
],
'TailZ25': [
 ("    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists) :\n"
  "    ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open18 (openResearchLeaves14_of_OpenResearchLeaves15 r) t l g hYu h6 hSS\n",
  "    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists)\n"
  "    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open18 (openResearchLeaves14_of_OpenResearchLeaves15 r) t l g hYu h6 hSS hY3\n"),
],
'TailZ26': [
 ("(g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open19 (openResearchLeaves15_of_OpenResearchLeaves16 r) t (openAddedLeaves13_of_OpenAddedLeaves14 l) g hYu\n",
  "(g : OpenGlue7) (hYu : QMLattice.YuB6Alg)\n    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open19 (openResearchLeaves15_of_OpenResearchLeaves16 r) t (openAddedLeaves13_of_OpenAddedLeaves14 l) g hYu\n"),
 ("      (addedLeaves12_of_open13 (openAddedLeaves13_of_OpenAddedLeaves14 l)))\n\n",
  "      (addedLeaves12_of_open13 (openAddedLeaves13_of_OpenAddedLeaves14 l))) hY3\n\n"),
],
'TailZ27': [
 ("(g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open20 (openResearchLeaves16_of_OpenResearchLeaves17 r) t l g hYu\n",
  "(g : OpenGlue7) (hYu : QMLattice.YuB6Alg)\n    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open20 (openResearchLeaves16_of_OpenResearchLeaves17 r) t l g hYu hY3\n"),
],
'TailZ28': [
 ("(g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open21 (openResearchLeaves17_of_OpenResearchLeaves18 r) t l g hYu\n",
  "(g : OpenGlue7) (hYu : QMLattice.YuB6Alg)\n    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open21 (openResearchLeaves17_of_OpenResearchLeaves18 r) t l g hYu hY3\n"),
],
'TailZ29': [
 ("(g : OpenGlue7) (hYu : QMLattice.YuB6Alg) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open22 (openResearchLeaves18_of_OpenResearchLeaves19 r) t l g hYu\n",
  "(g : OpenGlue7) (hYu : QMLattice.YuB6Alg)\n    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open22 (openResearchLeaves18_of_OpenResearchLeaves19 r) t l g hYu hY3\n"),
],
'TailZ30': [
 ("(l : OpenAddedLeaves15) (g : OpenGlue7) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open23 r t (openAddedLeaves14_of_OpenAddedLeaves15 l t) g\n"
  "    (QMLattice.yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed)\n",
  "(l : OpenAddedLeaves15) (g : OpenGlue7)\n    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open23 r t (openAddedLeaves14_of_OpenAddedLeaves15 l t) g\n"
  "    (QMLattice.yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed) hY3\n"),
],
'TailZ31': [
 ("(l : OpenAddedLeaves16) (g : OpenGlue7) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open24 r t (openAddedLeaves15_of_OpenAddedLeaves16 l) g\n",
  "(l : OpenAddedLeaves16) (g : OpenGlue7)\n    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open24 r t (openAddedLeaves15_of_OpenAddedLeaves16 l) g hY3\n"),
],
'TailZ32': [
 ("(l : OpenAddedLeaves16) (g : OpenGlue7) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open25 r (openTextbookLeaves10_of_OpenTextbookLeaves11 t) l g\n",
  "(l : OpenAddedLeaves16) (g : OpenGlue7)\n    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open25 r (openTextbookLeaves10_of_OpenTextbookLeaves11 t) l g hY3\n"),
],
'TailZ33': [
 ("(l : OpenAddedLeaves16) (g : OpenGlue7) : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open26 (openResearchLeaves19_of_OpenResearchLeaves20 r t) t l g\n",
  "(l : OpenAddedLeaves16) (g : OpenGlue7)\n    " + B + " : ZInQ.SixContactMin :=\n"
  "  sixContactMin_of_open26 (openResearchLeaves19_of_OpenResearchLeaves20 r t) t l g hY3\n"),
],
'TailZ34': [
 ("import ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard\n",
  "import ZInQKernel.Contrib.OneProof.ShimuraGoodReductionNoGuard\n"
  "import ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used\n"),
 ("  sixContactMin_of_open27 (openResearchLeaves20_of_OpenResearchLeaves21 r t) t (openAddedLeaves16_of_OpenAddedLeaves17 l) g\n",
  "  sixContactMin_of_open27 (openResearchLeaves20_of_OpenResearchLeaves21 r t) t (openAddedLeaves16_of_OpenAddedLeaves17 l) g\n"
  "    (_root_.DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU)\n"),
],
}
for f, es in edits.items():
    p = H + f + '.lean'
    s = open(p).read()
    for old, new in es:
        assert s.count(old) == 1, (f, old[:80], s.count(old))
        s = s.replace(old, new)
    open(p, 'w').write(s)
    print('edited', f, len(es))
