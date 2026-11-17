"""Hand edits on the generated No5 files (R5ptProps := True): drop every use of González–Rotger's content."""
import re, os
D=os.path.expanduser('~/dzq-wt/cm-branch/ZInQKernel/Contrib/OneProof/CMBranch/')
def edit(fn, f):
    p='/tmp/no5_all.lean'; s=open(p).read(); s2=f(s); open(p,'w').write(s2)
def rep(s, a, b, count=1):
    assert a in s, ('MISSING', a[:80])
    return s.replace(a, b, count)
def delthm(s, name):
    # delete a theorem (with docstring) named `name`
    m=re.search(r'(/--(?:(?!-/).)*-/\n)?theorem '+re.escape(name)+r'\b.*?(?=\n\n|\n(?:theorem|/--|end |namespace |section |open |-- ====))', s, re.S)
    assert m, ('NOTHM', name)
    return s[:m.start()]+'-- cm-branch edit: `'+name+'` deleted (it used González–Rotger\'s content)\n'+s[m.end():]
def B(s):
    for nm in ['r5ptProps_of_thm512_no5','gonzalezRotgerX6Ab_of_witness_no5','gonzalezRotgerX6Ab_of_coarse_no5',
               'gonzalezRotgerX6Ab_of_print_no5']:
        s=delthm(s,nm)
    if 'theorem gonzalezRotgerThm512X6_of_rcf_no5' in s: s=delthm(s,'gonzalezRotgerThm512X6_of_rcf_no5')
    s=delthm(s,'r5fp_of_point_no5')
    s=delthm(s,'r5fp_of_rep_no5')
    s=re.sub(r'(theorem point_of_r5fp_no5 .*?: R5ptProps_no5 X Ψ := ).*?(?=\n\n|\n/--|\nend )', lambda m: m.group(1)+'trivial -- cm-branch edit', s, count=1, flags=re.S)
    s=rep(s,'''(hR : LeafQM.AV.R1rec)
    (h5_no5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRepW_no5 :=''','''(hR : LeafQM.AV.R1rec) : LeafAdopt.R1R2fpRepW_no5 := -- cm-branch edit: no R5fp''')
    s=rep(s,'(residueOfX6_of_r5fp_no5 h5_no5)','(fun _ _ _ _ _ _ _ => trivial) -- cm-branch edit')
    s=rep(s,'''(hR : LeafQM.AV.R1rec) (h5_no5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRepW_no5 :=
  r1r2fpRep_of_splitW_no5 (canonicalCoarseX6_ofW hG hL) hB hR h5_no5''','''(hR : LeafQM.AV.R1rec) : LeafAdopt.R1R2fpRepW_no5 := -- cm-branch edit: no R5fp
  r1r2fpRep_of_splitW_no5 (canonicalCoarseX6_ofW hG hL) hB hR''')
    s=rep(s,'''(hR : LeafQM.AV.R1rec) (h5_no5 : LeafQM.AV.R5fp) : LeafAdopt.R1R2fpRepW_no5 :=
  r1r2fpRep_of_split5W_no5 hG hL (babaGranathX6_of hB) hR h5_no5''','''(hR : LeafQM.AV.R1rec) : LeafAdopt.R1R2fpRepW_no5 := -- cm-branch edit: no R5fp
  r1r2fpRep_of_split5W_no5 hG hL (babaGranathX6_of hB) hR''')
    s=rep(s,'''  refine r1r2fpRep_of_split6W_no5 (geomConnX6W_of_gr_no5 hG) hL hB (r1rec_of_reciprocityCanonical hR) ?_
  obtain ⟨Y, Φ, X, Ψ, fY, -, h6, h5_no5⟩ := hG
  exact ShimuraSplit.r5fp_of_point_no5 ⟨Y, Φ, X, Ψ, fY, h6, h5_no5⟩''','''  exact r1r2fpRep_of_split6W_no5 (geomConnX6W_of_gr_no5 hG) hL hB (r1rec_of_reciprocityCanonical hR)
  -- cm-branch edit: no R5fp''')
    s=rep(s,'''end GRX6AbPrint
end
-- ==== end ZInQKernel.Contrib.OneProof.GRX6AbPrint ====''','''/-- **cm-branch: the pruned field from the coarse-moduli leaf alone** (no González–Rotger): the witness of
`x6ModuliWitness_of_coarse`, with the conjunct `R5ptProps_no5 = True`. -/
theorem gonzalezRotgerX6Ab_of_coarseNoGR_no5 (hY : RayClassCFT.ShimuraMainThmIDeligneY3AbU)
    (hX : X6CoarseModuli) : HDec.QMSplit.Moduli.GonzalezRotgerX6Ab_no5 := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6⟩ := x6ModuliWitness_of_coarse hY hX
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, trivial⟩

end GRX6AbPrint
end
-- ==== end ZInQKernel.Contrib.OneProof.GRX6AbPrint ====''')
    return s
edit('No5B.lean',B)
def C(s):
    s=rep(s,'_root_.GRX6AbPrint.gonzalezRotgerX6Ab_of_print_no5 n.gonzalezRotgerThm512X6 n.shimuraMainThmIDeligneY3AbU n.x6CoarseModuli t.gagaMorphism t.mumfordTorsionAlgClosed','_root_.GRX6AbPrint.gonzalezRotgerX6Ab_of_coarseNoGR_no5 n.shimuraMainThmIDeligneY3AbU n.x6CoarseModuli -- cm-branch edit')
    # drop the field r5 : LeafQM.AV.R5fp (with its doc comment) and every `r5 := …` line
    s=re.sub(r'(\n  /--(?:(?!-/).)*-/)?\n  r5 : LeafQM\.AV\.R5fp', '', s, flags=re.S)
    s=re.sub(r'\n  r5 := [^\n]*', '', s)
    # drop the González–Rotger 5.12 fields (both forms) and their assignments
    s=re.sub(r'(\n  /--(?:(?!-/).)*-/)?\n  gonzalezRotgerThm512X6(RCF)?(_no5)? : [^\n]*', '', s, flags=re.S)
    s=re.sub(r'\n  gonzalezRotgerThm512X6(RCF)?(_no5)? := [^\n]*', '', s)
    return s
edit('No5C.lean',C)
print('edits applied')

