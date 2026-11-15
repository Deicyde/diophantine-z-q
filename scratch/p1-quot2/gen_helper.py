# writes ZInQKernel/Contrib/OneProof/QuotientP1/Lichtenbaum.lean from scratch/p1-quot2/L1.lean
s=open('scratch/p1-quot2/L1.lean').read()
s=s[:s.index('\n#print axioms')]+'\n'
s=s.replace('P1Quot2','QuotientP1Proof')
hdr='''/-!
# p1-quot2, helper: Lichtenbaum's projectivity theorem gives affine neighbourhoods of finite sets

* `QuotientP1Proof.exists_isAffineOpen_superset_of_isClosedImmersion_spec` (EGA II 4.5.4 / Liu Prop. 3.3.36 over an
  affine base; the vendored Jacobian-Challenge field case, whose proof uses only that the base is affine);
* `QuotientP1Proof.topologicalKrullDim_eq_two`: an integral scheme, proper and smooth of relative dimension 1 over a
  DVR, has dimension 2 (fibres of dimension `≤ 1`, and the local ring at a maximal point of the special fibre is a
  DVR by the vendored FLT theorem);
* the leaf `QuotientP1Proof.LichtenbaumProjective` (Lichtenbaum 1968 Thm 2.8; Liu Thm 8.3.16; case `S = Spec R`, `R`
  a DVR) and `QuotientP1Proof.exists_affine_of_lichtenbaum`: finite sets of points of an integral proper smooth
  relative curve over a DVR lie in an affine open (mcr-glue's leaf L1 for integral models).
docs/research/p1-quot2.md. -/
'''
i=s.index('\n/-! p1-quot2: EGA II'); j=s.index('-/',i)+2
s=s[:i]+'\n'+hdr+s[j:]
open('ZInQKernel/Contrib/OneProof/QuotientP1/Lichtenbaum.lean','w').write(s)
