import ZInQKernel.Target
import ZInQKernel.Hypotheses.HeightMin
import ZInQKernel.Contrib.OneProof.KolyvWeil.PoleCompleteness

/-- The headline splice checked at the interface of
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`
(`MainGreenTao.lean` L33–34). Its already-proved type is passed as `assemble`, so this
check needs neither its proof dependencies nor the H assembly behind `hH`. -/
theorem ZInQ.OneProof.frozenTargetKolyvWeilDryRun
    (assemble : ZInQ.SixContactMin → ZInQ.PoleCompleteness → ZInQ.FrozenTarget)
    (hH : ZInQ.SixContactMin)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (h54 : ZInQ.Manuscript.PoleS12.Lemma54)
    (hB6 : ZInQ.Manuscript.KolyvWeil.BCDTThmA6)
    (hKPrint : ZInQ.Manuscript.KolyvWeil.KolyvaginThm1Print) : ZInQ.FrozenTarget :=
  assemble hH
    (ZInQ.Manuscript.KolyvWeil.poleCompleteness_of_restrictedConverseGenuine_print hRC h54 hB6 hKPrint)

#print axioms ZInQ.OneProof.frozenTargetKolyvWeilDryRun
