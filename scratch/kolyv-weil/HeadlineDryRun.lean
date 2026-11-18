import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.KolyvWeil.PoleCompleteness

/-- The headline's call with the revised pole leaves, factored at the output of the already
assembled H proof. This isolates the replacement from the private H bundle machinery. -/
theorem ZInQ.OneProof.frozenTargetKolyvWeilDryRun
    (hH : ZInQ.SixContactMin)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (h54 : ZInQ.Manuscript.PoleS12.Lemma54)
    (hB6 : ZInQ.Manuscript.KolyvWeil.BCDTThmA6)
    (hKPrint : ZInQ.Manuscript.KolyvWeil.KolyvaginThm1Print) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    hH
    (ZInQ.Manuscript.KolyvWeil.poleCompleteness_of_restrictedConverseGenuine_print hRC h54 hB6 hKPrint)

#print axioms ZInQ.OneProof.frozenTargetKolyvWeilDryRun
