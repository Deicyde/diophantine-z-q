import ZInQKernel.Contrib.OneProof.KolyvWeil.PoleCompleteness

open ZInQ.Manuscript

#check (KolyvWeil.kolyvaginThm1_of_prints :
  KolyvWeil.BCDTThmA6 → KolyvWeil.KolyvaginThm1Print → PoleS12.KolyvaginThm1)
#check (KolyvWeil.poleCompleteness_of_restrictedConverseGenuine_print :
  SelmerTwoPower.RestrictedConverseGenuine → PoleS12.CasselsTatePairingCurves →
    KolyvWeil.BCDTThmA6 → KolyvWeil.KolyvaginThm1Print → ZInQ.Manuscript.PoleCompleteness)
#print axioms KolyvWeil.kolyvaginThm1_of_prints
#print axioms KolyvWeil.poleCompleteness_of_restrictedConverseGenuine_print
