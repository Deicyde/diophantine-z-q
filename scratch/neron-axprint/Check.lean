import ZInQKernel.Contrib.OneProof.NeronDVR.RelativeSquare
import ZInQKernel.Contrib.OneProof.NeronSchemeExtensionExists

#print axioms NeronDVR.neronSchemeExtensionDedekind_proof
#print axioms ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind
#print axioms NeronExt.dvrLocal_of_extension
#print axioms NeronExt.extension_of_dvrLocal
#print axioms ZInQ.Contrib.NeronC.neronSchemeExtensionExists_of_neronModelExists
#print axioms NeronDVR.neronSchemeExtensionDedekind_of_relativeSquare
#print axioms NeronDVR.neronSchemeExtensionDedekind_of_strictHenselizationDescent
#print axioms NeronExtDedekind.neronSchemeExtensionDedekind_of_dvr
#print axioms ZInQ.Contrib.GroupLawNeron.dvr_of_dedekind

private theorem closedDVRLocal : NeronExt.NeronDVRLocal :=
  NeronExt.dvrLocal_of_extension
    (ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind
      NeronDVR.neronSchemeExtensionDedekind_proof)

example : NeronExt.NeronDVRLocal := closedDVRLocal

#print axioms closedDVRLocal
