import ZInQKernel.Contrib.OneProof.FaltingsDVR.SemiabelianFiniteness
import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsAbelianImage
import ZInQKernel.Contrib.OneProof.FaltingsDVR.AbelianTorsionPoint

namespace ZInQ.FaltingsRestate

/-- Faltings' extension lemma for semiabelian schemes over a DVR. -/
theorem faltingsLemma1DVRPrint_proof : FaltingsLemma1DVRPrint :=
  faltingsLemma1DVRPrint_of_torsion_detects_finite_kernel
    (semiabelianTorsionDetectsFiniteKernel_of_abelian_image
      (finiteAbelianImageOfNoInvertibleTorsion (by
        intro k _ _ A n hd ht
        exact subsingleton_abelian_points_of_no_invertible_torsion A n hd ht)))

end ZInQ.FaltingsRestate
