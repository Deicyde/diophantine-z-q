import TailN
import ZInQKernel.HDecomp.Textbook.T10Etale
import ZInQKernel.Contrib.HomUnify.Corr
import ZInQKernel.HDecomp.ModCurves.C9
namespace HDec
namespace HSyn
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

set_option maxHeartbeats 8000000 in
theorem eigenformTwist_ofK5 (h : _root_.PkgI4.EigenformTwist) : EigenformTwist := h

set_option maxHeartbeats 8000000 in
theorem t10_ofK5 (h : _root_.T10Etale.T10_TateDuality) : T10Etale.T10_TateDuality :=
  fun K _ A ℓ _ hℓ => h K (toAbVarK4 A) ℓ hℓ

set_option maxHeartbeats 8000000 in
theorem homLatticeCorr_ofK5 (h : _root_.ZInQ.HomUnify.HomLatticeCorr) : HomUnify.HomLatticeCorr :=
  ⟨fun K _ A B σ g k ΛA ΛB ΦA ΦB hA hB hUA hUB f =>
      h.1 K (toAbVarK4 A) (toAbVarK4 B) σ g k ΛA ΛB ΦA ΦB hA hB hUA hUB f,
   fun A B g k ΛA ΛB ΦA ΦB hA hB hUA hUB M hM =>
      h.2 (toAbVarK4 A) (toAbVarK4 B) g k ΛA ΛB ΦA ΦB hA hB hUA hUB M hM⟩

end HSyn
end HDec
