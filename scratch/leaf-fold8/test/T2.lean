import ZInQKernel.OneProof.H.TailX
namespace HDec
namespace HSyn
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem r22_lf8 (h : _root_.ZInQ.LeafPush2.R22_Pazuki) : ZInQ.LeafPush2.R22_Pazuki := by
  intro K _ _ A hA x hx
  rw [G0HeightCopies.heightCopiesAgree K A] at hx
  exact h K A hA x hx

theorem r18_lf8 (h : _root_.ZInQ.LeafPush2.R18_Javanpeykar) : ZInQ.LeafPush2.R18_Javanpeykar := by
  intro K _ _ X hX _ P₀ J aj hJac g hg hg1 t ht d hd hd0
  haveI : _root_.LeafModCurves.IsCurve X := ⟨hX.proper, hX.smooth, hX.geomConnected⟩
  rw [G0HeightCopies.heightCopiesAgree K J]
  exact h K X P₀ J aj ⟨hJac.base, hJac.univ⟩ g hg hg1 t ht d hd hd0

end HSyn
end HDec
