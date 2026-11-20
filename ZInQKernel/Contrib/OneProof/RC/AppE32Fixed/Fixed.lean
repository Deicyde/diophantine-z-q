import ZInQKernel.Contrib.OneProof.RC.Even.KatoBridge
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Serre
import ZInQKernel.Contrib.RC53Assist.EvenUpper.Faithful

/-! The remaining arithmetic input for (3.2), instantiated at the newform
level and normalization used by the genuine even sources. -/

namespace ZInQ.Manuscript.RC.AppE32Fixed

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53
open EvenUpperText PrintsArith Wiring

/-- App E at the curve and level of the even upper bound, conditional on
the retained construction in tex 6846–7787. This is the input to the two
existing upper estimate consumers on the genuine source family. -/
theorem appEOutputs_of_kato_fixed (hK : KatoZetaLeaf) (hcm : CMjInteger)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (C : Even.CentralNormalization (Ecurve ℓ))
    (hE : @Even.AppEFromKato (Ecurve ℓ)
      (PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')) (N₀ ℓ) C) :
    Even.AppEOutputs (Ecurve ℓ) (N₀ ℓ) C := by
  have : (Ecurve ℓ).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  have hCM : HasNoCM (Ecurve ℓ) := curve_hasNoCM hcm (by exact_mod_cast hℓ.ne')
  exact hE fun Sbad h2 hgood => hK (Ecurve ℓ) hCM Sbad h2 hgood

/-- (3.2) for the normalization `C` of the sources, at exactly `N₀ ℓ`.
The second conclusion identifies the same scalar input on the original
data `W` using only equality of central-value functions. -/
theorem evenScalar32_of_kato_fixed (hK : KatoZetaLeaf) (hcm : CMjInteger)
    (hB : PoleS12.BCDTThmA) {ℓ : ℕ} (hℓ : 0 < ℓ) {W : WData ℓ}
    (C : Even.CentralNormalization (Ecurve ℓ)) (hCW : C.Lstar = W.Lstar)
    (hE : @Even.AppEFromKato (Ecurve ℓ)
      (PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')) (N₀ ℓ) C) :
    Even.EvenScalar32 (Ecurve ℓ) (N₀ ℓ) C ∧ Scalar32 W := by
  have h := Even.evenScalar32_of_appE (level_pos_of_bcdt hB hℓ).ne'
    (appEOutputs_of_kato_fixed hK hcm hℓ C hE)
  exact ⟨h, (scalar32_iff_even C hCW).mpr h⟩


end ZInQ.Manuscript.RC.AppE32Fixed
