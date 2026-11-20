import ZInQKernel.Contrib.RC53Assist.EvenUpper.Faithful
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LevelGood
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaLevel

/-! The least matching cusp form level is the level of the genuine newform.
The existing local coefficient comparison excludes good primes from this level. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenUpperCubes

open ZInQ.Manuscript Wiring PrintsAnalytic EvenUpperText
open ZInQ.Contrib.CloudB3RC53 HeckeRing.GL2 UpperHalfPlane

theorem fixedLevel_eq_newformLevel {ℓ N : ℕ} [NeZero N] {f : Newform N 2}
    (hf : IsNewformOf (Ecurve ℓ) f) : N₀ ℓ = N := by
  have hmem : f.toCuspForm ∈ cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ) := by
    have h := f.mem_charSpace
    rwa [hf.1] at h
  have hN : CST.HasCuspFormAtLevel (Ecurve ℓ) N := by
    refine ⟨TauCeti.cuspFormCharSpaceOneEquiv N 2 ⟨f.toCuspForm, hmem⟩, fun n hn => ?_⟩
    rw [TauCeti.coe_cuspFormCharSpaceOneEquiv_apply]
    exact hf.2 n hn
  let s := {n : ℕ | 0 < n ∧ CST.HasCuspFormAtLevel (Ecurve ℓ) n}
  have hNs : N ∈ s := ⟨NeZero.pos N, hN⟩
  have hs := Nat.sInf_mem (show s.Nonempty from ⟨N, hNs⟩)
  exact le_antisymm (Nat.sInf_le hNs)
    (Nat.le_of_dvd hs.1 (GenusOdd.dvd_of_hasCuspFormAtLevel hf hs.1 hs.2))

theorem curveLevel_and_support {ℓ : ℕ} {W : WData ℓ} (hS : SupportSpec W)
    (hℓ : 0 < ℓ) (hM : ModularNewform) (hH : HasseConvergence) :
    CurveLevel ℓ ∧ ∀ p : ℕ, p.Prime → p ∣ N₀ ℓ → p ∈ W.S := by
  let : (Ecurve ℓ).IsElliptic := PoleRC.curve_isElliptic (by exact_mod_cast hℓ.ne')
  obtain ⟨N, _, f, hf⟩ := hM (Ecurve ℓ) inferInstance
  obtain ⟨w, _, hw⟩ := rootNumberAt_of_isNewformOf hH hf
  have he := fixedLevel_eq_newformLevel hf
  refine ⟨⟨w, he ▸ hw⟩, fun p hp hpN => ?_⟩
  rw [he] at hpN
  have hbad := Nonvanishing.bad_curve_mem (m := (ℓ : ℤ)) hS.2.1 hS.2.2.1
    (fun p hp hd => hS.2.2.2 p hp (Int.natCast_dvd_natCast.mp hd))
  apply hbad p hp
  simpa only [Ecurve, Int.cast_natCast] using
    (GlueSweep.Ana.levelSupport_of_modularNewform hM _ inferInstance _ _ hw p hp hpN)

end ZInQ.Manuscript.RC.EvenUpperCubes
