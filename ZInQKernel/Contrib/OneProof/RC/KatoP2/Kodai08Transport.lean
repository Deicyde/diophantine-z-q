import ZInQKernel.Contrib.OneProof.RC.KatoP2.Kodai08Support
import ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiLambdaTorsion
import ZInQKernel.Contrib.OneProof.RC.KatoP2.Comparison

/-! The use of Kato 1999 at (K15). Global torsion and comparison of the
localized kernels are separate glue steps. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2.Checked

open PrintsArith

/-- Finite generation (Kato 1999 p. 316) and the structure of Λ promote
the printed primewise torsion to global torsion. This is GLUE, separate
from the transcription of Theorem 0.8. -/
theorem kodai08_globalTorsion {NK : ℕ} {full : KodaiFullOpen NK}
    (hfinite : Module.Finite KatoLambda2 full.iw.H2) (h : Kodai08AwayTwo full) :
    Module.IsTorsion KatoLambda2 full.iw.H2 := by
  letI := hfinite
  obtain ⟨a, ha⟩ := exists_regular_annihilator_of_kodaiLocal (M := full.iw.H2)
    (fun p _ hp h2 => (h p hp h2).1)
  exact fun {x} => ⟨a, ha x⟩

/-- Transport (K15) to the retained `j_*` complex. Its length inequality
uses the all-prime kernel and the unchanged comparison of evaluation
ideals. Its global torsion uses the separate finite generation argument. -/
theorem retainedK15_of_kodai08 {es : EulerSystemData ℤ_[2]} {NK : ℕ}
    {full : KodaiFullOpen NK} {retained : KodaiJStar} {t : KodaiTower es NK full.iw}
    (C₁ : KatoH1Comparison es NK full.iw retained.iw t)
    (C₂ : KatoOddSupportCone full retained)
    (hz : C₁.res retained.iw.zIw = full.iw.zIw)
    (hfinite : Module.Finite KatoLambda2 full.iw.H2) (h08 : Kodai08AwayTwo full) :
    RetainedK15 retained.iw := by
  have hfull := kodai08_globalTorsion hfinite h08
  have hker : Module.IsTorsion KatoLambda2 (LinearMap.ker C₂.res) := by
    apply isTorsion_of_kodaiLocal
    intro p _ hp h2 y
    let i := LocalizedModule.map p.primeCompl (LinearMap.ker C₂.res).subtype
    have hi := LocalizedModule.map_injective p.primeCompl (LinearMap.ker C₂.res).subtype
      (LinearMap.ker C₂.res).subtype_injective
    have hy : localMap p C₂.res (i y) = 0 := by
      induction y using LocalizedModule.induction_on with
      | _ x s => simp [i, localMap, LocalizedModule.map_mk, LinearMap.mem_ker.mp x.property]
    have hy' : y = 0 := hi ((C₂.inj_away p hp h2) (hy.trans (map_zero _).symm) |>.trans
      (map_zero _).symm)
    exact ⟨1, by rw [hy', smul_zero]⟩
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := hfull (x := C₂.res x)
    have hax : C₂.res ((a : KatoLambda2) • x) = 0 := by
      rw [map_smul]
      exact ha
    obtain ⟨b, hb⟩ := hker (x := ⟨_, hax⟩)
    exact ⟨b * a, by simpa [Submonoid.smul_def, mul_smul] using congrArg Subtype.val hb⟩
  · intro p _ hp h2
    let e := C₂.toComparison.onKernel p hp h2
    have hJ := map_J_le_of_extend C₁ hz p hp h2
    exact (Module.length_le_of_injective e.toLinearMap e.injective).trans
      ((h08 p hp h2).2.trans
        (Module.length_le_of_surjective (Submodule.factor hJ) (Submodule.factor_surjective hJ)))

end ZInQ.Manuscript.RC.KatoP2.Checked
