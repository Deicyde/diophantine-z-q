import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Cd
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Heegner

/-!
# gz-heegner: the `C_d` form of `HeegnerPointRational`

Task gz-heegner (2026-11-15). Report: `docs/research/gz-heegner.md`.

gz-hl3's `C_d` split (`GrossZagierHeegner/Cd.lean`) uses `HeegnerPointRationalCd`, the restriction of
`HeegnerPointRational` to the curves `C_d`. It follows from the same two printed leaves.

No `sorry`, no `axiom`.
-/

namespace ZInQ.GZHeegner

/-- **`HeegnerPointRationalCd` from `ShimuraMainCM` and `X0ModuliGaloisMero`.** -/
theorem heegnerPointRationalCd_of_printed (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisMero) :
    ZInQ.GZHL3.HeegnerPointRationalCd :=
  ZInQ.GZHL3.heegnerPointRationalCd_of (heegnerPointRational_of_printed hCM hX)

/-- **gz-hl3's `C_d` form with `HeegnerPointRationalCd` replaced.** -/
theorem grossZagierHeegnerCd_of_printed (hU : ZInQ.GZHL3.WeierstrassUniformization)
    (hES : ZInQ.GZHL3.ShimuraCMParamCd) (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd)
    (hGC : ZInQ.GZHL3.GrossConjugationCd) (hCM : T5Glue.ShimuraMainCM) (hX : X0ModuliGaloisMero) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  ZInQ.GZHL3.grossZagierHeegnerCd_of_leaves hU hES (heegnerPointRationalCd_of_printed hCM hX) hGZ hGC

end ZInQ.GZHeegner
