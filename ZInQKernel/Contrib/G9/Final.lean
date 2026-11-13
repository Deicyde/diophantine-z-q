import ZInQKernel.Contrib.G9.Reduction
import ZInQKernel.Contrib.G9.G9

/-!
# G9: `G9Glue` from two bridge statements

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

The embedding `F' ⊆ B_dR` (`G9Bridge.FieldEmbBdR`) is proved by the second run of this task
(`iotaDR`, `bdrAct_iotaDR` in `G9.lean`: Hensel's lemma in `B_dR^+` through bdr-kertheta's
`θ⁺ : B_dR^+ → ℂ_p`, `KerTheta.lean`, `HenselEmb.lean`, `BdREmb.lean`). Hence

`g9Glue_of_localModel : G9Bridge.LocalModel → G9Bridge.R10Weights → G9Glue`

with the standard axioms only. The two remaining hypotheses are findings F2 (base change of
`A/K` to a local field with its Tate module) and F1 (Hodge–Tate multiplicities outside `{0, −1}`
vanish, a clause of the published R10 missing from its Lean form).
-/

namespace ZInQ.Contrib.G9

open PkgI4 G0Galois

theorem fieldEmbBdR : G9Bridge.FieldEmbBdR := by
  intro p _ F _ _ _ _
  exact ⟨iotaDR p F, bdrAct_iotaDR p F⟩

/-- **G9 (N5's Lemma `lem:de-rham-descent`, g0-mod-galois's `G9Glue`) from F2 and F1.** -/
theorem g9Glue_of_localModel (hLM : G9Bridge.LocalModel) (hW : G9Bridge.R10Weights) :
    G9Glue :=
  g9Glue_of_fieldEmb hLM hW fieldEmbBdR

end ZInQ.Contrib.G9

#print axioms ZInQ.Contrib.G9.fieldEmbBdR
#print axioms ZInQ.Contrib.G9.g9Glue_of_localModel
