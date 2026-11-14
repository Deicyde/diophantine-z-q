import ZInQKernel.Contrib.FrobChain.LinkedFrob

/-!
# Frob chain, 10: the closed reductions

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task frobchain-contrib,
2026-11-13). New code (not generated).

The frob chain (tasks frob-trace, mul-rigidity, alg-frob-red, afr-absfrob with frob-contrib's
adoption `ZInQKernel/Contrib/AbsFrob/`, frob-pieces, linked-frob) proves, over the kernel, three
glue statements from the same four inputs:
* `FrobPiecesNeron.AbVarSpreadsOut` — neron-lg's glue N1-g1 (spreading out of an abelian variety
  over a number field to an abelian scheme away from finitely many primes);
* `FrobPiecesNeron.ProperSmoothGenConnected` — frob-pieces' leaf candidate (Zariski's
  connectedness theorem for proper smooth morphisms with connected generic fibre);
* the kernel's textbook leaves I2-Red `PkgI2.ReductionTorsionBijective` (T4) and I2-NMP
  `PkgI2.NeronMappingAbelianScheme` (T3), `ZInQKernel/HDecomp/Objects.lean`.
`G14Bridge.TateBridge35` needs in addition the kernel's leaf I3.M0 `PkgI3.TateModuleFree`.

The statements `FrobTrace.AlgFrobRed`, `G14Bridge.TateBridge35`, `UnramTate.LinkedFrob` are the
owners' texts (frob-trace, g14-trace, linked-tate), copied verbatim in the generated modules of this
directory; none of them is defined by the kernel. The hypotheses I2-Red, I2-NMP and I3.M0 are the
kernel's own definitions (no copy is involved). Two statements of the chain exist in two copies;
the copies are equal by `Iff.rfl` below.
-/

namespace ZInQ.Contrib.FrobChain

/-- **`FrobTrace.AlgFrobRed` (frob-trace's AV-side glue) from N1-g1, Zariski's connectedness
theorem, I2-Red and I2-NMP.** frob-pieces' `algFrobRed_of_neron_nmp`, whose proof uses
alg-frob-red's reduction, afr-absfrob's `FExtendGen` from I2-NMP, frob-contrib's `absFrob` and
frob-pieces' `smoothGeomConnIntegral` (Tau Ceti). -/
theorem algFrobRed_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    FrobTrace.AlgFrobRed :=
  FrobPiecesGood.algFrobRed_of_neron_nmp hsp hc hRed hN

/-- **`G14Bridge.TateBridge35` (g14-trace's linked Tate bridge at `ℓ = 3, 5`) from I3.M0, N1-g1,
Zariski's connectedness theorem, I2-Red and I2-NMP.** frob-trace's
`tateBridge35_of_algFrobRed` applied to `algFrobRed_of_neron_nmp`. -/
theorem tateBridge35_of_neron_nmp (hT : PkgI3.TateModuleFree)
    (hsp : FrobPiecesNeron.AbVarSpreadsOut) (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    G14Bridge.TateBridge35 :=
  FrobTrace.tateBridge35_of_algFrobRed hT (algFrobRed_of_neron_nmp hsp hc hRed hN)

/-- **`UnramTate.LinkedFrob` (linked-tate's glue: the Frobenius trace link for the canonical
operators) from N1-g1, Zariski's connectedness theorem, I2-Red and I2-NMP.** linked-frob's
`linkedFrob_of_algFrobRed` applied to `algFrobRed_of_neron_nmp`. -/
theorem linkedFrob_of_neron_nmp (hsp : FrobPiecesNeron.AbVarSpreadsOut)
    (hc : FrobPiecesNeron.ProperSmoothGenConnected)
    (hRed : PkgI2.ReductionTorsionBijective.{0}) (hN : PkgI2.NeronMappingAbelianScheme.{0}) :
    UnramTate.LinkedFrob :=
  LinkedFrobRed.linkedFrob_of_algFrobRed (algFrobRed_of_neron_nmp hsp hc hRed hN)

/-! ## Copies -/

/-- g14-trace's two texts of the Frobenius trace link: `G14Bridge.FrobTraceLink` (its copy over
`GaloisCopy.Vb`, used by `TateBridge35`) and `G14Trace.FrobTraceLink` (used by `LinkedFrob`) are the
same Prop. -/
theorem frobTraceLink_copy_iff {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5) (G0ModField.GaloisCopy.Vb A 5))
    (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3) (G0ModField.GaloisCopy.Vb A 3)) :
    G14Bridge.FrobTraceLink A Tm5 Tm3 ↔ G14Trace.FrobTraceLink A Tm5 Tm3 :=
  Iff.rfl

/-- alg-frob-red's `SmoothGeomConnIntegral` (consumed by the chain) is frob-pieces' Contrib
statement `FrobPieces.SmoothGeomConnIntegral`. -/
theorem smoothGeomConnIntegral_copy_iff :
    AlgFrobRedRed.SmoothGeomConnIntegral ↔ FrobPieces.SmoothGeomConnIntegral :=
  Iff.rfl

/-- The kernel's object-bridge forms of the two kernel leaves I2-Red and I2-NMP used as
hypotheses (`ZInQKernel/HDecomp/Objects.lean`, where the same `Iff.rfl` is proved). -/
theorem kernel_leaves_iff :
    (_root_.ObjBridge.ReductionTorsionBijective ↔ PkgI2.ReductionTorsionBijective.{0}) ∧
    (_root_.ObjBridge.NeronMappingAbelianScheme ↔ PkgI2.NeronMappingAbelianScheme.{0}) :=
  ⟨Iff.rfl, Iff.rfl⟩

end ZInQ.Contrib.FrobChain
