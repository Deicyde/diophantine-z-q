/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.GAGA.SheafAnalytificationCoherent
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Geometry.RingedSpace.LocallyRingedSpace.RestrictModulesOver

/-!
# The analytification of a coherent sheaf is coherent

For `X` a scheme locally of finite type over `ℂ` and `F` a coherent sheaf of `𝒪_X`-modules, the
analytification `F^an` is a coherent sheaf of `𝒪_{X^an}`-modules. Every point of `X^an` has an open
neighbourhood on which `F^an` is coherent
(`ComplexAnalytic.exists_isCoherent_restrictModules_analytificationModules`), and coherence is local
for covers by open subspaces
(`AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_isCoherent_restrictModules`).
-/

universe u

namespace ComplexAnalytic

variable (X : SchemeLFTℂ.{u})

/-- **The analytification of a coherent sheaf is coherent.** -/
theorem isCoherent_analytificationModules
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] :
    ((analytificationModules X).obj F).IsCoherent :=
  AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_isCoherent_restrictModules _ _
    (exists_isCoherent_restrictModules_analytificationModules X F)

end ComplexAnalytic
