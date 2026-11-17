/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AlgebraicGeometry.ProjectiveSpace.Basic
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.GAGA.ProjectiveSpaceDefinition
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytification.SchemeAffine

/-!
# Projective space over `ℂ` as a scheme locally of finite type

`ComplexAnalytic.projectiveSpace n` is `ℙ(n; ℂ) = Proj ℂ[X₀, …, Xₙ]` (with `ℂ` lifted to
universe `u`), as an object of `ComplexAnalytic.SchemeLFTℂ.{u}`; its structure morphism is proper
(`ComplexAnalytic.isProper_projectiveSpace_hom`). The standard charts are morphisms
`ComplexAnalytic.projectiveSpaceChart i : affineSpace n ⟶ projectiveSpace n` over `ℂ` from affine
space `affineSpace n = Spec ℂ[Y₀, …, Yₙ₋₁]`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-- **Affine `n`-space over `ℂ`**, `Spec ℂ[Y₀, …, Yₙ₋₁]`, as a scheme locally of finite type. -/
noncomputable def affineSpace (n : ℕ) : SchemeLFTℂ.{u} :=
  SchemeLFTℂ.spec (CommRingCat.ofHom (MvPolynomial.C (σ := Fin n) (R := ULift.{u} ℂ)))
    (RingHom.finiteType_algebraMap.mpr inferInstance)

@[simp]
lemma affineSpace_obj_hom (n : ℕ) :
    (affineSpace.{u} n).obj.hom = Spec.map (CommRingCat.ofHom MvPolynomial.C) :=
  rfl

-- projectiveSpace and its original object-component lemmas are imported from
-- ProjectiveSpaceDefinition, moved unchanged after the explicit type/API rename.

instance isProper_projectiveSpace_hom (n : ℕ) : IsProper (projectiveSpace.{u} n).obj.hom :=
  inferInstanceAs (IsProper (CloudB3W17bOkaProjectiveSpace.toSpec n _))

/-- The **standard chart** `i` of `ℙⁿ`, `𝔸ⁿ ⟶ ℙⁿ` over `ℂ`, an open immersion onto
`ProjectiveSpace.U n _ i = D₊(Xᵢ)`. -/
noncomputable def projectiveSpaceChart {n : ℕ} (i : Fin (n + 1)) :
    affineSpace.{u} n ⟶ projectiveSpace.{u} n :=
  ObjectProperty.homMk (Over.homMk (CloudB3W17bOkaProjectiveSpace.chart i) (CloudB3W17bOkaProjectiveSpace.chart_toSpec i))

@[simp]
lemma projectiveSpaceChart_hom_left {n : ℕ} (i : Fin (n + 1)) :
    (projectiveSpaceChart.{u} i).hom.left = CloudB3W17bOkaProjectiveSpace.chart i :=
  rfl

instance {n : ℕ} (i : Fin (n + 1)) : IsOpenImmersion (projectiveSpaceChart.{u} i).hom.left :=
  inferInstanceAs (IsOpenImmersion (CloudB3W17bOkaProjectiveSpace.chart i))

end ComplexAnalytic
