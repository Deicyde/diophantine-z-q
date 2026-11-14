/-! ## leaf-fold5: the chain's textbook fields from the kernel's av-b1, curves-g and neron-c theorems

Each theorem below has as its type the chain's own Prop (the field of `OpenTextbookLeaves4`) and is proved by
applying a kernel theorem (`ZInQKernel/Contrib/AVB1`, `CurvesG`, `NeronC`, imported), whose hypotheses are the
kernel's own leaf Props over the kernel's objects (`ZInQKernel/HDecomp/Objects.lean`). The chain's `PkgI3.AbVar`
is a copy of the kernel's; `HSyn.toAbVarK4` and `HSyn.ofAbVarK4` (leaf-fold4) pass between the two with the
same scheme, and Lean accepts the remaining identifications (`Hom`, `T`, `V`, `dim`, `baseChange`, ...) by
unfolding, as it did for leaf-fold4's T26. -/

noncomputable section

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ### av-b1: T6, T7 from their algebraically closed forms; T8 from Poincaré's complement form -/

/-- **T6 from `HomFreeFiniteAlgClosed`** (Mumford §19 Thm 3 over an algebraically closed field; the kernel's
`ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed`). -/
theorem t6_of_algClosed5 (h : _root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) : PkgI3.HomFreeFinite :=
  fun k _ A B => _root_.ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed h k (toAbVarK4 A) (toAbVarK4 B)

/-- **T7 from `CharPolyIndepOfEllAlgClosed`** (Mumford §19 Thm 4 over an algebraically closed field; the
kernel's `ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed`). -/
theorem t7_of_algClosed5 (h : _root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed) :
    PkgI3.CharPolyIndepOfEll :=
  fun k _ A φ => _root_.ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed h k (toAbVarK4 A) φ

/-- **T8 from `PoincareComplement` and `SimpleImageIsogeny`** (the kernel's
`ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage`; the complement `Z` is the kernel's abelian
variety, read back with `ofAbVarK4`). -/
theorem t8_of_simpleImage5 (hP : _root_.ZInQ.Contrib.AVB1.PoincareComplement)
    (hSI : _root_.ZInQ.Contrib.AVB1.SimpleImageIsogeny) : PkgI3.PoincareReducibility := by
  intro k _ _ A J hA f hf
  obtain ⟨Z, g, hg⟩ := _root_.ZInQ.Contrib.AVB1.poincareReducibility_of_simpleImage hP hSI k
    (toAbVarK4 A) (toAbVarK4 J) hA f hf
  exact ⟨ofAbVarK4 Z, g, hg⟩

/-! ### curves-g: T38 with its rational-point clause proved; T34 from its two published halves -/

/-- **T38 from three textbook facts** (the kernel's `ZInQ.Contrib.CurvesG.curveOfFunctionFieldQ_of_split`:
the rational-point clause is proved by the valuative criterion; (A) normal models of function fields, (B) normal
curves over `ℚ` are smooth, (C) geometric connectedness from the constant field). `X1Belyi.CurveOfFunctionFieldQ`
is over Mathlib definitions only. -/
theorem t38_of_split5 (hA : _root_.ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ)
    (hB : _root_.ZInQ.Contrib.CurvesG.NormalCurveSmoothQ)
    (hC : _root_.ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ) : X1Belyi.CurveOfFunctionFieldQ :=
  _root_.ZInQ.Contrib.CurvesG.curveOfFunctionFieldQ_of_split hA hB hC

/-- The chain's Jacobian property gives the kernel's, for the kernel's copy of the abelian variety. -/
theorem isJacobianK_of5 {X : Over (Spec (CommRingCat.of ℚ))}
    {P₀ : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ X} {J : PkgI3.AbVar ℚ} {aj : X ⟶ J.X}
    (h : LeafModCurves.IsJacobian X P₀ J aj) :
    _root_.LeafModCurves.IsJacobian X P₀ (toAbVarK4 J) aj :=
  ⟨h.base, fun A f hf => h.univ (ofAbVarK4 A) f hf⟩

/-- **T34 from its two halves** (the kernel's `ZInQ.Contrib.CurvesG.dimJ1Genus_of_split`: `dim Jac X = genus`
for curves over `ℚ`, and the genus of `K_N` is the genus of `Γ₁(N)`). -/
theorem t34_of_split5 (h1 : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus)
    (h2 : _root_.ZInQ.Contrib.CurvesG.GenusX1Field) : LeafModCurves.DimJ1Genus := by
  rintro N J hN ⟨X, P₀, aj, hX, hJ⟩
  exact _root_.ZInQ.Contrib.CurvesG.dimJ1Genus_of_split h1 h2 N (toAbVarK4 J) hN
    ⟨X, P₀, aj, hX, isJacobianK_of5 hJ⟩

/-! ### neron-c: T3 from its surjective half; T41 from the scheme-level Néron extension property -/

/-- **T3 from `NeronMappingAbelianSchemeSurj`** (BLR §1.2 Prop. 8, surjective half; the injective half is
the kernel's proved `ZInQ.Contrib.NeronC.neronMappingAbelianScheme_injective`). The two `IsAbelianScheme`
classes are copies; only the instances are transported. -/
theorem t3_of_surj5 (h : _root_.ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{0}) :
    PkgI2.NeronMappingAbelianScheme.{0} := by
  intro K _ O _ 𝒜 ℬ h𝒜 hℬ
  haveI : _root_.PkgI2.IsAbelianScheme 𝒜 := ⟨h𝒜.proper, h𝒜.smooth, h𝒜.geomConnected⟩
  haveI : _root_.PkgI2.IsAbelianScheme ℬ := ⟨hℬ.proper, hℬ.smooth, hℬ.geomConnected⟩
  exact _root_.ZInQ.Contrib.NeronC.neronMappingAbelianScheme_of_surj h K O 𝒜 ℬ

/-- **T41 from `NeronSchemeExtensionExists`** (BLR §1.4 Thm 3 at the level of schemes; the group law and the
uniqueness of extensions are the kernel's proved `ZInQ.Contrib.NeronC.neronModelExists_of_extension`). The
kernel's Néron model, a `GroupModel` of `toAbVarK4 A`, is read as the chain's `GroupModel` of `A` (same fields). -/
theorem t41_of_extension5 (h : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists) :
    ZInQ.H5Neron.NeronModelExists := by
  intro K _ A L _ _ _
  obtain ⟨𝒩, h𝒩⟩ := _root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension h K (toAbVarK4 A) L
  exact ⟨⟨𝒩.G, 𝒩.gen, 𝒩.gen_hom⟩, h𝒩⟩

end HSyn

end
