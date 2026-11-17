import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-!
# The unconditional canonical degree-one Leray edge

Only the actual native injective resolution, pushed-forward complex, homology
projection and native cohomology/cycles quotient are used. This map does not
assume R⁰ f_* F = 0 and is not obtained by choosing an equivalence from ranks.
Existing native providers and the earlier certified edge-Leray sources are
read-only. Source credit: the native resolution/cycles maps are those in W07
Jacobian-Challenge c4254cce15b3e284a0a3ae1d73936f2ee195d272 (Apache-2.0).
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits Abelian

namespace ZInQ.Contrib.CloudR2Poincare.L3.LerayOneConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u
variable {X Y : Scheme.{u}}

/-- Actual cycle sections modulo actual preceding-term sections, in degree one. -/
abbrev CyclesQuotient (L : CochainComplex Y.Modules ℕ) :=
  Γ(L.cycles 1, ⊤) ⧸ ((L.toCycles 0 1).app ⊤).hom.range

/-- The actual homology projection descends without any homology-vanishing premise. -/
def quotientHomology (L : CochainComplex Y.Modules ℕ) :
    CyclesQuotient L →+ Γ(L.homology 1, ⊤) :=
  QuotientAddGroup.lift _ ((L.homologyπ 1).app ⊤).hom (by
    rintro _ ⟨x, rfl⟩
    change ((L.homologyπ 1).app ⊤) (((L.toCycles 0 1).app ⊤) x) = 0
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      HomologicalComplex.toCycles_comp_homologyπ]
    rfl)

@[simp]
theorem quotientHomology_mk (L : CochainComplex Y.Modules ℕ)
    (z : Γ(L.cycles 1, ⊤)) :
    quotientHomology L (QuotientAddGroup.mk z) = (L.homologyπ 1).app ⊤ z := rfl

/-- Coefficient-chain-map naturality of the actual quotient homology map. -/
theorem quotientHomology_naturality {L L' : CochainComplex Y.Modules ℕ}
    (χ : L ⟶ L') (z : CyclesQuotient L) :
    quotientHomology L'
        (QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap χ 1).app ⊤).hom
          (Scheme.Modules.range_app_toCycles_le_comap χ 0) z) =
      ((HomologicalComplex.homologyMap χ 1).app ⊤) (quotientHomology L z) := by
  induction z using QuotientAddGroup.induction_on with | H z => ?_
  rw [QuotientAddGroup.map_mk, quotientHomology_mk, quotientHomology_mk]
  change ((HomologicalComplex.cyclesMap χ 1 ≫ L'.homologyπ 1).app ⊤) z =
    ((L.homologyπ 1 ≫ HomologicalComplex.homologyMap χ 1).app ⊤) z
  rw [HomologicalComplex.homologyπ_naturality]

/-- The native source degree-one cohomology as its actual resolution cycle quotient. -/
def sourceCyclesEquiv (F : X.Modules) (I : InjectiveResolution F) :
    F.H 1 ≃+ CyclesQuotient I.cocomplex :=
  (Scheme.Modules.H.mapAddEquiv I.isoCyclesZero 1).trans
    (Scheme.Modules.H.cyclesZeroSuccAddEquiv I.cocomplex I.cocomplex_exactAt_succ
      (fun _ m => Scheme.Modules.subsingleton_H_of_injective _ m) 0)

/-- Evaluate only the forward arrow of a native cohomology isomorphism. -/
theorem cohomologyIso_apply {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N)
    (n : ℕ) (z : M.H n) :
    Scheme.Modules.H.mapAddEquiv e n z = Scheme.Modules.H.map e.hom n z := rfl

/-- One explicit evaluation stage of the fixed source/cycle comparison. -/
theorem sourceCyclesEquiv_apply (F : X.Modules) (I : InjectiveResolution F) (z : F.H 1) :
    sourceCyclesEquiv F I z =
      (Scheme.Modules.H.cyclesZeroSuccAddEquiv I.cocomplex I.cocomplex_exactAt_succ
        (fun _ m => Scheme.Modules.subsingleton_H_of_injective _ m) 0)
        (Scheme.Modules.H.map I.isoCyclesZero.hom 1 z) := by
  simp only [sourceCyclesEquiv, AddEquiv.trans_apply, cohomologyIso_apply]

/-- The pushed-forward complex on the actual target. -/
abbrev pushedComplex (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    CochainComplex Y.Modules ℕ :=
  ((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj I.cocomplex

/-- The equality of global sections of I and f_* I, expressed through the actual
native cycle/coboundary quotients. No exactness of f_* is used here. -/
def pushedCyclesEquiv (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    CyclesQuotient I.cocomplex ≃+ CyclesQuotient (pushedComplex f F I) :=
  (Scheme.Modules.cyclesQuotientAddEquiv I.cocomplex 0).trans
    ((AddEquiv.refl (Scheme.Modules.sectionsCycles I.cocomplex 0 ⧸
      Scheme.Modules.sectionsBoundaries I.cocomplex 0)).trans
      (Scheme.Modules.cyclesQuotientAddEquiv (pushedComplex f F I) 0).symm)

/-- The canonical source-to-pushed-cycle quotient comparison. -/
def sourcePushedCyclesEquiv (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    F.H 1 ≃+ CyclesQuotient (pushedComplex f F I) :=
  (sourceCyclesEquiv F I).trans (pushedCyclesEquiv f F I)

/-- The edge map for a specified actual injective resolution. -/
def resolutionEdge (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    F.H 1 →+ ((Scheme.Modules.higherDirectImage f 1).obj F).H 0 :=
  (((Scheme.Modules.H.zeroLinearEquiv
      ((Scheme.Modules.higherDirectImage f 1).obj F)).symm.toAddEquiv.toAddMonoidHom).comp
    (Scheme.Modules.appTopAddEquiv
      (I.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).symm).toAddMonoidHom).comp
      ((quotientHomology (pushedComplex f F I)).comp
        (sourcePushedCyclesEquiv f F I).toAddMonoidHom)

/-- Evaluate one native section isomorphism by its actual hom component. -/
theorem sectionsIso_apply {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N)
    (z : Γ(M, ⊤)) : Scheme.Modules.appTopAddEquiv e z = e.hom.app ⊤ z := rfl

/-- The four fixed edge stages evaluated by named additive/section equations.
This avoids unfolding the entire equivalence tower in the main naturality proof. -/
theorem resolutionEdge_apply (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F)
    (z : F.H 1) :
    resolutionEdge f F I z =
      (Scheme.Modules.H.zeroLinearEquiv ((Scheme.Modules.higherDirectImage f 1).obj F)).symm
        ((I.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).inv.app ⊤
          (quotientHomology (pushedComplex f F I) (sourcePushedCyclesEquiv f F I z))) := by
  simp only [resolutionEdge, AddMonoidHom.comp_apply]
  exact congrArg
    (fun w => (Scheme.Modules.H.zeroLinearEquiv
      ((Scheme.Modules.higherDirectImage f 1).obj F)).symm w)
    (sectionsIso_apply (I.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).symm _)

/-- The source comparison is natural through the native comparison of resolutions. -/
theorem sourceCyclesEquiv_naturality {F G : X.Modules} (φ : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (z : F.H 1) :
    sourceCyclesEquiv G J (Scheme.Modules.H.map φ 1 z) =
      QuotientAddGroup.map _ _
        ((HomologicalComplex.cyclesMap (InjectiveResolution.desc φ J I) 1).app ⊤).hom
        (Scheme.Modules.range_app_toCycles_le_comap (InjectiveResolution.desc φ J I) 0)
        (sourceCyclesEquiv F I z) := by
  let ψ := InjectiveResolution.desc φ J I
  have hzero : I.isoCyclesZero.hom ≫ HomologicalComplex.cyclesMap ψ 0 =
      φ ≫ J.isoCyclesZero.hom := by
    rw [← cancel_mono J.isoCyclesZero.inv, Category.assoc,
      ← InjectiveResolution.isoCyclesZero_inv_naturality φ J I]
    simp
  have hz : Scheme.Modules.H.map (HomologicalComplex.cyclesMap ψ 0) 1
      (Scheme.Modules.H.map I.isoCyclesZero.hom 1 z) =
      Scheme.Modules.H.map J.isoCyclesZero.hom 1 (Scheme.Modules.H.map φ 1 z) := by
    rw [← Scheme.Modules.H.map_comp_apply, ← Scheme.Modules.H.map_comp_apply, hzero]
  rw [sourceCyclesEquiv_apply, sourceCyclesEquiv_apply, ← hz]
  exact Scheme.Modules.H.cyclesZeroSuccAddEquiv_naturality ψ
    I.cocomplex_exactAt_succ (fun _ m => Scheme.Modules.subsingleton_H_of_injective _ m)
    J.cocomplex_exactAt_succ (fun _ m => Scheme.Modules.subsingleton_H_of_injective _ m) 0 _

/-- The source/pushed comparison has this literal native cocycle quotient value. -/
theorem sourcePushedCyclesEquiv_cyclesQuotient (f : X ⟶ Y) (F : X.Modules)
    (I : InjectiveResolution F) (z : F.H 1) :
    Scheme.Modules.cyclesQuotientAddEquiv (pushedComplex f F I) 0
        (sourcePushedCyclesEquiv f F I z) =
      Scheme.Modules.cyclesQuotientAddEquiv I.cocomplex 0 (sourceCyclesEquiv F I z) := by
  dsimp only [sourcePushedCyclesEquiv, pushedCyclesEquiv]
  simp only [AddEquiv.trans_apply, AddEquiv.refl_apply]
  exact (Scheme.Modules.cyclesQuotientAddEquiv (pushedComplex f F I) 0).apply_symm_apply _

/-- Evaluate the existing pushforward map on the underlying global-section
value. The section type is fixed explicitly before the top-open reduction. -/
theorem pushforwardSectionMap_top_apply (f : X ⟶ Y) {M N : X.Modules}
    (phi : M ⟶ N) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pushforward f).map phi).app ⊤
        (show Γ((Scheme.Modules.pushforward f).obj M, ⊤) from s) =
      phi.app ⊤ s := by
  rw [Scheme.Modules.pushforward_map_app]
  rfl

/-- The global-section cocycle map of pushforward is the original map. The
only open comparison is handled explicitly, rather than by a whole-complex rfl. -/
theorem sectionsCyclesMap_pushforward {K K' : CochainComplex X.Modules ℕ}
    (f : X ⟶ Y) (psi : K ⟶ K') (n : ℕ) (z : Scheme.Modules.sectionsCycles K n) :
    Scheme.Modules.sectionsCyclesMap
        (((Scheme.Modules.pushforward f).mapHomologicalComplex _).map psi) n z =
      Scheme.Modules.sectionsCyclesMap psi n z := by
  apply Subtype.ext
  exact pushforwardSectionMap_top_apply f (psi.f (n + 1)) z.1

/-- The same explicit global-section identification descends to the actual
cocycle/coboundary quotient. No quotient map is selected by dimensions. -/
theorem sectionsCycleQuotientMap_pushforward {K K' : CochainComplex X.Modules ℕ}
    (f : X ⟶ Y) (psi : K ⟶ K') (n : ℕ)
    (z : Scheme.Modules.sectionsCycles K n ⧸ Scheme.Modules.sectionsBoundaries K n) :
    QuotientAddGroup.map _ _
        (Scheme.Modules.sectionsCyclesMap
          (((Scheme.Modules.pushforward f).mapHomologicalComplex _).map psi) n)
        (Scheme.Modules.sectionsBoundaries_le_comap
          (((Scheme.Modules.pushforward f).mapHomologicalComplex _).map psi) n) z =
      QuotientAddGroup.map _ _ (Scheme.Modules.sectionsCyclesMap psi n)
        (Scheme.Modules.sectionsBoundaries_le_comap psi n) z := by
  induction z using QuotientAddGroup.induction_on with | H z => ?_
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, sectionsCyclesMap_pushforward]
  rfl

/-- Naturality of the actual source/pushforward cycle quotient comparison. -/
theorem sourcePushedCyclesEquiv_naturality {F G : X.Modules} (f : X ⟶ Y) (φ : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (z : F.H 1) :
    sourcePushedCyclesEquiv f G J (Scheme.Modules.H.map φ 1 z) =
      QuotientAddGroup.map _ _
        ((HomologicalComplex.cyclesMap
          (((Scheme.Modules.pushforward f).mapHomologicalComplex _).map
            (InjectiveResolution.desc φ J I)) 1).app ⊤).hom
        (Scheme.Modules.range_app_toCycles_le_comap
          (((Scheme.Modules.pushforward f).mapHomologicalComplex _).map
            (InjectiveResolution.desc φ J I)) 0)
        (sourcePushedCyclesEquiv f F I z) := by
  let ψ := InjectiveResolution.desc φ J I
  let χ := ((Scheme.Modules.pushforward f).mapHomologicalComplex _).map ψ
  apply (Scheme.Modules.cyclesQuotientAddEquiv (pushedComplex f G J) 0).injective
  rw [Scheme.Modules.cyclesQuotientAddEquiv_naturality,
    sourcePushedCyclesEquiv_cyclesQuotient, sourcePushedCyclesEquiv_cyclesQuotient,
    sourceCyclesEquiv_naturality, Scheme.Modules.cyclesQuotientAddEquiv_naturality]
  exact (sectionsCycleQuotientMap_pushforward f ψ 0 _).symm

/-- The edge is literally the transported native homology projection on sections. -/
theorem resolutionEdge_zero (f : X ⟶ Y) (F : X.Modules)
    (I : InjectiveResolution F) (z : F.H 1) :
    Scheme.Modules.H.zeroLinearEquiv ((Scheme.Modules.higherDirectImage f 1).obj F)
        (resolutionEdge f F I z) =
      ((I.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).inv.app ⊤)
        (quotientHomology (pushedComplex f F I) (sourcePushedCyclesEquiv f F I z)) := by
  rw [resolutionEdge_apply, LinearEquiv.apply_symm_apply]

/-- Naturality of the edge for the actual specified resolutions. -/
theorem resolutionEdge_naturality {F G : X.Modules} (f : X ⟶ Y) (φ : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G) (z : F.H 1) :
    resolutionEdge f G J (Scheme.Modules.H.map φ 1 z) =
      Scheme.Modules.H.map ((Scheme.Modules.higherDirectImage f 1).map φ) 0
        (resolutionEdge f F I z) := by
  let ψ := InjectiveResolution.desc φ J I
  let χ := ((Scheme.Modules.pushforward f).mapHomologicalComplex _).map ψ
  apply (Scheme.Modules.H.zeroLinearEquiv
    ((Scheme.Modules.higherDirectImage f 1).obj G)).injective
  rw [resolutionEdge_zero, Scheme.Modules.H.zeroLinearEquiv_map,
    resolutionEdge_zero, sourcePushedCyclesEquiv_naturality, quotientHomology_naturality]
  have h : (Scheme.Modules.higherDirectImage f 1).map φ ≫
      (J.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).hom =
      (I.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).hom ≫
        HomologicalComplex.homologyMap χ 1 :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality φ I J ψ
      (InjectiveResolution.desc_commutes_zero φ J I) (Scheme.Modules.pushforward f) 1
  have hinv : HomologicalComplex.homologyMap χ 1 ≫
      (J.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).inv =
      (I.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).inv ≫
        (Scheme.Modules.higherDirectImage f 1).map φ := by
    rw [← cancel_epi (I.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).hom]
    simpa [Category.assoc] using congrArg
      (fun t => t ≫ (J.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).inv) h.symm
  change ((HomologicalComplex.homologyMap χ 1 ≫
      (J.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).inv).app ⊤) _ =
    (((I.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).inv ≫
      (Scheme.Modules.higherDirectImage f 1).map φ).app ⊤) _
  rw [hinv]
  rfl

end ZInQ.Contrib.CloudR2Poincare.L3.LerayOneConstruction

namespace ZInQ.Contrib.CloudR2Poincare.L3

universe u

/-- The canonical low-degree Leray edge; no lower vanishing is assumed. -/
def nativeLerayOneEdge {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) :
    F.H 1 →+ ((Scheme.Modules.higherDirectImage f 1).obj F).H 0 :=
  LerayOneConstruction.resolutionEdge f F (injectiveResolution F)

/-- Coefficient naturality of the same canonical edge. -/
theorem nativeLerayOneEdge_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G : X.Modules} (φ : F ⟶ G) (z : F.H 1) :
    nativeLerayOneEdge f G (Scheme.Modules.H.map φ 1 z) =
      Scheme.Modules.H.map ((Scheme.Modules.higherDirectImage f 1).map φ) 0
        (nativeLerayOneEdge f F z) :=
  LerayOneConstruction.resolutionEdge_naturality f φ _ _ z

/-- Semilinearity along the actual map on global functions. -/
theorem nativeLerayOneEdge_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (a : Γ(Y, ⊤)) (z : F.H 1) :
    nativeLerayOneEdge f F (f.appTop a • z) = a • nativeLerayOneEdge f F z := by
  change nativeLerayOneEdge f F (Scheme.Modules.H.map (F.smulHom (f.appTop a)) 1 z) =
    Scheme.Modules.H.map (((Scheme.Modules.higherDirectImage f 1).obj F).smulHom a) 0 _
  rw [nativeLerayOneEdge_naturality, Scheme.Modules.higherDirectImage_map_smulHom]

end ZInQ.Contrib.CloudR2Poincare.L3
