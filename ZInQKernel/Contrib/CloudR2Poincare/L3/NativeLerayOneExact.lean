import ZInQKernel.Contrib.CloudR2Poincare.L3.NativeLerayOneEdge
import ZInQKernel.Contrib.CloudR2Poincare.L3.NativeLerayOneAdjunction
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.SectionsBaseChange

/-!
# Exactness of the actual degree-one Leray segment

Pushforward preserves kernels, not arbitrary short exact sequences. Its zeroth
cycles are identified with f_*F by the actual augmentation. The boundary
connecting map and native H.mapOfAdjunction compatibility identify the
inflation with the inclusion into the source cycle quotient.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits Abelian

namespace ZInQ.Contrib.CloudR2Poincare.L3.LerayOneConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u
variable {X Y : Scheme.{u}}

/-- The actual kernel-preservation comparison for the cycles of a pushed complex. -/
def pushedCyclesIso (f : X ⟶ Y) (K : CochainComplex X.Modules ℕ) (j : ℕ) :
    (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj K).cycles j ≅
      (Scheme.Modules.pushforward f).obj (K.cycles j) :=
  IsLimit.conePointUniqueUpToIso
    ((((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj K).cyclesIsKernel
      j (j + 1) (by simp))
    (KernelFork.mapIsLimit _ (K.cyclesIsKernel j (j + 1) (by simp))
      (Scheme.Modules.pushforward f))

@[reassoc]
theorem pushedCyclesIso_hom_iCycles (f : X ⟶ Y) (K : CochainComplex X.Modules ℕ) (j : ℕ) :
    (pushedCyclesIso f K j).hom ≫ (Scheme.Modules.pushforward f).map (K.iCycles j) =
      (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj K).iCycles j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

@[reassoc]
theorem pushedCyclesIso_inv_iCycles (f : X ⟶ Y) (K : CochainComplex X.Modules ℕ) (j : ℕ) :
    (pushedCyclesIso f K j).inv ≫
      (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj K).iCycles j =
        (Scheme.Modules.pushforward f).map (K.iCycles j) := by
  rw [← cancel_epi (pushedCyclesIso f K j).hom]
  simp [Category.assoc, pushedCyclesIso_hom_iCycles]

/-- The comparison preserves the actual incoming differential to cycles. -/
theorem pushed_map_toCycles (f : X ⟶ Y) (K : CochainComplex X.Modules ℕ) :
    (Scheme.Modules.pushforward f).map (K.toCycles 0 1) =
      (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj K).toCycles 0 1 ≫
        (pushedCyclesIso f K 1).hom := by
  rw [← cancel_mono ((Scheme.Modules.pushforward f).map (K.iCycles 1))]
  rw [← Functor.map_comp, HomologicalComplex.toCycles_i, Category.assoc,
    pushedCyclesIso_hom_iCycles, HomologicalComplex.toCycles_i]
  rfl

/-- The actual augmentation identifies zeroth pushed cycles with f_*F. -/
def pushedSourceIso (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    (Scheme.Modules.pushforward f).obj F ≅ (pushedComplex f F I).cycles 0 :=
  (Scheme.Modules.pushforward f).mapIso I.isoCyclesZero ≪≫
    (pushedCyclesIso f I.cocomplex 0).symm

@[reassoc]
theorem pushedSourceIso_hom_iCycles (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    (pushedSourceIso f F I).hom ≫ (pushedComplex f F I).iCycles 0 =
      (Scheme.Modules.pushforward f).map (I.ι.f 0) := by
  simp only [pushedSourceIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, pushedCyclesIso_inv_iCycles]
  simpa only [Functor.mapIso_hom, Functor.map_comp] using
    (Scheme.Modules.pushforward f).congr_map (I.isoCyclesZero_hom_iCycles)

@[reassoc]
theorem pushedSourceIso_hom_cyclesIso (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    (pushedSourceIso f F I).hom ≫ (pushedCyclesIso f I.cocomplex 0).hom =
      (Scheme.Modules.pushforward f).map I.isoCyclesZero.hom := by
  simp [pushedSourceIso, Category.assoc]

/-- The actual cycle/boundary short complex maps to the pushed source-cycle sequence. -/
def boundariesAdjunctionMap (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    Scheme.Modules.cyclesBoundariesShortComplex (pushedComplex f F I) 0 ⟶
      (I.cocomplex.cyclesShortComplex 0 1).map (Scheme.Modules.pushforward f) where
  τ₁ := (pushedCyclesIso f I.cocomplex 0).hom
  τ₂ := 𝟙 _
  τ₃ := Limits.image.ι ((pushedComplex f F I).toCycles 0 1) ≫
    (pushedCyclesIso f I.cocomplex 1).hom
  comm₁₂ := by
    simpa [Scheme.Modules.cyclesBoundariesShortComplex,
      HomologicalComplex.cyclesShortComplex] using pushedCyclesIso_hom_iCycles f I.cocomplex 0
  comm₂₃ := by
    simp only [ShortComplex.map_g, HomologicalComplex.cyclesShortComplex_g, Category.id_comp,
      Scheme.Modules.cyclesBoundariesShortComplex, ← Category.assoc, Limits.image.fac]
    exact pushed_map_toCycles f I.cocomplex

/-- The boundary connecting class on global sections. -/
def boundaryClass (L : CochainComplex Y.Modules ℕ) :
    Γ(Limits.image (L.toCycles 0 1), ⊤) →+ (L.cycles 0).H 1 :=
  (Scheme.Modules.H.δ (Scheme.Modules.shortExact_cyclesBoundariesShortComplex L 0) 0).comp
    (Scheme.Modules.H.zeroLinearEquiv (Limits.image (L.toCycles 0 1))).symm.toAddEquiv.toAddMonoidHom

/-- Every target zeroth-cycle H¹ class has this boundary representative, since L⁰
is Γ-acyclic. No assumption on H¹(Z⁰) itself is used. -/
theorem boundaryClass_surjective (L : CochainComplex Y.Modules ℕ)
    (hL : Subsingleton ((L.X 0).H 1)) : Function.Surjective (boundaryClass L) := by
  haveI : Subsingleton ((Scheme.Modules.cyclesBoundariesShortComplex L 0).X₂.H 1) := hL
  exact (Scheme.Modules.H.surjective_δ_zero
    (Scheme.Modules.shortExact_cyclesBoundariesShortComplex L 0)).comp
      (Scheme.Modules.H.zeroLinearEquiv (Limits.image (L.toCycles 0 1))).symm.surjective

/-- On a native source acyclic resolution, the degree-one cycle comparison sends
its actual connecting class to the corresponding cycle class. -/
theorem sourceCycles_delta (F : X.Modules) (I : InjectiveResolution F)
    (z : Γ(I.cocomplex.cycles 1, ⊤)) :
    Scheme.Modules.H.cyclesZeroSuccAddEquiv I.cocomplex I.cocomplex_exactAt_succ
      (fun _ m => Scheme.Modules.subsingleton_H_of_injective _ m) 0
      (Scheme.Modules.H.δ
        (Scheme.Modules.shortExact_cyclesShortComplex I.cocomplex I.cocomplex_exactAt_succ 0)
        0 ((Scheme.Modules.H.zeroLinearEquiv (I.cocomplex.cycles 1)).symm z)) =
      QuotientAddGroup.mk z := by
  change Scheme.Modules.H.cyclesOneAddEquiv I.cocomplex I.cocomplex_exactAt_succ
      (fun _ m => Scheme.Modules.subsingleton_H_of_injective _ m) 0
      (Scheme.Modules.H.map (𝟙 (I.cocomplex.cycles 0)) 1
        (Scheme.Modules.H.cyclesδZero I.cocomplex I.cocomplex_exactAt_succ 0 z)) = _
  rw [Scheme.Modules.H.map_id_apply]
  exact Scheme.Modules.H.cyclesOneAddEquiv_cyclesδZero (K := I.cocomplex)
    I.cocomplex_exactAt_succ (fun _ m => Scheme.Modules.subsingleton_H_of_injective _ m) 0 z

/-- The already-defined Ext adjunction inflation commutes with the native
augmentation identification; this is a map equality, not a rank argument. -/
theorem inflation_cycles (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F)
    (z : ((pushedComplex f F I).cycles 0).H 1) :
    Scheme.Modules.H.map I.isoCyclesZero.hom 1
        (Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1
          (Scheme.Modules.H.map (pushedSourceIso f F I).inv 1 z)) =
      Scheme.Modules.H.mapOfAdjunction f (boundariesAdjunctionMap f F I).τ₁ 1 z := by
  have h := Scheme.Modules.H.mapOfAdjunction_naturality f
    (𝟙 ((Scheme.Modules.pushforward f).obj F))
    (boundariesAdjunctionMap f F I).τ₁
    (pushedSourceIso f F I).hom I.isoCyclesZero.hom (by
      simpa [boundariesAdjunctionMap] using pushedSourceIso_hom_cyclesIso f F I)
    1 (Scheme.Modules.H.map (pushedSourceIso f F I).inv 1 z)
  have hh : Scheme.Modules.H.map (pushedSourceIso f F I).hom 1
      (Scheme.Modules.H.map (pushedSourceIso f F I).inv 1 z) = z :=
    (Scheme.Modules.H.mapAddEquiv (pushedSourceIso f F I) 1).apply_symm_apply z
  change Scheme.Modules.H.mapOfAdjunction f (boundariesAdjunctionMap f F I).τ₁ 1
    (Scheme.Modules.H.map (pushedSourceIso f F I).hom 1
      (Scheme.Modules.H.map (pushedSourceIso f F I).inv 1 z)) = _ at h
  rw [hh] at h
  exact h.symm

/-- The native boundary map has precisely the previous-term sections as its kernel. -/
theorem boundaryClass_ker (L : CochainComplex Y.Modules ℕ) :
    (boundaryClass L).ker = ((factorThruImage (L.toCycles 0 1)).app ⊤).hom.range := by
  ext b
  change Scheme.Modules.H.δ (Scheme.Modules.shortExact_cyclesBoundariesShortComplex L 0) 0
    ((Scheme.Modules.H.zeroLinearEquiv _).symm b) = 0 ↔ _
  rw [← AddMonoidHom.mem_ker, Scheme.Modules.H.ker_δ_eq_range_map_g]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Scheme.Modules.H.zeroLinearEquiv _ x, ?_⟩
    have he := Scheme.Modules.H.zeroLinearEquiv_map (factorThruImage (L.toCycles 0 1)) x
    change Scheme.Modules.H.zeroLinearEquiv _
      (Scheme.Modules.H.map (Scheme.Modules.cyclesBoundariesShortComplex L 0).g 0 x) = _ at he
    rw [hx, LinearEquiv.apply_symm_apply] at he
    exact he.symm
  · rintro ⟨x, rfl⟩
    refine ⟨(Scheme.Modules.H.zeroLinearEquiv _).symm x,
      (Scheme.Modules.H.zeroLinearEquiv _).injective ?_⟩
    rw [Scheme.Modules.H.zeroLinearEquiv_map]
    erw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl

/-- The actual pushed-cycle comparison preserves cycle classes through the
kernel-preservation isomorphism, not a chosen rank isomorphism. -/
theorem pushedCyclesEquiv_mk (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F)
    (z : Γ((pushedComplex f F I).cycles 1, ⊤)) :
    pushedCyclesEquiv f F I
        (QuotientAddGroup.mk ((pushedCyclesIso f I.cocomplex 1).hom.app ⊤ z)) =
      QuotientAddGroup.mk z := by
  apply (Scheme.Modules.cyclesQuotientAddEquiv (pushedComplex f F I) 0).injective
  calc
    Scheme.Modules.cyclesQuotientAddEquiv (pushedComplex f F I) 0
        (pushedCyclesEquiv f F I
          (QuotientAddGroup.mk ((pushedCyclesIso f I.cocomplex 1).hom.app ⊤ z))) =
      Scheme.Modules.cyclesQuotientAddEquiv I.cocomplex 0
        (QuotientAddGroup.mk ((pushedCyclesIso f I.cocomplex 1).hom.app ⊤ z)) := by
          dsimp only [pushedCyclesEquiv]
          simp only [AddEquiv.trans_apply, AddEquiv.refl_apply]
          exact (Scheme.Modules.cyclesQuotientAddEquiv (pushedComplex f F I) 0).apply_symm_apply _
    _ = Scheme.Modules.cyclesQuotientAddEquiv (pushedComplex f F I) 0
        (QuotientAddGroup.mk z) := by
      change QuotientAddGroup.mk
          (⟨((I.cocomplex.iCycles 1).app ⊤)
            (((pushedCyclesIso f I.cocomplex 1).hom.app ⊤) z), _⟩ :
              Scheme.Modules.sectionsCycles I.cocomplex 0) =
        QuotientAddGroup.mk
          (⟨(((pushedComplex f F I).iCycles 1).app ⊤) z, _⟩ :
            Scheme.Modules.sectionsCycles (pushedComplex f F I) 0)
      congr 1
      apply Subtype.ext
      change (((pushedCyclesIso f I.cocomplex 1).hom ≫
        (Scheme.Modules.pushforward f).map (I.cocomplex.iCycles 1)).app ⊤) z = _
      rw [pushedCyclesIso_hom_iCycles]
      rfl

/-- Evaluate the actual boundary representative by its single connecting-map stage. -/
theorem boundaryClass_apply (L : CochainComplex Y.Modules ℕ)
    (b : Γ(Limits.image (L.toCycles 0 1), ⊤)) :
    boundaryClass L b =
      Scheme.Modules.H.δ (Scheme.Modules.shortExact_cyclesBoundariesShortComplex L 0) 0
        ((Scheme.Modules.H.zeroLinearEquiv (Limits.image (L.toCycles 0 1))).symm b) := by
  unfold boundaryClass
  rfl

/-- The original adjunction map in degree zero is evaluated separately by the
native H-zero map, explicit coefficient composition and the presheaf identity. -/
theorem boundariesAdjunction_zero (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F)
    (b : Γ(Limits.image ((pushedComplex f F I).toCycles 0 1), ⊤)) :
    Scheme.Modules.H.zeroLinearEquiv (I.cocomplex.cycles 1)
      (Scheme.Modules.H.mapOfAdjunction f (boundariesAdjunctionMap f F I).τ₃ 0
        ((Scheme.Modules.H.zeroLinearEquiv
          (Limits.image ((pushedComplex f F I).toCycles 0 1))).symm b)) =
      (pushedCyclesIso f I.cocomplex 1).hom.app ⊤
        ((Limits.image.ι ((pushedComplex f F I).toCycles 0 1)).app ⊤ b) := by
  let L := pushedComplex f F I
  let u : Γ(I.cocomplex.cycles 1, ⊤) :=
    (pushedCyclesIso f I.cocomplex 1).hom.app ⊤
      ((Limits.image.ι (L.toCycles 0 1)).app ⊤ b)
  have h := Scheme.Modules.H.mapOfAdjunction_zeroLinearEquiv f
    (Limits.image (L.toCycles 0 1)) (I.cocomplex.cycles 1)
    (Limits.image.ι (L.toCycles 0 1) ≫ (pushedCyclesIso f I.cocomplex 1).hom)
    ((Scheme.Modules.H.zeroLinearEquiv (Limits.image (L.toCycles 0 1))).symm b)
  rw [LinearEquiv.apply_symm_apply] at h
  have htop : (I.cocomplex.cycles 1).presheaf.map
      (homOfLE (by simp : ⊤ ≤ f ⁻¹ᵁ ⊤)).op
      (((Limits.image.ι (L.toCycles 0 1) ≫
        (pushedCyclesIso f I.cocomplex 1).hom).app ⊤) b) = u := by
    let v : (I.cocomplex.cycles 1).presheaf.obj (Opposite.op (f ⁻¹ᵁ ⊤)) :=
      ((Limits.image.ι (L.toCycles 0 1) ≫
        (pushedCyclesIso f I.cocomplex 1).hom).app ⊤) b
    have hid := ConcreteCategory.congr_hom
      (CategoryTheory.Functor.map_id (I.cocomplex.cycles 1).presheaf
        (Opposite.op (f ⁻¹ᵁ ⊤))) v
    have valueEquation : v = u := by
      simp only [v, u, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
      rfl
    exact hid.trans valueEquation
  exact h.trans htop

/-- The degree-one connecting-map stage is checked independently of the
quotient/inverse equivalence stages. No caller-supplied compatibility is used. -/
theorem boundaryInflation_source_delta (f : X ⟶ Y) (F : X.Modules)
    (I : InjectiveResolution F)
    (b : Γ(Limits.image ((pushedComplex f F I).toCycles 0 1), ⊤)) :
    Scheme.Modules.H.map I.isoCyclesZero.hom 1
      (Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1
        (Scheme.Modules.H.map (pushedSourceIso f F I).inv 1
          (boundaryClass (pushedComplex f F I) b))) =
      Scheme.Modules.H.δ
        (Scheme.Modules.shortExact_cyclesShortComplex I.cocomplex I.cocomplex_exactAt_succ 0) 0
        ((Scheme.Modules.H.zeroLinearEquiv (I.cocomplex.cycles 1)).symm
          ((pushedCyclesIso f I.cocomplex 1).hom.app ⊤
            ((Limits.image.ι ((pushedComplex f F I).toCycles 0 1)).app ⊤ b))) := by
  rw [inflation_cycles, boundaryClass_apply]
  rw [mapOfAdjunction_delta f
    (Scheme.Modules.shortExact_cyclesBoundariesShortComplex (pushedComplex f F I) 0)
    (Scheme.Modules.shortExact_cyclesShortComplex I.cocomplex I.cocomplex_exactAt_succ 0)
    (boundariesAdjunctionMap f F I) 0]
  congr 1
  apply (Scheme.Modules.H.zeroLinearEquiv (I.cocomplex.cycles 1)).injective
  rw [boundariesAdjunction_zero, LinearEquiv.apply_symm_apply]

/-- The actual inflation, expressed on every native boundary representative, is
literally the inclusion of B¹ into the source cycle quotient. -/
theorem inflation_boundaryClass (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F)
    (b : Γ(Limits.image ((pushedComplex f F I).toCycles 0 1), ⊤)) :
    sourcePushedCyclesEquiv f F I
        (Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1
          (Scheme.Modules.H.map (pushedSourceIso f F I).inv 1
            (boundaryClass (pushedComplex f F I) b))) =
      QuotientAddGroup.mk
        ((Limits.image.ι ((pushedComplex f F I).toCycles 0 1)).app ⊤ b) := by
  simp only [sourcePushedCyclesEquiv, AddEquiv.trans_apply, sourceCyclesEquiv_apply]
  rw [boundaryInflation_source_delta, sourceCycles_delta]
  exact pushedCyclesEquiv_mk f F I _

/-- The actual boundary representatives of H¹(f_*F). -/
def inflationRepresentative (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    Γ(Limits.image ((pushedComplex f F I).toCycles 0 1), ⊤) →+
      ((Scheme.Modules.pushforward f).obj F).H 1 :=
  (Scheme.Modules.H.map (pushedSourceIso f F I).inv 1).comp
    (boundaryClass (pushedComplex f F I))

/-- Every inflation-domain class is represented by the actual B¹ sections. -/
theorem inflationRepresentative_surjective (f : X ⟶ Y) (F : X.Modules)
    (I : InjectiveResolution F) : Function.Surjective (inflationRepresentative f F I) := by
  intro z
  have hL : Subsingleton (((pushedComplex f F I).X 0).H 1) :=
    Scheme.Modules.subsingleton_H_pushforward_of_injective f (I.cocomplex.X 0) 0
  obtain ⟨b, hb⟩ := boundaryClass_surjective (pushedComplex f F I) hL
    (Scheme.Modules.H.map (pushedSourceIso f F I).hom 1 z)
  refine ⟨b, ?_⟩
  change Scheme.Modules.H.map (pushedSourceIso f F I).inv 1
    (boundaryClass (pushedComplex f F I) b) = z
  rw [hb, ← Scheme.Modules.H.map_comp_apply, Iso.hom_inv_id,
    Scheme.Modules.H.map_id_apply]

/-- Injectivity is checked as its own named proof, not as a local subterm in
one large exactness proof. All representative/acyclicity inputs are intrinsic. -/
theorem resolutionInflation_injective (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    Function.Injective
      (Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1) := by
  let L := pushedComplex f F I
  let alpha := Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1
  let e := sourcePushedCyclesEquiv f F I
  let inc := Limits.image.ι (L.toCycles 0 1)
  have hrep := inflationRepresentative_surjective f F I
  apply (injective_iff_map_eq_zero alpha).2
  intro x hx
  obtain ⟨b, rfl⟩ := hrep x
  have hm : (QuotientAddGroup.mk (inc.app ⊤ b) : CyclesQuotient L) = 0 := by
    rw [← inflation_boundaryClass f F I b]
    change e (alpha (inflationRepresentative f F I b)) = 0
    rw [hx, map_zero]
  have hbmem : inc.app ⊤ b ∈ ((L.toCycles 0 1).app ⊤).hom.range :=
    (QuotientAddGroup.eq_zero_iff _).mp hm
  obtain ⟨t, ht⟩ := hbmem
  have hb : b ∈ ((factorThruImage (L.toCycles 0 1)).app ⊤).hom.range := by
    refine ⟨t, Scheme.Modules.injective_app_of_mono inc ?_⟩
    change ((factorThruImage (L.toCycles 0 1) ≫ inc).app ⊤) t = inc.app ⊤ b
    rw [Limits.image.fac]
    exact ht
  have hbker : b ∈ (boundaryClass L).ker := by
    rw [boundaryClass_ker]
    exact hb
  have hbzero := AddMonoidHom.mem_ker.mp hbker
  change Scheme.Modules.H.map (pushedSourceIso f F I).inv 1 (boundaryClass L b) = 0
  rw [hbzero, map_zero]

/-- The range/kernel assertion is independently factored, using the same
canonical arrow and native cycle quotient, never a replacement or rank map. -/
theorem resolutionInflation_range_eq_ker (f : X ⟶ Y) (F : X.Modules)
    (I : InjectiveResolution F) :
    (Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1).range =
      (resolutionEdge f F I).ker := by
  let L := pushedComplex f F I
  let e := sourcePushedCyclesEquiv f F I
  let inc := Limits.image.ι (L.toCycles 0 1)
  have hrep := inflationRepresentative_surjective f F I
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨b, rfl⟩ := hrep z
    rw [AddMonoidHom.mem_ker]
    apply (Scheme.Modules.H.zeroLinearEquiv
      ((Scheme.Modules.higherDirectImage f 1).obj F)).injective
    rw [resolutionEdge_zero, map_zero]
    simp only [inflationRepresentative, AddMonoidHom.comp_apply]
    rw [inflation_boundaryClass, quotientHomology_mk]
    have hpi : (L.homologyπ 1).app ⊤ (inc.app ⊤ b) = 0 := by
      have zeroComposite := (Scheme.Modules.boundariesHomologyShortComplex L 0).zero
      change inc ≫ L.homologyπ 1 = 0 at zeroComposite
      have sectionEquation := congrArg
        (fun phi : Limits.image (L.toCycles 0 1) ⟶ L.homology 1 => phi.app ⊤ b)
        zeroComposite
      rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at sectionEquation
      have zeroSection : (0 : Limits.image (L.toCycles 0 1) ⟶ L.homology 1).app ⊤ b = 0 := by
        rw [Scheme.Modules.Hom.zero_app]
        rfl
      exact sectionEquation.trans zeroSection
    rw [hpi, map_zero]
  · intro hx
    have hxzero := AddMonoidHom.mem_ker.mp hx
    have hzero := congrArg (Scheme.Modules.H.zeroLinearEquiv
      ((Scheme.Modules.higherDirectImage f 1).obj F)) hxzero
    rw [resolutionEdge_zero, map_zero] at hzero
    have hq : quotientHomology L (e x) = 0 := by
      apply Scheme.Modules.injective_app_of_mono
        (I.isoRightDerivedObj (Scheme.Modules.pushforward f) 1).inv
      simpa only [map_zero] using hzero
    obtain ⟨z, hz⟩ : ∃ z : Γ(L.cycles 1, ⊤),
        (QuotientAddGroup.mk z : CyclesQuotient L) = e x :=
      QuotientAddGroup.mk_surjective (e x)
    rw [← hz, quotientHomology_mk] at hq
    have hzmem : z ∈ (inc.app ⊤).hom.range := by
      have hm : z ∈ ((Scheme.Modules.boundariesHomologyShortComplex L 0).g.app ⊤).hom.ker := hq
      rw [← Scheme.Modules.range_app_f_eq_ker_app_g
        (Scheme.Modules.shortExact_boundariesHomologyShortComplex L 0)] at hm
      exact hm
    obtain ⟨b, hb⟩ := hzmem
    refine ⟨inflationRepresentative f F I b, e.injective ?_⟩
    change sourcePushedCyclesEquiv f F I
      (Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1
        (Scheme.Modules.H.map (pushedSourceIso f F I).inv 1 (boundaryClass L b))) = e x
    rw [inflation_boundaryClass, hb, hz]

/-- The actual low-degree segment is exact for each actual injective resolution. -/
theorem resolutionEdge_exact (f : X ⟶ Y) (F : X.Modules) (I : InjectiveResolution F) :
    Function.Injective
      (Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1) ∧
      (Scheme.Modules.H.mapOfAdjunction f (𝟙 ((Scheme.Modules.pushforward f).obj F)) 1).range =
        (resolutionEdge f F I).ker :=
  ⟨resolutionInflation_injective f F I, resolutionInflation_range_eq_ker f F I⟩

end ZInQ.Contrib.CloudR2Poincare.L3.LerayOneConstruction
