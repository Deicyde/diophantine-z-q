import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Smooth.Basic
import ZInQKernel.Contrib.OneProof.HeightModelM2.GlobalSections

/-! # `e*Ω¹_{𝒢/S}` injects into its generic fibre

`HeightModelM2` takes the sections of `e*Ω¹` inside the generic fibre `𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]`,
i.e. it computes the sections of the image of `e*Ω¹` there. This file proves that `e*Ω¹` is that
image: its stalks inject into the generic fibre.

* `stalkOmega s = 𝒪_{S,s} ⊗_{𝒪_{𝒢,e(s)}} Ω[𝒪_{𝒢,e(s)}/𝓞_L]` is the stalk of `e*Ω¹_{𝒢/S}` at `s`
  (the stalk of `Ω_{𝒢/S}` at `e(s)` is `Ω[𝒪_{𝒢,e(s)}/𝒪_{S,s}] = Ω[𝒪_{𝒢,e(s)}/𝓞_L]`), and
  `stalkToGeneric s` its map to the generic fibre, `r ⊗ ω ↦ σ(r) ⊗ ω|_ξ`.
* `stalkToGeneric_injective`: the map is injective. On an affine chart `U = Spec A ∋ e(s)` of the
  smooth model, `A` is smooth over `𝓞_L`, so `Ω[A/𝓞_L]` is projective
  (`Algebra.FormallySmooth.projective_kaehlerDifferential`), hence flat; both local rings are
  localizations of `A`, hence formally étale over it, so both sides are base changes of
  `Ω[A/𝓞_L]` (`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`), and the map becomes
  `σ ⊗ Ω[A/𝓞_L]` with `σ : 𝒪_{S,s} → 𝒪_{S,η}` injective.
* `range_stalkToGeneric`: its image is the tree's `printedOmegaAt s`.
* `secOmega_existsUnique_germ`: a section over `V ∋ s` has a unique germ in the stalk at `s`.
* `mem_globalOmega_iff`: `t ∈ globalOmega` iff at every `s` it is the image of exactly one
  element of the stalk. So `globalOmega` is the module of compatible families of germs of
  `e*Ω¹`: the sections of `e*Ω¹` (not only of its image in the generic fibre), up to README
  reading 1. -/
open CategoryTheory AlgebraicGeometry Opposite
open NumberField KaehlerDifferential
open ZInQ.DefFaltings ZInQ.HeightDict ZInQ.HeightDict.Conormal ZInQ.HeightModelM2
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightModelM3

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]
variable (𝒢 : GroupModel A L)

attribute [local instance] Conormal.algXi Conormal.algEta Conormal.algXiEta

/-- The specialization `σ : 𝒪_{S,s} → 𝒪_{S,η}`. -/
noncomputable def sigma (s : Spec (CommRingCat.of (𝓞 L))) :
    (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s →+* Reta L :=
  ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalkSpecializes (genericPt_specializes s)).hom

theorem sigma_baseStalk (s : Spec (CommRingCat.of (𝓞 L))) (a : 𝓞 L) :
    sigma s (baseStalk s a) = baseStalk (genericPt L) a :=
  TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _

theorem sigma_injective (s : Spec (CommRingCat.of (𝓞 L))) : Function.Injective (sigma s) := by
  haveI : s.asIdeal.IsPrime := s.isPrime
  letI : Algebra (𝓞 L) ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) := (baseStalk s).toAlgebra
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) s.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (𝓞 L)) s
  haveI := isLocalization_Reta (L := L)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj s.asIdeal.primeCompl x
  have h1 := congrArg (sigma s) h
  rw [map_mul, hx, zero_mul] at h1
  have h2 : baseStalk (genericPt L) a = 0 := by
    rw [← sigma_baseStalk]; exact h1.symm
  have hinj : Function.Injective (baseStalk (genericPt L)) :=
    IsLocalization.injective (Reta L) (Ideal.primeCompl_le_nonZeroDivisors ⊥)
  have ha : a = 0 := hinj (by rw [h2, map_zero])
  have hu : IsUnit (baseStalk s t) := IsLocalization.map_units _ t
  apply hu.mul_left_eq_zero.mp
  change x * algebraMap (𝓞 L) _ t = 0
  rw [h, ha, map_zero]

/-! ## The stalk of `e*Ω¹` and its map to the generic fibre -/

section Stalk

variable (s : Spec (CommRingCat.of (𝓞 L)))

/-- `𝓞_L → 𝒪_{𝒢,e(s)}`. -/
noncomputable def algB : Algebra (𝓞 L) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) :=
  (stalkAlg 𝒢 (𝒢.unitSection s)).toAlgebra
/-- The unit section on stalks, `𝒪_{𝒢,e(s)} → 𝒪_{S,s}`. -/
noncomputable def algBO : Algebra (𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
    ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) := (unitStalk 𝒢 s).toAlgebra
/-- The specialization `𝒪_{𝒢,e(s)} → 𝒪_{𝒢,ξ}`. -/
noncomputable def algBXi : Algebra (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) 𝒢.genStalk :=
  (specMap 𝒢 s).toAlgebra
/-- `σ : 𝒪_{S,s} → 𝒪_{S,η}`. -/
noncomputable def algOEta : Algebra ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) (Reta L) :=
  (sigma s).toAlgebra
/-- `𝒪_{𝒢,e(s)} → 𝒪_{𝒢,ξ} → 𝒪_{S,η}`. -/
noncomputable def algBEta : Algebra (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) (Reta L) :=
  ((unitStalk 𝒢 (genericPt L)).comp (specMap 𝒢 s)).toAlgebra

attribute [local instance] algB algBO algBXi algOEta algBEta

theorem towerRBXi : IsScalarTower (𝓞 L) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) 𝒢.genStalk :=
  IsScalarTower.of_algebraMap_eq fun a => (specMap_stalkAlg 𝒢 s a).symm

theorem towerBXiEta :
    IsScalarTower (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) 𝒢.genStalk (Reta L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem unitStalk_specMap (b : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) :
    unitStalk 𝒢 (genericPt L) (specMap 𝒢 s b) = sigma s (unitStalk 𝒢 s b) := by
  have h := Scheme.Hom.stalkSpecializes_stalkMap 𝒢.unitSection (genericPt L) s
    (genericPt_specializes s)
  exact congrArg (fun f => f.hom b) h

theorem towerBOEta : IsScalarTower (𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
    ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) (Reta L) :=
  IsScalarTower.of_algebraMap_eq fun b => unitStalk_specMap 𝒢 s b

attribute [local instance] towerRBXi towerBXiEta towerBOEta

/-- **The stalk of `e*Ω¹_{𝒢/S}` at `s`**: `𝒪_{S,s} ⊗_{𝒪_{𝒢,e(s)}} Ω[𝒪_{𝒢,e(s)}/𝓞_L]` (the stalk
of `Ω_{𝒢/S}` at `e(s)` is `Ω[𝒪_{𝒢,e(s)}/𝒪_{S,s}] = Ω[𝒪_{𝒢,e(s)}/𝓞_L]`). -/
abbrev stalkOmega : Type :=
  ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) ⊗[𝒢.G.left.presheaf.stalk (𝒢.unitSection s)]
    Ω[𝒢.G.left.presheaf.stalk (𝒢.unitSection s)⁄𝓞 L]

/-- **The map from the stalk at `s` to the generic fibre** `𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]`:
`r ⊗ ω ↦ σ(r) ⊗ ω|_ξ`. -/
noncomputable def stalkToGeneric :
    stalkOmega 𝒢 s →+ (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L] :=
  (LinearMap.lTensor (Reta L)
      (mapBaseChange (𝓞 L) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
        𝒢.genStalk)).toAddMonoidHom.comp
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange
        (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) 𝒢.genStalk (Reta L) (Reta L)
        Ω[𝒢.G.left.presheaf.stalk (𝒢.unitSection s)⁄𝓞 L]).symm.toLinearMap.toAddMonoidHom.comp
      (LinearMap.rTensor Ω[𝒢.G.left.presheaf.stalk (𝒢.unitSection s)⁄𝓞 L]
        (IsScalarTower.toAlgHom (𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
          ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) (Reta L)).toLinearMap).toAddMonoidHom)

theorem stalkToGeneric_tmul (r : (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s)
    (ω : Ω[𝒢.G.left.presheaf.stalk (𝒢.unitSection s)⁄𝓞 L]) :
    stalkToGeneric 𝒢 s (r ⊗ₜ ω) =
      sigma s r ⊗ₜ map (𝓞 L) (𝓞 L) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) 𝒢.genStalk ω := by
  simp only [stalkToGeneric, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
    LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearMap.lTensor_tmul, mapBaseChange_tmul, one_smul]
  rfl

theorem stalkToGeneric_tmul_D (r : (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s)
    (b : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) :
    stalkToGeneric 𝒢 s (r ⊗ₜ D (𝓞 L) _ b) =
      sigma s r • ((1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s b)) := by
  rw [stalkToGeneric_tmul, map_D, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  rfl

theorem stalkToGeneric_smul (r' : (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s)
    (x : stalkOmega 𝒢 s) : stalkToGeneric 𝒢 s (r' • x) = sigma s r' • stalkToGeneric 𝒢 s x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul r ω =>
    rw [TensorProduct.smul_tmul', stalkToGeneric_tmul, stalkToGeneric_tmul, smul_eq_mul, map_mul,
      TensorProduct.smul_tmul', smul_eq_mul]

/-- **The image of the stalk at `s` is the tree's `printedOmegaAt s`.** -/
theorem range_stalkToGeneric :
    Set.range (stalkToGeneric 𝒢 s) = (printedOmegaAt 𝒢 s : Set _) := by
  haveI : s.asIdeal.IsPrime := s.isPrime
  letI : Algebra (𝓞 L) ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) := (baseStalk s).toAlgebra
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) s.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (𝓞 L)) s
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul r ω =>
      have hω : ω ∈ Submodule.span (𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
          (Set.range (D (𝓞 L) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)))) := by
        rw [span_range_derivation]; trivial
      induction hω using Submodule.span_induction generalizing r with
      | mem y hy =>
        obtain ⟨b, rfl⟩ := hy
        rw [stalkToGeneric_tmul_D]
        obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj s.asIdeal.primeCompl r
        have h' : sigma s r * baseStalk (genericPt L) t = baseStalk (genericPt L) a := by
          have := congrArg (sigma s) h
          rwa [map_mul, show algebraMap (𝓞 L) _ (t : 𝓞 L) = baseStalk s t from rfl,
            show algebraMap (𝓞 L) _ a = baseStalk s a from rfl, sigma_baseStalk,
            sigma_baseStalk] at this
        exact smul_mem_printedOmegaAt_of_mem 𝒢 s (Submodule.subset_span ⟨b, rfl⟩) a t t.2 _ h'
      | zero => rw [TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        rw [TensorProduct.tmul_add, map_add]; exact Submodule.add_mem _ (hx r) (hy r)
      | smul b x _ hx => rw [← TensorProduct.smul_tmul]; exact hx _
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      refine ⟨1 ⊗ₜ D (𝓞 L) _ b, ?_⟩
      rw [stalkToGeneric_tmul_D, map_one, one_smul]
    | zero => exact ⟨0, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
    | smul a x _ hx =>
      obtain ⟨x', rfl⟩ := hx
      refine ⟨baseStalk s a • x', ?_⟩
      rw [stalkToGeneric_smul, sigma_baseStalk]
      exact algebraMap_smul (Reta L) a _

/-- **`e*Ω¹_{𝒢/S}` injects into its generic fibre**: the map from the stalk at `s` to
`𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]` is injective. On an affine chart `U = Spec A ∋ e(s)` both stalks are
base changes of `Ω[A/𝓞_L]` (`A → 𝒪_{𝒢,e(s)}` and `A → 𝒪_{𝒢,ξ}` are localizations, hence formally
étale), and `Ω[A/𝓞_L]` is projective, hence flat, since `A` is smooth over `𝓞_L`; so the map is
`σ ⊗ Ω[A/𝓞_L]` with `σ : 𝒪_{S,s} → 𝒪_{S,η}` injective. -/
theorem stalkToGeneric_injective : Function.Injective (stalkToGeneric 𝒢 s) := by
  classical
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (x := 𝒢.unitSection s)
    (U := ⊤) trivial
  have hξU : 𝒢.genericUnit ∈ U := (𝒢.specializes_genericUnit s).mem_open U.isOpen hsU
  have hle : U ≤ 𝒢.G.hom ⁻¹ᵁ ⊤ := by simp
  let φ : CommRingCat.of (𝓞 L) ⟶ Γ(𝒢.G.left, U) :=
    (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv ≫ 𝒢.G.hom.appLE ⊤ U hle
  letI algRA : Algebra (𝓞 L) Γ(𝒢.G.left, U) := φ.hom.toAlgebra
  haveI hsm : Algebra.Smooth (𝓞 L) Γ(𝒢.G.left, U) := by
    have h1 := HasRingHomProperty.appLE @Smooth 𝒢.G.hom inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ hle
    have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv.hom :=
      RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact RingHom.Smooth.comp h2 h1
  letI algAB : Algebra Γ(𝒢.G.left, U) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) :=
    TopCat.Presheaf.algebra_section_stalk 𝒢.G.left.presheaf (⟨𝒢.unitSection s, hsU⟩ : U)
  letI algAX : Algebra Γ(𝒢.G.left, U) 𝒢.genStalk :=
    TopCat.Presheaf.algebra_section_stalk 𝒢.G.left.presheaf (⟨𝒢.genericUnit, hξU⟩ : U)
  haveI hlocB := hU.isLocalization_stalk ⟨𝒢.unitSection s, hsU⟩
  haveI hlocX := hU.isLocalization_stalk ⟨𝒢.genericUnit, hξU⟩
  haveI : Algebra.FormallyEtale Γ(𝒢.G.left, U) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨_, hsU⟩).asIdeal.primeCompl
  haveI : Algebra.FormallyEtale Γ(𝒢.G.left, U) 𝒢.genStalk :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨_, hξU⟩).asIdeal.primeCompl
  have hgerm : ∀ (x : 𝒢.G.left) (hx : x ∈ U) (a : 𝓞 L),
      (𝒢.G.left.presheaf.germ U x hx).hom (φ.hom a) = stalkAlg 𝒢 x a := by
    intro x hx a
    simp only [φ, stalkAlg, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appLE]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  haveI : IsScalarTower (𝓞 L) Γ(𝒢.G.left, U) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hgerm _ hsU a).symm
  haveI : IsScalarTower (𝓞 L) Γ(𝒢.G.left, U) 𝒢.genStalk :=
    IsScalarTower.of_algebraMap_eq fun a => (hgerm _ hξU a).symm
  have hspec : ∀ a : Γ(𝒢.G.left, U), specMap 𝒢 s ((𝒢.G.left.presheaf.germ U _ hsU).hom a) =
      (𝒢.G.left.presheaf.germ U _ hξU).hom a :=
    fun a => TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  haveI : IsScalarTower Γ(𝒢.G.left, U) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
      𝒢.genStalk := IsScalarTower.of_algebraMap_eq fun a => (hspec a).symm
  letI algAO : Algebra Γ(𝒢.G.left, U) ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) :=
    ((unitStalk 𝒢 s).comp (algebraMap Γ(𝒢.G.left, U)
      (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)))).toAlgebra
  haveI : IsScalarTower Γ(𝒢.G.left, U) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
      ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI algAE : Algebra Γ(𝒢.G.left, U) (Reta L) :=
    ((unitStalk 𝒢 (genericPt L)).comp (algebraMap Γ(𝒢.G.left, U) 𝒢.genStalk)).toAlgebra
  haveI : IsScalarTower Γ(𝒢.G.left, U) 𝒢.genStalk (Reta L) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower Γ(𝒢.G.left, U) ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s)
      (Reta L) := IsScalarTower.of_algebraMap_eq fun a => by
    show unitStalk 𝒢 (genericPt L) ((𝒢.G.left.presheaf.germ U _ hξU).hom a) =
      sigma s (unitStalk 𝒢 s ((𝒢.G.left.presheaf.germ U _ hsU).hom a))
    rw [← unitStalk_specMap, hspec]
  let E1 := tensorKaehlerEquivOfFormallyEtale (𝓞 L) Γ(𝒢.G.left, U)
    (𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
  let E2 := tensorKaehlerEquivOfFormallyEtale (𝓞 L) Γ(𝒢.G.left, U) 𝒢.genStalk
  let F' : stalkOmega 𝒢 s ≃+ ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) ⊗[Γ(𝒢.G.left, U)]
      Ω[Γ(𝒢.G.left, U)⁄𝓞 L] :=
    ((LinearEquiv.lTensor ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s)
        E1).symm.toAddEquiv).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(𝒢.G.left, U)
        (𝒢.G.left.presheaf.stalk (𝒢.unitSection s))
        ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s)
        ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s) Ω[Γ(𝒢.G.left, U)⁄𝓞 L]).toAddEquiv
  let F : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L] ≃+ (Reta L) ⊗[Γ(𝒢.G.left, U)]
      Ω[Γ(𝒢.G.left, U)⁄𝓞 L] :=
    ((LinearEquiv.lTensor (Reta L) E2).symm.toAddEquiv).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(𝒢.G.left, U) 𝒢.genStalk
        (Reta L) (Reta L) Ω[Γ(𝒢.G.left, U)⁄𝓞 L]).toAddEquiv
  let ρ := LinearMap.rTensor Ω[Γ(𝒢.G.left, U)⁄𝓞 L]
    (IsScalarTower.toAlgHom Γ(𝒢.G.left, U) ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s)
      (Reta L)).toLinearMap
  have hρ : Function.Injective ρ :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (sigma_injective s)
  have hE1 : ∀ a : Γ(𝒢.G.left, U), E1 (1 ⊗ₜ D (𝓞 L) _ a) =
      D (𝓞 L) _ (algebraMap Γ(𝒢.G.left, U) (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) a) := by
    intro a
    rw [← tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearEquiv.apply_symm_apply]
  have hE2 : ∀ a : Γ(𝒢.G.left, U), E2.symm (D (𝓞 L) _ (algebraMap Γ(𝒢.G.left, U)
      𝒢.genStalk a)) = 1 ⊗ₜ D (𝓞 L) _ a :=
    fun a => tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap _ _ _ a
  have key : ∀ y, F (stalkToGeneric 𝒢 s (F'.symm y)) = ρ y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r ω =>
      have hω : ω ∈ Submodule.span Γ(𝒢.G.left, U) (Set.range (D (𝓞 L) Γ(𝒢.G.left, U))) := by
        rw [span_range_derivation]; trivial
      induction hω using Submodule.span_induction generalizing r with
      | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        have h1 : F'.symm (r ⊗ₜ D (𝓞 L) _ a) =
            r ⊗ₜ D (𝓞 L) _ (algebraMap Γ(𝒢.G.left, U)
              (𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) a) := by
          show (LinearEquiv.lTensor _ E1) ((TensorProduct.AlgebraTensorModule.cancelBaseChange
            _ _ _ _ _).symm (r ⊗ₜ D (𝓞 L) _ a)) = _
          rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
            LinearEquiv.lTensor_tmul, hE1]
        rw [h1, stalkToGeneric_tmul, map_D,
          ← IsScalarTower.algebraMap_apply]
        show (TensorProduct.AlgebraTensorModule.cancelBaseChange _ _ _ _ _)
          ((LinearEquiv.lTensor _ E2).symm (sigma s r ⊗ₜ D (𝓞 L) _ _)) = _
        rw [LinearEquiv.symm_lTensor, LinearEquiv.lTensor_tmul, hE2,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
        rfl
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add x y _ _ hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
      | smul b x _ hx => rw [← TensorProduct.smul_tmul]; exact hx _
  intro x y hxy
  apply F'.injective
  apply hρ
  rw [← key, ← key, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hxy]

/-- An element of the generic fibre lies in `printedOmegaAt s` iff it is the image of exactly one
element of the stalk of `e*Ω¹` at `s`. -/
theorem mem_printedOmegaAt_iff (t : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) :
    t ∈ printedOmegaAt 𝒢 s ↔ ∃! m : stalkOmega 𝒢 s, stalkToGeneric 𝒢 s m = t := by
  constructor
  · intro ht
    have : t ∈ Set.range (stalkToGeneric 𝒢 s) := by
      rw [range_stalkToGeneric]; exact ht
    obtain ⟨m, hm⟩ := this
    exact ⟨m, hm, fun m' hm' => stalkToGeneric_injective 𝒢 s (hm'.trans hm.symm)⟩
  · rintro ⟨m, hm, -⟩
    have : t ∈ Set.range (stalkToGeneric 𝒢 s) := ⟨m, hm⟩
    rwa [range_stalkToGeneric] at this

/-- **`secOmega` are sections of `e*Ω¹`**: a section over `V ∋ s` has a unique germ in the stalk
at `s` mapping to it. -/
theorem secOmega_existsUnique_germ {V : (Spec (CommRingCat.of (𝓞 L))).Opens}
    {W : 𝒢.G.left.Opens} (hs : s ∈ V) (hVW : V ≤ 𝒢.unitSection ⁻¹ᵁ W)
    {t : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]}
    (ht : t ∈ secOmega 𝒢 V W (genericPt_mem hs) hVW) :
    ∃! m : stalkOmega 𝒢 s, stalkToGeneric 𝒢 s m = t :=
  (mem_printedOmegaAt_iff 𝒢 s t).mp (secOmega_le 𝒢 hs hVW ht)

end Stalk

/-- **`globalOmega` consists of the sections of `e*Ω¹` (not only of its image in the generic
fibre), up to README reading 1**: an element of the generic fibre is a
global section iff at every point `s` it is the image of exactly one element of the stalk
`(e*Ω¹)_s`. So a global section is the same as a family of germs, one in each stalk, with a common
generic image; since every stalk injects into the generic fibre, this family is determined by
that image. -/
theorem mem_globalOmega_iff (t : (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) :
    t ∈ globalOmega 𝒢 ↔ ∀ s, ∃! m : stalkOmega 𝒢 s, stalkToGeneric 𝒢 s m = t := by
  rw [globalOmega_eq, Submodule.mem_iInf]
  exact forall_congr' fun s => mem_printedOmegaAt_iff 𝒢 s t

end ZInQ.HeightModelM3
