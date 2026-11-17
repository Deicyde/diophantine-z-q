import ZInQKernel.Contrib.HeightBC.OmegaBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.DefFaltings ZInQ.HeightBC KaehlerDifferential
open scoped NumberField TensorProduct

set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

namespace ZInQ.HeightDict.Conormal

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `𝓞_L → 𝒪_{𝒢,x}`. -/
noncomputable def stalkAlg (x : 𝒢.G.left) : 𝓞 L →+* 𝒢.G.left.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv ≫ 𝒢.G.hom.appTop ≫
    𝒢.G.left.presheaf.germ ⊤ x trivial).hom

/-- `𝓞_L → 𝒪_{S,s}`. -/
noncomputable def baseStalk (s : Spec (CommRingCat.of (𝓞 L))) :
    𝓞 L →+* (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s :=
  ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv ≫
    (Spec (CommRingCat.of (𝓞 L))).presheaf.germ ⊤ s trivial).hom

/-- `e^#_s : 𝒪_{𝒢,e(s)} → 𝒪_{S,s}`. -/
noncomputable def unitStalk (s : Spec (CommRingCat.of (𝓞 L))) :
    𝒢.G.left.presheaf.stalk (𝒢.unitSection s) →+* (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s :=
  (𝒢.unitSection.stalkMap s).hom

/-- The specialization `𝒪_{𝒢,e(s)} → 𝒪_{𝒢,ξ}`. -/
noncomputable def specMap (s : Spec (CommRingCat.of (𝓞 L))) :
    𝒢.G.left.presheaf.stalk (𝒢.unitSection s) →+* 𝒢.genStalk :=
  (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s)).hom

theorem stalkAlg_eq (s : Spec (CommRingCat.of (𝓞 L))) (a : 𝓞 L) :
    stalkAlg 𝒢 (𝒢.unitSection s) a = (𝒢.G.hom.stalkMapAt (hom_unitSection 𝒢 s)).hom (baseStalk s a) := by
  unfold baseStalk
  rw [CommRingCat.hom_comp, RingHom.comp_apply, stalkMapAt_germ' _ _ ⊤ (by trivial) (by trivial)]
  erw [Scheme.Hom.germ_stalkMap_apply 𝒢.G.hom ⊤ (𝒢.unitSection s) (by trivial)]
  rfl

theorem unitStalk_stalkAlg (s : Spec (CommRingCat.of (𝓞 L))) (a : 𝓞 L) :
    unitStalk 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) a) = baseStalk s a := by
  rw [stalkAlg_eq]
  have := unitSection_stalkMapAt_hom 𝒢 (rfl : 𝒢.unitSection s = 𝒢.unitSection s)
    (hom_unitSection 𝒢 s) (baseStalk s a)
  rw [Scheme.Hom.stalkMapAt_rfl] at this
  exact this

instance isLocalHom_unitStalk (s : Spec (CommRingCat.of (𝓞 L))) : IsLocalHom (unitStalk 𝒢 s) := by
  unfold unitStalk; infer_instance

theorem specMap_stalkAlg (s : Spec (CommRingCat.of (𝓞 L))) (a : 𝓞 L) :
    specMap 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) a) = 𝒢.structMap a := by
  unfold specMap stalkAlg GroupModel.structMap
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]


/-! ## The generic fibre of `e*Ω¹` and the comparison map -/

/-- `𝒪_{S,η}` (a field, `≅ L`). -/
noncomputable abbrev Reta (L : Type) [Field L] [NumberField L] : CommRingCat :=
  (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)

theorem isField_Reta : IsField (Reta L) := by
  have : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
    (genericPoint_eq_bot_of_affine (CommRingCat.of (𝓞 L))).symm
  unfold Reta
  rw [this]
  exact Field.toIsField _

noncomputable def algXi : Algebra (𝓞 L) 𝒢.genStalk := 𝒢.structMap.toAlgebra
noncomputable def algEta : Algebra (𝓞 L) (Reta L) := (baseStalk (genericPt L)).toAlgebra
noncomputable def algXiEta : Algebra 𝒢.genStalk (Reta L) := (unitStalk 𝒢 (genericPt L)).toAlgebra

attribute [local instance] algXi algEta algXiEta

instance towerXiEta : IsScalarTower (𝓞 L) 𝒢.genStalk (Reta L) :=
  IsScalarTower.of_algebraMap_eq fun a => (unitStalk_stalkAlg 𝒢 (genericPt L) a).symm

theorem maximalIdeal_le_ker : IsLocalRing.maximalIdeal 𝒢.genStalk ≤
    (RingHom.ker (algebraMap 𝒢.genStalk (Reta L))).comap (AlgHom.id 𝒢.genStalk 𝒢.genStalk) := by
  intro x hx
  show unitStalk 𝒢 (genericPt L) x = 0
  have hloc : unitStalk 𝒢 (genericPt L) x ∈ IsLocalRing.maximalIdeal (Reta L) :=
    map_nonunit (unitStalk 𝒢 (genericPt L)) _ ((IsLocalRing.mem_maximalIdeal _).mp hx)
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp isField_Reta] at hloc
  exact hloc

/-- `θ : 𝔪_ξ/𝔪_ξ² → 𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]`, `df ↦ 1 ⊗ df` (Mathlib's `kerCotangentToTensor`). -/
noncomputable def theta : 𝒢.cotangent →ₗ[𝒢.genStalk] (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L] :=
  kerCotangentToTensor (𝓞 L) 𝒢.genStalk (Reta L) ∘ₗ
    Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk)
      (RingHom.ker (algebraMap 𝒢.genStalk (Reta L))) (AlgHom.id 𝒢.genStalk 𝒢.genStalk)
      (maximalIdeal_le_ker 𝒢)

theorem theta_dCls (f : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    theta 𝒢 (𝒢.dCls f) = (1 : Reta L) ⊗ₜ D (𝓞 L) 𝒢.genStalk (f : 𝒢.genStalk) := rfl

/-- `θ` is `𝓞_L`-linear. -/
noncomputable def theta' : 𝒢.cotangent →ₗ[𝓞 L] (Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L] where
  toFun := theta 𝒢
  map_add' := map_add _
  map_smul' a x := by
    show theta 𝒢 (𝒢.structMap a • x) = a • theta 𝒢 x
    rw [map_smul]
    exact algebraMap_smul 𝒢.genStalk a (theta 𝒢 x)

/-- **The stalk at `s` of `e*Ω¹_{𝒢/S}` in the generic fibre**: the image of
`𝒪_{S,s} ⊗ Ω[𝒪_{𝒢,e(s)}/𝓞_L]` in `𝒪_{S,η} ⊗ Ω[𝒪_{𝒢,ξ}/𝓞_L]`, i.e. the `𝓞_L`-span of the
`1 ⊗ d(b|_ξ)`, `b ∈ 𝒪_{𝒢,e(s)}` (the set is stable under `𝒪_{S,s}` by the Leibniz rule). -/
noncomputable def printedOmegaAt (s : Spec (CommRingCat.of (𝓞 L))) :
    Submodule (𝓞 L) ((Reta L) ⊗[𝒢.genStalk] Ω[𝒢.genStalk⁄𝓞 L]) :=
  Submodule.span (𝓞 L) (Set.range fun b : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s) =>
    (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s b))

theorem D_inv_of_unit {v : 𝒢.genStalk} (hv : IsUnit v) (hDv : D (𝓞 L) 𝒢.genStalk v = 0) :
    D (𝓞 L) 𝒢.genStalk (↑hv.unit⁻¹ : 𝒢.genStalk) = 0 := by
  have h : (↑hv.unit⁻¹ : 𝒢.genStalk) * v = 1 := by
    have h0 := hv.unit.inv_mul
    rwa [hv.unit_spec] at h0
  rw [(D (𝓞 L) 𝒢.genStalk).leibniz_of_mul_eq_one h, hDv, smul_zero]

/-- **EGA IV 17.2.5 at the stalks (proved):** under `θ`, the kernel's conormal lattice
`omegaAt s` is the image of `(e*Ω¹_{𝒢/S})_s`. -/
theorem omegaAt_map (s : Spec (CommRingCat.of (𝓞 L))) :
    (𝒢.omegaAt s).map (theta' 𝒢) = printedOmegaAt 𝒢 s := by
  unfold GroupModel.omegaAt printedOmegaAt
  rw [Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨m, ⟨f, hf, h, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨f, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    haveI : s.asIdeal.IsPrime := s.isPrime
    set Os := (Spec (CommRingCat.of (𝓞 L))).presheaf.stalk s
    letI : Algebra (𝓞 L) Os := (baseStalk s).toAlgebra
    haveI : IsLocalization.AtPrime Os s.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (𝓞 L)) s
    obtain ⟨⟨p, t⟩, hpt⟩ := IsLocalization.surj s.asIdeal.primeCompl (unitStalk 𝒢 s b)
    have htu : IsUnit (unitStalk 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) t)) := by
      rw [unitStalk_stalkAlg]
      exact IsLocalization.map_units Os t
    have hu : IsUnit (stalkAlg 𝒢 (𝒢.unitSection s) t) :=
      isUnit_of_map_unit (unitStalk 𝒢 s) _ htu
    set c := stalkAlg 𝒢 (𝒢.unitSection s) p * ↑hu.unit⁻¹
    have hc : unitStalk 𝒢 s c = unitStalk 𝒢 s b := by
      have e1 : unitStalk 𝒢 s b * unitStalk 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) t) =
          unitStalk 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) p) := by
        rw [unitStalk_stalkAlg, unitStalk_stalkAlg]; exact hpt
      have e2 : unitStalk 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) t) *
          unitStalk 𝒢 s (↑hu.unit⁻¹ : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) = 1 := by
        rw [← map_mul, Units.mul_inv_of_eq hu.unit_spec, map_one]
      calc unitStalk 𝒢 s c = unitStalk 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) p) *
            unitStalk 𝒢 s (↑hu.unit⁻¹ : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) := map_mul _ _ _
        _ = unitStalk 𝒢 s b * (unitStalk 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) t) *
            unitStalk 𝒢 s (↑hu.unit⁻¹ : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s))) := by
              rw [← e1, _root_.mul_assoc]
        _ = unitStalk 𝒢 s b := by rw [e2, _root_.mul_one]
    have hf : (𝒢.unitSection.stalkMap s).hom (b - c) = 0 := by
      show unitStalk 𝒢 s (b - c) = 0
      rw [map_sub, hc, sub_self]
    have hm := spec_mem_of_ker 𝒢 s (b - c) hf
    -- `d(c|_ξ) = 0`
    have hDc : D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s c) = 0 := by
      have hsu : IsUnit (specMap 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) t)) := hu.map (specMap 𝒢 s)
      have hinv : specMap 𝒢 s (↑hu.unit⁻¹ : 𝒢.G.left.presheaf.stalk (𝒢.unitSection s)) =
          ↑hsu.unit⁻¹ := by
        apply Units.eq_inv_of_mul_eq_one_left
        rw [IsUnit.unit_spec, ← map_mul]
        have h0 := hu.unit.mul_inv
        rw [hu.unit_spec] at h0
        rw [h0, map_one]
      have hDt : D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) t)) = 0 := by
        rw [specMap_stalkAlg]; exact (D (𝓞 L) 𝒢.genStalk).map_algebraMap (t : 𝓞 L)
      have hDp : D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s (stalkAlg 𝒢 (𝒢.unitSection s) p)) = 0 := by
        rw [specMap_stalkAlg]; exact (D (𝓞 L) 𝒢.genStalk).map_algebraMap p
      rw [map_mul, Derivation.leibniz, hinv, D_inv_of_unit 𝒢 hsu hDt, hDp, smul_zero, smul_zero,
        add_zero]
    have key : (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s b) =
        theta' 𝒢 (𝒢.dCls ⟨_, hm⟩) := by
      show _ = (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk
        (𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) (b - c))
      have : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) (b - c) =
          specMap 𝒢 s b - specMap 𝒢 s c := map_sub (specMap 𝒢 s) b c
      rw [this, map_sub, hDc, sub_zero]
    show (1 : Reta L) ⊗ₜ[𝒢.genStalk] D (𝓞 L) 𝒢.genStalk (specMap 𝒢 s b) ∈ _
    rw [key]
    exact Submodule.subset_span ⟨_, ⟨b - c, hf, hm, rfl⟩, rfl⟩


/-! ## `θ` is injective, hence the global lattices correspond -/

theorem isLocalization_Reta :
    IsLocalization.AtPrime (Reta L) (⊥ : Ideal (𝓞 L)) := by
  have h := StructureSheaf.IsLocalization.to_stalk (CommRingCat.of (𝓞 L)) (genericPt L)
  exact h

theorem structMap_isUnit (t : 𝓞 L) (ht : t ≠ 0) : IsUnit (𝒢.structMap t) := by
  haveI := isLocalization_Reta (L := L)
  have h1 : IsUnit (unitStalk 𝒢 (genericPt L) (𝒢.structMap t)) := by
    rw [show 𝒢.structMap t = stalkAlg 𝒢 (𝒢.unitSection (genericPt L)) t from rfl,
      unitStalk_stalkAlg]
    exact IsLocalization.map_units (Reta L) (⟨t, Ideal.mem_primeCompl_iff.mpr (by simpa using ht)⟩ :
      (⊥ : Ideal (𝓞 L)).primeCompl)
  exact isUnit_of_map_unit (unitStalk 𝒢 (genericPt L)) _ h1

theorem ker_eq_maximalIdeal :
    RingHom.ker (algebraMap 𝒢.genStalk (Reta L)) = IsLocalRing.maximalIdeal 𝒢.genStalk := by
  apply le_antisymm
  · intro x hx hu
    have h0 : unitStalk 𝒢 (genericPt L) x = 0 := hx
    haveI : Nontrivial (Reta L) := (isField_Reta (L := L)).nontrivial
    apply not_isUnit_zero (M₀ := Reta L)
    rw [← h0]
    exact hu.map _
  · intro x hx
    exact maximalIdeal_le_ker 𝒢 hx

theorem algebraMap_surjective : Function.Surjective (algebraMap 𝒢.genStalk (Reta L)) := by
  haveI := isLocalization_Reta (L := L)
  intro y
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective (⊥ : Ideal (𝓞 L)).primeCompl y
  have ht : (t : 𝓞 L) ≠ 0 := fun h =>
    (Ideal.mem_primeCompl_iff.mp t.2) (by rw [h]; exact Ideal.zero_mem _)
  have hu := structMap_isUnit 𝒢 t ht
  refine ⟨𝒢.structMap a * ↑hu.unit⁻¹, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, _root_.mul_assoc]
  have e1 : ∀ c : 𝓞 L, algebraMap 𝒢.genStalk (Reta L) (𝒢.structMap c) = algebraMap (𝓞 L) (Reta L) c :=
    fun c => unitStalk_stalkAlg 𝒢 (genericPt L) c
  rw [← e1 t, ← map_mul]
  have h0 := hu.unit.inv_mul
  rw [hu.unit_spec] at h0
  rw [h0, map_one, _root_.mul_one, e1]

/-- **`θ` is injective** (Mathlib's `retractionKerCotangentToTensorEquivSection`, from the section
`𝒪_{S,η} → 𝒪_{𝒢,ξ}/I²` given by the structure map). -/
theorem theta_injective : Function.Injective (theta 𝒢) := by
  haveI := isLocalization_Reta (L := L)
  set I := RingHom.ker (algebraMap 𝒢.genStalk (Reta L))
  -- the section
  let f₀ : 𝓞 L →ₐ[𝓞 L] 𝒢.genStalk ⧸ I ^ 2 :=
    (Ideal.Quotient.mkₐ (𝓞 L) (I ^ 2)).comp (Algebra.ofId (𝓞 L) 𝒢.genStalk)
  have hf₀ : ∀ y : (⊥ : Ideal (𝓞 L)).primeCompl, IsUnit (f₀ y) := by
    intro y
    have hy : (y : 𝓞 L) ≠ 0 := fun h =>
      (Ideal.mem_primeCompl_iff.mp y.2) (by rw [h]; exact Ideal.zero_mem _)
    exact (structMap_isUnit 𝒢 y hy).map (Ideal.Quotient.mk (I ^ 2))
  let g : Reta L →ₐ[𝓞 L] 𝒢.genStalk ⧸ I ^ 2 :=
    IsLocalization.liftAlgHom (M := (⊥ : Ideal (𝓞 L)).primeCompl) hf₀
  have hg : (IsScalarTower.toAlgHom (𝓞 L) 𝒢.genStalk (Reta L)).kerSquareLift.comp g =
      AlgHom.id (𝓞 L) (Reta L) := by
    apply AlgHom.toRingHom_injective
    apply IsLocalization.ringHom_ext (⊥ : Ideal (𝓞 L)).primeCompl
    ext a
    show (IsScalarTower.toAlgHom (𝓞 L) 𝒢.genStalk (Reta L)).kerSquareLift
      (g (algebraMap (𝓞 L) (Reta L) a)) = algebraMap (𝓞 L) (Reta L) a
    rw [show g (algebraMap (𝓞 L) (Reta L) a) = f₀ a from IsLocalization.lift_eq hf₀ a]
    show unitStalk 𝒢 (genericPt L) (𝒢.structMap a) = _
    exact unitStalk_stalkAlg 𝒢 (genericPt L) a
  obtain ⟨l, hl⟩ := (retractionKerCotangentToTensorEquivSection (R := 𝓞 L)
    (algebraMap_surjective 𝒢)).symm ⟨g, hg⟩
  have hinj1 : Function.Injective (kerCotangentToTensor (𝓞 L) 𝒢.genStalk (Reta L)) := by
    intro x y hxy
    have h := congrArg l hxy
    have h1 := LinearMap.congr_fun hl x
    have h2 := LinearMap.congr_fun hl y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    rw [← h1, ← h2]
    exact h
  have hinj2 : Function.Injective (Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒢.genStalk) I
      (AlgHom.id 𝒢.genStalk 𝒢.genStalk) (maximalIdeal_le_ker 𝒢)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ x
    rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq_zero] at hx
    rw [Ideal.toCotangent_eq_zero]
    have hI : I = IsLocalRing.maximalIdeal 𝒢.genStalk := ker_eq_maximalIdeal 𝒢
    have hx' : (y : 𝒢.genStalk) ∈ I ^ 2 := hx
    rw [hI] at hx'
    exact hx'
  exact hinj1.comp hinj2

/-- **`ω_𝒢 = Γ(S, e*Ω¹_{𝒢/S})` (EGA IV 17.2.5 with global sections as the intersection of the stalks
of a lattice):** under the injective `θ`, the kernel's `omega` is the intersection over `s` of the
images of the stalks `(e*Ω¹)_s`. -/
theorem omega_map : 𝒢.omega.map (theta' 𝒢) = ⨅ s, printedOmegaAt 𝒢 s := by
  unfold GroupModel.omega
  haveI : Nonempty (Spec (CommRingCat.of (𝓞 L))) := ⟨genericPt L⟩
  rw [Submodule.map_iInf (theta' 𝒢) (theta_injective 𝒢)]
  exact iInf_congr fun s => omegaAt_map 𝒢 s

end ZInQ.HeightDict.Conormal
