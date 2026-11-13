
/-! ## Consistency check in dimension 0 (the only abelian variety Mathlib v4.35 can construct)

`AbVar.zero` is copied from `ZInQKernel/HDecomp/Objects.lean` (`PkgI3.AbVar.zero`) for
def-faltings' copy of the structure; h5-neron's part B (`scratch/h5-neron/H5Neron.lean`
l. 245-559, the zero abelian variety: every metrization has dimension 0 and height 0) is copied
with `open PkgI3 (AbVar)` dropped. Then the three new glue Props are checked for `A = B = C = 0`. -/

namespace ZInQ.DefFaltings.AbVar

open CategoryTheory AlgebraicGeometry MonoidalCategory

/-- (copied from `PkgI3.AbVar.zero`) The zero abelian variety `Spec K`. -/
def zero (K : Type) [Field K] : AbVar K :=
  haveI : IsProper (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by
    dsimp; infer_instance
  { X := 𝟙_ (Over (Spec (CommRingCat.of K))) }

end ZInQ.DefFaltings.AbVar

namespace ZInQ.H5Neron



open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings
open scoped TensorProduct

/-- Maps into an object isomorphic to the unit are equal. -/
theorem hom_ext_of_iso_unit {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y : C}
    (i : X ≅ 𝟙_ C) (f g : Y ⟶ X) : f = g := by
  rw [← cancel_mono i.hom]; exact toUnit_unique _ _

section DimZero

variable {L : Type} [Field L] [NumberField L] {K : Type} [Field K] [Algebra K L] {A : AbVar K}

/-- `⋀^0 ω ≅ L`. -/
noncomputable def hodgeZeroEquiv (𝒢 : GroupModel A L) : 𝒢.hodgeSpace 0 ≃ₗ[L] L :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
      (exteriorPower.zeroEquiv (𝓞 L) 𝒢.cotangent) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid (𝓞 L) L L

/-- The empty wedge `1 ⊗ 1 ∈ ⋀^0`. -/
noncomputable def wedge0 (𝒢 : GroupModel A L) : 𝒢.hodgeSpace 0 :=
  (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) 0 (fun i : Fin 0 => (i.elim0 : 𝒢.cotangent))

theorem hodgeZeroEquiv_wedge0 (𝒢 : GroupModel A L) : hodgeZeroEquiv 𝒢 (wedge0 𝒢) = 1 := by
  simp [hodgeZeroEquiv, wedge0]

theorem wedge0_ne_zero (𝒢 : GroupModel A L) : wedge0 𝒢 ≠ 0 := by
  intro h
  have := congrArg (hodgeZeroEquiv 𝒢) h
  rw [hodgeZeroEquiv_wedge0, LinearEquiv.map_zero] at this
  exact one_ne_zero this

theorem wedge_eq_wedge0 (𝒢 : GroupModel A L) (f : Fin 0 → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.wedge f = wedge0 𝒢 := by
  unfold GroupModel.wedge wedge0
  congr 2
  funext i
  exact i.elim0

theorem detLattice_zero (𝒢 : GroupModel A L) :
    𝒢.detLattice 0 = Submodule.span (𝓞 L) {wedge0 𝒢} := by
  unfold GroupModel.detLattice
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, rfl⟩
    unfold wedge0
    congr 2
    funext i
    exact i.elim0
  · rintro rfl
    refine ⟨fun i => i.elim0, ?_⟩
    unfold wedge0
    congr 2
    funext i
    exact i.elim0

/-- The covolume of the (only) lattice in `ℂ⁰` is `1`. -/
theorem covolume_fin_zero (Λ : Submodule ℤ (Fin 0 → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ZLattice.covolume Λ = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume (F := Set.univ)
    (IsAddFundamentalDomain.mk' nullMeasurableSet_univ fun x =>
      ⟨0, Set.mem_univ _, fun y _ => Subsingleton.elim _ _⟩)]
  simp [Measure.real, volume_pi]

/-- **Every metrized model of dimension `0` has height `0`** (for every `A`). -/
theorem modelHeight_dim_zero (M : MetrizedModel A L 0) : M.hodge.modelHeight = 0 := by
  have hs : M.hodge.lattice = Submodule.span (𝓞 L) {wedge0 M.model} :=
    M.lattice_eq.trans (detLattice_zero _)
  rw [M.hodge.modelHeight_of_span hs (wedge0_ne_zero _)]
  have hc : ∀ τ, M.hodge.coeff τ (wedge0 M.model) = 1 := by
    intro τ
    obtain ⟨Φ, -, hΦ⟩ := M.arch τ
    have := hΦ (fun i => i.elim0)
    rw [wedge_eq_wedge0] at this
    rw [this]
    simp [GroupModel.jacDet]
  have hcov : ∀ τ, torusMetricSq (M.hodge.periods τ) 1 = 1 := by
    intro τ
    have := M.hodge.periods_discrete τ
    have := M.hodge.periods_isZLattice τ
    simp [torusMetricSq, covolume_fin_zero]
  simp [hc, hcov]

end DimZero

section ZeroAV

variable (K : Type) [Field K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- `((Spec K)_L) ≅ 𝟙`. -/
noncomputable def bcUnitIso : ((AbVar.zero K).baseChange L).X ≅ 𝟙_ _ :=
  (Functor.Monoidal.εIso (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))).symm

/-- The trivial group model `Spec 𝓞_L` of `(Spec K)_L`. -/
noncomputable def trivModel : GroupModel (AbVar.zero K) L where
  G := 𝟙_ _
  smooth := by dsimp; infer_instance
  separated := by dsimp; infer_instance
  qc := by dsimp; infer_instance
  gen := (Functor.Monoidal.εIso (Over.pullback (jL L))).symm ≪≫ (bcUnitIso K L).symm
  gen_hom := by
    letI : GrpObj (genericFibre L (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))))) :=
      Functor.grpObjObj
    exact ⟨hom_ext_of_iso_unit (bcUnitIso K L) _ _, hom_ext_of_iso_unit (bcUnitIso K L) _ _⟩

/-- `Spec 𝓞_L` is a Néron model of `(Spec K)_L`. -/
theorem trivModel_isNeronModel : (trivModel K L).IsNeronModel := by
  intro Y _
  refine ⟨fun f g _ => toUnit_unique _ _, fun g => ⟨toUnit Y, hom_ext_of_iso_unit (bcUnitIso K L) _ _⟩⟩

/-- A group model of `(Spec K)_L` has exactly one complex point at each `τ`: `𝒢(ℂ)_τ` injects
into `(Spec K)_L(ℂ)_τ` (adjunction `Over.map ⊣ Over.pullback`), which is a point. -/
theorem pts_subsingleton (𝒢 : GroupModel (AbVar.zero K) L) (τ : L →+* ℂ) :
    Subsingleton (𝒢.Pts τ) := by
  constructor
  intro p q
  let P' : Over (Spec (CommRingCat.of L)) := Over.mk (Spec.map (CommRingCat.ofHom τ))
  let e : GroupModel.ptC τ ≅ (Over.map (jL L)).obj P' := Over.isoMk (Iso.refl _) (by
    simp only [GroupModel.ptC, P', jL, Over.map_obj_hom, Over.mk_hom, Iso.refl_hom,
      Category.id_comp, ← Spec.map_comp]
    rfl)
  let adj := Over.mapPullbackAdj (jL L)
  rw [← cancel_epi e.inv]
  apply (adj.homEquiv P' 𝒢.G).injective
  have := hom_ext_of_iso_unit (bcUnitIso K L) ((adj.homEquiv P' 𝒢.G) (e.inv ≫ p) ≫ 𝒢.gen.hom)
    ((adj.homEquiv P' 𝒢.G) (e.inv ≫ q) ≫ 𝒢.gen.hom)
  exact (cancel_mono 𝒢.gen.hom).mp this

/-- The zero abelian variety has no metrized model of dimension `g ≥ 1`: the kernel of a
uniformization `ℂ^g → 𝒢(ℂ)_τ = {pt}` would be all of `ℂ^g`, which is not discrete. -/
theorem no_metrized_succ (n : ℕ) (M : MetrizedModel (AbVar.zero K) L (n + 1)) : False := by
  haveI : Algebra.IsAlgebraic ℚ L := inferInstance
  let τ : L →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := L)).toRingHom
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  have hall : ∀ z, z ∈ M.hodge.periods τ := fun z => by
    have := pts_subsingleton K L M.model τ
    exact (hΦ.2.1 z).mp (Subsingleton.elim _ _)
  have := M.hodge.periods_discrete τ
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.mp
    (isOpen_discrete ({⟨0, hall 0⟩} : Set (M.hodge.periods τ)))
  have h0 : (0 : Fin (n + 1) → ℂ) ∈ t := by
    have : (⟨0, hall 0⟩ : M.hodge.periods τ) ∈ Subtype.val ⁻¹' t := by
      rw [hpre]; exact Set.mem_singleton _
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ht 0 h0
  let y : Fin (n + 1) → ℂ := fun _ => ((ε / 2 : ℝ) : ℂ)
  have hy : y ∈ t := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, pi_norm_const, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have : (⟨y, hall y⟩ : M.hodge.periods τ) ∈ ({⟨0, hall 0⟩} : Set (M.hodge.periods τ)) := by
    rw [← hpre]; exact hy
  have hy0 : y = 0 := congrArg Subtype.val (Set.mem_singleton_iff.mp this)
  have := congrFun hy0 0
  simp only [y, Pi.zero_apply, Complex.ofReal_eq_zero] at this
  linarith

/-- `τ` as a `τ`-semilinear map `L → ℂ`. -/
noncomputable def semσ (σ : L →+* ℂ) : L →ₛₗ[σ] ℂ where
  toFun := σ
  map_add' := map_add σ
  map_smul' a x := map_mul σ a x

/-- The Hodge data of a group model in dimension `0`. -/
noncomputable def trivHodge (𝒢 : GroupModel (AbVar.zero K) L) : HodgeData L 0 (𝒢.hodgeSpace 0) where
  lattice := 𝒢.detLattice 0
  finrank_eq_one := by rw [(hodgeZeroEquiv 𝒢).finrank_eq, Module.finrank_self]
  isLattice := ⟨wedge0 𝒢, by rw [detLattice_zero]; exact Submodule.mem_span_singleton_self _,
    wedge0_ne_zero 𝒢, by
      rw [detLattice_zero]; unfold secIndex; rw [AddSubgroup.relIndex_self]; norm_num⟩
  periods _ := ⊤
  periods_discrete _ := inferInstance
  periods_isZLattice _ := ⟨eq_top_iff.mpr fun x _ => by
    rw [Subsingleton.elim x 0]; exact zero_mem _⟩
  coeff σ := (semσ L σ).comp (hodgeZeroEquiv 𝒢).toLinearMap
  coeff_ne_zero σ h := by
    have := LinearMap.congr_fun h (wedge0 𝒢)
    simp [semσ, hodgeZeroEquiv_wedge0] at this

/-- The metrized trivial model. -/
noncomputable def trivMetrized : MetrizedModel (AbVar.zero K) L 0 where
  model := trivModel K L
  hodge := trivHodge K L (trivModel K L)
  lattice_eq := rfl
  arch τ := ⟨fun _ => toUnit _,
    ⟨fun _ _ => toUnit_unique _ _, fun z => ⟨fun _ => Submodule.mem_top, fun _ => toUnit_unique _ _⟩,
      fun p => ⟨0, toUnit_unique _ _⟩,
      fun U => by
        rcases Set.eq_empty_or_nonempty ((trivModel K L).dom (fun _ => toUnit _) U) with h | ⟨x, hx⟩
        · rw [h]; exact isOpen_empty
        · have : (trivModel K L).dom (fun _ => toUnit _) U = Set.univ :=
            Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
          rw [this]; exact isOpen_univ,
      fun U s => differentiableOn_const _⟩,
    fun f => by
      show semσ L τ (hodgeZeroEquiv _ ((trivModel K L).wedge f)) = _
      rw [wedge_eq_wedge0, hodgeZeroEquiv_wedge0]
      simp [semσ, GroupModel.jacDet]⟩

/-- **The stable Faltings height of the zero abelian variety is `0`.** -/
theorem stableFaltingsHeight_zero [NumberField K] : stableFaltingsHeight (AbVar.zero K) = 0 := by
  refine le_antisymm ?_ ?_
  · have := stableFaltingsHeight_le (AbVar.zero K) (trivMetrized K K)
    rwa [modelHeight_dim_zero, EReal.coe_zero] at this
  · refine le_stableFaltingsHeight _ fun E g M => ?_
    cases g with
    | zero => rw [modelHeight_dim_zero, EReal.coe_zero]
    | succ n => exact (no_metrized_succ K E.L n M).elim

/-- Every group model of `(Spec K)_L` has a metrized model of dimension `0`. -/
noncomputable def metrizedOf (𝒢 : GroupModel (AbVar.zero K) L) :
    MetrizedModel (AbVar.zero K) L 0 where
  model := 𝒢
  hodge := trivHodge K L 𝒢
  lattice_eq := rfl
  arch τ := by
    have hs := pts_subsingleton K L 𝒢 τ
    refine ⟨fun _ => 1, ⟨fun _ _ => Subsingleton.elim _ _,
      fun z => ⟨fun _ => Submodule.mem_top, fun _ => rfl⟩,
      fun p => ⟨0, Subsingleton.elim _ _⟩, fun U => ?_, fun U s => differentiableOn_const _⟩,
      fun f => ?_⟩
    · rcases Set.eq_empty_or_nonempty (𝒢.dom (fun _ => (1 : 𝒢.Pts τ)) U) with h | ⟨x, hx⟩
      · rw [h]; exact isOpen_empty
      · have : 𝒢.dom (fun _ => (1 : 𝒢.Pts τ)) U = Set.univ :=
          Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
        rw [this]; exact isOpen_univ
    · show semσ L τ (hodgeZeroEquiv _ (𝒢.wedge f)) = _
      rw [wedge_eq_wedge0, hodgeZeroEquiv_wedge0]
      simp [semσ, GroupModel.jacDet]

/-- **Every group model of the zero abelian variety has height `0`.** -/
theorem groupModel_height_zero (𝒢 : GroupModel (AbVar.zero K) L) : 𝒢.height = 0 := by
  refine le_antisymm ?_ ?_
  · refine iInf_le_of_le 0 (iInf_le_of_le (metrizedOf K L 𝒢) (iInf_le_of_le rfl ?_))
    rw [modelHeight_dim_zero, EReal.coe_zero]
  · refine le_iInf fun g => le_iInf fun M => le_iInf fun _ => ?_
    cases g with
    | zero => rw [modelHeight_dim_zero, EReal.coe_zero]
    | succ n => exact (no_metrized_succ K L n M).elim

/-- **`NeronModelMinimal` holds for the zero abelian variety.** -/
theorem neronModelMinimal_zero (𝒩 𝒢 : GroupModel (AbVar.zero K) L) (_ : 𝒩.IsNeronModel) :
    𝒩.height ≤ 𝒢.height := by
  rw [groupModel_height_zero, groupModel_height_zero]

/-- **`StableHeightFinite` holds for the zero abelian variety.** -/
theorem stableHeightFinite_zero [NumberField K] :
    stableFaltingsHeight (AbVar.zero K) ≠ ⊤ ∧ stableFaltingsHeight (AbVar.zero K) ≠ ⊥ := by
  rw [stableFaltingsHeight_zero]; exact ⟨EReal.zero_ne_top, EReal.zero_ne_bot⟩

/-- The identity of `Spec K` is an isogeny (so the hypothesis of R19 is satisfiable). -/
theorem isIsogeny_id_zero : IsIsogeny (𝟙 (AbVar.zero K).X) :=
  ⟨inferInstance, by rw [Over.id_left]; infer_instance, by rw [Over.id_left]; infer_instance⟩

/-- Every endomorphism of the zero abelian variety has degree `≤ 1`. -/
theorem isogDeg_zero_le_one (φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X) : isogDeg φ ≤ 1 := by
  unfold isogDeg
  have : Subsingleton {P : ptObj K (AlgebraicClosure K) ⟶ (AbVar.zero K).X // P ≫ φ = 1} :=
    ⟨fun a b => Subtype.ext (toUnit_unique _ _)⟩
  rcases isEmpty_or_nonempty {P : ptObj K (AlgebraicClosure K) ⟶ (AbVar.zero K).X // P ≫ φ = 1}
    with h | h
  · rw [Nat.card_of_isEmpty]; exact zero_le_one
  · rw [Nat.card_of_subsingleton h.some]

/-- **R21 for the zero abelian variety** (for every `g`, not only `g = dim`). -/
theorem R21_zero [NumberField K] (g : ℕ) :
    ((-(3 / 2) * g : ℝ) : EReal) ≤ stableFaltingsHeight (AbVar.zero K) := by
  rw [stableFaltingsHeight_zero]
  exact_mod_cast (by nlinarith [(Nat.cast_nonneg g : (0 : ℝ) ≤ g)] : -(3 / 2) * (g : ℝ) ≤ 0)

/-- **R20 for the zero abelian variety.** -/
theorem R20_zero [NumberField K] (φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X) (x y : ℝ)
    (hx : stableFaltingsHeight (AbVar.zero K) = x) (hy : stableFaltingsHeight (AbVar.zero K) = y) :
    |x - y| ≤ (1 / 2) * Real.log (isogDeg φ) := by
  rw [stableFaltingsHeight_zero] at hx hy
  have hx' : x = 0 := by exact_mod_cast hx.symm
  have hy' : y = 0 := by exact_mod_cast hy.symm
  rw [hx', hy', sub_zero, abs_zero]
  have := Real.log_natCast_nonneg (isogDeg φ)
  linarith

theorem one_le_grKappa (g d : ℕ) (hd : 1 ≤ d) (x : ℝ) : 1 ≤ grKappa g d x := by
  unfold grKappa
  apply one_le_pow₀
  have hm : 1 ≤ (max (max x (Real.log d)) 1) ^ 2 := one_le_pow₀ (le_max_right _ _)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h14 : (1 : ℝ) ≤ (14 * g : ℝ) ^ (64 * g ^ 2) := by
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · simp
    · apply one_le_pow₀
      have : (1 : ℝ) ≤ g := by exact_mod_cast hg
      linarith
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

/-- **R19 for the zero abelian variety** (for every `g`). -/
theorem R19_zero [NumberField K] (g : ℕ) (x : ℝ) (_ : stableFaltingsHeight (AbVar.zero K) = x)
    (h : ∃ φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X, IsIsogeny φ) :
    (∃ φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X, IsIsogeny φ ∧
        (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
      (∃ ψ : (AbVar.zero K).X ⟶ (AbVar.zero K).X, IsIsogeny ψ ∧
        (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) := by
  obtain ⟨φ, hφ⟩ := h
  have hb : (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x :=
    le_trans (by exact_mod_cast isogDeg_zero_le_one K φ)
      (one_le_grKappa g _ Module.finrank_pos x)
  exact ⟨⟨φ, hφ, hb⟩, ⟨φ, hφ, hb⟩⟩

end ZeroAV

end ZInQ.H5Neron

namespace ZInQ.G0HeightAdd

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings H5Neron

variable (K : Type) [Field K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- `MetrizationExists` holds for the zero abelian variety. -/
theorem metrizationExists_zero (𝒢 : GroupModel (AbVar.zero K) L) :
    ∃ (g : ℕ) (M : MetrizedModel (AbVar.zero K) L g), M.model = 𝒢 :=
  ⟨0, metrizedOf K L 𝒢, rfl⟩

/-- `MetrizationDimUnique` holds for the zero abelian variety. -/
theorem metrizationDimUnique_zero (g g' : ℕ) (M : MetrizedModel (AbVar.zero K) L g)
    (M' : MetrizedModel (AbVar.zero K) L g') : g = g' := by
  cases g with
  | succ n => exact (no_metrized_succ K L n M).elim
  | zero =>
    cases g' with
    | zero => rfl
    | succ n => exact (no_metrized_succ K L n M').elim

/-- `ProductMetrization` holds for `A = B = C = 0` (with every hypothesis allowed). -/
theorem productMetrization_zero (eC : (AbVar.zero K).X ≅ (AbVar.zero K).X ⊗ (AbVar.zero K).X)
    (𝒢P 𝒢₁ 𝒢₂ : GroupModel (AbVar.zero K) L) (_ : IsProductModel eC 𝒢P 𝒢₁ 𝒢₂) (g₁ g₂ : ℕ)
    (M₁ : MetrizedModel (AbVar.zero K) L g₁) (M₂ : MetrizedModel (AbVar.zero K) L g₂)
    (_ : M₁.model = 𝒢₁) (_ : M₂.model = 𝒢₂) :
    ∃ MP : MetrizedModel (AbVar.zero K) L (g₁ + g₂), MP.model = 𝒢P ∧
      MP.hodge.modelHeight = M₁.hodge.modelHeight + M₂.hodge.modelHeight := by
  cases g₁ with
  | succ n => exact (no_metrized_succ K L n M₁).elim
  | zero =>
    cases g₂ with
    | succ n => exact (no_metrized_succ K L n M₂).elim
    | zero =>
      refine ⟨metrizedOf K L 𝒢P, rfl, ?_⟩
      rw [modelHeight_dim_zero, modelHeight_dim_zero, modelHeight_dim_zero, add_zero]

end ZInQ.G0HeightAdd

#print axioms ZInQ.G0HeightAdd.metrizationExists_zero
#print axioms ZInQ.G0HeightAdd.metrizationDimUnique_zero
#print axioms ZInQ.G0HeightAdd.productMetrization_zero
