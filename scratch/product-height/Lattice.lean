import Mathlib

/-! # product-height: the product lattice `Λ₁ × Λ₂` (an ingredient of S-alg / P2a-geo)

`prodLattice` is copied from `ProductHeight.lean` §5. Proved: it is discrete, a full `ℤ`-lattice,
and `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂` (`prodLattice_facts`). Mathlib only. -/

open MeasureTheory Module ZSpan

namespace ZInQ.ProductHeight

section General

variable {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] [MeasurableSpace E₁]
  [BorelSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] [MeasurableSpace E₂]
  [BorelSpace E₂]
  (Λ₁ : Submodule ℤ E₁) (Λ₂ : Submodule ℤ E₂)

omit [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] [MeasurableSpace E₂] [BorelSpace E₂] in
theorem discreteTopology_prod [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] :
    DiscreteTopology (Λ₁.prod Λ₂) := by
  let f : Λ₁.prod Λ₂ → Λ₁ × Λ₂ := fun x =>
    (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
  have hf : Continuous f := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  have : ({x} : Set (Λ₁.prod Λ₂)) = f ⁻¹' {f x} := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]
  rw [this]
  exact (isOpen_discrete _).preimage hf

instance instDiscreteTopologyProd [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] :
    DiscreteTopology (Λ₁.prod Λ₂) :=
  discreteTopology_prod Λ₁ Λ₂

instance instIsZLatticeProd [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₁]
    [IsZLattice ℝ Λ₂] : IsZLattice ℝ (Λ₁.prod Λ₂) := by
  refine ⟨?_⟩
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have hx : x ∈ Submodule.span ℝ (Λ₁ : Set E₁) := by rw [IsZLattice.span_top]; trivial
  have hy : y ∈ Submodule.span ℝ (Λ₂ : Set E₂) := by rw [IsZLattice.span_top]; trivial
  have h1 : Submodule.map (LinearMap.inl ℝ E₁ E₂) (Submodule.span ℝ (Λ₁ : Set E₁)) ≤
      Submodule.span ℝ ((Λ₁.prod Λ₂ : Submodule ℤ (E₁ × E₂)) : Set (E₁ × E₂)) := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.mem_prod.mpr ⟨ha, Λ₂.zero_mem⟩
  have h2 : Submodule.map (LinearMap.inr ℝ E₁ E₂) (Submodule.span ℝ (Λ₂ : Set E₂)) ≤
      Submodule.span ℝ ((Λ₁.prod Λ₂ : Submodule ℤ (E₁ × E₂)) : Set (E₁ × E₂)) := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.mem_prod.mpr ⟨Λ₁.zero_mem, ha⟩
  have : ((x, y) : E₁ × E₂) = LinearMap.inl ℝ E₁ E₂ x + LinearMap.inr ℝ E₁ E₂ y := by simp
  rw [this]
  exact Submodule.add_mem _ (h1 ⟨x, hx, rfl⟩) (h2 ⟨y, hy, rfl⟩)

/-- Unique translates into the fundamental domain of a basis, for the lattice itself. -/
theorem exists_unique_add_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (x : E) :
    ∃! l : L, (l : E) + x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ) := by
  have hs := b.ofZLatticeBasis_span ℝ
  obtain ⟨v, hv, hu⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) x
  refine ⟨⟨v, hs.le v.2⟩, hv, fun l hl => ?_⟩
  have := hu ⟨l, hs.ge l.2⟩ hl
  have h : ((⟨(l : E), hs.ge l.2⟩ : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ))) : E) =
      (v : E) := congrArg Subtype.val this
  exact Subtype.ext h

theorem isAddFundamentalDomain_prod [DiscreteTopology Λ₁] [DiscreteTopology Λ₂]
    [IsZLattice ℝ Λ₁] [IsZLattice ℝ Λ₂] {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (b₁ : Basis ι₁ ℤ Λ₁) (b₂ : Basis ι₂ ℤ Λ₂) (μ₁ : Measure E₁) (μ₂ : Measure E₂) :
    IsAddFundamentalDomain (Λ₁.prod Λ₂)
      (fundamentalDomain (b₁.ofZLatticeBasis ℝ) ×ˢ fundamentalDomain (b₂.ofZLatticeBasis ℝ))
      (μ₁.prod μ₂) := by
  refine IsAddFundamentalDomain.mk' (((fundamentalDomain_measurableSet _).prod
    (fundamentalDomain_measurableSet _)).nullMeasurableSet) fun x => ?_
  obtain ⟨l₁, h₁, u₁⟩ := exists_unique_add_mem Λ₁ b₁ x.1
  obtain ⟨l₂, h₂, u₂⟩ := exists_unique_add_mem Λ₂ b₂ x.2
  refine ⟨⟨((l₁ : E₁), (l₂ : E₂)), Submodule.mem_prod.mpr ⟨l₁.2, l₂.2⟩⟩, ⟨h₁, h₂⟩, ?_⟩
  rintro ⟨⟨y₁, y₂⟩, hy⟩ hm
  obtain ⟨hm₁, hm₂⟩ := hm
  have e1 := u₁ ⟨y₁, (Submodule.mem_prod.mp hy).1⟩ hm₁
  have e2 := u₂ ⟨y₂, (Submodule.mem_prod.mp hy).2⟩ hm₂
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)

/-- **`covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`** (proved). -/
theorem covolume_prod [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₁]
    [IsZLattice ℝ Λ₂] (μ₁ : Measure E₁) (μ₂ : Measure E₂) [μ₁.IsAddHaarMeasure]
    [μ₂.IsAddHaarMeasure] :
    ZLattice.covolume (Λ₁.prod Λ₂) (μ₁.prod μ₂) =
      ZLattice.covolume Λ₁ μ₁ * ZLattice.covolume Λ₂ μ₂ := by
  let b₁ := Free.chooseBasis ℤ Λ₁
  let b₂ := Free.chooseBasis ℤ Λ₂
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (Λ₁.prod Λ₂) (μ₁.prod μ₂)
      (isAddFundamentalDomain_prod Λ₁ Λ₂ b₁ b₂ μ₁ μ₂),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ₁ μ₁ (ZLattice.isAddFundamentalDomain b₁ μ₁),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ₂ μ₂ (ZLattice.isAddFundamentalDomain b₂ μ₂),
    measureReal_def, measureReal_def, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]

end General

section Split

/-- `ℂ^{g₁+g₂} ≅ ℂ^{g₁} × ℂ^{g₂}`, `z ↦ (z ∘ castAdd, z ∘ natAdd)`. -/
def splitLE (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) ≃ₗ[ℝ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) where
  toFun z := (fun i => z (Fin.castAdd g₂ i), fun i => z (Fin.natAdd g₁ i))
  invFun p := Fin.append p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv p := by ext i <;> simp

/-- The continuous version. -/
noncomputable def splitCL (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) ≃L[ℝ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) :=
  (splitLE g₁ g₂).toContinuousLinearEquiv

theorem splitCL_apply (g₁ g₂ : ℕ) (z : Fin (g₁ + g₂) → ℂ) :
    splitCL g₁ g₂ z = (fun i => z (Fin.castAdd g₂ i), fun i => z (Fin.natAdd g₁ i)) := rfl

theorem splitCL_measurePreserving (g₁ g₂ : ℕ) :
    MeasurePreserving (splitCL g₁ g₂) volume volume := by
  have h1 := MeasurePreserving.symm _
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (g₁ + g₂) => ℂ) finSumFinEquiv)
  have h2 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)
  have h := h2.comp h1
  convert h using 1
  funext z
  rw [splitCL_apply]
  ext i
  · simp only [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi,
      Equiv.sumPiEquivProdPi_apply]
    show z _ = (Equiv.piCongrLeft (fun _ => ℂ) finSumFinEquiv).symm z (Sum.inl i)
    rw [Equiv.piCongrLeft_symm_apply, finSumFinEquiv_apply_left]
  · simp only [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi,
      Equiv.sumPiEquivProdPi_apply]
    show z _ = (Equiv.piCongrLeft (fun _ => ℂ) finSumFinEquiv).symm z (Sum.inr i)
    rw [Equiv.piCongrLeft_symm_apply, finSumFinEquiv_apply_right]

/-- The lattice `Λ₁ × Λ₂ ⊂ ℂ^{g₁+g₂}` (coordinates `Fin.append`); copied from
`ProductHeight.lean` §5. -/
def prodLattice {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) :
    Submodule ℤ (Fin (g₁ + g₂) → ℂ) :=
  Λ₁.comap (LinearMap.funLeft ℤ ℂ (Fin.castAdd g₂)) ⊓
    Λ₂.comap (LinearMap.funLeft ℤ ℂ (Fin.natAdd g₁))

theorem prodLattice_eq_comap {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) :
    prodLattice Λ₁ Λ₂ = ZLattice.comap ℝ (Λ₁.prod Λ₂) (splitCL g₁ g₂).toLinearMap := by
  ext z
  simp only [prodLattice, Submodule.mem_inf, Submodule.mem_comap]
  rfl

/-- **The product lattice is a full discrete lattice with `covol = covol Λ₁ · covol Λ₂`**
(proved). -/
theorem prodLattice_facts {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) [DiscreteTopology Λ₁] [IsZLattice ℝ Λ₁]
    [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₂] :
    ∃ _ : DiscreteTopology (prodLattice Λ₁ Λ₂), IsZLattice ℝ (prodLattice Λ₁ Λ₂) ∧
      ZLattice.covolume (prodLattice Λ₁ Λ₂) = ZLattice.covolume Λ₁ * ZLattice.covolume Λ₂ := by
  have h01 : (volume : Measure (Fin g₁ → ℂ)).IsAddHaarMeasure := inferInstance
  have h02 : (volume : Measure (Fin g₂ → ℂ)).IsAddHaarMeasure := inferInstance
  have : (volume : Measure ((Fin g₁ → ℂ) × (Fin g₂ → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin g₁ → ℂ))
      (volume : Measure (Fin g₂ → ℂ))
  rw [prodLattice_eq_comap]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [ZLattice.covolume_comap (Λ₁.prod Λ₂) volume volume (splitCL_measurePreserving g₁ g₂)]
  exact covolume_prod Λ₁ Λ₂ volume volume

end Split

end ZInQ.ProductHeight

#print axioms ZInQ.ProductHeight.covolume_prod
#print axioms ZInQ.ProductHeight.prodLattice_facts
