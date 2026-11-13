
/-! ## metrization: `ProductLatticeFacts`, proved (body of ProdLattice.lean, section Proof) -/

namespace ZInQ.Metrization

open MeasureTheory

section Proof

variable {g₁ g₂ : ℕ}

@[simp] theorem leftBlock_apply (z : Fin (g₁ + g₂) → ℂ) (i : Fin g₁) :
    leftBlock g₁ g₂ z i = z (Fin.castAdd g₂ i) := rfl

@[simp] theorem rightBlock_apply (z : Fin (g₁ + g₂) → ℂ) (j : Fin g₂) :
    rightBlock g₁ g₂ z j = z (Fin.natAdd g₁ j) := rfl

theorem mem_prodLattice {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {z : Fin (g₁ + g₂) → ℂ} :
    z ∈ prodLattice Λ₁ Λ₂ ↔ leftBlock g₁ g₂ z ∈ Λ₁ ∧ rightBlock g₁ g₂ z ∈ Λ₂ := Iff.rfl

theorem eq_of_blocks {z w : Fin (g₁ + g₂) → ℂ} (h1 : leftBlock g₁ g₂ z = leftBlock g₁ g₂ w)
    (h2 : rightBlock g₁ g₂ z = rightBlock g₁ g₂ w) : z = w := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · exact congrFun h1 i
  · exact congrFun h2 j

@[simp] theorem leftBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    leftBlock g₁ g₂ (Fin.append x y) = x := by
  funext i; simp

@[simp] theorem rightBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    rightBlock g₁ g₂ (Fin.append x y) = y := by
  funext j; simp

/-- `ℂ^{g₁+g₂} ≃ ℂ^{g₁} × ℂ^{g₂}` over `ℝ`. -/
noncomputable def blockLinearEquiv (g₁ g₂ : ℕ) :
    (Fin (g₁ + g₂) → ℂ) ≃ₗ[ℝ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) where
  toFun z := (leftBlock g₁ g₂ z, rightBlock g₁ g₂ z)
  invFun p := Fin.append p.1 p.2
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp
  left_inv z := eq_of_blocks (by simp) (by simp)
  right_inv p := by ext <;> simp

/-- `blockLinearEquiv` preserves `volume`. -/
theorem measurePreserving_blockLinearEquiv (g₁ g₂ : ℕ) :
    MeasurePreserving (blockLinearEquiv g₁ g₂) volume volume := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)
    (finSumFinEquiv (m := g₁) (n := g₂)).symm
  have h2 := (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)).symm
  have hc := h2.comp h1
  convert hc using 1
  funext z
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [Function.comp_apply, MeasurableEquiv.symm_symm,
      MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply,
      MeasurableEquiv.coe_piCongrLeft]
    rw [show (Sum.inl i : Fin g₁ ⊕ Fin g₂) = finSumFinEquiv.symm (Fin.castAdd g₂ i) by simp,
      Equiv.piCongrLeft_apply_apply]
    rfl
  · simp only [Function.comp_apply, MeasurableEquiv.symm_symm,
      MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply,
      MeasurableEquiv.coe_piCongrLeft]
    rw [show (Sum.inr j : Fin g₁ ⊕ Fin g₂) = finSumFinEquiv.symm (Fin.natAdd g₁ j) by simp,
      Equiv.piCongrLeft_apply_apply]
    rfl

/-- A full lattice has a measurable fundamental domain with unique translates, whose volume is
the covolume. -/
theorem exists_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ F : Set E, MeasurableSet F ∧ (∀ x, ∃! g : Λ, (g : E) + x ∈ F) ∧
      ZLattice.covolume Λ μ = μ.real F := by
  let b := Module.Free.chooseBasis ℤ Λ
  let b' := b.ofZLatticeBasis ℝ Λ
  have hspan : Submodule.span ℤ (Set.range b') = Λ := b.ofZLatticeBasis_span ℝ Λ
  refine ⟨ZSpan.fundamentalDomain b', ZSpan.fundamentalDomain_measurableSet b', fun x => ?_,
    ZLattice.covolume_eq_measure_fundamentalDomain Λ μ (ZLattice.isAddFundamentalDomain b μ)⟩
  obtain ⟨⟨v, hv⟩, h1, h2⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b' x
  refine ⟨⟨v, hspan ▸ hv⟩, h1, fun w hw => ?_⟩
  have h3 := h2 ⟨w, hspan.symm ▸ w.2⟩ hw
  have h4 : (w : E) = v := congrArg Subtype.val h3
  exact Subtype.ext h4

/-- **`ProductLatticeFacts`, proved.** -/
theorem productLatticeFacts : ProductLatticeFacts := by
  intro g₁ g₂ Λ₁ Λ₂ _ _ hZ₁ hZ₂
  -- discreteness: inject into `Λ₁ × Λ₂`
  have hdisc : DiscreteTopology (prodLattice Λ₁ Λ₂) := by
    let f : prodLattice Λ₁ Λ₂ → Λ₁ × Λ₂ := fun z =>
      (⟨leftBlock g₁ g₂ z, z.2.1⟩, ⟨rightBlock g₁ g₂ z, z.2.2⟩)
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · refine Continuous.prodMk ?_ ?_
      · exact Continuous.subtype_mk
          ((leftBlock g₁ g₂).continuous_of_finiteDimensional.comp continuous_subtype_val) _
      · exact Continuous.subtype_mk
          ((rightBlock g₁ g₂).continuous_of_finiteDimensional.comp continuous_subtype_val) _
    · intro z w h
      have h1 := congrArg (fun p => (p.1 : Fin g₁ → ℂ)) h
      have h2 := congrArg (fun p => (p.2 : Fin g₂ → ℂ)) h
      exact Subtype.ext (eq_of_blocks h1 h2)
  -- full rank
  have hZ : IsZLattice ℝ (prodLattice Λ₁ Λ₂) := by
    refine ⟨?_⟩
    rw [eq_top_iff]
    rintro z -
    have hz : z = Fin.append (leftBlock g₁ g₂ z) 0 + Fin.append 0 (rightBlock g₁ g₂ z) :=
      eq_of_blocks (by funext i; simp) (by funext j; simp)
    rw [hz]
    refine Submodule.add_mem _ ?_ ?_
    · let ι₁ : (Fin g₁ → ℂ) →ₗ[ℝ] (Fin (g₁ + g₂) → ℂ) :=
        (blockLinearEquiv g₁ g₂).symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _
      have hι : ∀ x, ι₁ x = Fin.append x 0 := fun x => rfl
      have hle : (Submodule.span ℝ (Λ₁ : Set (Fin g₁ → ℂ))).map ι₁ ≤
          Submodule.span ℝ (prodLattice Λ₁ Λ₂ : Set (Fin (g₁ + g₂) → ℂ)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨x, hx, rfl⟩
        rw [hι]
        exact ⟨by simpa using hx, by simp [Submodule.zero_mem]⟩
      apply hle
      rw [hZ₁.span_top]
      exact ⟨leftBlock g₁ g₂ z, Submodule.mem_top, hι _⟩
    · let ι₂ : (Fin g₂ → ℂ) →ₗ[ℝ] (Fin (g₁ + g₂) → ℂ) :=
        (blockLinearEquiv g₁ g₂).symm.toLinearMap ∘ₗ LinearMap.inr ℝ _ _
      have hι : ∀ y, ι₂ y = Fin.append 0 y := fun y => rfl
      have hle : (Submodule.span ℝ (Λ₂ : Set (Fin g₂ → ℂ))).map ι₂ ≤
          Submodule.span ℝ (prodLattice Λ₁ Λ₂ : Set (Fin (g₁ + g₂) → ℂ)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨y, hy, rfl⟩
        rw [hι]
        exact ⟨by simp [Submodule.zero_mem], by simpa using hy⟩
      apply hle
      rw [hZ₂.span_top]
      exact ⟨rightBlock g₁ g₂ z, Submodule.mem_top, hι _⟩
  refine ⟨hdisc, hZ, ?_⟩
  -- covolume
  obtain ⟨F₁, hF₁m, hF₁u, hF₁c⟩ := exists_fd Λ₁ volume
  obtain ⟨F₂, hF₂m, hF₂u, hF₂c⟩ := exists_fd Λ₂ volume
  let φ := blockLinearEquiv g₁ g₂
  have hφm : Measurable φ := (measurePreserving_blockLinearEquiv g₁ g₂).measurable
  let F : Set (Fin (g₁ + g₂) → ℂ) := φ ⁻¹' (F₁ ×ˢ F₂)
  have hFd : IsAddFundamentalDomain (prodLattice Λ₁ Λ₂) F volume := by
    refine IsAddFundamentalDomain.mk' ((hφm (hF₁m.prod hF₂m)).nullMeasurableSet) fun z => ?_
    obtain ⟨a, ha, hau⟩ := hF₁u (leftBlock g₁ g₂ z)
    obtain ⟨b, hb, hbu⟩ := hF₂u (rightBlock g₁ g₂ z)
    refine ⟨⟨Fin.append (a : Fin g₁ → ℂ) (b : Fin g₂ → ℂ),
      mem_prodLattice.mpr ⟨by simpa using a.2, by simpa using b.2⟩⟩, ?_, fun w hw => ?_⟩
    · beta_reduce
      rw [Submodule.vadd_def, vadd_eq_add]
      show (leftBlock g₁ g₂ _, rightBlock g₁ g₂ _) ∈ F₁ ×ˢ F₂
      simpa using ⟨ha, hb⟩
    · beta_reduce at hw
      rw [Submodule.vadd_def, vadd_eq_add] at hw
      have hw' : (leftBlock g₁ g₂ ((w : Fin (g₁ + g₂) → ℂ) + z),
          rightBlock g₁ g₂ ((w : Fin (g₁ + g₂) → ℂ) + z)) ∈ F₁ ×ˢ F₂ := hw
      simp only [map_add, Set.mem_prod] at hw'
      have e1 := hau ⟨leftBlock g₁ g₂ w, w.2.1⟩ hw'.1
      have e2 := hbu ⟨rightBlock g₁ g₂ w, w.2.2⟩ hw'.2
      apply Subtype.ext
      apply eq_of_blocks
      · simpa using congrArg Subtype.val e1
      · simpa using congrArg Subtype.val e2
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume hFd, hF₁c, hF₂c,
    (measurePreserving_blockLinearEquiv g₁ g₂).measureReal_preimage
      (hF₁m.prod hF₂m).nullMeasurableSet,
    Measure.volume_eq_prod, measureReal_def, measureReal_def, measureReal_def,
    Measure.prod_prod, ENNReal.toReal_mul]

end Proof

end ZInQ.Metrization

#print axioms ZInQ.Metrization.productLatticeFacts
