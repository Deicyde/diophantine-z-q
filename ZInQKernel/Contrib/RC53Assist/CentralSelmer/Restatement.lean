import ZInQKernel.Contrib.RC53Assist.CentralSelmer.Comparison

/-! # The remaining inputs of the central Selmer constructor, as typed

`centralSelmerComparisonOfSpecializedModel` takes a rational complex `K` with a map `i` that is a
quasi-isomorphism in degree one, a group `S` with a bounded-defect map `j`, and a bounded-defect map
`f : S → fullSelmerProduct`. As typed, these inputs are not tied to the rational Kummer complex, to
the Selmer group over the quadratic field, or to the restriction-corestriction pair: `K` may be the
scalar-changed model itself with `i` the identity, and `f` may be the identity of
`fullSelmerProduct`. This file records that, after these choices, the remaining inputs are
equivalent to the conclusion `hcentral` under `SelmerCorankOneOverK` (`inputs_iff_hcentral`). The
constructor therefore shrinks the base-zero leaf only when its inputs are supplied by the genuine
objects; until then `central` and `hcentral` stay open at their present strength.
-/

namespace ZInQ.Manuscript.RC53Assist.CentralSelmer

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC
open ZInQ.Manuscript.RC.BaseZeroLimit
open CategoryTheory Matrix

/-! ## The remaining inputs, as typed, are equivalent to the conclusion -/

/-- Input 1 as typed is met by `K := scalarChangedComplex ρ CU` and `i := 𝟙`. -/
theorem quasiIsoAt_id_scalarChanged (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ) :
    QuasiIsoAt (𝟙 (scalarChangedComplex Rings.rhoT CU)) 1 := inferInstance

/-- Input 3 as typed is met by `S := fullSelmerProduct` and `f := id`. -/
theorem boundedDefects_id (S : Type*) [AddCommGroup S] : BoundedDefects (AddMonoidHom.id S) :=
  ⟨1, 1, one_ne_zero, one_ne_zero, fun x hx => by simpa using hx, fun y => ⟨y, by simp⟩⟩

/-- **The constructor's remaining inputs restate `hcentral`.** For any integral model data, after the trivial choices above the
whole remaining hypothesis bundle of `centralSelmerComparisonOfSpecializedModel` is
`∃ r eK j, BoundedDefects j`, and under the lemma's own hypothesis `SelmerCorankOneOverK ℓ k`
this is *equivalent* to the conclusion `hcentral`. -/
theorem inputs_iff_hcentral {ℓ : ℕ} {k : ℤ} {m : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (hSel : SelmerCorankOneOverK ℓ k) :
    (∃ (r : ℕ) (_ : (scalarChangedComplex Rings.rhoT CU).homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
        (j : (Fin r → Q2Z2) →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)), BoundedDefects j) ↔
      (Dm.map Rings.rhoT).rank = m := by
  constructor
  · rintro ⟨r, eK, j, hj⟩
    exact hcentral_of_specializedModel Dm CU e1 e2 hzero hd _ (𝟙 _) eK j hj
      (AddMonoidHom.id _) (boundedDefects_id _) hSel
  · intro hc
    have hker : Module.finrank ℚ_[2] (LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) = 1 :=
      finrank_ker_of_rank_eq _ hc
    let eK : (scalarChangedComplex Rings.rhoT CU).homology 1 ≃ₗ[ℚ_[2]] (Fin 1 → ℚ_[2]) :=
      (specializedModelHomologyOneEquiv Rings.rhoT CU Dm e1 e2 hzero hd).trans
        (LinearEquiv.ofFinrankEq _ _ (by rw [hker, Module.finrank_fin_fun]))
    obtain ⟨F₁, _, _, ⟨c₁⟩⟩ := hSel.1
    obtain ⟨F₂, _, _, ⟨c₂⟩⟩ := hSel.2
    let φ := fullSelmerProductAddEquiv (Ecurve ℓ) (Etw ℓ k)
    let j : (Fin 1 → Q2Z2) →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k) :=
      φ.symm.toAddMonoidHom.comp
        ((AddMonoidHom.inl _ _).comp (c₁.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)))
    have hj_apply : ∀ x, φ (j x) = (c₁.symm (x, 0), 0) := fun x => by
      simp [j, φ]
    have hF₁ : ∀ t : F₁, (Nat.card F₁ * Nat.card F₂) • t = 0 := fun t => by
      have h : Nat.card F₁ • t = 0 := card_nsmul_eq_zero'
      rw [mul_comm, mul_smul, h, smul_zero]
    have hF₂ : ∀ t : F₂, (Nat.card F₁ * Nat.card F₂) • t = 0 := fun t => by
      have h : Nat.card F₂ • t = 0 := card_nsmul_eq_zero'
      rw [mul_smul, h, smul_zero]
    refine ⟨1, eK, j, 1, Nat.card F₁ * Nat.card F₂, one_ne_zero,
      Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne', fun x hx => ?_, fun y => ?_⟩
    · rw [one_smul]
      have h1 : φ (j x) = 0 := by rw [hx, map_zero]
      rw [hj_apply] at h1
      have h3 : c₁.symm (x, 0) = 0 := congrArg Prod.fst h1
      have h4 : ((x, 0) : (Fin 1 → Q2Z2) × F₁) = 0 := by
        have := congrArg c₁ h3
        rwa [AddEquiv.apply_symm_apply, map_zero] at this
      exact congrArg Prod.fst h4
    · refine ⟨(Nat.card F₁ * Nat.card F₂) • (c₁ (φ y).1).1, φ.injective ?_⟩
      rw [hj_apply, map_nsmul]
      refine Prod.ext ?_ ?_
      · apply c₁.injective
        rw [AddEquiv.apply_symm_apply, Prod.smul_fst, map_nsmul]
        refine Prod.ext rfl ?_
        exact (hF₁ _).symm
      · apply c₂.injective
        rw [Prod.smul_snd, map_nsmul, map_zero]
        refine Prod.ext (Subsingleton.elim _ _) ?_
        exact (hF₂ _).symm

end ZInQ.Manuscript.RC53Assist.CentralSelmer
