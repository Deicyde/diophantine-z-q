import ZInQKernel.HDecomp.Faltings.HodgeLattice

/-! # unif-dims: `DetLatticeProd` (determinant lattice of a direct sum), proof attempt -/

namespace ZInQ.UnifDims

open NumberField TensorProduct ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice
open scoped nonZeroDivisors

section Line

variable {K : Type} [Field K] [NumberField K]
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M]

/-- The determinant functional `K ⊗ ⋀^g M → K` of a `K`-basis of `K ⊗ M`. -/
noncomputable def detFun {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) :
    (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) →ₗ[K] K :=
  (exteriorPower.alternatingMapLinearEquiv
    ({ toMultilinearMap := (b.det.toMultilinearMap.restrictScalars (𝓞 K)).compLinearMap
          (fun _ => TensorProduct.mk (𝓞 K) K M 1)
       map_eq_zero_of_eq' := fun v i j hv hij =>
          b.det.map_eq_zero_of_eq (fun k => (1 : K) ⊗ₜ[𝓞 K] v k) (by simp [hv]) hij } :
      M [⋀^Fin g]→ₗ[𝓞 K] K)).liftBaseChange K

theorem detFun_tmul {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) (v : Fin g → M) :
    detFun b ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g v) =
      b.det (fun k => (1 : K) ⊗ₜ[𝓞 K] v k) := by
  simp only [detFun, LinearMap.liftBaseChange_one_tmul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The determinant functional of a basis `1 ⊗ wⱼ` is injective (the Hodge space is the line
spanned by `1 ⊗ ∧w`); steps 2-4 of hodge-lattice's `hodgeLattice_of_lattice`. -/
theorem detFun_injective {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) (w : Fin g → M)
    (hbw : ∀ j, (1 : K) ⊗ₜ[𝓞 K] w j = b j) : Function.Injective (detFun b) := by
  have hclear := exists_clear (K := K) w (fun v => by
    have hr : Set.range (fun j => (1 : K) ⊗ₜ[𝓞 K] w j) = Set.range b := by
      rw [show (fun j => (1 : K) ⊗ₜ[𝓞 K] w j) = b from funext hbw]
    rw [hr, b.span_eq]; exact Submodule.mem_top)
  set s0 : K ⊗[𝓞 K] ⋀[𝓞 K]^g M := (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g w with hs0
  have hone : ∀ x : ⋀[𝓞 K]^g M, (1 : K) ⊗ₜ[𝓞 K] x ∈ Submodule.span K {s0} := by
    intro x
    have hx : x ∈ Submodule.span (𝓞 K) (Set.range (exteriorPower.ιMulti (𝓞 K) g)) := by
      rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact tmul_ιMulti_mem_span w hclear v
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ r hy
  have htop : Submodule.span K {s0} = ⊤ := by
    rw [eq_top_iff]
    rintro h -
    induction h using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul k x =>
      have : k ⊗ₜ[𝓞 K] x = k • ((1 : K) ⊗ₜ[𝓞 K] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ k (hone x)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have hΨ : detFun b s0 = 1 := by
    rw [hs0, detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] w k) = b from funext hbw,
      Module.Basis.det_self]
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have : x ∈ Submodule.span K {s0} := htop ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp this
  rw [LinearMap.mem_ker, map_smul, hΨ, smul_eq_mul, mul_one] at hx
  rw [hx, zero_smul]
  exact Submodule.zero_mem _

/-- Step 1 of hodge-lattice's `hodgeLattice_of_lattice`: a `K`-basis of `K ⊗ M` of the form
`1 ⊗ wⱼ` with `wⱼ ∈ ω`. -/
theorem exists_basis_of_span {g : ℕ} (ω : Submodule (𝓞 K) M)
    (hrank : Module.rank K (K ⊗[𝓞 K] M) = g)
    (hspan : Submodule.span K (Set.range fun x : ω => (1 : K) ⊗ₜ[𝓞 K] (x : M)) = ⊤) :
    ∃ (w : Fin g → ω) (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)),
      ∀ j, (1 : K) ⊗ₜ[𝓞 K] (w j : M) = b j := by
  classical
  set V := K ⊗[𝓞 K] M
  set f : ω → V := fun x => (1 : K) ⊗ₜ[𝓞 K] (x : M) with hf
  have : FiniteDimensional K V := Module.finite_of_rank_eq_nat hrank
  have hfin : Module.finrank K V = g := Module.finrank_eq_of_rank_eq hrank
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range f)
  let bs : Module.Basis s K V := Module.Basis.mk hs_li (by
    rw [Subtype.range_coe, hs_span, hspan])
  let b : Module.Basis (Fin g) K V :=
    bs.reindex (bs.indexEquiv (Module.finBasisOfFinrankEq K V hfin))
  have hmem : ∀ j, ∃ x : ω, f x = b j := fun j => by
    have : (b j : V) ∈ s := by
      simp only [b, Module.Basis.reindex_apply, bs, Module.Basis.coe_mk]
      exact Subtype.mem _
    exact hs_sub this
  choose w hw using hmem
  exact ⟨w, b, hw⟩

/-- `secIndex` is invariant under an injective `K`-linear map. -/
theorem secIndex_map {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (Ψ : V →ₗ[K] K) (hΨ : Function.Injective Ψ)
    (Λ : Submodule (𝓞 K) V) (s : V) :
    secIndex Λ s = secIndex (Λ.map (Ψ.restrictScalars (𝓞 K))) (Ψ s) := by
  unfold secIndex
  have hspan : Submodule.map (Ψ.restrictScalars (𝓞 K)) (Submodule.span (𝓞 K) {s}) =
      Submodule.span (𝓞 K) {Ψ s} := by
    rw [Submodule.map_span, Set.image_singleton]; rfl
  rw [← hspan, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact (AddSubgroup.relIndex_map_map_of_injective _ _
    (f := ((Ψ.restrictScalars (𝓞 K)) : V →+ K)) hΨ).symm

/-- **Indices of `1` multiply** in a product of finitely generated `𝓞_K`-submodules of `K`
containing `1` (through `FractionalIdeal.absNorm` and the kernel's `secIndex_mul_absNorm`). -/
theorem secIndex_one_mul (I J : Submodule (𝓞 K) K) (hI : I.FG) (hJ : J.FG) (h1I : (1 : K) ∈ I)
    (h1J : (1 : K) ∈ J) : secIndex (I * J) 1 = secIndex I 1 * secIndex J 1 := by
  let I' : FractionalIdeal (𝓞 K)⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  let J' : FractionalIdeal (𝓞 K)⁰ K := ⟨J, FractionalIdeal.isFractional_of_fg hJ⟩
  have hIJ : ((I' * J' : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = I * J :=
    FractionalIdeal.coe_mul _ _
  have h1 : (1 : K) ∈ (I' * J' : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.mem_coe, hIJ, ← mul_one (1 : K)]
    exact Submodule.mul_mem_mul h1I h1J
  have e1 := secIndex_mul_absNorm I' h1I one_ne_zero
  have e2 := secIndex_mul_absNorm J' h1J one_ne_zero
  have e3 := secIndex_mul_absNorm (I' * J') h1 one_ne_zero
  rw [hIJ] at e3
  simp only [map_one, abs_one, map_mul] at e1 e2 e3
  have : (secIndex (I * J) 1 : ℚ) = secIndex I 1 * secIndex J 1 := by
    have hI0 : FractionalIdeal.absNorm I' ≠ 0 := by
      intro h; rw [h, mul_zero] at e1; exact zero_ne_one e1
    have hJ0 : FractionalIdeal.absNorm J' ≠ 0 := by
      intro h; rw [h, mul_zero] at e2; exact zero_ne_one e2
    change (secIndex (I * J) 1 : ℚ) * (FractionalIdeal.absNorm I' * FractionalIdeal.absNorm J')
      = 1 at e3
    change (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I' = 1 at e1
    change (secIndex J 1 : ℚ) * FractionalIdeal.absNorm J' = 1 at e2
    linear_combination (-(secIndex (I * J) 1 : ℚ)) * e1 +
      (-(secIndex (I * J) 1 : ℚ) * secIndex I 1 * FractionalIdeal.absNorm I') * e2 +
      ((secIndex I 1 : ℚ) * secIndex J 1) * e3
  exact_mod_cast this

end Line


section Prod

variable {K : Type} [Field K] [NumberField K]
variable {M₁ M₂ M : Type} [AddCommGroup M₁] [Module (𝓞 K) M₁] [AddCommGroup M₂] [Module (𝓞 K) M₂]
  [AddCommGroup M] [Module (𝓞 K) M]

/-- `K ⊗ M₁ × K ⊗ M₂ ≃ K ⊗ M` from `M₁ × M₂ ≃ M`. -/
noncomputable def sumIso (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) :
    ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M) :=
  (TensorProduct.prodRight (𝓞 K) K K M₁ M₂).symm ≪≫ₗ
    LinearEquiv.baseChange (𝓞 K) K _ _ (LinearEquiv.ofBijective _ hbij)

theorem sumIso_inl (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) (m : M₁) :
    sumIso j₁ j₂ hbij ((1 : K) ⊗ₜ[𝓞 K] m, 0) = (1 : K) ⊗ₜ[𝓞 K] j₁ m := by
  simp only [sumIso, LinearEquiv.trans_apply]
  rw [show ((1 : K) ⊗ₜ[𝓞 K] m, (0 : K ⊗[𝓞 K] M₂)) = ((1 : K) ⊗ₜ m, (1 : K) ⊗ₜ (0 : M₂)) by
    rw [tmul_zero], prodRight_symm_tmul]
  simp [LinearEquiv.baseChange, AlgebraTensorModule.congr_tmul]

theorem sumIso_inr (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) (m : M₂) :
    sumIso j₁ j₂ hbij (0, (1 : K) ⊗ₜ[𝓞 K] m) = (1 : K) ⊗ₜ[𝓞 K] j₂ m := by
  simp only [sumIso, LinearEquiv.trans_apply]
  rw [show ((0 : K ⊗[𝓞 K] M₁), (1 : K) ⊗ₜ[𝓞 K] m) = ((1 : K) ⊗ₜ (0 : M₁), (1 : K) ⊗ₜ m) by
    rw [tmul_zero], prodRight_symm_tmul]
  simp [LinearEquiv.baseChange, AlgebraTensorModule.congr_tmul]

/-- The concatenated basis of `K ⊗ M`. -/
noncomputable def prodBasis {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M)) :
    Module.Basis (Fin (g₁ + g₂)) K (K ⊗[𝓞 K] M) :=
  ((b₁.prod b₂).map E).reindex finSumFinEquiv

theorem prodBasis_castAdd {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M)) (i : Fin g₁) :
    prodBasis b₁ b₂ E (Fin.castAdd g₂ i) = E (b₁ i, 0) := by
  simp [prodBasis, Module.Basis.prod_apply]

theorem prodBasis_natAdd {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M)) (i : Fin g₂) :
    prodBasis b₁ b₂ E (Fin.natAdd g₁ i) = E (0, b₂ i) := by
  simp [prodBasis, Module.Basis.prod_apply]

/-- **Block determinant.** -/
theorem det_prodBasis_append {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M))
    (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hE1 : ∀ m, E ((1 : K) ⊗ₜ[𝓞 K] m, 0) = (1 : K) ⊗ₜ[𝓞 K] j₁ m)
    (hE2 : ∀ m, E (0, (1 : K) ⊗ₜ[𝓞 K] m) = (1 : K) ⊗ₜ[𝓞 K] j₂ m)
    (u : Fin g₁ → M₁) (v : Fin g₂ → M₂) :
    (prodBasis b₁ b₂ E).det (fun k => (1 : K) ⊗ₜ[𝓞 K] Fin.append (j₁ ∘ u) (j₂ ∘ v) k) =
      b₁.det (fun i => (1 : K) ⊗ₜ[𝓞 K] u i) * b₂.det (fun j => (1 : K) ⊗ₜ[𝓞 K] v j) := by
  have h1 : ∀ m, E.symm ((1 : K) ⊗ₜ[𝓞 K] j₁ m) = ((1 : K) ⊗ₜ m, 0) := fun m => by
    rw [LinearEquiv.symm_apply_eq, hE1]
  have h2 : ∀ m, E.symm ((1 : K) ⊗ₜ[𝓞 K] j₂ m) = (0, (1 : K) ⊗ₜ m) := fun m => by
    rw [LinearEquiv.symm_apply_eq, hE2]
  rw [prodBasis, Module.Basis.det_reindex, Module.Basis.det_map, Module.Basis.det_apply,
    Module.Basis.det_apply, Module.Basis.det_apply]
  have hM : (b₁.prod b₂).toMatrix (⇑E.symm ∘
      (fun k => (1 : K) ⊗ₜ[𝓞 K] Fin.append (j₁ ∘ u) (j₂ ∘ v) k) ∘ ⇑finSumFinEquiv) =
      Matrix.fromBlocks (b₁.toMatrix (fun i => (1 : K) ⊗ₜ[𝓞 K] u i)) 0 0
        (b₂.toMatrix (fun j => (1 : K) ⊗ₜ[𝓞 K] v j)) := by
    ext (i | i) (j | j) <;>
      simp [Module.Basis.toMatrix_apply, Matrix.fromBlocks, h1, h2,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr]
  rw [hM, Matrix.det_fromBlocks_zero₂₁]

/-- A linearly independent family inside the range of a map from a space of dimension `n` has
at most `n` members. -/
theorem card_le_of_li_range {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [FiniteDimensional K V] [FiniteDimensional K W] (J : V →ₗ[K] W) {ι : Type*}
    [Fintype ι] (F : ι → W) (hF : LinearIndependent K F) (hr : ∀ i, F i ∈ LinearMap.range J) :
    Fintype.card ι ≤ Module.finrank K V := by
  rw [linearIndependent_iff_card_eq_finrank_span.mp hF]
  calc Module.finrank K (Submodule.span K (Set.range F))
      ≤ Module.finrank K (LinearMap.range J) :=
        Submodule.finrank_mono (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hr i))
    _ ≤ _ := LinearMap.finrank_range_le J

end Prod

/-- **`DetLatticeProd`, proved** (the statement is the body of `ZInQ.UnifDims.DetLatticeProd`). -/
theorem detLatticeProd_aux :
  ∀ (K : Type) [Field K] [NumberField K] (M₁ M₂ M : Type) [AddCommGroup M₁] [Module (𝓞 K) M₁]
    [AddCommGroup M₂] [Module (𝓞 K) M₂] [AddCommGroup M] [Module (𝓞 K) M]
    (ω₁ : Submodule (𝓞 K) M₁) (ω₂ : Submodule (𝓞 K) M₂) (j₁ : M₁ →ₗ[𝓞 K] M)
    (j₂ : M₂ →ₗ[𝓞 K] M) (g₁ g₂ : ℕ),
    Function.Bijective (LinearMap.coprod j₁ j₂) → ω₁.FG → ω₂.FG →
    Module.rank K (K ⊗[𝓞 K] M₁) = g₁ → Module.rank K (K ⊗[𝓞 K] M₂) = g₂ →
    Submodule.span K (Set.range fun x : ω₁ => (1 : K) ⊗ₜ[𝓞 K] (x : M₁)) = ⊤ →
    Submodule.span K (Set.range fun x : ω₂ => (1 : K) ⊗ₜ[𝓞 K] (x : M₂)) = ⊤ →
    ∃ (x₁ : Fin g₁ → M₁) (x₂ : Fin g₂ → M₂) (a₁ a₂ : K),
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ∈ detLat ω₁ g₁ ∧
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ≠ 0 ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ∈ detLat ω₂ g₂ ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ≠ 0 ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ∈ detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂) ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ≠ 0 ∧
      secIndex (detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂))
          ((a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
            (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂)))) =
        secIndex (detLat ω₁ g₁) (a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁)) *
          secIndex (detLat ω₂ g₂) (a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂)) := by
  intro K _ _ M₁ M₂ M _ _ _ _ _ _ ω₁ ω₂ j₁ j₂ g₁ g₂ hbij hfg₁ hfg₂ hr₁ hr₂ hsp₁ hsp₂
  classical
  have : FiniteDimensional K (K ⊗[𝓞 K] M₁) := Module.finite_of_rank_eq_nat hr₁
  have : FiniteDimensional K (K ⊗[𝓞 K] M₂) := Module.finite_of_rank_eq_nat hr₂
  obtain ⟨w₁, b₁, hb₁⟩ := exists_basis_of_span ω₁ hr₁ hsp₁
  obtain ⟨w₂, b₂, hb₂⟩ := exists_basis_of_span ω₂ hr₂ hsp₂
  set E := sumIso (K := K) j₁ j₂ hbij
  have hE1 : ∀ m, E ((1 : K) ⊗ₜ[𝓞 K] m, 0) = (1 : K) ⊗ₜ[𝓞 K] j₁ m := sumIso_inl j₁ j₂ hbij
  have hE2 : ∀ m, E (0, (1 : K) ⊗ₜ[𝓞 K] m) = (1 : K) ⊗ₜ[𝓞 K] j₂ m := sumIso_inr j₁ j₂ hbij
  set b := prodBasis b₁ b₂ E
  have : FiniteDimensional K (K ⊗[𝓞 K] M) := Module.Basis.finiteDimensional_of_finite b
  set x₁ : Fin g₁ → M₁ := fun i => (w₁ i : M₁)
  set x₂ : Fin g₂ → M₂ := fun i => (w₂ i : M₂)
  set y : Fin (g₁ + g₂) → M := Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂) with hy
  have hb : ∀ k, (1 : K) ⊗ₜ[𝓞 K] y k = b k := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [prodBasis_castAdd, ← hb₁, hE1, hy, Fin.append_left]; rfl
    · rw [prodBasis_natAdd, ← hb₂, hE2, hy, Fin.append_right]; rfl
  set ω := ω₁.map j₁ ⊔ ω₂.map j₂ with hω
  have hi₁ := detFun_injective b₁ x₁ hb₁
  have hi₂ := detFun_injective b₂ x₂ hb₂
  have hi := detFun_injective b y hb
  set I₁ := (detLat ω₁ g₁).map ((detFun b₁).restrictScalars (𝓞 K)) with hI₁
  set I₂ := (detLat ω₂ g₂).map ((detFun b₂).restrictScalars (𝓞 K)) with hI₂
  set I := (detLat ω (g₁ + g₂)).map ((detFun b).restrictScalars (𝓞 K)) with hI
  have hblock := det_prodBasis_append b₁ b₂ E j₁ j₂ hE1 hE2
  have happ : ∀ (u : Fin g₁ → ω₁) (v : Fin g₂ → ω₂) (k : Fin (g₁ + g₂)),
      Fin.append (j₁ ∘ fun i => (u i : M₁)) (j₂ ∘ fun i => (v i : M₂)) k ∈ ω := by
    intro u v k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]
      exact Submodule.mem_sup_left (Submodule.mem_map_of_mem (u i).2)
    · rw [Fin.append_right]
      exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (v i).2)
  have hgen₁ : ∀ u : Fin g₁ → ω₁, b₁.det (fun i => (1 : K) ⊗ₜ[𝓞 K] (u i : M₁)) ∈ I₁ := by
    intro u
    rw [← detFun_tmul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, rfl⟩)
  have hgen₂ : ∀ u : Fin g₂ → ω₂, b₂.det (fun i => (1 : K) ⊗ₜ[𝓞 K] (u i : M₂)) ∈ I₂ := by
    intro u
    rw [← detFun_tmul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, rfl⟩)
  have hge : I₁ * I₂ ≤ I := by
    rw [hI₁, hI₂, detLat, detLat, Submodule.map_span, Submodule.map_span, Submodule.span_mul_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨_, ⟨u, rfl⟩, rfl⟩, _, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩
    simp only [LinearMap.coe_restrictScalars]
    rw [detFun_tmul, detFun_tmul, ← hblock, ← detFun_tmul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨fun k => ⟨_, happ u v k⟩, rfl⟩)
  have hle : I ≤ I₁ * I₂ := by
    rw [hI, detLat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    have hdec : ∀ k, ∃ (a : ω₁) (c : ω₂), (v k : M) = j₁ a + j₂ c := fun k => by
      obtain ⟨y', hy', z, hz, hyz⟩ := Submodule.mem_sup.mp (v k).2
      obtain ⟨a, ha, rfl⟩ := hy'
      obtain ⟨c, hc, rfl⟩ := hz
      exact ⟨⟨a, ha⟩, ⟨c, hc⟩, hyz.symm⟩
    choose a c hac using hdec
    simp only [SetLike.mem_coe, LinearMap.coe_restrictScalars]
    rw [detFun_tmul]
    have hsplit : (fun k => (1 : K) ⊗ₜ[𝓞 K] (v k : M)) = fun k =>
        (1 : K) ⊗ₜ[𝓞 K] j₁ (a k) + (1 : K) ⊗ₜ[𝓞 K] j₂ (c k) := funext fun k => by
      rw [hac, tmul_add]
    rw [hsplit]
    have hexp := (b.det : (K ⊗[𝓞 K] M) [⋀^Fin (g₁ + g₂)]→ₗ[K] K).toMultilinearMap.map_add_univ
      (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k)) (fun k => (1 : K) ⊗ₜ[𝓞 K] j₂ (c k))
    simp only [AlternatingMap.coe_multilinearMap] at hexp
    rw [show (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k) + (1 : K) ⊗ₜ[𝓞 K] j₂ (c k)) =
      (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k)) + (fun k => (1 : K) ⊗ₜ[𝓞 K] j₂ (c k)) from rfl, hexp]
    refine Submodule.sum_mem _ fun T _ => ?_
    set F := T.piecewise (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k)) (fun k => (1 : K) ⊗ₜ[𝓞 K] j₂ (c k))
      with hF
    show b.det F ∈ _
    by_cases hT : T.card = g₁
    · have hTc : Tᶜ.card = g₂ := by rw [Finset.card_compl, Fintype.card_fin, hT]; omega
      let e1 := T.orderIsoOfFin hT
      let e2 := Tᶜ.orderIsoOfFin hTc
      let σ : Equiv.Perm (Fin (g₁ + g₂)) := finSumFinEquiv.symm.trans
        ((Equiv.sumCongr e1.toEquiv
          (e2.toEquiv.trans (Equiv.subtypeEquivRight (fun x => Finset.mem_compl)))).trans
          (Equiv.sumCompl (· ∈ T)))
      have hσ1 : ∀ i, σ (Fin.castAdd g₂ i) = (e1 i : Fin (g₁ + g₂)) := by
        intro i; simp [σ]
      have hσ2 : ∀ i, σ (Fin.natAdd g₁ i) = (e2 i : Fin (g₁ + g₂)) := by
        intro i; simp [σ]
      have hFσ : F ∘ σ = fun k => (1 : K) ⊗ₜ[𝓞 K] Fin.append (j₁ ∘ fun i => ((a (e1 i)) : M₁))
          (j₂ ∘ fun i => ((c (e2 i)) : M₂)) k := by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k
        · rw [Function.comp_apply, hσ1, Fin.append_left, hF,
            Finset.piecewise_eq_of_mem _ _ _ (e1 i).2]
          rfl
        · rw [Function.comp_apply, hσ2, Fin.append_right, hF,
            Finset.piecewise_eq_of_notMem _ _ _ (Finset.mem_compl.mp (e2 i).2)]
          rfl
      have key : b.det F = (Equiv.Perm.sign σ) • b.det (F ∘ σ) := by
        rw [AlternatingMap.map_perm, smul_smul, Int.units_mul_self, one_smul]
      rw [key, hFσ, hblock]
      have hm := Submodule.mul_mem_mul (hgen₁ fun i => a (e1 i)) (hgen₂ fun i => c (e2 i))
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h, one_smul]; exact hm
      · rw [h, Units.neg_smul, one_smul]; exact neg_mem hm
    · have hnli : ¬ LinearIndependent K F := by
        intro hli
        have h1 : T.card ≤ g₁ := by
          have := card_le_of_li_range (E.toLinearMap ∘ₗ LinearMap.inl K _ _)
            (fun k : T => F k) (hli.comp _ Subtype.val_injective) (fun k =>
              ⟨(1 : K) ⊗ₜ[𝓞 K] (a k : M₁), by
                simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe, hE1]
                rw [hF, Finset.piecewise_eq_of_mem _ _ _ k.2]⟩)
          rwa [Fintype.card_coe, Module.finrank_eq_of_rank_eq hr₁] at this
        have h2 : Tᶜ.card ≤ g₂ := by
          have := card_le_of_li_range (E.toLinearMap ∘ₗ LinearMap.inr K _ _)
            (fun k : (Tᶜ : Finset _) => F k) (hli.comp _ Subtype.val_injective) (fun k =>
              ⟨(1 : K) ⊗ₜ[𝓞 K] (c k : M₂), by
                simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_coe, hE2]
                rw [hF, Finset.piecewise_eq_of_notMem _ _ _ (Finset.mem_compl.mp k.2)]⟩)
          rwa [Fintype.card_coe, Module.finrank_eq_of_rank_eq hr₂] at this
        have h3 : T.card + Tᶜ.card = g₁ + g₂ := by
          rw [Finset.card_add_card_compl, Fintype.card_fin]
        omega
      rw [b.det.map_linearDependent F hnli]
      exact Submodule.zero_mem _
  have hIP : I = I₁ * I₂ := le_antisymm hle hge
  have hΨ1 : detFun b₁ ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) = 1 := by
    rw [detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] x₁ k) = b₁ from funext hb₁,
      Module.Basis.det_self]
  have hΨ2 : detFun b₂ ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) = 1 := by
    rw [detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] x₂ k) = b₂ from funext hb₂,
      Module.Basis.det_self]
  have hΨ : detFun b ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂) y) = 1 := by
    rw [detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] y k) = b from funext hb,
      Module.Basis.det_self]
  have hm₁ : (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁ ∈ detLat ω₁ g₁ :=
    Submodule.subset_span ⟨w₁, rfl⟩
  have hm₂ : (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂ ∈ detLat ω₂ g₂ :=
    Submodule.subset_span ⟨w₂, rfl⟩
  have hm : (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂) y ∈ detLat ω (g₁ + g₂) :=
    Submodule.subset_span ⟨fun k => ⟨y k, happ w₁ w₂ k⟩, rfl⟩
  have h1I₁ : (1 : K) ∈ I₁ := hΨ1 ▸ Submodule.mem_map_of_mem hm₁
  have h1I₂ : (1 : K) ∈ I₂ := hΨ2 ▸ Submodule.mem_map_of_mem hm₂
  have hne : ∀ {V : Type} [AddCommGroup V] [Module K V] (Ψ : V →ₗ[K] K) (s : V), Ψ s = 1 →
      s ≠ 0 := fun Ψ s h hs => by rw [hs, map_zero] at h; exact zero_ne_one h
  refine ⟨x₁, x₂, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [one_smul]; exact hm₁
  · rw [one_smul]; exact hne _ _ hΨ1
  · rw [one_smul]; exact hm₂
  · rw [one_smul]; exact hne _ _ hΨ2
  · rw [mul_one, one_smul]; exact hm
  · rw [mul_one, one_smul]; exact hne _ _ hΨ
  · rw [mul_one, one_smul, one_smul, one_smul, secIndex_map _ hi, secIndex_map _ hi₁,
      secIndex_map _ hi₂, hΨ, hΨ1, hΨ2]
    change secIndex I 1 = secIndex I₁ 1 * secIndex I₂ 1
    rw [hIP]
    exact secIndex_one_mul I₁ I₂ ((detLat_fg ω₁ hfg₁ g₁).map _) ((detLat_fg ω₂ hfg₂ g₂).map _)
      h1I₁ h1I₂

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.detFun_injective
#print axioms ZInQ.UnifDims.secIndex_map
#print axioms ZInQ.UnifDims.secIndex_one_mul
#print axioms ZInQ.UnifDims.det_prodBasis_append
#print axioms ZInQ.UnifDims.detLatticeProd_aux
