import ZInQKernel.HDecomp.Faltings.Leaves

/-! # height-bc: towards `GermDerivation` (the differential at the origin along `Φ`) -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

section GermDer

variable {K : Type} [Field K] {A : AbVar K}

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) Restriction does not change values
at points that land in the smaller open. -/
theorem evalAt_res {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens}
    (i : W ⟶ U) (hp : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U s = 𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) := by
  unfold GroupModel.evalAt
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hp.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  rw [dif_pos hU, dif_pos hp]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem ptC_hom_apply {L : Type} [Field L] [NumberField L] (τ : L →+* ℂ) (x : PrimeSpectrum ℂ) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  change PrimeSpectrum.comap (τ.comp (algebraMap (𝓞 L) L)) x = _
  haveI := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  show τ (algebraMap (𝓞 L) L a) ∈ x.asIdeal ↔ a ∈ (⊥ : Ideal (𝓞 L))
  rw [hx, Ideal.mem_bot, Ideal.mem_bot, map_eq_zero_iff _ τ.injective]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem one_mem_dom {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)
    (τ : L →+* ℂ) {W : 𝒢.G.left.Opens}
    (hW : 𝒢.genericUnit ∈ W) : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x ∈ W
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  show (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left ((GroupModel.ptC τ).hom x) ∈ W
  have hx : (GroupModel.ptC (L := L) τ).hom x = genericPt L := ptC_hom_apply τ x
  rw [hx]
  exact hW

/-- (copied from `scratch/h5-glue/H5Final.lean`, proved there) -/
theorem map_zero_of_hom {G : Type*} [Group G] {g : ℕ} (Φ : (Fin g → ℂ) → G)
    (h : ∀ z w, Φ (z + w) = Φ z * Φ w) : Φ 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact (mul_eq_left.mp this.symm)

variable {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L)

/-- Values at a point of `V(ℂ)` are additive in the section. -/
theorem evalAt_add {τ : L →+* ℂ} (p : 𝒢.Pts τ) (V : 𝒢.G.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ V)
    (r₁ r₂ : Γ(𝒢.G.left, V)) : 𝒢.evalAt p V (r₁ + r₂) = 𝒢.evalAt p V r₁ + 𝒢.evalAt p V r₂ := by
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp, dif_pos hp, map_add]
  exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _

/-- Values at a point of `V(ℂ)` are multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (V : 𝒢.G.left.Opens) (hp : ⊤ ≤ p.left ⁻¹ᵁ V)
    (r₁ r₂ : Γ(𝒢.G.left, V)) : 𝒢.evalAt p V (r₁ * r₂) = 𝒢.evalAt p V r₁ * 𝒢.evalAt p V r₂ := by
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp, dif_pos hp, map_mul]
  exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _

variable {𝒢}

/-- **Any representative computes the germ along `Φ` near `0`.** -/
theorem germAlong_eventuallyEq_rep {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (V : 𝒢.G.left.Opens) (mV : 𝒢.genericUnit ∈ V) (r : Γ(𝒢.G.left, V))
    (ht : 𝒢.G.left.presheaf.germ V 𝒢.genericUnit mV r = t) :
    𝒢.germAlong Φ t =ᶠ[nhds 0] fun z => 𝒢.evalAt (Φ z) V r := by
  obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
  set U := (𝒢.exists_rep t).choose
  set m := (𝒢.exists_rep t).choose_spec.choose
  set s := (𝒢.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  have heq : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s =
      𝒢.G.left.presheaf.germ V 𝒢.genericUnit mV r := by rw [hs, ht]
  obtain ⟨W, mW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ m mV _ _ heq
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  filter_upwards [hnhds] with z hz
  show 𝒢.evalAt (Φ z) U s = 𝒢.evalAt (Φ z) V r
  rw [evalAt_res 𝒢 (Φ z) iU hz, hW, ← evalAt_res 𝒢 (Φ z) iV hz]

/-- The germ along `Φ` is differentiable at `0`. -/
theorem germAlong_differentiableAt {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk) :
    DifferentiableAt ℂ (𝒢.germAlong Φ t) 0 := by
  obtain ⟨V, mV, r, hr⟩ := 𝒢.exists_rep t
  have hev := germAlong_eventuallyEq_rep hΦ t V mV r hr
  obtain ⟨hmul, -, -, hopen, hdiff⟩ := hΦ
  have h0 : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ V := by
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ V
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mV
  have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) V r) 0 :=
    (hdiff V r).differentiableAt ((hopen V).mem_nhds h0)
  exact hev.differentiableAt_iff.mpr hd

/-- **Eventual additivity and multiplicativity of germs along `Φ`.** -/
theorem germAlong_add_mul {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    (𝒢.germAlong Φ (t₁ + t₂) =ᶠ[nhds 0] fun z => 𝒢.germAlong Φ t₁ z + 𝒢.germAlong Φ t₂ z) ∧
      (𝒢.germAlong Φ (t₁ * t₂) =ᶠ[nhds 0] fun z => 𝒢.germAlong Φ t₁ z * 𝒢.germAlong Φ t₂ z) := by
  obtain ⟨V₁, m₁, r₁, h₁⟩ := 𝒢.exists_rep t₁
  obtain ⟨V₂, m₂, r₂, h₂⟩ := 𝒢.exists_rep t₂
  have e₁ := germAlong_eventuallyEq_rep hΦ t₁ V₁ m₁ r₁ h₁
  have e₂ := germAlong_eventuallyEq_rep hΦ t₂ V₂ m₂ r₂ h₂
  set W := V₁ ⊓ V₂
  have mW : 𝒢.genericUnit ∈ W := ⟨m₁, m₂⟩
  let i₁ : W ⟶ V₁ := homOfLE inf_le_left
  let i₂ : W ⟶ V₂ := homOfLE inf_le_right
  let ρ₁ := 𝒢.G.left.presheaf.map i₁.op r₁
  let ρ₂ := 𝒢.G.left.presheaf.map i₂.op r₂
  have g₁ : 𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW ρ₁ = t₁ := by
    rw [TopCat.Presheaf.germ_res_apply]; exact h₁
  have g₂ : 𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW ρ₂ = t₂ := by
    rw [TopCat.Presheaf.germ_res_apply]; exact h₂
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  constructor
  · have eS := germAlong_eventuallyEq_rep hΦ (t₁ + t₂) W mW (ρ₁ + ρ₂)
      (by rw [map_add, g₁, g₂])
    filter_upwards [eS, e₁, e₂, hnhds] with z hS hz₁ hz₂ hz
    rw [hS, hz₁, hz₂, evalAt_add 𝒢 (Φ z) W hz, evalAt_res 𝒢 (Φ z) i₁ hz r₁,
      evalAt_res 𝒢 (Φ z) i₂ hz r₂]
  · have eP := germAlong_eventuallyEq_rep hΦ (t₁ * t₂) W mW (ρ₁ * ρ₂)
      (by rw [map_mul, g₁, g₂])
    filter_upwards [eP, e₁, e₂, hnhds] with z hP hz₁ hz₂ hz
    rw [hP, hz₁, hz₂, evalAt_mul 𝒢 (Φ z) W hz, evalAt_res 𝒢 (Φ z) i₁ hz r₁,
      evalAt_res 𝒢 (Φ z) i₂ hz r₂]

end GermDer

end ZInQ.HeightBC
