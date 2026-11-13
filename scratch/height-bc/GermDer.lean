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

/-- `appLE ⊤ ⊤` is `appTop`. -/
theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app (U := ⊤) f

/-- **Structure sections take the value `τ(r)` at every complex point.** -/
theorem evalAt_structSection {τ : L →+* ℂ} (p : 𝒢.Pts τ) (r : 𝓞 L) :
    𝒢.evalAt p ⊤ (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) =
      τ (algebraMap (𝓞 L) L r) := by
  unfold GroupModel.evalAt
  have h : ⊤ ≤ p.left ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) := fun x _ => trivial
  rw [dif_pos h, appLE_top_top, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have hw : p.left ≫ 𝒢.G.hom = Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))) :=
    Over.w p
  rw [hw]
  have hN := congrArg (fun φ => (ConcreteCategory.hom φ)
      ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))
  refine hN.trans ?_
  erw [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- **Germs in `𝔪_ξ` vanish at the unit complex point.** -/
theorem evalAt_one_eq_zero (τ : L →+* ℂ) (U : 𝒢.G.left.Opens) (hU : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U))
    (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit hU s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.evalAt (1 : 𝒢.Pts τ) U s = 0 := by
  unfold GroupModel.evalAt
  have h : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ U := one_mem_dom 𝒢 τ hU
  rw [dif_pos h]
  have h1 : (1 : 𝒢.Pts τ).left = (GroupModel.ptC τ).hom ≫ 𝒢.unitSection := rfl
  have hgen : genericPt L ∈ 𝒢.unitSection ⁻¹ᵁ U := hU
  have hz : 𝒢.unitSection.app U s = 0 := by
    apply germ_injective_of_isIntegral _ (genericPt L) hgen
    rw [map_zero]
    refine (Scheme.Hom.germ_stalkMap_apply 𝒢.unitSection U (genericPt L) hgen s).symm.trans ?_
    have hfield : IsField ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) := by
      have : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) :=
        (genericPoint_eq_bot_of_affine (CommRingCat.of (𝓞 L))).symm
      rw [this]
      exact Field.toIsField _
    have hloc := map_nonunit (𝒢.unitSection.stalkMap (genericPt L)).hom _
      ((IsLocalRing.mem_maximalIdeal _).mp hs)
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at hloc
    exact hloc
  have h2 : (1 : 𝒢.Pts τ).left.appLE U ⊤ h s =
      ((GroupModel.ptC τ).hom.appLE (𝒢.unitSection ⁻¹ᵁ U) ⊤ h) (𝒢.unitSection.app U s) := by
    have := Scheme.Hom.comp_appLE (GroupModel.ptC τ).hom 𝒢.unitSection U ⊤ h
    exact congrArg (fun φ => (ConcreteCategory.hom φ) s) this
  rw [h2, hz, map_zero]
  exact map_zero _

section Derivation

variable {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}

/-- Germs in `𝔪_ξ` vanish at `0` along `Φ`. -/
theorem germAlong_zero_of_mem (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.germAlong Φ t 0 = 0 := by
  have hs : 𝒢.G.left.presheaf.germ (𝒢.exists_rep t).choose 𝒢.genericUnit
      (𝒢.exists_rep t).choose_spec.choose (𝒢.exists_rep t).choose_spec.choose_spec.choose = t :=
    (𝒢.exists_rep t).choose_spec.choose_spec.choose_spec
  show 𝒢.evalAt (Φ 0) _ _ = 0
  rw [map_zero_of_hom Φ hΦ.1]
  exact evalAt_one_eq_zero τ _ _ _ (hs ▸ ht)

/-- Structure sections are constant `τ(r)` along `Φ` near `0`. -/
theorem germAlong_structMap (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (r : 𝓞 L) :
    𝒢.germAlong Φ (𝒢.structMap r) =ᶠ[nhds 0] fun _ => τ (algebraMap (𝓞 L) L r) := by
  have e1 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  filter_upwards [germAlong_eventuallyEq_rep hΦ _ ⊤ trivial _ e1.symm] with z hz
  rw [hz, evalAt_structSection]

/-- The derivative at `0` of the germ along `Φ`. -/
noncomputable def D0 (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (t : 𝒢.genStalk) : (Fin g → ℂ) →L[ℂ] ℂ :=
  fderiv ℂ (𝒢.germAlong Φ t) 0

theorem D0_add (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    D0 Φ (t₁ + t₂) = D0 Φ t₁ + D0 Φ t₂ := by
  unfold D0
  rw [(germAlong_add_mul hΦ t₁ t₂).1.fderiv_eq]
  exact fderiv_add (germAlong_differentiableAt hΦ t₁) (germAlong_differentiableAt hΦ t₂)

theorem D0_mul (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk) :
    D0 Φ (t₁ * t₂) = 𝒢.germAlong Φ t₁ 0 • D0 Φ t₂ + 𝒢.germAlong Φ t₂ 0 • D0 Φ t₁ := by
  unfold D0
  rw [(germAlong_add_mul hΦ t₁ t₂).2.fderiv_eq]
  exact fderiv_mul (germAlong_differentiableAt hΦ t₁) (germAlong_differentiableAt hΦ t₂)

theorem D0_mul_apply (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (t₁ * t₂) v =
      𝒢.germAlong Φ t₁ 0 * D0 Φ t₂ v + 𝒢.germAlong Φ t₂ 0 * D0 Φ t₁ v := by
  rw [D0_mul hΦ]
  rfl

theorem D0_add_apply (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t₁ t₂ : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (t₁ + t₂) v = D0 Φ t₁ v + D0 Φ t₂ v := by
  rw [D0_add hΦ]
  rfl

theorem D0_structMap_mul (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (r : 𝓞 L) (t : 𝒢.genStalk)
    (v : Fin g → ℂ) : D0 Φ (𝒢.structMap r * t) v = τ (algebraMap (𝓞 L) L r) * D0 Φ t v := by
  rw [D0_mul_apply hΦ]
  have h0 : D0 Φ (𝒢.structMap r) = 0 := by
    unfold D0
    rw [(germAlong_structMap hΦ r).fderiv_eq, fderiv_const_apply]
  rw [h0, (germAlong_structMap hΦ r).eq_of_nhds]
  simp

theorem D0_sq (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x : 𝒢.genStalk)
    (hx : x ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2) (v : Fin g → ℂ) : D0 Φ x v = 0 := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on (C := fun x => D0 Φ x v = 0) hx ?_ ?_
  · intro a ha b hb
    rw [D0_mul_apply hΦ, germAlong_zero_of_mem hΦ a ha, germAlong_zero_of_mem hΦ b hb]
    ring
  · intro x y hx hy
    rw [D0_add_apply hΦ, hx, hy, add_zero]

/-- **`GermDerivation` holds for every analytic uniformization** (proved). -/
theorem germDerivation_at (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) :
    ∃ D : 𝒢.cotangent →+ (Fin g → ℂ),
      (∀ (r : 𝓞 L) x, D (r • x) = τ (algebraMap (𝓞 L) L r) • D x) ∧
      ∀ (t : IsLocalRing.maximalIdeal 𝒢.genStalk) (j : Fin g),
        D (𝒢.dCls t) j = fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1) := by
  let 𝔪 := IsLocalRing.maximalIdeal 𝒢.genStalk
  let D1 : 𝔪 → (Fin g → ℂ) := fun t j => D0 Φ (t : 𝒢.genStalk) (Pi.single j 1)
  have hD1add : ∀ a b : 𝔪, D1 (a + b) = D1 a + D1 b := by
    intro a b
    funext j
    simp only [D1, Submodule.coe_add, D0_add_apply hΦ, Pi.add_apply]
  have hD1wd : ∀ a b : 𝔪, 𝔪.toCotangent a = 𝔪.toCotangent b → D1 a = D1 b := by
    intro a b hab
    rw [Ideal.toCotangent_eq] at hab
    have this : D0 Φ (a : 𝒢.genStalk) = D0 Φ ((a : 𝒢.genStalk) - b) + D0 Φ (b : 𝒢.genStalk) := by
      rw [← D0_add hΦ, sub_add_cancel]
    funext j
    simp only [D1]
    rw [this, ContinuousLinearMap.add_apply, D0_sq hΦ _ hab, zero_add]
  let sec : 𝒢.cotangent → 𝔪 := Function.surjInv (𝔪.toCotangent_surjective)
  have hsec : ∀ x : 𝒢.cotangent, 𝔪.toCotangent (sec x) = x :=
    Function.surjInv_eq _
  let D : 𝒢.cotangent →+ (Fin g → ℂ) :=
    { toFun := fun x => D1 (sec x)
      map_zero' := by
        have : D1 (sec 0) = D1 0 := hD1wd _ _ (by rw [hsec, map_zero]; rfl)
        rw [this]
        have h00 : D0 Φ (0 : 𝒢.genStalk) = 0 := by
          have := D0_add hΦ (0 : 𝒢.genStalk) 0
          rw [add_zero] at this
          exact add_eq_left.mp this.symm
        funext j
        simp [D1, h00]
      map_add' := fun x y => by
        show D1 (sec (x + y)) = D1 (sec x) + D1 (sec y)
        rw [← hD1add]
        exact hD1wd _ _ (by rw [hsec, map_add, hsec, hsec]; rfl) }
  have hD : ∀ t : 𝔪, D (𝔪.toCotangent t) = D1 t := fun t => hD1wd _ _ (hsec _)
  refine ⟨D, fun r x => ?_, fun t j => ?_⟩
  · obtain ⟨t, rfl⟩ := 𝔪.toCotangent_surjective x
    have hrx : r • 𝒢.dCls t = 𝔪.toCotangent (𝒢.structMap r • t) := by
      show 𝒢.structMap r • 𝔪.toCotangent t = _
      rw [LinearMap.map_smul]
    show D (r • 𝒢.dCls t) = _ • D (𝒢.dCls t)
    rw [hrx]
    show D (𝔪.toCotangent _) = _ • D (𝔪.toCotangent t)
    rw [hD, hD]
    funext j
    simp only [D1, SetLike.val_smul, smul_eq_mul, Pi.smul_apply]
    rw [D0_structMap_mul hΦ]
  · show D (𝔪.toCotangent t) j = _
    rw [hD]
    rfl

end Derivation

end GermDer

end ZInQ.HeightBC
