
/-! ## metrization: clause (iii) of `JacDetMultilinear` (scaling by `τ(a)`), proved -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section Scalar

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `evalAt` is multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s * s') = 𝒢.evalAt p U s * 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- A function from `𝓞_L` evaluates to `τ(a)` at every complex point. -/
theorem evalAt_structSection {τ : L →+* ℂ} (p : 𝒢.Pts τ) (a : 𝓞 L) :
    𝒢.evalAt p ⊤ (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      τ (algebraMap (𝓞 L) L a) := by
  have htop : ⊤ ≤ p.left ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) := fun x _ => trivial
  unfold GroupModel.evalAt
  rw [dif_pos htop]
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have h1 : p.left.appLE ⊤ ⊤ htop = p.left.appTop := Scheme.Hom.appLE_eq_app p.left
  have h2 : (p.left.appTop) (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      ((p.left ≫ 𝒢.G.hom).appTop) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [h1, h2, hw]
  have h3 := congrArg (fun f => f ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))
  simp only [ConcreteCategory.comp_apply] at h3
  refine h3.trans ?_
  simp

/-- `germAlong Φ (structMap a * x) = τ(a) · germAlong Φ x` near `0`. -/
theorem germAlong_structMap_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (a : 𝓞 L)
    (x : 𝒢.genStalk) :
    𝒢.germAlong Φ (𝒢.structMap a * x) =ᶠ[𝓝 0]
      fun z => τ (algebraMap (𝓞 L) L a) * 𝒢.germAlong Φ x z := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  set σa : Γ(𝒢.G.left, ⊤) :=
    𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) with hσa
  have hprod : 𝒢.structMap a * 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s =
      𝒢.G.left.presheaf.germ U 𝒢.genericUnit m
        (𝒢.G.left.presheaf.map (homOfLE le_top).op σa * s) := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply]
    rfl
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ U m _, germAlong_eventuallyEq 𝒢 hΦ U m s,
    (hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m)] with z h1 h2 hz
  rw [h1, h2, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz, hσa, evalAt_structSection]

/-- **Clause (iii) of `JacDetMultilinear`, proved: scaling by `τ(a)`.** -/
theorem jacDet_update_smul {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
    (x : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
      τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((𝒢.structMap a • x : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      τ (algebraMap (𝓞 L) L a) • row (x : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_smul, smul_eq_mul, Pi.smul_apply]
    rw [(germAlong_structMap_mul_eventuallyEq 𝒢 hΦ a _).fderiv_eq,
      fderiv_const_mul (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, hrow, Matrix.det_updateRow_smul]

end Scalar

/-- **Glue (the last clause of `JacDetMultilinear`: class invariance).** `jacDet Φ f` depends
only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`. Why true: by `germAlong_eventuallyEq` and
`germAlong_add_eventuallyEq` it suffices that `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`, a sum of
products `uv` with `u, v ∈ 𝔪_ξ`; `germAlong Φ (uv) = (germAlong Φ u)(germAlong Φ v)` near `0` (as
for sums, with `evalAt_mul`), and `germAlong Φ u` vanishes at `0` because the identity point
`Spec ℂ → 𝒢` lies over `ξ` (`one_left_apply`) and induces a local map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ`,
which kills `𝔪_ξ`; then Leibniz. Unproved (needs `evalAt` through `Scheme.Hom.stalkMap` at the
identity point). -/
def JacDetClassInvariant : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f'

/-- **`JacDetClassScalar` from `JacDetClassInvariant` (proved).** -/
theorem jacDetClassScalar_of (h : JacDetClassInvariant) : JacDetClassScalar := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  exact ⟨h K A L 𝒢 τ g Λ Φ hΦ, fun f i a x => jacDet_update_smul 𝒢 hΦ f i a x⟩

end ZInQ.Metrization

#print axioms ZInQ.Metrization.evalAt_structSection
#print axioms ZInQ.Metrization.jacDet_update_smul
#print axioms ZInQ.Metrization.jacDetClassScalar_of
