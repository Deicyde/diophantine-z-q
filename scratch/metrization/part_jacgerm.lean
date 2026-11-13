
/-! ## metrization: two of the four clauses of `JacDetMultilinear`, proved

`Φ 0 = 1` lies over `ξ` (`zero_mem_dom`); `germAlong Φ t` agrees near `0` with `z ↦ evalAt (Φ z) U s`
for every representative `(U, s)` of `t` (`germAlong_eventuallyEq`); hence slot additivity
(`jacDet_update_add`). Vanishing on equal slots is immediate (`jacDet_eq_zero_of_eq`). What
remains is `JacDetClassScalar` (clauses (i) and (iii)). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section Germ

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec ℂ → Spec 𝓞_L` (via `τ`) hits the generic point. -/
theorem ptC_hom_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  haveI : x.asIdeal.IsPrime := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal
  apply PrimeSpectrum.ext
  show Ideal.comap (τ.comp (algebraMap (𝓞 L) L)) x.asIdeal = ⊥
  rw [hx]
  exact Ideal.comap_bot_of_injective _
    (τ.injective.comp (IsFractionRing.injective (𝓞 L) L))

/-- The identity complex point lies over `ξ`. -/
theorem one_left_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (1 : 𝒢.Pts τ).left x = 𝒢.genericUnit := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x = 𝒢.unitSection (genericPt L)
  rw [Over.comp_left]
  change (η[𝒢.G]).left ((toUnit (GroupModel.ptC (L := L) τ)).left x) = _
  rw [hw, ptC_hom_apply]
  rfl

/-- For an analytic uniformization, `0 ∈ dom Φ U` whenever `ξ ∈ U`. -/
theorem zero_mem_dom {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := by
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  show ⊤ ≤ (Φ 0).left ⁻¹ᵁ U
  rw [h1]
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ U
  erw [one_left_apply]
  exact m

/-- `evalAt` is compatible with restriction. -/
theorem evalAt_res {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens} (i : W ⟶ U)
    (hW : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) = 𝒢.evalAt p U s := by
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hW.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  unfold GroupModel.evalAt
  rw [dif_pos hW, dif_pos hU, ← Scheme.Hom.map_appLE p.left hW i.op]
  rfl

/-- `evalAt` is additive in the section. -/
theorem evalAt_add {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s + s') = 𝒢.evalAt p U s + 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- **`germAlong Φ t` is, near `0`, the function of any representative of `t`.** -/
theorem germAlong_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) (s : Γ(𝒢.G.left, U)) :
    𝒢.germAlong Φ (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s) =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) U s := by
  unfold GroupModel.germAlong
  obtain ⟨W, mW, i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit _ m _ s
    (𝒢.exists_rep (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s)).choose_spec.choose_spec.choose_spec
  filter_upwards [(hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz
  rw [← evalAt_res 𝒢 (Φ z) i₁ hz, ← evalAt_res 𝒢 (Φ z) i₂ hz s, hW]

/-- `germAlong Φ t` is differentiable at `0`. -/
theorem germAlong_differentiableAt {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk) :
    DifferentiableAt ℂ (𝒢.germAlong Φ t) 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep t
  have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) U s) 0 :=
    (hΦ.2.2.2.2 U s).differentiableAt ((hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m))
  exact hd.congr_of_eventuallyEq (germAlong_eventuallyEq 𝒢 hΦ U m s)

/-- `germAlong Φ (x + y) = germAlong Φ x + germAlong Φ y` near `0`. -/
theorem germAlong_add_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x + y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x + 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hsum : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s +
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s +
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_add, TopCat.Presheaf.germ_res_apply]
  rw [hsum]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.add_apply, h1, h2, h3, evalAt_add, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- **Clause (ii) of `JacDetMultilinear`, proved: slot additivity.** -/
theorem jacDet_update_add {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
    (x y : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (x + y)) =
      𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((x + y : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      row (x : 𝒢.genStalk) + row (y : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_add, Pi.add_apply]
    rw [(germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _)]
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
  rw [e, e, e, hrow, Matrix.det_updateRow_add]

/-- **Clause (iv) of `JacDetMultilinear`, proved: equal slots give `0`.** -/
theorem jacDet_eq_zero_of_eq {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g) (h : f i = f j)
    (hij : i ≠ j) : 𝒢.jacDet Φ f = 0 := by
  unfold GroupModel.jacDet
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp [h]

end Germ

/-- **Glue (the two remaining clauses of `JacDetMultilinear`).** (i) `jacDet Φ f` depends only on
the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`; (iii) multiplying slot `i` by the image of `a ∈ 𝓞_L` multiplies
`jacDet` by `τ(a)`. Why true: by `germAlong_eventuallyEq` it suffices that for `f ∈ 𝔪_ξ²` the
function `evalAt (Φ z) U s` of a representative has derivative `0` at `0` (it is a sum of products
of functions vanishing at `0`, as evaluation at a complex point over `ξ` kills `𝔪_ξ`: the induced
map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ` is local), and that the image of `a` evaluates to `τ(a)` (the point
lies over `Spec 𝓞_L` through `τ`). Unproved: needs `evalAt` through `Scheme.Hom.stalkMap` and
`ΓSpecIso`. -/
def JacDetClassScalar : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x))

/-- **`JacDetMultilinear` from `JacDetClassScalar` (proved).** -/
theorem jacDetMultilinear_of (h : JacDetClassScalar) : JacDetMultilinear := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨h1, h3⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  exact ⟨h1, fun f i x y => jacDet_update_add 𝒢 hΦ f i x y, h3,
    fun f i j hij hne => jacDet_eq_zero_of_eq 𝒢 Φ f i j hij hne⟩

end ZInQ.Metrization

#print axioms ZInQ.Metrization.zero_mem_dom
#print axioms ZInQ.Metrization.germAlong_eventuallyEq
#print axioms ZInQ.Metrization.jacDet_update_add
#print axioms ZInQ.Metrization.jacDetMultilinear_of
