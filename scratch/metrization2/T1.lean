import MetrBase
/-! ## metrization2: `JacDetNondegenerate` from the local structure of morphisms out of a product

Step 1 (linear algebra): if every `jacDet Φ f` vanishes, some `v ≠ 0` is killed by
`d(germAlong Φ t)(0)` for every `t ∈ 𝔪_ξ`. Step 2: then by every regular function near `ξ`
(subtract the pull-back along `𝒢 → Spec 𝓞_L` of its restriction to the unit section). -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

/-- Step 1 (pure linear algebra). If every `g × g` matrix whose rows are taken from a family
`F` of vectors of `ℂ^g` has determinant `0`, a nonzero vector is orthogonal (for the bilinear
pairing `Σ_j x_j y_j`) to every member of the family. -/
theorem exists_null_of_det_eq_zero {J : Type*} {g : ℕ} (F : J → (Fin g → ℂ))
    (h : ∀ f : Fin g → J, (Matrix.of fun i j => F (f i) j).det = 0) :
    ∃ v : Fin g → ℂ, v ≠ 0 ∧ ∀ i, ∑ j, F i j * v j = 0 := by
  by_cases hW : Submodule.span ℂ (Set.range F) = ⊤
  · exfalso
    obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ F
    rw [hW] at hspan
    have : Finite κ := hli.finite
    haveI := Fintype.ofFinite κ
    have hcard : Fintype.card κ = g := by
      rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hspan, finrank_top,
        Module.finrank_fin_fun]
    let eqv : Fin g ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    have hli' : LinearIndependent ℂ ((F ∘ a) ∘ eqv) := hli.comp eqv eqv.injective
    have hU : IsUnit (Matrix.of fun i j => F (a (eqv i)) j) :=
      Matrix.linearIndependent_row_iff_isUnit.mp hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero (h (a ∘ eqv))
  · obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hW)
    refine ⟨fun j => φ (fun k => if j = k then 1 else 0), ?_, ?_⟩
    · intro hv
      apply hφ0
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp only [LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrFun hv j
      simp only [Pi.zero_apply] at this
      rw [this, smul_zero]
    · intro i
      have h1 := hle (Submodule.subset_span ⟨i, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [smul_eq_mul] using h1

section Eval

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- The value at the complex point `Spec ℂ → Spec 𝓞_L` (via `τ`) of a function on an open of
`Spec 𝓞_L` (`0` off the open). -/
noncomputable def baseVal (τ : L →+* ℂ) (O : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (x : Γ(Spec (CommRingCat.of (𝓞 L)), O)) : ℂ := by
  classical
  exact if h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((GroupModel.ptC (L := L) τ).hom.appLE O ⊤ h x)
  else 0

/-- A function pulled back from `Spec 𝓞_L` takes the same value at every complex point. -/
theorem evalAt_pullback_base {τ : L →+* ℂ} (p : 𝒢.Pts τ) (O : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (x : Γ(Spec (CommRingCat.of (𝓞 L)), O)) :
    𝒢.evalAt p (𝒢.G.hom ⁻¹ᵁ O) (𝒢.G.hom.app O x) = baseVal τ O x := by
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have hpre : p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) = (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O := by
    rw [← hw]; rfl
  unfold GroupModel.evalAt baseVal
  by_cases h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O
  · have h' : ⊤ ≤ p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) := hpre ▸ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have key : ∀ (f : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (𝓞 L)))
        (hf : f = (GroupModel.ptC (L := L) τ).hom) (e : ⊤ ≤ f ⁻¹ᵁ O),
        f.appLE O ⊤ e x = (GroupModel.ptC (L := L) τ).hom.appLE O ⊤ h x := by
      rintro f rfl e; rfl
    have h'' : ⊤ ≤ (p.left ≫ 𝒢.G.hom) ⁻¹ᵁ O := h'
    refine Eq.trans ?_ (key _ hw h'')
    have hc := Scheme.Hom.comp_appLE p.left 𝒢.G.hom O ⊤ h''
    exact congrArg (fun φ => (ConcreteCategory.hom φ) x) hc.symm
  · have h' : ¬ ⊤ ≤ p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) := fun h' => h (hpre ▸ h')
    rw [dif_neg h', dif_neg h]

/-- A complex point factoring as `Spec ℂ → Spec 𝓞_L → 𝒢` evaluates through the section. -/
theorem evalAt_of_left_eq {τ : L →+* ℂ} (p : 𝒢.Pts τ)
    (f : Spec (CommRingCat.of (𝓞 L)) ⟶ 𝒢.G.left) (hp : p.left = (GroupModel.ptC τ).hom ≫ f)
    (V : 𝒢.G.left.Opens) (b : Γ(𝒢.G.left, V)) :
    𝒢.evalAt p V b = baseVal τ (f ⁻¹ᵁ V) (f.app V b) := by
  have hpre : p.left ⁻¹ᵁ V = (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [hp]; rfl
  unfold GroupModel.evalAt baseVal
  by_cases h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ (f ⁻¹ᵁ V)
  · have h' : ⊤ ≤ p.left ⁻¹ᵁ V := hpre ▸ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have key : ∀ (q : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left)
        (hq : q = (GroupModel.ptC (L := L) τ).hom ≫ f) (e : ⊤ ≤ q ⁻¹ᵁ V),
        q.appLE V ⊤ e b = ((GroupModel.ptC (L := L) τ).hom ≫ f).appLE V ⊤ h b := by
      rintro q rfl e; rfl
    refine (key _ hp h').trans ?_
    have hc := Scheme.Hom.comp_appLE (GroupModel.ptC (L := L) τ).hom f V ⊤ h
    exact congrArg (fun φ => (ConcreteCategory.hom φ) b) hc
  · have h' : ¬ ⊤ ≤ p.left ⁻¹ᵁ V := fun h' => h (hpre ▸ h')
    rw [dif_neg h', dif_neg h]

/-- `(1 : 𝒢(ℂ)_τ)` is `Spec ℂ → Spec 𝓞_L → 𝒢` through the unit section. -/
theorem one_left_eq (τ : L →+* ℂ) :
    (1 : 𝒢.Pts τ).left = (GroupModel.ptC τ).hom ≫ 𝒢.unitSection := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left = _
  rw [Over.comp_left, hw]
  rfl

/-- The unit section is a section of the structure map. -/
theorem unitSection_comp_hom : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  show (η[𝒢.G] : 𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))) ⟶ 𝒢.G).left ≫ 𝒢.G.hom = 𝟙 _
  rw [Over.w]
  rfl

theorem one_mem_dom (τ : L →+* ℂ) (W : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ W) :
    ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ W
  erw [one_left_apply]
  exact m

theorem evalAt_sub {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s - s') = 𝒢.evalAt p U s - 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_sub]
    exact map_sub (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem evalAt_one_sec {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (h : ⊤ ≤ p.left ⁻¹ᵁ U) :
    𝒢.evalAt p U 1 = 1 := by
  unfold GroupModel.evalAt
  rw [dif_pos h, map_one]
  exact map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)

/-- A section vanishing at the identity complex point has its germ at `ξ` in `𝔪_ξ`. -/
theorem germ_mem_of_evalAt_one {τ : L →+* ℂ} (W : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ W)
    (s : Γ(𝒢.G.left, W)) (h : 𝒢.evalAt (1 : 𝒢.Pts τ) W s = 0) :
    𝒢.G.left.presheaf.germ W 𝒢.genericUnit m s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  by_contra hn
  obtain ⟨u, hu⟩ := (IsLocalRing.notMem_maximalIdeal.mp hn).exists_right_inv
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep u
  have mm : 𝒢.genericUnit ∈ W ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hg : 𝒢.G.left.presheaf.germ (W ⊓ U') 𝒢.genericUnit mm
      (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s *
        𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') =
      𝒢.G.left.presheaf.germ (W ⊓ U') 𝒢.genericUnit mm 1 := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hu, map_one]
  obtain ⟨W'', m'', i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit mm mm _ _ hg
  have hd := one_mem_dom 𝒢 τ W'' m''
  have e1 := congrArg (𝒢.evalAt (1 : 𝒢.Pts τ) W'') hW
  rw [map_mul, map_one, evalAt_mul, evalAt_one_sec 𝒢 _ _ hd, evalAt_res 𝒢 _ _ hd,
    evalAt_res 𝒢 _ _ hd] at e1
  rw [evalAt_res 𝒢 (1 : 𝒢.Pts τ) (homOfLE inf_le_left)
    ((one_mem_dom 𝒢 τ _ mm)) s, h, zero_mul] at e1
  exact zero_ne_one e1

end Eval

end ZInQ.Metrization2
/-! ## metrization2: the glue Prop, step 2 (all regular functions) and step 3 (translation) -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

/-- **Glue (local structure of a morphism out of a fibre product, at complex points).** For group
models `𝒢₁`, `𝒢₂`, `ℋ` over `𝓞_L`, a morphism `m : 𝒢₁ ×_{𝓞_L} 𝒢₂ → ℋ` of `𝓞_L`-schemes, an open
`U ⊆ ℋ`, `s ∈ Γ(U, 𝒪_ℋ)` and complex points `p₁`, `p₂` with `m(p₁, p₂) ∈ U(ℂ)`: there are opens
`Vᵢ ∋ pᵢ` and regular functions `a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that
`H = Σ c_k(·) d_k(·)` is nonzero at `(p₁, p₂)` and, wherever `H(p₁', p₂') ≠ 0` on
`V₁(ℂ) × V₂(ℂ)`, `m(p₁', p₂') ∈ U(ℂ)` and `s(m(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`.
Why true (STANDARD; pure scheme theory, no analysis): take affine opens `Vᵢ = Spec Rᵢ ∋ pᵢ`;
`V₁ ×_{𝓞_L} V₂ = Spec (R₁ ⊗_{𝓞_L} R₂)` is an open of the product (Mathlib: `pullbackSpecIso`);
choose a basic open `D(h) ∋ (p₁, p₂)` inside `m⁻¹(U) ∩ (V₁ × V₂)`; on it `m^*s = a / h^N`; write
`h^N = Σ c_k ⊗ d_k`, `a = Σ a_k ⊗ b_k`; a complex point `(p₁', p₂')` of `V₁ × V₂` is the ring map
`r₁ ⊗ r₂ ↦ r₁(p₁') r₂(p₂')`, and it lies in `D(h)` iff `h^N(p₁', p₂') ≠ 0`.
Special cases: `m = e.inv` for `e : 𝒢P ≅ 𝒢₁ × 𝒢₂` is metrization's `ProductLocalStructure`
(`productLocalStructure_of`); `m = μ` (the group law) gives `JacDetNondegenerate`
(`jacDetNondegenerate_of`). -/
def ProductMapLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (ℋ : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (m : 𝒢₁.G ⊗ 𝒢₂.G ⟶ ℋ.G) (τ : L →+* ℂ) (U : ℋ.G.left.Opens) (s : Γ(ℋ.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ m).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ m).left ⁻¹ᵁ U ∧
        ℋ.evalAt (lift p₁' p₂' ≫ m) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)

/-- `ProductMapLocalStructure` contains metrization's `ProductLocalStructure` (`m = e.inv`). -/
theorem productLocalStructure_of (h : ProductMapLocalStructure) :
    ZInQ.Metrization.ProductLocalStructure := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e τ U s p₁ p₂ hp
  exact h K A B C L 𝒢P 𝒢₁ 𝒢₂ e.inv τ U s p₁ p₂ hp

section Steps

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem hom_genericUnit : 𝒢.G.hom 𝒢.genericUnit = genericPt L := by
  show 𝒢.G.hom (𝒢.unitSection (genericPt L)) = genericPt L
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]
  rfl

/-- Step 2. If `d(germAlong Φ t)(0)` kills `v` for every `t ∈ 𝔪_ξ`, then the differential at `0`
of `z ↦ b(Φ z)` kills `v` for every regular function `b` near `ξ`. -/
theorem fderiv_evalAt_apply_eq_zero {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (v : Fin g → ℂ)
    (hv : ∀ t : IsLocalRing.maximalIdeal 𝒢.genStalk,
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 v = 0)
    (V : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)) :
    fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0 := by
  set O := 𝒢.unitSection ⁻¹ᵁ V with hO
  set c : Γ(𝒢.G.left, 𝒢.G.hom ⁻¹ᵁ O) := 𝒢.G.hom.app O (𝒢.unitSection.app V b) with hc
  have mO : 𝒢.genericUnit ∈ 𝒢.G.hom ⁻¹ᵁ O := by
    show 𝒢.unitSection (𝒢.G.hom 𝒢.genericUnit) ∈ V
    rw [hom_genericUnit]
    exact m
  set W := V ⊓ 𝒢.G.hom ⁻¹ᵁ O with hW
  have mW : 𝒢.genericUnit ∈ W := TopologicalSpace.Opens.mem_inf.mpr ⟨m, mO⟩
  set b' : Γ(𝒢.G.left, W) := 𝒢.G.left.presheaf.map (homOfLE inf_le_left).op b -
    𝒢.G.left.presheaf.map (homOfLE inf_le_right).op c with hb'
  have h1 : 𝒢.evalAt (1 : 𝒢.Pts τ) W b' = 0 := by
    have hd := one_mem_dom 𝒢 τ W mW
    rw [hb', evalAt_sub, evalAt_res 𝒢 _ _ hd, evalAt_res 𝒢 _ _ hd,
      evalAt_of_left_eq 𝒢 1 𝒢.unitSection (one_left_eq 𝒢 τ) V b, hc, evalAt_pullback_base,
      sub_self]
  have hgerm := germ_mem_of_evalAt_one 𝒢 W mW b' h1
  have hv' := hv ⟨_, hgerm⟩
  have heq : 𝒢.germAlong Φ (𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW b') =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) V b - baseVal τ O (𝒢.unitSection.app V b) := by
    filter_upwards [germAlong_eventuallyEq 𝒢 hΦ W mW b',
      (hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz1 hz
    rw [hz1, hb', evalAt_sub, evalAt_res 𝒢 _ _ hz, evalAt_res 𝒢 _ _ hz, hc,
      evalAt_pullback_base]
  simp only at hv'
  rw [heq.fderiv_eq, fderiv_sub_const] at hv'
  exact hv'

/-- Step 3 (translation). If every regular function near `ξ` has `d(b ∘ Φ)(0) v = 0`, then for
every regular function `s` on `U` and every `w ∈ Φ⁻¹(U(ℂ))`, `t ↦ s(Φ(w + t v))` has derivative
`0` at `t = 0`: near `0`, `s(Φ w · Φ z) = N(z)/D(z)` with `N`, `D` combinations of regular
functions near `ξ` along `Φ` (`ProductMapLocalStructure` for the group law `μ`). -/
theorem hasDerivAt_line_zero (hML : ProductMapLocalStructure) {τ : L →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (v : Fin g → ℂ)
    (hv2 : ∀ (V : 𝒢.G.left.Opens) (_ : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)),
      fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0)
    (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) (w : Fin g → ℂ) (hw : w ∈ 𝒢.dom Φ U) :
    HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (w + t • v)) U s) 0 0 := by
  have h0 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  have hmul : ∀ z, lift (Φ w) (Φ z) ≫ μ[𝒢.G] = Φ (w + z) := fun z => (hΦ.1 w z).symm
  have hU' : ⊤ ≤ (lift (Φ w) (Φ 0) ≫ μ[𝒢.G]).left ⁻¹ᵁ U := by
    rw [hmul, add_zero]; exact hw
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    hML K A A A L 𝒢 𝒢 𝒢 μ[𝒢.G] τ U s (Φ w) (Φ 0) hU'
  have mV₂ : 𝒢.genericUnit ∈ V₂ := by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of ℂ)) := inferInstance
    have hx := hV₂ (show x ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
    change (Φ 0).left x ∈ V₂ at hx
    rw [h0] at hx
    erw [one_left_apply] at hx
    exact hx
  set Nf : (Fin g → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢.evalAt (Φ w) V₁ (a k) * 𝒢.evalAt (Φ z) V₂ (b k) with hNf
  set Df : (Fin g → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢.evalAt (Φ w) V₁ (c k) * 𝒢.evalAt (Φ z) V₂ (d k) with hDf
  have hdom2 : IsOpen (𝒢.dom Φ V₂) := hΦ.2.2.2.1 V₂
  have h0dom : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ V₂ := hV₂
  have hDcont : ContinuousOn Df (𝒢.dom Φ V₂) := by
    have : DifferentiableOn ℂ Df (𝒢.dom Φ V₂) := by
      simp only [hDf]
      exact DifferentiableOn.fun_sum fun k _ =>
        (hΦ.2.2.2.2 V₂ (d k)).const_mul _
    exact this.continuousOn
  set O := 𝒢.dom Φ V₂ ∩ Df ⁻¹' {0}ᶜ with hO
  have hOopen : IsOpen O := hDcont.isOpen_inter_preimage hdom2 isOpen_compl_singleton
  have hD0 : Df 0 ≠ 0 := hne
  have h0O : (0 : Fin g → ℂ) ∈ O := ⟨h0dom, hD0⟩
  -- derivative along the line of each regular function near `ξ`
  have hline : ∀ (bb : Γ(𝒢.G.left, V₂)),
      HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) V₂ bb) 0 0 := by
    intro bb
    have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) V₂ bb) 0 :=
      (hΦ.2.2.2.2 V₂ bb).differentiableAt (hdom2.mem_nhds h0dom)
    have hF : HasFDerivAt (fun z => 𝒢.evalAt (Φ z) V₂ bb)
        (fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V₂ bb) 0) ((0 : ℂ) • v) := by
      rw [zero_smul]; exact hd.hasFDerivAt
    have := hF.comp_hasDerivAt (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).smul_const v)
    simp only [one_smul, hv2 V₂ mV₂ bb] at this
    exact this
  have hN : HasDerivAt (fun t : ℂ => Nf (t • v)) 0 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hline (b k)).const_mul (𝒢.evalAt (Φ w) V₁ (a k))
    simpa [hNf] using this
  have hD : HasDerivAt (fun t : ℂ => Df (t • v)) 0 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hline (d k)).const_mul (𝒢.evalAt (Φ w) V₁ (c k))
    simpa [hDf] using this
  have hD0' : Df ((0 : ℂ) • v) ≠ 0 := by rw [zero_smul]; exact hD0
  have hq := hN.div hD hD0'
  simp only [zero_mul, mul_zero, sub_zero, zero_div] at hq
  refine hq.congr_of_eventuallyEq ?_
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ O :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hOopen.mem_nhds h0O)
  filter_upwards [hev] with t ht
  obtain ⟨-, heq⟩ := hall (Φ w) (Φ (t • v)) hV₁ ht.1 ht.2
  rw [hmul] at heq
  exact eq_div_of_mul_eq ht.2 heq

end Steps

end ZInQ.Metrization2
#print axioms ZInQ.Metrization2.hasDerivAt_line_zero
