import ZInQKernel.HDecomp.Faltings.H5Neron

/-! # product-height: the glue Prop `ProductModelHeight` (P2)

Task product-height. Imports only the kernel module `ZInQKernel.HDecomp.Faltings.H5Neron`
(no scratch import). No `sorry`, no `axiom`. See `docs/research/product-height.md`.

Contents.
* §0 A verbatim copy of `ProductModelHeight` (from `scratch/h5-neron/H5Neron.lean`, identical to
  `scratch/h5-glue/H5Final.lean` and to the kernel's `ZInQ.H5Neron.ProductModelHeight`) with the
  definitions it uses, and `copy_iff : Copy.ProductModelHeight ↔ H5Neron.ProductModelHeight`
  (`Iff.rfl`), so that everything below is about the same Prop.
* §1 Route S (new, no `AnalyticUniformizationUnique`): `ProductModelHeight` from one glue Prop
  `ProductMetrizationSplit` (every metrization of a product model splits into metrizations of the
  factors whose heights add up to at most its height).
* §2 Route U (g0-heightadd's reduction, ported to the kernel's types): `ProductModelHeight` from
  `AnalyticUniformizationUnique`, `MetrizationDimUnique`, `MetrizationExists`,
  `ProductMetrizationGeo`; and the sharper form with the single Prop `MetrizationHeightUnique`
  in place of the first two.
* §3 Route U implies route S (`productMetrizationSplit_of`): the two routes are consistent, and S
  is no stronger than the inputs of U.
* §4 What `ProductModelHeight` forces (the necessity argument, formal part):
  `metrizable_left_of_productModelHeight`, `metrizable_right_of_productModelHeight`: a metrization
  of the product forces metrizations of the factors. And `le_of_productModelHeight`: every single
  metrization of the product is bounded below by the sum of the factor heights. -/

namespace ZInQ.ProductHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings
open PkgI3 (AbVar)

/-! ## §0. Verbatim copy (from `scratch/h5-neron/H5Neron.lean`) -/

namespace Copy

section General

variable {S S' : Scheme.{0}} (j : S' ⟶ S) (P : Over S → Prop)

variable {j P}

/-- The identification of the generic fibre of `N₁ ⊗ N₂` with `A₁ ⊗ A₂`. -/
noncomputable def tensorGen {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (Over.pullback j).obj (N₁ ⊗ N₂) ≅ A₁ ⊗ A₂ :=
  prodComparisonIso (Over.pullback j) N₁ N₂ ≪≫ tensorIso e₁ e₂

end General

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

variable {K : Type} [Field K]

/-- `C_L ≅ A_L ⊗ B_L`. -/
noncomputable def bcProd {A B C : AbVar K} (L : Type) [Field L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) : (C.baseChange L).X ≅ (A.baseChange L).X ⊗ (B.baseChange L).X :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso eC ≪≫
    prodComparisonIso (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))) A.X B.X

/-- `𝒢P ≅ 𝒢₁ × 𝒢₂` as group models of `C_L ≅ A_L × B_L`. -/
def IsProductModel {A B C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) :
    Prop :=
  ∃ e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G, IsMonHom (e.hom ≫ fst _ _) ∧ IsMonHom (e.hom ≫ snd _ _) ∧
    (Over.pullback (jL L)).map e.hom ≫ (tensorGen 𝒢₁.gen 𝒢₂.gen).hom =
      𝒢P.gen.hom ≫ (bcProd L eC).hom

/-- **Glue P2** (the direction used). The height of a product model is at least the sum of the
heights: `ω_{𝒢₁×𝒢₂} = ω_{𝒢₁} ⊕ ω_{𝒢₂}`, `det(ω₁ ⊕ ω₂) = det ω₁ ⊗ det ω₂`, the Arakelov degree is
additive, and a product of uniformizations is a uniformization of the product (equality holds). -/
def ProductModelHeight : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ → 𝒢₁.height + 𝒢₂.height ≤ 𝒢P.height

end Copy

/-- The copy is the kernel's Prop (definitional equality). -/
theorem copy_iff : Copy.ProductModelHeight ↔ H5Neron.ProductModelHeight := Iff.rfl

open H5Neron

/-! ## Basic facts about `GroupModel.height` -/

section Basic

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A metrization bounds the height of its model from above. -/
theorem height_le_of_model {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L}
    (h : M.model = 𝒢) : 𝒢.height ≤ (M.hodge.modelHeight : EReal) :=
  iInf_le_of_le g (iInf_le_of_le M (iInf_le_of_le h le_rfl))

/-- A group model without metrization has height `⊤`. -/
theorem height_eq_top_of_not_metrizable {𝒢 : GroupModel A L}
    (h : ¬ ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒢) : 𝒢.height = ⊤ := by
  refine eq_top_iff.mpr (le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_)
  exact absurd ⟨g, M, hM⟩ h

/-- A metrizable group model has height `< ⊤`. -/
theorem height_ne_top_of_model {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L}
    (h : M.model = 𝒢) : 𝒢.height ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (height_le_of_model M h)

end Basic

/-! ## §1. Route S: `ProductModelHeight` from the splitting of metrizations (no AN3-uniqueness) -/

/-- **Glue S (splitting of a metrization of a product model).** If `𝒢P ≅ 𝒢₁ × 𝒢₂`
(`IsProductModel`), then every metrization `MP` of `𝒢P` (of any dimension `g`) yields metrizations
`M₁` of `𝒢₁` and `M₂` of `𝒢₂` with `h(M₁) + h(M₂) ≤ h(MP)`.

Why true (STANDARD; the input is analytic, of type AN3): `g = g₁ + g₂`, and a holomorphic
surjective homomorphism `Φ : ℂ^g → 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` with lattice kernel splits, after a
`ℂ`-linear change of coordinates `T`, as `Φ₁ × Φ₂` (a holomorphic homomorphism of complex tori
lifts to a linear map; Mumford, *Abelian varieties* §1, UNVERIFIED locator). Then
`⋀^{g}ω_{𝒢P} = ⋀^{g₁}ω_{𝒢₁} ⊗ ⋀^{g₂}ω_{𝒢₂}`, the Jacobian is block diagonal and
`covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`, so equality holds (`modelHeight_add_of`). The
algebraic half is the same as in `ProductMetrizationGeo`. Unproved. -/
def ProductMetrizationSplit : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g : ℕ) (MP : MetrizedModel C L g), MP.model = 𝒢P →
      ∃ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
        M₁.model = 𝒢₁ ∧ M₂.model = 𝒢₂ ∧
        M₁.hodge.modelHeight + M₂.hodge.modelHeight ≤ MP.hodge.modelHeight

/-- **`ProductModelHeight` from `ProductMetrizationSplit` alone (proved).** No uniqueness of
uniformizations, no existence of metrizations and no dimension statement is used. -/
theorem productModelHeight_of_split (h : ProductMetrizationSplit) : ProductModelHeight := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hPM
  refine le_iInf fun g => le_iInf fun MP => le_iInf fun hMP => ?_
  obtain ⟨g₁, g₂, M₁, M₂, h₁, h₂, hle⟩ := h K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM g MP hMP
  calc 𝒢₁.height + 𝒢₂.height
      ≤ (M₁.hodge.modelHeight : EReal) + (M₂.hodge.modelHeight : EReal) :=
        add_le_add (height_le_of_model M₁ h₁) (height_le_of_model M₂ h₂)
    _ = ((M₁.hodge.modelHeight + M₂.hodge.modelHeight : ℝ) : EReal) := (EReal.coe_add _ _).symm
    _ ≤ (MP.hodge.modelHeight : EReal) := EReal.coe_le_coe_iff.mpr hle

/-! ## §2. Route U (g0-heightadd's reduction, on the kernel's types)

The four Props `ProductMetrization`, `MetrizationExists`, `MetrizationDimUnique`,
`ProductMetrizationGeo` and the lemmas `modelHeight_add_of`, `productModelHeight_of`,
`productMetrization_of_geo` are copied from `scratch/g0-heightadd/part_heightadd.lean` and
`part_prod.lean` (there over the def-faltings copy `Prefix.lean`); here they are over the kernel's
`PkgI3.AbVar`, `DefFaltings.GroupModel` and `H5Neron.IsProductModel`. Statements unchanged. -/

/-- **Glue P2a (product of metrized models).** If `𝒢P ≅ 𝒢₁ × 𝒢₂` (`IsProductModel`) and `M₁`, `M₂`
are metrizations of `𝒢₁`, `𝒢₂` of dimensions `g₁`, `g₂`, then `𝒢P` has a metrization of
dimension `g₁ + g₂` whose model height is the sum. (Copied from g0-heightadd; STANDARD, unproved:
`ω_{𝒢P} = ω₁ ⊕ ω₂`, `Φ₁ × Φ₂` is a uniformization with lattice `Λ₁ × Λ₂`.) -/
def ProductMetrization : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ → M₂.model = 𝒢₂ →
      ∃ MP : MetrizedModel C L (g₁ + g₂), MP.model = 𝒢P ∧
        MP.hodge.modelHeight = M₁.hodge.modelHeight + M₂.hodge.modelHeight

/-- **Glue (existence of metrizations; correctness of def-faltings' definition).** Every smooth
group model `𝒢` of `A_L` carries a metrization (copied from g0-heightadd; from
`HodgeLatticeTheorem` and `AnalyticUniformizationExists`, AN3-existence; unproved). -/
def MetrizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒢

/-- **Glue (the dimension of a metrization).** Two metrizations of the same group model have
the same dimension (copied from g0-heightadd; both equal `dim A`; unproved). -/
def MetrizationDimUnique : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (g g' : ℕ) (M : MetrizedModel A L g) (M' : MetrizedModel A L g'), M.model = M'.model → g = g'

/-- **Glue H (new; what U and `MetrizationDimUnique` are used for).** Two metrizations of the
same group model (of any dimensions) have the same model height: the height of a group model
does not depend on the choice of analytic uniformization. Follows from
`AnalyticUniformizationUnique` and `MetrizationDimUnique` (`metrizationHeightUnique_of`). -/
def MetrizationHeightUnique : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (g g' : ℕ) (M : MetrizedModel A L g) (M' : MetrizedModel A L g'), M.model = M'.model →
      M.hodge.modelHeight = M'.hodge.modelHeight

/-- `MetrizationHeightUnique` from U and `MetrizationDimUnique` (proved). -/
theorem metrizationHeightUnique_of (hU : AnalyticUniformizationUnique)
    (hD : MetrizationDimUnique) : MetrizationHeightUnique := by
  intro K _ A L _ _ _ g g' M M' h
  obtain rfl := hD K A L g g' M M' h
  exact MetrizedModel.modelHeight_eq_of_model_eq hU M M' h

section HeightOf

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Under `MetrizationHeightUnique`, a metrization computes the height of its model. -/
theorem height_eq_of_model (hH : MetrizationHeightUnique) {g : ℕ} (M : MetrizedModel A L g)
    {𝒢 : GroupModel A L} (h : M.model = 𝒢) : 𝒢.height = (M.hodge.modelHeight : EReal) := by
  refine le_antisymm (height_le_of_model M h) ?_
  refine le_iInf fun g' => le_iInf fun M' => le_iInf fun hM' => ?_
  rw [hH K A L g g' M M' (h.trans hM'.symm)]

/-- Given AN3-uniqueness and `MetrizationDimUnique`, a metrization computes the height of its
model from below (g0-heightadd's lemma). -/
theorem le_height_of_model (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L} (h : M.model = 𝒢) :
    (M.hodge.modelHeight : EReal) ≤ 𝒢.height :=
  (height_eq_of_model (metrizationHeightUnique_of hU hD) M h).ge

end HeightOf

/-- **`ProductModelHeight` from `MetrizationHeightUnique`, `MetrizationExists` and
`ProductMetrization` (proved).** -/
theorem productModelHeight_of_unique (hH : MetrizationHeightUnique) (hE : MetrizationExists)
    (hP : ProductMetrization) : ProductModelHeight := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hPM
  obtain ⟨g₁, M₁, h₁⟩ := hE K A L 𝒢₁
  obtain ⟨g₂, M₂, h₂⟩ := hE K B L 𝒢₂
  obtain ⟨MP, hMP, hh⟩ := hP K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM g₁ g₂ M₁ M₂ h₁ h₂
  rw [height_eq_of_model hH M₁ h₁, height_eq_of_model hH M₂ h₂, height_eq_of_model hH MP hMP,
    hh, EReal.coe_add]

/-- **g0-heightadd's `productModelHeight_of`, on the kernel's types (proved).** -/
theorem productModelHeight_of (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    (hE : MetrizationExists) (hP : ProductMetrization) : ProductModelHeight :=
  productModelHeight_of_unique (metrizationHeightUnique_of hU hD) hE hP

section HodgeAdd

variable {K : Type*} [Field K] [NumberField K]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V₁] [Module K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁]
  [AddCommGroup V₂] [Module K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂]

/-- **Additivity of the model height (copied from g0-heightadd, proved).** If the Hodge data `D`
(dimension `g₁ + g₂`) has a nonzero section `s` whose lattice index, coefficients and period
covolumes are the products of those of nonzero sections `s₁`, `s₂` of `D₁`, `D₂`, then
`h(D) = h(D₁) + h(D₂)`. -/
theorem modelHeight_add_of {g₁ g₂ : ℕ} (D : HodgeData K (g₁ + g₂) V) (D₁ : HodgeData K g₁ V₁)
    (D₂ : HodgeData K g₂ V₂) {s : V} {s₁ : V₁} {s₂ : V₂} (hs : s ∈ D.lattice) (hs0 : s ≠ 0)
    (hs₁ : s₁ ∈ D₁.lattice) (hs₁0 : s₁ ≠ 0) (hs₂ : s₂ ∈ D₂.lattice) (hs₂0 : s₂ ≠ 0)
    (hidx : secIndex D.lattice s = secIndex D₁.lattice s₁ * secIndex D₂.lattice s₂)
    (hcoeff : ∀ σ, D.coeff σ s = D₁.coeff σ s₁ * D₂.coeff σ s₂)
    (hcov : ∀ σ, ZLattice.covolume (D.periods σ) =
      ZLattice.covolume (D₁.periods σ) * ZLattice.covolume (D₂.periods σ)) :
    D.modelHeight = D₁.modelHeight + D₂.modelHeight := by
  rw [D.modelHeight_eq hs hs0, D₁.modelHeight_eq hs₁ hs₁0, D₂.modelHeight_eq hs₂ hs₂0]
  have ht : ∀ σ : K →+* ℂ, torusMetricSq (D.periods σ) (D.coeff σ s) =
      torusMetricSq (D₁.periods σ) (D₁.coeff σ s₁) *
        torusMetricSq (D₂.periods σ) (D₂.coeff σ s₂) := by
    intro σ
    simp only [torusMetricSq, hcoeff σ, hcov σ, norm_mul]
    ring
  have hlog : ∀ σ : K →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ s)) =
      Real.log (torusMetricSq (D₁.periods σ) (D₁.coeff σ s₁)) +
        Real.log (torusMetricSq (D₂.periods σ) (D₂.coeff σ s₂)) := by
    intro σ
    rw [ht σ]
    have := D₁.periods_discrete σ
    have := D₁.periods_isZLattice σ
    have := D₂.periods_discrete σ
    have := D₂.periods_isZLattice σ
    exact Real.log_mul (torusMetricSq_pos _ (D₁.coeff_apply_ne_zero σ hs₁0)).ne'
      (torusMetricSq_pos _ (D₂.coeff_apply_ne_zero σ hs₂0)).ne'
  have hi₁ : (secIndex D₁.lattice s₁ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D₁.hodgeBundle.secIndex_ne_zero hs₁ hs₁0)
  have hi₂ : (secIndex D₂.lattice s₂ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D₂.hodgeBundle.secIndex_ne_zero hs₂ hs₂0)
  rw [hidx, Nat.cast_mul, Real.log_mul hi₁ hi₂, Finset.sum_congr rfl (fun σ _ => hlog σ),
    Finset.sum_add_distrib]
  ring

end HodgeAdd

/-- **Glue P2a-geo (copied from g0-heightadd).** For `𝒢P ≅ 𝒢₁ × 𝒢₂` and metrizations `M₁`, `M₂`,
there is a metrization `MP` of `𝒢P` of dimension `g₁ + g₂` and nonzero sections
`s ∈ ⋀^{g₁+g₂}ω_{𝒢P}`, `sᵢ ∈ ⋀^{gᵢ}ω_{𝒢ᵢ}` whose lattice index, coefficients and period
covolumes multiply (`s = p₁*s₁ ∧ p₂*s₂`, `Φ₁ × Φ₂` with lattice `Λ₁ × Λ₂`; STANDARD, unproved). -/
def ProductMetrizationGeo : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ → M₂.model = 𝒢₂ →
      ∃ (MP : MetrizedModel C L (g₁ + g₂)) (s : MP.model.hodgeSpace (g₁ + g₂))
        (s₁ : M₁.model.hodgeSpace g₁) (s₂ : M₂.model.hodgeSpace g₂),
        MP.model = 𝒢P ∧ s ∈ MP.hodge.lattice ∧ s ≠ 0 ∧ s₁ ∈ M₁.hodge.lattice ∧ s₁ ≠ 0 ∧
        s₂ ∈ M₂.hodge.lattice ∧ s₂ ≠ 0 ∧
        secIndex MP.hodge.lattice s = secIndex M₁.hodge.lattice s₁ * secIndex M₂.hodge.lattice s₂ ∧
        (∀ σ, MP.hodge.coeff σ s = M₁.hodge.coeff σ s₁ * M₂.hodge.coeff σ s₂) ∧
        (∀ σ, ZLattice.covolume (MP.hodge.periods σ) =
          ZLattice.covolume (M₁.hodge.periods σ) * ZLattice.covolume (M₂.hodge.periods σ))

/-- **P2a from P2a-geo (copied from g0-heightadd, proved).** -/
theorem productMetrization_of_geo (h : ProductMetrizationGeo) : ProductMetrization := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  obtain ⟨MP, s, s₁, s₂, hMP, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hc, hcov⟩ :=
    h K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  exact ⟨MP, hMP, modelHeight_add_of MP.hodge M₁.hodge M₂.hodge hs hs0 hs₁ hs₁0 hs₂ hs₂0 hidx hc hcov⟩

/-- **`ProductModelHeight` from U, `MetrizationDimUnique`, `MetrizationExists` and
`ProductMetrizationGeo` (proved).** -/
theorem productModelHeight_of_geo (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    (hE : MetrizationExists) (hG : ProductMetrizationGeo) : ProductModelHeight :=
  productModelHeight_of hU hD hE (productMetrization_of_geo hG)

/-! ## §3. Route U implies route S -/

/-- **`ProductMetrizationSplit` from `MetrizationHeightUnique`, `MetrizationExists` and
`ProductMetrization` (proved).** So S is implied by the inputs of route U. -/
theorem productMetrizationSplit_of (hH : MetrizationHeightUnique) (hE : MetrizationExists)
    (hP : ProductMetrization) : ProductMetrizationSplit := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hPM g MP hMP
  obtain ⟨g₁, M₁, h₁⟩ := hE K A L 𝒢₁
  obtain ⟨g₂, M₂, h₂⟩ := hE K B L 𝒢₂
  obtain ⟨MP', hMP', hh⟩ := hP K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM g₁ g₂ M₁ M₂ h₁ h₂
  refine ⟨g₁, g₂, M₁, M₂, h₁, h₂, ?_⟩
  rw [← hh, hH K C L _ g MP' MP (hMP'.trans hMP.symm)]

/-! ## §4. What `ProductModelHeight` forces

`ProductModelHeight` is not a statement about the algebraic data alone: it forces, from a single
metrization of the product (an analytic uniformization `Φ` of `(𝒢₁ × 𝒢₂)(ℂ)_τ` at every `τ`, with
its Hodge data), the existence of metrizations of each factor, i.e. of analytic uniformizations
of `𝒢₁(ℂ)_τ` with a *discrete* kernel. The composite `p₁ ∘ Φ` is onto but has a non-discrete
kernel; producing a discrete one is the splitting of complex tori (AN3-type input). It also bounds
every single metrization of the product from below, whatever its uniformization. -/

section Forces

variable {K : Type} [Field K] {A B C : AbVar K} {eC : C.X ≅ A.X ⊗ B.X} {L : Type} [Field L]
  [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}

/-- `ProductModelHeight` bounds every single metrization of the product from below. -/
theorem le_of_productModelHeight (h : ProductModelHeight) (hPM : IsProductModel eC 𝒢P 𝒢₁ 𝒢₂)
    {g : ℕ} (MP : MetrizedModel C L g) (hMP : MP.model = 𝒢P) :
    𝒢₁.height + 𝒢₂.height ≤ (MP.hodge.modelHeight : EReal) :=
  (h K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM).trans (height_le_of_model MP hMP)

/-- **`ProductModelHeight` forces metrizations of the left factor** (proved): if the product
model has a metrization and `h(𝒢₂) ≠ ⊥`, then `𝒢₁` has a metrization. -/
theorem metrizable_left_of_productModelHeight (h : ProductModelHeight)
    (hPM : IsProductModel eC 𝒢P 𝒢₁ 𝒢₂) {g : ℕ} (MP : MetrizedModel C L g) (hMP : MP.model = 𝒢P)
    (h₂ : 𝒢₂.height ≠ ⊥) : ∃ (g₁ : ℕ) (M₁ : MetrizedModel A L g₁), M₁.model = 𝒢₁ := by
  by_contra hn
  have h1 := height_eq_top_of_not_metrizable hn
  have key := le_of_productModelHeight h hPM MP hMP
  rw [h1, EReal.top_add_of_ne_bot h₂, top_le_iff] at key
  exact EReal.coe_ne_top _ key

/-- **`ProductModelHeight` forces metrizations of the right factor** (proved). -/
theorem metrizable_right_of_productModelHeight (h : ProductModelHeight)
    (hPM : IsProductModel eC 𝒢P 𝒢₁ 𝒢₂) {g : ℕ} (MP : MetrizedModel C L g) (hMP : MP.model = 𝒢P)
    (h₁ : 𝒢₁.height ≠ ⊥) : ∃ (g₂ : ℕ) (M₂ : MetrizedModel B L g₂), M₂.model = 𝒢₂ := by
  by_contra hn
  have h2 := height_eq_top_of_not_metrizable hn
  have key := le_of_productModelHeight h hPM MP hMP
  rw [h2, EReal.add_top_of_ne_bot h₁, top_le_iff] at key
  exact EReal.coe_ne_top _ key

end Forces

end ZInQ.ProductHeight

#print axioms ZInQ.ProductHeight.copy_iff
#print axioms ZInQ.ProductHeight.productModelHeight_of_split
#print axioms ZInQ.ProductHeight.metrizationHeightUnique_of
#print axioms ZInQ.ProductHeight.productModelHeight_of_unique
#print axioms ZInQ.ProductHeight.productModelHeight_of
#print axioms ZInQ.ProductHeight.productModelHeight_of_geo
#print axioms ZInQ.ProductHeight.productMetrizationSplit_of
#print axioms ZInQ.ProductHeight.metrizable_left_of_productModelHeight
#print axioms ZInQ.ProductHeight.metrizable_right_of_productModelHeight
