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

/-- **`ProductModelHeight` forces AN3-existence on the left factor** (proved): if the product
model has a metrization and `h(𝒢₂) ≠ ⊥`, then at every `τ` the complex points `𝒢₁(ℂ)_τ` have an
analytic uniformization with a full discrete lattice as kernel: the conclusion of
`AnalyticUniformizationExists` for `𝒢₁`, obtained from the product's. -/
theorem analyticUnif_left_of_productModelHeight (h : ProductModelHeight)
    {K : Type} [Field K] {A B C : AbVar K} {eC : C.X ≅ A.X ⊗ B.X} {L : Type} [Field L]
    [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (hPM : IsProductModel eC 𝒢P 𝒢₁ 𝒢₂) {g : ℕ}
    (MP : MetrizedModel C L g) (hMP : MP.model = 𝒢P) (h₂ : 𝒢₂.height ≠ ⊥) (τ : L →+* ℂ) :
    ∃ (g₁ : ℕ) (Λ : Submodule ℤ (Fin g₁ → ℂ)) (Φ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢₁.IsAnalyticUniformization τ Λ Φ := by
  obtain ⟨g₁, M₁, rfl⟩ := metrizable_left_of_productModelHeight h hPM MP hMP h₂
  obtain ⟨Φ, hΦ, -⟩ := M₁.arch τ
  exact ⟨g₁, _, Φ, M₁.hodge.periods_discrete τ, M₁.hodge.periods_isZLattice τ, hΦ⟩

/-! ## §5. Complex points of a product model, and the product uniformization (algebraic half)

For `e : 𝒢P ≅ 𝒢₁ ⊗ 𝒢₂` with homomorphic components, `𝒢P(ℂ)_τ ≅ 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` as groups
(`ptsEquiv`, proved). For uniformizations `Φ₁`, `Φ₂` of the factors, the product
`Φ(z) = (Φ₁(z₁), Φ₂(z₂))` (`z = Fin.append z₁ z₂`) satisfies the three algebraic clauses of
`IsAnalyticUniformization` with kernel `Λ₁ × Λ₂` (`prodUnif_clauses`, proved); the two analytic
clauses (openness of `Φ⁻¹(U(ℂ))`, holomorphy of regular functions along `Φ`) are the glue Prop
`ProductUnifAnalytic`. This is the "easy" direction (products of uniformizations), used by
`ProductMetrizationGeo`; it is not the splitting of §1. -/

section Points

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
  {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}

/-- The two projections on complex points, as one homomorphism. -/
noncomputable def ptsProj (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] (τ : L →+* ℂ) : 𝒢P.Pts τ →* 𝒢₁.Pts τ × 𝒢₂.Pts τ :=
  (IsMonHom.monoidHom (e.hom ≫ fst _ _) (GroupModel.ptC τ)).prod
    (IsMonHom.monoidHom (e.hom ≫ snd _ _) (GroupModel.ptC τ))

theorem ptsProj_bijective (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] (τ : L →+* ℂ) : Function.Bijective (ptsProj e τ) := by
  constructor
  · intro p q hpq
    simp only [ptsProj, MonoidHom.prod_apply, IsMonHom.monoidHom_apply, Prod.mk.injEq] at hpq
    rw [← cancel_mono e.hom]
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc] using hpq.1
    · simpa only [Category.assoc] using hpq.2
  · rintro ⟨a, b⟩
    refine ⟨lift a b ≫ e.inv, ?_⟩
    simp only [ptsProj, MonoidHom.prod_apply, IsMonHom.monoidHom_apply, Category.assoc,
      Iso.inv_hom_id_assoc, lift_fst, lift_snd]

/-- **`𝒢P(ℂ)_τ ≅ 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` as groups (proved).** -/
noncomputable def ptsEquiv (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] (τ : L →+* ℂ) : 𝒢P.Pts τ ≃* 𝒢₁.Pts τ × 𝒢₂.Pts τ :=
  MulEquiv.ofBijective (ptsProj e τ) (ptsProj_bijective e τ)

/-- The lattice `Λ₁ × Λ₂ ⊂ ℂ^{g₁+g₂}` (coordinates `Fin.append`). -/
def prodLattice {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) :
    Submodule ℤ (Fin (g₁ + g₂) → ℂ) :=
  Λ₁.comap (LinearMap.funLeft ℤ ℂ (Fin.castAdd g₂)) ⊓
    Λ₂.comap (LinearMap.funLeft ℤ ℂ (Fin.natAdd g₁))

/-- The product uniformization `z ↦ (Φ₁(z₁), Φ₂(z₂))`. -/
noncomputable def prodUnif (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) : (Fin (g₁ + g₂) → ℂ) → 𝒢P.Pts τ := fun z =>
  (ptsEquiv e τ).symm (Φ₁ fun i => z (Fin.castAdd g₂ i), Φ₂ fun i => z (Fin.natAdd g₁ i))

/-- **The algebraic clauses of `IsAnalyticUniformization` for the product (proved).** -/
theorem prodUnif_clauses (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)}
    {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ}
    {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ} (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    (∀ z w, prodUnif e Φ₁ Φ₂ (z + w) = prodUnif e Φ₁ Φ₂ z * prodUnif e Φ₁ Φ₂ w) ∧
    (∀ z, prodUnif e Φ₁ Φ₂ z = 1 ↔ z ∈ prodLattice Λ₁ Λ₂) ∧
    Function.Surjective (prodUnif e Φ₁ Φ₂) := by
  obtain ⟨m₁, k₁, s₁, -, -⟩ := h₁
  obtain ⟨m₂, k₂, s₂, -, -⟩ := h₂
  refine ⟨fun z w => ?_, fun z => ?_, fun p => ?_⟩
  · simp only [prodUnif, ← map_mul, Prod.mk_mul_mk]
    congr 2
    · exact m₁ _ _
    · exact m₂ _ _
  · simp only [prodUnif, MulEquiv.map_eq_one_iff, Prod.mk_eq_one, k₁, k₂, prodLattice,
      Submodule.mem_inf, Submodule.mem_comap]
    rfl
  · obtain ⟨z₁, hz₁⟩ := s₁ (ptsEquiv e τ p).1
    obtain ⟨z₂, hz₂⟩ := s₂ (ptsEquiv e τ p).2
    refine ⟨Fin.append z₁ z₂, ?_⟩
    simp only [prodUnif, Fin.append_left, Fin.append_right, hz₁, hz₂, Prod.mk.eta,
      MulEquiv.symm_apply_apply]

/-- **Glue (analytic half of the product uniformization).** For analytic uniformizations `Φ₁`,
`Φ₂` of the factors, the product uniformization satisfies the two analytic clauses of
`IsAnalyticUniformization`: each `Φ⁻¹(U(ℂ))` is open and each regular function on an open of
`𝒢P` is holomorphic along `Φ` there. Why true (STANDARD): the affine products
`U₁ ×_{𝓞_L} U₂ = Spec(R₁ ⊗ R₂)` cover `𝒢₁ ×_{𝓞_L} 𝒢₂`, and their basic opens `D(f)`,
`f = Σ aᵢ ⊗ bᵢ`, form a basis (products of opens alone do not: the Zariski topology of a product
is finer than the product topology). On `U₁ × U₂` the preimage under `Φ` is
`Φ₁⁻¹(U₁) × Φ₂⁻¹(U₂)` (open), the value of `a ⊗ b` at `Φ z` is `a(Φ₁ z₁) b(Φ₂ z₂)` (holomorphic),
so `Φ⁻¹(D(f))` is open and the sections `h / fⁿ` of `D(f)` are holomorphic along `Φ`; both
properties are local (EGA I 3.2.2 / Stacks 01JR for the affine product, UNVERIFIED). Needs
Mathlib's affine fibre products (`pullbackSpecIso`) and the comparison of evaluations; unproved.
No AN3 input. -/
def ProductUnifAnalytic : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
      (∀ U, IsOpen (𝒢P.dom (prodUnif e Φ₁ Φ₂) U)) ∧
      (∀ U (s : Γ(𝒢P.G.left, U)),
        DifferentiableOn ℂ (fun z => 𝒢P.evalAt (prodUnif e Φ₁ Φ₂ z) U s)
          (𝒢P.dom (prodUnif e Φ₁ Φ₂) U))

/-- **The product of analytic uniformizations is an analytic uniformization of the product
model, with lattice `Λ₁ × Λ₂`** (proved from `ProductUnifAnalytic`). -/
theorem prodUnif_isAnalyticUniformization (hA : ProductUnifAnalytic)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)}
    {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ}
    {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ} (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodUnif e Φ₁ Φ₂) := by
  obtain ⟨hm, hk, hs⟩ := prodUnif_clauses e h₁ h₂
  obtain ⟨ho, hd⟩ := hA K A B C L 𝒢P 𝒢₁ 𝒢₂ e τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  exact ⟨hm, hk, hs, ho, hd⟩

/-- The splitting direction, formal part: for any uniformization `Φ` of the product, `p₁ ∘ Φ`
is a surjective homomorphism `ℂ^g → 𝒢₁(ℂ)_τ` (proved). Its kernel `Φ⁻¹(1 × 𝒢₂(ℂ)_τ)` is not
discrete when `𝒢₂(ℂ)_τ` is infinite; extracting a uniformization of `𝒢₁` from it is the
AN3-type step of §4. -/
theorem proj_comp_unif (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢P.Pts τ} (hΦ : 𝒢P.IsAnalyticUniformization τ Λ Φ) :
    (∀ z w, (ptsEquiv e τ (Φ (z + w))).1 = (ptsEquiv e τ (Φ z)).1 * (ptsEquiv e τ (Φ w)).1) ∧
    Function.Surjective fun z => (ptsEquiv e τ (Φ z)).1 := by
  obtain ⟨m, -, s, -, -⟩ := hΦ
  refine ⟨fun z w => by rw [m, map_mul, Prod.fst_mul], fun a => ?_⟩
  obtain ⟨z, hz⟩ := s ((ptsEquiv e τ).symm (a, 1))
  exact ⟨z, by simp only [hz, MulEquiv.apply_symm_apply]⟩

end Points

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
#print axioms ZInQ.ProductHeight.analyticUnif_left_of_productModelHeight
#print axioms ZInQ.ProductHeight.ptsEquiv
#print axioms ZInQ.ProductHeight.prodUnif_clauses
#print axioms ZInQ.ProductHeight.prodUnif_isAnalyticUniformization
#print axioms ZInQ.ProductHeight.proj_comp_unif
