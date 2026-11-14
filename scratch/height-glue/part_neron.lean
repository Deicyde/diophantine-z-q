
end ZInQ.HeightGlue

/-! ## Verbatim copies from `scratch/height-split/HeightSplit.lean` (task height-split): the glue
Props `NeronMetrizable`, `UniformizationDim`, `MetrizationOfUniformization`, the theorem
`neronMetrizable_of` and the bundle `HeightGlue`, in their original namespace. -/

namespace ZInQ.HeightSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.H5Neron

/-- **Glue `NeronMetrizable`.** The Néron model of `A_L` carries a metrization: a `g`, the Hodge
lattice `⋀^g ω_𝒩` and, at every `τ : L → ℂ`, an analytic uniformization with the coefficient map
`η ↦ c`, `η ⊗_τ 1 = c·dz₁∧⋯∧dz_g`. Needs: AN3 existence (the kernel's
`AnalyticUniformizationExists`, the uniformization theorem `A_τ(ℂ) ≅ ℂ^g/Λ`, Mumford AV §1), the
kernel's `HodgeLatticeTheorem` (proved: `ZInQ.Contrib.Dim.hodgeLatticeTheorem`) with `g = dim A` equal
to the dimension of the uniformization, and the construction of the coefficient map from the
differential at `0` of germs along `Φ` (well defined on `𝔪/𝔪²`, nonzero on the Hodge line). -/
def NeronMetrizable : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] (𝒩 : GroupModel A L), 𝒩.IsNeronModel →
    ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒩

/-- **Glue `UniformizationDim`.** The dimension `g` of an analytic uniformization `ℂ^g → 𝒢(ℂ)_τ` of
a group model of `A_L` with kernel a full lattice is `dim A` (the complex Lie group `A_τ(ℂ)` has
complex dimension `dim A`; `Φ` induces a continuous bijection from the compact torus `ℂ^g/Λ`).
The lattice hypotheses are needed: without them `Φ₀ ∘ pr : ℂ^{g+1} → 𝒢(ℂ)_τ` would be a
uniformization with kernel `Λ₀ × ℂ`. Needs: the analytic topology on `𝒢(ℂ)_τ` and its manifold
structure from regular functions (smoothness of relative dimension `dim A`, Jacobian criterion) and
invariance of domain. -/
def UniformizationDim : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), ∀ _ : DiscreteTopology Λ, IsZLattice ℝ Λ →
    𝒢.IsAnalyticUniformization τ Λ Φ → A.dim = (g : WithBot ℕ∞)

/-- **Glue `MetrizationOfUniformization`.** A group model of `A_L` with an analytic uniformization of
dimension `g = dim A` (lattice a full `ℤ`-lattice) at every `τ` carries a metrization of dimension
`g`. Needs: the kernel's `HodgeLatticeTheorem` (proved, `ZInQ.Contrib.Dim.hodgeLatticeTheorem`) for
the lattice `⋀^g ω_𝒢`; the coefficient map `coeff_τ : L ⊗ ⋀^g(𝔪/𝔪²) → ℂ`, `τ`-semilinear, from
`f ↦ d(f ∘ Φ)_0` (independent of the representative of the germ, `𝓞_L`-linear through `τ`, zero on
`𝔪²` by the product rule since `f(Φ(0)) = 0`), whose `g`-th exterior power is `jacDet Φ`; and
`coeff_τ ≠ 0` (regular functions with independent differentials are local coordinates, so the
Jacobian at `0` is invertible). -/
def MetrizationOfUniformization : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L]
    [Algebra K L] (𝒢 : GroupModel A L) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    (∀ τ : L →+* ℂ, ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ) →
    ∃ M : MetrizedModel A L g, M.model = 𝒢

/-- **`NeronMetrizable` from the kernel's AN3 existence and the two construction glues.** In fact
every group model is metrizable (the Néron property is not used). -/
theorem neronMetrizable_of (hE : AnalyticUniformizationExists) (hD : UniformizationDim)
    (hM : MetrizationOfUniformization) : NeronMetrizable := by
  intro K _ _ A L _ _ _ 𝒩 _
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨g, Λ₀, Φ₀, hd₀, hz₀, hΦ₀⟩ := hE K A L 𝒩 τ₀
  have hg : A.dim = (g : WithBot ℕ∞) := hD K A L 𝒩 τ₀ g Λ₀ Φ₀ hd₀ hz₀ hΦ₀
  obtain ⟨M, hM'⟩ := hM K A L 𝒩 g hg (fun τ => by
    obtain ⟨g', Λ, Φ, hd, hz, hΦ⟩ := hE K A L 𝒩 τ
    have hg' : g' = g := by
      have := (hD K A L 𝒩 τ g' Λ Φ hd hz hΦ).symm.trans hg
      exact_mod_cast this
    subst hg'
    exact ⟨Λ, Φ, hd, hz, hΦ⟩)
  exact ⟨g, M, hM'⟩

/-- **The remaining glue**: the kernel's two halves of AN3 and the two construction glues. -/
structure HeightGlue : Prop where
  an3Exists : AnalyticUniformizationExists
  an3Unique : AnalyticUniformizationUnique
  unifDim : UniformizationDim
  metrize : MetrizationOfUniformization

end ZInQ.HeightSplit

namespace ZInQ.HeightGlue

open ZInQ.DefFaltings ZInQ.HeightSplit CategoryTheory AlgebraicGeometry Topology MonObj
open PkgI3 (AbVar)
set_option linter.style.haveILetI false

/-- **`UniformizationDim`, from the textbook leaf T35** (proved). T35 (through metrization2's
transport) gives a full-lattice analytic uniformization `Φ'` of dimension `dim A`; a full-lattice
`Φ` of dimension `g` and `Φ'` factor through each other by surjective `ℂ`-linear maps
(`exists_linear_factor`, with `analyticPointsT2` and `isImmersiveAtZero_of_discrete`), so
`g = dim A`. -/
theorem uniformizationDim_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    UniformizationDim := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hd hz hΦ
  obtain ⟨g', hg'⟩ := abVar_dim_finite K A
  obtain ⟨Λ', Φ', hd', hz', hΦ'⟩ :=
    ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35 K A L 𝒢 τ g' hg'
  haveI := hd; haveI := hd'; haveI := hz; haveI := hz'
  have hT2 := analyticPointsT2 K A L 𝒢 τ
  obtain ⟨M, hM, -⟩ :=
    exists_linear_factor hT2 Λ' hΦ' (isImmersiveAtZero_of_discrete 𝒢 τ hΦ') hΦ
  obtain ⟨M', hM', -⟩ :=
    exists_linear_factor hT2 Λ hΦ (isImmersiveAtZero_of_discrete 𝒢 τ hΦ) hΦ'
  have h1 := M.finrank_range_le
  have h2 := M'.finrank_range_le
  rw [LinearMap.range_eq_top.mpr hM, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h1
  rw [LinearMap.range_eq_top.mpr hM', finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h2
  rw [hg', le_antisymm h1 h2]

/-- **`MetrizationOfUniformization`, proved** (no hypotheses): the lattice and line from
`ZInQ.Contrib.Dim.hodgeLatticeTheorem` (in the build), the coefficient maps from metrization's
`jacDetDescends` (proved, unif-dims' kernel-type copy), nonvanishing from metrization2's
`jacDetNondegenerate` (proved); the assembly is metrization's `exists_metrization_of_dim` with the
given uniformizations in place of `AnalyticUniformizationOfDim`. -/
theorem metrizationOfUniformization : MetrizationOfUniformization := by
  intro K _ _ A L _ _ _ 𝒢 g hg hU
  obtain ⟨hfr, hlat⟩ := ZInQ.Contrib.Dim.hodgeLatticeTheorem K A L 𝒢 g hg
  choose Λ Φ hdisc hZ hΦ using hU
  choose c hc using fun τ => ZInQ.Metrization.jacDetDescends K A L 𝒢 τ g (Λ τ) (Φ τ) (hΦ τ)
  have hc0 : ∀ τ, c τ ≠ 0 := by
    intro τ h0
    haveI := hdisc τ
    obtain ⟨f, hf⟩ :=
      ZInQ.Metrization2.jacDetNondegenerate K A L 𝒢 τ g hg (Λ τ) (Φ τ) (hZ τ) (hΦ τ)
    apply hf
    rw [← hc τ f, h0]
    rfl
  exact ⟨{ model := 𝒢
           hodge :=
            { lattice := 𝒢.detLattice g
              finrank_eq_one := hfr
              isLattice := hlat
              periods := Λ
              periods_discrete := hdisc
              periods_isZLattice := hZ
              coeff := c
              coeff_ne_zero := hc0 }
           lattice_eq := rfl
           arch := fun τ => ⟨Φ τ, hΦ τ, hc τ⟩ }, rfl⟩

/-- **`NeronMetrizable` from the textbook leaf T35** (proved). -/
theorem neronMetrizable_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    NeronMetrizable :=
  neronMetrizable_of (analyticUniformizationExists_of_t35 hT35) (uniformizationDim_of_t35 hT35)
    metrizationOfUniformization

/-- **height-split's whole `HeightGlue` bundle from the textbook leaf T35** (proved). -/
theorem heightGlue_of_t35 (hT35 : ZInQ.LeafPush2.UniformizationExists) : HeightGlue :=
  ⟨analyticUniformizationExists_of_t35 hT35, analyticUniformizationUnique_of_t35 hT35,
    uniformizationDim_of_t35 hT35, metrizationOfUniformization⟩

/-- The same bundle from the kernel's own Prop `AnalyticUniformizationExists` plus
`UniformizationDim` (T35 is used only for `UniformizationDim`). -/
theorem heightGlue_of_exists_dim (hE : AnalyticUniformizationExists) (hD : UniformizationDim) :
    HeightGlue :=
  ⟨hE, analyticUniformizationUnique_of_exists hE, hD, metrizationOfUniformization⟩
