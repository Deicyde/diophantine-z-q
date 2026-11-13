
/-! ## metrization (2026-11-13): `MetrizationExists` reduced to `HodgeLatticeTheorem`, one leaf
(the uniformization theorem with its dimension) and two glue Props on Jacobians -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- An abelian variety (def-faltings' copy) has finite dimension (proved, from g0-dim's
`G0Dim.dim_finite`; the same proof as g0-dim's `dimFinite` for `PkgI3.AbVar`). -/
theorem abVar_dim_finite (K : Type) [Field K] (A : AbVar K) : ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact G0Dim.dim_finite A.X.left A.X.hom

/-- **Leaf (AN3 with its dimension: the uniformization theorem).** For every smooth group model
`𝒢` of `A_L`, every `τ : L → ℂ` and `g = dim A`, there are a full lattice `Λ ⊂ ℂ^g` and an analytic
uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel `Λ`. This is def-faltings'
`AnalyticUniformizationExists` with the dimension pinned to `dim A` (`𝒢(ℂ)_τ = A_τ(ℂ)` is a compact
connected complex Lie group of dimension `dim A`, hence `≅ ℂ^g/Λ`: Mumford, *Abelian varieties*,
§1 and §4 (UNVERIFIED locators), with Serre's GAGA for the analytic structure of `A_τ(ℂ)`).
Implies `AnalyticUniformizationExists` (`analyticUniformizationExists_of`). -/
def AnalyticUniformizationOfDim : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ

/-- **Glue (the Jacobian descends to the Hodge line).** For an analytic uniformization `Φ` of
`𝒢(ℂ)_τ`, the Jacobian determinant `jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` depends only on the
classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`, is `𝓞_L`-multilinear (through `τ`) and alternating in them, hence is
the value on `1 ⊗ df₁ ∧ ⋯ ∧ df_g` of a `τ`-semilinear map `hodgeSpace g → ℂ`. Why true: `Φ 0 = 1`
lies over `ξ`; the germ `f ∘ Φ` at `0` is independent of the representative of `f` (`dom Φ U`
open); evaluation at a complex point is a ring map, so `(f f') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)` near `0`,
and for `f, f' ∈ 𝔪_ξ` both vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz); a function from
`𝓞_L` acts by the constant `τ(a)`. Then `⋀^g` (universal property) and `L ⊗_{𝓞_L} -` (extension
of scalars along `τ`) give the map. Elementary calculus plus Mathlib's scheme API; unproved. -/
def JacDetDescends : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ, ∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f

/-- **Glue (local parameters are analytic coordinates).** For `g = dim A` and an analytic
uniformization `Φ` of `𝒢(ℂ)_τ` with a full lattice as kernel, some `f₁, …, f_g ∈ 𝔪_ξ` have
`jacDet Φ f ≠ 0`. Why true (STANDARD): `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}` is regular of dimension `g`
(smoothness); a regular system of parameters `f₁, …, f_g` gives holomorphic coordinates of the
complex manifold `A_τ(ℂ)` at `0` (Serre, GAGA, or the holomorphic implicit function theorem),
and `Φ` is a local biholomorphism at `0`, so `(f_i ∘ Φ)` has invertible Jacobian at `0`.
Unproved (needs the analytic structure of `A_τ(ℂ)`). -/
def JacDetNondegenerate : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      IsZLattice ℝ Λ → 𝒢.IsAnalyticUniformization τ Λ Φ →
      ∃ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk, 𝒢.jacDet Φ f ≠ 0

/-- `AnalyticUniformizationOfDim` is at least as strong as def-faltings'
`AnalyticUniformizationExists` (proved; with `abVar_dim_finite`). -/
theorem analyticUniformizationExists_of (h : AnalyticUniformizationOfDim) :
    AnalyticUniformizationExists := by
  intro K _ A L _ _ _ 𝒢 τ
  obtain ⟨g, hg⟩ := abVar_dim_finite K A
  exact ⟨g, h K A L 𝒢 τ g hg⟩

/-- The metrization at `g = dim A` (proved from the four hypotheses): lattice `⋀^g ω_𝒢`, periods
and coefficient maps from the uniformizations. -/
theorem exists_metrization_of_dim (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hJ : JacDetDescends) (hN : JacDetNondegenerate) {K : Type} [Field K] {A : AbVar K}
    {L : Type} [Field L] [NumberField L] [Algebra K L] (𝒢 : GroupModel A L) (g : ℕ)
    (hg : A.dim = g) : ∃ M : MetrizedModel A L g, M.model = 𝒢 := by
  obtain ⟨hfr, hlat⟩ := hH K A L 𝒢 g hg
  choose Λ Φ hdisc hZ hΦ using fun τ => hU K A L 𝒢 τ g hg
  choose c hc using fun τ => hJ K A L 𝒢 τ g (Λ τ) (Φ τ) (hΦ τ)
  have hc0 : ∀ τ, c τ ≠ 0 := by
    intro τ h0
    haveI := hdisc τ
    obtain ⟨f, hf⟩ := hN K A L 𝒢 τ g hg (Λ τ) (Φ τ) (hZ τ) (hΦ τ)
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

/-- **`MetrizationExists` from `HodgeLatticeTheorem`, the leaf `AnalyticUniformizationOfDim` and
the glue `JacDetDescends`, `JacDetNondegenerate` (proved).** -/
theorem metrizationExists_of (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hJ : JacDetDescends) (hN : JacDetNondegenerate) : ZInQ.G0HeightAdd.MetrizationExists := by
  intro K _ A L _ _ _ 𝒢
  obtain ⟨g, hg⟩ := abVar_dim_finite K A
  obtain ⟨M, hM⟩ := exists_metrization_of_dim hH hU hJ hN 𝒢 g hg
  exact ⟨g, M, hM⟩

/-- Every metrization has dimension `dim A` (proved, from the four hypotheses and
`metrizationDimUnique`). -/
theorem metrized_dim_eq (hH : HodgeLatticeTheorem) (hU : AnalyticUniformizationOfDim)
    (hJ : JacDetDescends) (hN : JacDetNondegenerate) {K : Type} [Field K] {A : AbVar K}
    {L : Type} [Field L] [NumberField L] [Algebra K L] {g : ℕ} (M : MetrizedModel A L g) :
    A.dim = g := by
  obtain ⟨d, hd⟩ := abVar_dim_finite K A
  obtain ⟨M', hM'⟩ := exists_metrization_of_dim hH hU hJ hN M.model d hd
  rw [hd, metrizationDimUnique K A L d g M' M hM']

end ZInQ.Metrization

#print axioms ZInQ.Metrization.abVar_dim_finite
#print axioms ZInQ.Metrization.analyticUniformizationExists_of
#print axioms ZInQ.Metrization.metrizationExists_of
#print axioms ZInQ.Metrization.metrized_dim_eq
