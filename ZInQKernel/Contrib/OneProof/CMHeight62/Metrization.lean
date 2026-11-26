import ZInQKernel.Contrib.OneProof.CMHeight62.Print

/-! # cmHeight62, step 2: a metrization of the abelian-scheme model

`stableFaltingsHeight` is an infimum over metrized models (`stableFaltingsHeight_le`), so the `≤`
half `CMHeight62` needs one metrization of the given model `𝒢` in dimension one, and no Néron or
semistable input. This file states the glue that builds it, in three named parts, and proves the
assembly:

* `HodgeLine62` — `⋀¹ ω_{E_L}` is an `L`-line and `⋀¹ ω_𝒢` a full lattice in it, for a proper
  group model `𝒢` of `E_L` with `dim E = 1` (the tree's `HodgeLatticeTheorem` at `g = 1`, which
  implies it: `hodgeLine62_of`);
* `UnifTransfer62` — an analytic uniformization of `E(ℂ)_{σ|_K}` gives one of `𝒢(ℂ)_σ` with the
  same kernel (`𝒢(ℂ)_σ = (E_L)(ℂ)_σ = E(ℂ)_{σ|_K}`, regular functions on opens of `𝒢` restricted
  to the generic fibre);
* `CoeffMap62` — a uniformization of `𝒢(ℂ)_σ` in dimension one gives a nonzero `σ`-semilinear
  coefficient map on the Hodge line with `1 ⊗ df ↦ (f ∘ Φ)'(0)`.

Proved here: the period lattice of a period `τ` (`periodPair`, `mem_lattice1_periodPair`), and
`metrizationExists62_of`, the assembly of a `MetrizedModel` from the three parts.
-/

namespace HDec
namespace CMBranch
namespace H62

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ.DefFaltings

/-! ## 1. The three glue parts (open) -/

/-- **Glue (open): the Hodge line of a proper group model of an elliptic curve.** -/
def HodgeLine62 : Prop :=
  ∀ (K : Type) [Field K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (E : ZInQ.DefFaltings.AbVar K), E.dim = 1 →
    ∀ 𝒢 : ZInQ.DefFaltings.GroupModel E L, IsProper 𝒢.G.hom →
      Module.finrank L (𝒢.hodgeSpace 1) = 1 ∧
        ∃ s ∈ 𝒢.detLattice 1, s ≠ 0 ∧ secIndex (𝒢.detLattice 1) s ≠ 0

/-- **Glue (open): uniformizations of the model's complex points**, from those of `E`. -/
def UnifTransfer62 : Prop :=
  ∀ (K : Type) [Field K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (E : ZInQ.DefFaltings.AbVar K) (𝒢 : ZInQ.DefFaltings.GroupModel E L) (σ : L →+* ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → ZInQ.LeafPush2.CPts (LeafAdopt.abVarEquiv K E) (σ.comp (algebraMap K L))),
    ZInQ.LeafPush2.IsUniformization (σ.comp (algebraMap K L)) Λ Φ →
      ∃ Ψ : (Fin g → ℂ) → 𝒢.Pts σ, 𝒢.IsAnalyticUniformization σ Λ Ψ

/-- **Glue (open): the coefficient map of a uniformization in dimension one.** -/
def CoeffMap62 : Prop :=
  ∀ (K : Type) [Field K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (E : ZInQ.DefFaltings.AbVar K), E.dim = 1 →
    ∀ (𝒢 : ZInQ.DefFaltings.GroupModel E L), IsProper 𝒢.G.hom →
    ∀ (σ : L →+* ℂ) (Λ : Submodule ℤ (Fin 1 → ℂ)) (Ψ : (Fin 1 → ℂ) → 𝒢.Pts σ),
      𝒢.IsAnalyticUniformization σ Λ Ψ →
      ∃ c : 𝒢.hodgeSpace 1 →ₛₗ[σ] ℂ, c ≠ 0 ∧ ∀ f, c (𝒢.wedge f) = 𝒢.jacDet Ψ f

/-- The tree's `HodgeLatticeTheorem` gives `HodgeLine62`. -/
theorem hodgeLine62_of (h : HodgeLatticeTheorem) : HodgeLine62 := by
  intro K _ L _ _ _ E hE 𝒢 _
  exact h K E L 𝒢 1 (by rw [hE]; rfl)

/-! ## 2. The period lattice `c (ℤ + ℤτ)` -/

/-- The period pair `(c, cτ)` of a period `τ` with `Im τ > 0` and `c ≠ 0`. -/
noncomputable def periodPair (c τ : ℂ) (hc : c ≠ 0) (hτ : 0 < τ.im) : PeriodPair where
  ω₁ := c
  ω₂ := c * τ
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h' : c * ((s : ℂ) + (t : ℂ) * τ) = 0 := by
      rw [← h, Complex.real_smul, Complex.real_smul]; ring
    have h2 : (s : ℂ) + (t : ℂ) * τ = 0 := (mul_eq_zero.mp h').resolve_left hc
    have him : t * τ.im = 0 := by
      have := congrArg Complex.im h2
      simpa using this
    have ht : t = 0 := (mul_eq_zero.mp him).resolve_right hτ.ne'
    subst ht
    have hre := congrArg Complex.re h2
    refine ⟨by simpa using hre, rfl⟩

theorem mem_lattice1_periodPair {c τ : ℂ} (hc : c ≠ 0) (hτ : 0 < τ.im) (z : Fin 1 → ℂ) :
    z ∈ (periodPair c τ hc hτ).lattice1 ↔ ∃ m n : ℤ, z 0 = c * (m + n * τ) := by
  have hmem : z ∈ (periodPair c τ hc hτ).lattice1 ↔
      z 0 ∈ (periodPair c τ hc hτ).lattice := Iff.rfl
  rw [hmem, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by rw [← h]; simp only [periodPair]; ring⟩
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by rw [h]; simp only [periodPair]; ring⟩

/-- The lattice of `IsPeriodAt` is the period lattice of `periodPair`. -/
theorem lattice_eq_lattice1 {c τ : ℂ} (hc : c ≠ 0) (hτ : 0 < τ.im) {Λ : Submodule ℤ (Fin 1 → ℂ)}
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = c * (m + n * τ)) :
    Λ = (periodPair c τ hc hτ).lattice1 := by
  ext z
  rw [hΛ, mem_lattice1_periodPair]

/-! ## 3. The metrization -/

/-- **The metrization exists.** For `E/K` with `dim E = 1`, a proper group model `𝒢` of `E_L` and
periods `τ_σ` of `E` at `σ|_K`, there is a metrization of `𝒢` in dimension one. -/
def MetrizationExists62 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (E : ZInQ.DefFaltings.AbVar K), E.dim = 1 →
    ∀ 𝒢 : ZInQ.DefFaltings.GroupModel E L, IsProper 𝒢.G.hom →
    ∀ τ : (L →+* ℂ) → ℂ,
      (∀ σ, 0 < (τ σ).im ∧
        IsPeriodAt (LeafAdopt.abVarEquiv K E) (σ.comp (algebraMap K L)) (τ σ)) →
      ∃ M : ZInQ.DefFaltings.MetrizedModel E L 1, M.model = 𝒢

/-- **Assembly (proved):** the three glue parts give the metrization. -/
theorem metrizationExists62_of (hH : HodgeLine62) (hU : UnifTransfer62) (hC : CoeffMap62) :
    MetrizationExists62 := by
  intro K _ _ L _ _ _ E hE 𝒢 h𝒢 τ hτ
  classical
  have hper : ∀ σ : L →+* ℂ, ∃ c : ℂ, ∃ hc : c ≠ 0,
      ∃ Ψ : (Fin 1 → ℂ) → 𝒢.Pts σ,
        𝒢.IsAnalyticUniformization σ (periodPair c (τ σ) hc (hτ σ).1).lattice1 Ψ := by
    intro σ
    obtain ⟨Λ, Φ, hΦ, c, hc, hΛ⟩ := (hτ σ).2
    obtain ⟨Ψ, hΨ⟩ := hU K L E 𝒢 σ 1 Λ Φ hΦ
    rw [lattice_eq_lattice1 hc (hτ σ).1 hΛ] at hΨ
    exact ⟨c, hc, Ψ, hΨ⟩
  choose c hc Ψ hΨ using hper
  have hcoeff : ∀ σ : L →+* ℂ, ∃ co : 𝒢.hodgeSpace 1 →ₛₗ[σ] ℂ, co ≠ 0 ∧
      ∀ f, co (𝒢.wedge f) = 𝒢.jacDet (Ψ σ) f := fun σ =>
    hC K L E hE 𝒢 h𝒢 σ _ (Ψ σ) (hΨ σ)
  choose co hco0 hco using hcoeff
  obtain ⟨hfin, hlat⟩ := hH K L E hE 𝒢 h𝒢
  let D : HodgeData L 1 (𝒢.hodgeSpace 1) :=
    { lattice := 𝒢.detLattice 1
      finrank_eq_one := hfin
      isLattice := hlat
      periods := fun σ => (periodPair (c σ) (τ σ) (hc σ) (hτ σ).1).lattice1
      periods_discrete := fun _ => inferInstance
      periods_isZLattice := fun _ => inferInstance
      coeff := co
      coeff_ne_zero := hco0 }
  exact ⟨⟨𝒢, D, rfl, fun σ => ⟨Ψ σ, hΨ σ, hco σ⟩⟩, rfl⟩

end H62
end CMBranch
end HDec
