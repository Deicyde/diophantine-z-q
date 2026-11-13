import ZInQKernel.HDecomp.LeafPush2.T
import ZInQKernel.HDecomp.Faltings.HodgeLattice
import Mathlib


/-! ## g0-dim: `DimFinite` and `DimBaseChange` proved (task g0-dim; body of `scratch/g0-dim/Dim.lean` §1-§2) -/

section G0DimSec

set_option linter.style.haveILetI false

open Order TensorProduct

namespace G0Dim

/-! ## §1. Commutative algebra -/


/-- Integral injective extensions have the same Krull dimension (going up + incomparability;
Stacks 00OK, Matsumura Thm 9.4 — STANDARD). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    have h : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) h
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- **Stacks 00P4 (affine case), proved.** For a finitely generated algebra `R` over a field `K`
and any field extension `L/K`, `dim (R ⊗_K L) = dim R`. Proof: Noether normalization
`K[X_1..X_s] → R` (finite, injective) base-changes to `L[X_1..X_s] → R ⊗ L` (finite, injective
since `L` is flat over `K`). -/
theorem ringKrullDim_tensor_field (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (L : Type*) [Field L] [Algebra K L] :
    ringKrullDim (R ⊗[K] L) = ringKrullDim R := by
  rcases subsingleton_or_nontrivial R with h | h
  · haveI : Subsingleton (R ⊗[K] L) := by
      have h1 : (1 : R ⊗[K] L) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : R) 0, TensorProduct.zero_tmul]
      exact subsingleton_of_zero_eq_one h1.symm
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    have hR : ringKrullDim R = s := by
      letI := g.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
      rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
        ringKrullDim_mvPolynomial_field]
    let g' := Algebra.TensorProduct.map g (AlgHom.id K L)
    have g'inj : Function.Injective g' :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := L) g.toLinearMap ginj
    have g'fin : g'.toRingHom.Finite := RingHom.Finite.tensorProductMap gfin (by exact RingHom.Finite.id L)
    have hP : ringKrullDim (MvPolynomial (Fin s) K ⊗[K] L) = s := by
      rw [ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm K _ L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv), ringKrullDim_mvPolynomial_field]
    rw [hR, ← hP]
    letI := g'.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K ⊗[K] L) (R ⊗[K] L) := ⟨g'fin.to_isIntegral⟩
    exact ringKrullDim_eq_of_isIntegral_of_injective g'inj

/-- A finitely generated algebra over a field has finite Krull dimension (or is zero). -/
theorem ringKrullDim_le_of_finiteType (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] : ∃ n : ℕ, ringKrullDim R ≤ n := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le⟩
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    letI := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
    refine ⟨s, le_of_eq ?_⟩
    rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]


/-! ## §2. Topology and schemes -/

open TopologicalSpace Topology


/-- The Krull dimension of a space is the supremum of the dimensions of the members of a cover
by open embeddings (Stacks 0055 for open covers; STANDARD). -/
theorem topologicalKrullDim_eq_iSup_of_openEmbedding {X : Type*} [TopologicalSpace X] {ι : Type*}
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ krullDim {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} := q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

open AlgebraicGeometry CategoryTheory Limits

theorem scheme_dim_eq_iSup_cover {X : Scheme} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) :=
  topologicalKrullDim_eq_iSup_of_openEmbedding (fun i => 𝒰.f i) (fun i => (𝒰.f i).isOpenEmbedding)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)

theorem scheme_dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

theorem spec_dim (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R


/-- **Stacks 00P4, affine piece over `Spec K`.** For `m : Spec R → Spec K` locally of finite
type, `Spec R ×_K Spec L ≅ Spec (R ⊗_K L)` has the dimension of `Spec R`. -/
theorem dim_pullback_spec {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType m] :
    topologicalKrullDim (pullback m (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim (Spec R) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  have e := scheme_dim_eq_of_iso (pullbackSpecIso K R L)
  refine e.trans ?_
  rw [spec_dim, spec_dim]
  exact ringKrullDim_tensor_field K R L

/-- A scheme of finite type over a field: each affine piece `Spec R → Spec K` has bounded
dimension. -/
theorem dim_spec_le {K : Type} [Field K] (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType m] : ∃ n : ℕ, topologicalKrullDim (Spec R) ≤ n := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  rw [spec_dim]
  exact ringKrullDim_le_of_finiteType K R

/-- **Dimension is invariant under field base change** (Stacks 00P4 globalized; proved). For a
scheme `X` locally of finite type over a field `K` and any field extension `L/K`,
`dim (X ×_K L) = dim X`. -/
theorem dim_baseChange {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (X : Scheme.{0})
    (h : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] :
    topologicalKrullDim (pullback h (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim X := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let 𝒰 := X.affineCover
  rw [scheme_dim_eq_iSup_cover 𝒰, scheme_dim_eq_iSup_cover (𝒰.pullback₁ (pullback.fst h g))]
  refine iSup_congr fun i => ?_
  have e : (𝒰.pullback₁ (pullback.fst h g)).X i ≅ pullback (𝒰.f i ≫ h) g :=
    (pullbackSymmetry _ _).trans (pullbackRightPullbackFstIso h g (𝒰.f i))
  rw [scheme_dim_eq_of_iso e]
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
  exact @dim_pullback_spec K _ L _ _ _ (𝒰.f i ≫ h) hc

theorem exists_nat_of_le (x : WithBot ℕ∞) (h0 : x ≠ ⊥) (N : ℕ) (h : x ≤ N) :
    ∃ n : ℕ, x = n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((N : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.mp h') (by simp)
    | coe n => exact ⟨n, rfl⟩

/-- **A nonempty scheme of finite type over a field has finite dimension** (proved). -/
theorem dim_finite {K : Type} [Field K] (X : Scheme.{0}) (h : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType h] [QuasiCompact h] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  let 𝒰 := X.affineCover.finiteSubcover
  have hb : ∀ i, ∃ n : ℕ, topologicalKrullDim (𝒰.X i) ≤ n := fun i => by
    haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
    exact @dim_spec_le K _ _ (𝒰.f i ≫ h) hc
  choose n hn using hb
  have hle : topologicalKrullDim X ≤ ((∑ i, n i : ℕ) : WithBot ℕ∞) := by
    rw [scheme_dim_eq_iSup_cover 𝒰]
    refine iSup_le fun i => (hn i).trans ?_
    exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hne : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    haveI : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_ne_bot_iff.mpr inferInstance
  exact exists_nat_of_le _ hne _ hle

end G0Dim

end G0DimSec

namespace ZInQ.Metrization
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)
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
/-- **Glue (local product structure of `𝒢₁ ×_{𝓞_L} 𝒢₂` at complex points).** For
`e : 𝒢P ≅ 𝒢₁ × 𝒢₂`, an open `U ⊂ 𝒢P`, `s ∈ Γ(U)` and complex points `p₁`, `p₂` with
`e⁻¹(p₁, p₂) ∈ U(ℂ)`, there are opens `V₁ ∋ p₁`, `V₂ ∋ p₂` and regular functions
`a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that `H = Σ c_k ⊗ d_k` does not vanish at `(p₁, p₂)`,
and at every `(p₁', p₂') ∈ V₁(ℂ) × V₂(ℂ)` with `H(p₁', p₂') ≠ 0`: `e⁻¹(p₁', p₂') ∈ U(ℂ)` and
`s(e⁻¹(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`. Why true (STANDARD): take affine
`V₁ = Spec R₁`, `V₂ = Spec R₂` (over the affine `Spec 𝓞_L`), so `V₁ ×_{𝓞_L} V₂ = Spec(R₁ ⊗ R₂)`
is open in the product; choose a basic open `D(h)` of it with `(p₁, p₂) ∈ D(h) ⊆ e(U)`,
`h ∈ R₁ ⊗ R₂`; on `D(h)`, `s = a/h^m` with `a ∈ R₁ ⊗ R₂`; take `H = h^m` and expand `H` and `a`
as sums of pure tensors; a pure tensor `c ⊗ d` evaluates at `(p₁', p₂')` to `c(p₁') d(p₂')`.
Unproved (needs Mathlib's affine opens of pullbacks and sections on basic opens). -/
def ProductLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (τ : L →+* ℂ) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ e.inv).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ e.inv).left ⁻¹ᵁ U ∧
        𝒢P.evalAt (lift p₁' p₂' ≫ e.inv) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)
end ZInQ.Metrization


/-! ## metrization: two of the four clauses of `JacDetMultilinear`, proved

`Φ 0 = 1` lies over `ξ` (`zero_mem_dom`); `germAlong Φ t` agrees near `0` with `z ↦ evalAt (Φ z) U s`
for every representative `(U, s)` of `t` (`germAlong_eventuallyEq`); hence slot additivity
(`jacDet_update_add`). Vanishing on equal slots is immediate (`jacDet_eq_zero_of_eq`). What
remains is `JacDetClassScalar` (clauses (i) and (iii)). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology
open PkgI3 (AbVar)

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
section Scalar0
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

end Scalar0
end ZInQ.Metrization

/-! ## metrization2: `JacDetNondegenerate` from the local structure of morphisms out of a product

Step 1 (linear algebra): if every `jacDet Φ f` vanishes, some `v ≠ 0` is killed by
`d(germAlong Φ t)(0)` for every `t ∈ 𝔪_ξ`. Step 2: then by every regular function near `ξ`
(subtract the pull-back along `𝒢 → Spec 𝓞_L` of its restriction to the unit section). -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology
open PkgI3 (AbVar)

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
open PkgI3 (AbVar)

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
/-! ## metrization2: points are determined by their values on an affine open; the assembly -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology
open PkgI3 (AbVar)

section Final

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- Two complex points in `U(ℂ)`, `U` affine, with the same values on `Γ(U, 𝒪)` are equal. -/
theorem pts_eq_of_evalAt {τ : L →+* ℂ} (U : 𝒢.G.left.Opens) (hU : IsAffineOpen U)
    (p q : 𝒢.Pts τ) (hp : ⊤ ≤ p.left ⁻¹ᵁ U) (hq : ⊤ ≤ q.left ⁻¹ᵁ U)
    (h : ∀ s : Γ(𝒢.G.left, U), 𝒢.evalAt p U s = 𝒢.evalAt q U s) : p = q := by
  have hTop : IsAffineOpen (⊤ : (Spec (CommRingCat.of ℂ)).Opens) :=
    isAffineOpen_top (Spec (CommRingCat.of ℂ))
  have happ : p.left.appLE U ⊤ hp = q.left.appLE U ⊤ hq := by
    ext s
    have hs := h s
    unfold GroupModel.evalAt at hs
    rw [dif_pos hp, dif_pos hq] at hs
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective hs
  have e1 := IsAffineOpen.SpecMap_appLE_fromSpec p.left hU hTop hp
  have e2 := IsAffineOpen.SpecMap_appLE_fromSpec q.left hU hTop hq
  have e3 : hTop.fromSpec ≫ p.left = hTop.fromSpec ≫ q.left :=
    e1.symm.trans ((congrArg (fun φ => Spec.map φ ≫ hU.fromSpec) happ).trans e2)
  have hiso : IsIso hTop.fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  apply Over.OverMorphism.ext
  exact (cancel_epi hTop.fromSpec).mp e3

end Final

/-- **`JacDetNondegenerate` from `ProductMapLocalStructure` (proved).** If every `jacDet Φ f`
vanished, some `v ≠ 0` would be killed by the differential at `0` of every regular function near
`ξ` along `Φ` (steps 1 and 2), hence, by translation, by the differential at every point
(step 3); so on an affine `U ∋ ξ` every regular function is constant along `t ↦ Φ(t v)` for small
`t`, so `Φ(t v) = Φ 0 = 1` (points of an affine scheme are determined by their values), so
`t v ∈ Λ` for all small `t`, contradicting the discreteness of `Λ`. Neither `A.dim = g` nor
`IsZLattice ℝ Λ` is used. -/
theorem jacDetNondegenerate_of (hML : ProductMapLocalStructure) :
    ZInQ.Metrization.JacDetNondegenerate := by
  intro K _ A L _ _ _ 𝒢 τ g _ Λ hdisc Φ _ hΦ
  by_contra hcon
  push_neg at hcon
  -- step 1
  obtain ⟨v, hv0, hv⟩ := exists_null_of_det_eq_zero
    (fun t : IsLocalRing.maximalIdeal 𝒢.genStalk => fun j =>
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1)) (fun f => hcon f)
  have hsingle : ∀ j : Fin g, (fun k => if j = k then (1 : ℂ) else 0) = Pi.single j 1 := by
    intro j; ext k; simp [Pi.single_apply, eq_comm]
  have hv1 : ∀ t : IsLocalRing.maximalIdeal 𝒢.genStalk,
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 v = 0 := by
    intro t
    rw [pi_eq_sum_univ v, map_sum]
    simp only [hsingle, map_smul, smul_eq_mul]
    rw [← hv t]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- step 2
  have hv2 := fderiv_evalAt_apply_eq_zero 𝒢 hΦ v hv1
  -- an affine open around `ξ`
  obtain ⟨U, hU, mU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
  have hdomU : IsOpen (𝒢.dom Φ U) := hΦ.2.2.2.1 U
  have h0U : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := zero_mem_dom 𝒢 hΦ U mU
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hBopen : IsOpen {t : ℂ | t • v ∈ 𝒢.dom Φ U} := hdomU.preimage hcont
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hBopen 0 (by simp [h0U])
  -- steps 3-4: every regular function on `U` is constant along the line on the ball
  have hconst : ∀ t ∈ Metric.ball (0 : ℂ) r, Φ (t • v) = Φ 0 := by
    intro t ht
    have hderiv : ∀ (s : Γ(𝒢.G.left, U)), ∀ t₀ ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) U s) 0 t₀ := by
      intro s t₀ ht₀
      have h3 := hasDerivAt_line_zero 𝒢 hML hΦ v hv2 U s (t₀ • v) (hball ht₀)
      have h4 : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + (t - t₀) • v)) U s) 0 t₀ := by
        have h3' : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + t • v)) U s) 0 (t₀ - t₀) := by
          rw [sub_self]; exact h3
        exact h3'.comp_sub_const t₀ t₀
      refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [← add_smul, add_sub_cancel]
    apply pts_eq_of_evalAt 𝒢 U hU _ _ (hball ht) h0U
    intro s
    have := (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).differentiableAt.differentiableWithinAt)
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).deriv) ht (Metric.mem_ball_self hr)
    simpa using this
  -- step 5: discreteness of `Λ`
  have h0 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) r, t • v ∈ Λ := fun t ht =>
    (hΦ.2.1 _).mp ((hconst t ht).trans h0)
  obtain ⟨u, hu, hpre⟩ := isOpen_induced_iff.mp (isOpen_discrete ({0} : Set Λ))
  have hu0 : (0 : Fin g → ℂ) ∈ u := by
    have : (0 : Λ) ∈ ({0} : Set Λ) := rfl
    rw [← hpre] at this
    exact this
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ u :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hu.mem_nhds hu0)
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ Metric.ball (0 : ℂ) r := Metric.ball_mem_nhds 0 hr
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • v ∈ u ∧ t ∈ Metric.ball (0 : ℂ) r :=
    nhdsWithin_le_nhds (hev1.and hev2)
  obtain ⟨t, ⟨htu, htb⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hin : (⟨t • v, hmem t htb⟩ : Λ) ∈ Subtype.val ⁻¹' u := htu
  rw [hpre] at hin
  have : t • v = 0 := congrArg Subtype.val hin
  rcases smul_eq_zero.mp this with h | h
  · exact ht0 h
  · exact hv0 h


end ZInQ.Metrization2

/-! ## metrization2: complex points of a group model are complex points of `A_L`

For a group model `𝒢` of `A_L` and `τ : L → ℂ`, `θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ`,
`q ↦ (Spec ℂ → A_L ≅ 𝒢_L → 𝒢)`, is a group isomorphism (inverse `χ`, built from the monoidal
functor `Over.pullback (Spec L → Spec 𝓞_L)`), and evaluation of `s ∈ Γ(U, 𝒪_𝒢)` at `θ q` is
evaluation of the pulled-back section at `q`. So a uniformization of `A_L(ℂ)_τ` in leaf-push2's
sense gives one of `𝒢(ℂ)_τ` in def-faltings' sense. -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.LeafPush2
open PkgI3 (AbVar)
open scoped Obj

section Transport

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jO (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

theorem cpt_comp_jO (τ : L →+* ℂ) :
    (cptObj τ).hom ≫ jO L = (GroupModel.ptC (L := L) τ).hom := by
  show Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) =
    Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L)))
  rw [← Spec.map_comp]
  rfl

/-- The projection `𝒢_L → 𝒢`. -/
noncomputable def fstG : (genericFibre L 𝒢.G).left ⟶ 𝒢.G.left := pullback.fst 𝒢.G.hom (jO L)

theorem fstG_comp_hom : fstG 𝒢 ≫ 𝒢.G.hom = (genericFibre L 𝒢.G).hom ≫ jO L :=
  pullback.condition

/-- The morphism `A_L → 𝒢` (through `gen⁻¹ : A_L ≅ 𝒢_L` and the projection `𝒢_L → 𝒢`). -/
noncomputable def toModel : (A.baseChange L).X.left ⟶ 𝒢.G.left := 𝒢.gen.inv.left ≫ fstG 𝒢

theorem toModel_comp_hom :
    (toModel 𝒢) ≫ 𝒢.G.hom = (A.baseChange L).X.hom ≫ jO L := by
  unfold toModel
  rw [Category.assoc, fstG_comp_hom, ← Category.assoc, Over.w 𝒢.gen.inv]

/-- `θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ`. -/
noncomputable def theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) : 𝒢.Pts τ :=
  Over.homMk (q.left ≫ (toModel 𝒢))
    ((Category.assoc _ _ _).trans ((congrArg (q.left ≫ ·) (toModel_comp_hom 𝒢)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jO L) (Over.w q)).trans
        (cpt_comp_jO τ)))))

theorem theta_left {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) :
    ((theta 𝒢) q).left = q.left ≫ (toModel 𝒢) := rfl

/-- The base change `(Spec ℂ)_L` of `ptC τ`. -/
noncomputable abbrev ptCL (τ : L →+* ℂ) : Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (jO L)).obj (GroupModel.ptC (L := L) τ)

/-- Its projection to `Spec ℂ` (`ptC τ`'s underlying scheme). -/
noncomputable def fstC (τ : L →+* ℂ) : (ptCL τ).left ⟶ (GroupModel.ptC (L := L) τ).left :=
  pullback.fst (GroupModel.ptC (L := L) τ).hom (jO L)

/-- The section `Spec ℂ → (Spec ℂ)_L` of the base change of `ptC τ`. -/
noncomputable def secC (τ : L →+* ℂ) : cptObj τ ⟶ ptCL τ :=
  Over.homMk (pullback.lift (𝟙 (Spec (CommRingCat.of ℂ))) (cptObj τ).hom
    ((Category.id_comp _).trans (cpt_comp_jO τ).symm))
    (pullback.lift_snd _ _ _)

theorem secC_fstC (τ : L →+* ℂ) : (secC τ).left ≫ fstC τ = 𝟙 _ :=
  pullback.lift_fst _ _ _

theorem secC_snd (τ : L →+* ℂ) : (secC τ).left ≫ (ptCL τ).hom = (cptObj τ).hom :=
  pullback.lift_snd _ _ _

/-- The base change of a complex point `p` of `𝒢`, as a map to `𝒢_L`. -/
noncomputable def mapG {τ : L →+* ℂ} (p : 𝒢.Pts τ) : ptCL τ ⟶ genericFibre L 𝒢.G :=
  (Over.pullback (jO L)).map p

theorem mapG_fstG {τ : L →+* ℂ} (p : 𝒢.Pts τ) : (mapG 𝒢 p).left ≫ fstG 𝒢 = fstC τ ≫ p.left :=
  pullback.lift_fst _ _ _

theorem mapG_snd {τ : L →+* ℂ} (p : 𝒢.Pts τ) :
    (mapG 𝒢 p).left ≫ (genericFibre L 𝒢.G).hom = (ptCL τ).hom :=
  pullback.lift_snd _ _ _

/-- `χ : 𝒢(ℂ)_τ → A_L(ℂ)_τ`. -/
noncomputable def chi {τ : L →+* ℂ} (p : 𝒢.Pts τ) : CPts (A.baseChange L) τ :=
  secC τ ≫ mapG 𝒢 p ≫ 𝒢.gen.hom

theorem chi_mul {τ : L →+* ℂ} (p₁ p₂ : 𝒢.Pts τ) : (chi 𝒢) (p₁ * p₂) = (chi 𝒢) p₁ * (chi 𝒢) p₂ := by
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  haveI : IsMonHom 𝒢.gen.hom := 𝒢.gen_hom
  have hm : mapG 𝒢 (p₁ * p₂) = mapG 𝒢 p₁ * mapG 𝒢 p₂ := Functor.map_mul _ _ _
  unfold chi
  rw [hm, MonObj.mul_comp, MonObj.comp_mul]

theorem gen_hom_inv_left : 𝒢.gen.hom.left ≫ 𝒢.gen.inv.left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]

theorem gen_inv_hom_left : 𝒢.gen.inv.left ≫ 𝒢.gen.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]

theorem theta_chi {τ : L →+* ℂ} (p : 𝒢.Pts τ) : (theta 𝒢) ((chi 𝒢) p) = p := by
  apply Over.OverMorphism.ext
  rw [theta_left]
  unfold chi toModel
  simp only [Over.comp_left, Category.assoc]
  rw [← Category.assoc 𝒢.gen.hom.left, gen_hom_inv_left, Category.id_comp, mapG_fstG]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p.left) (secC_fstC τ)).trans
    (Category.id_comp _))

theorem chi_theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) : (chi 𝒢) ((theta 𝒢) q) = q := by
  apply Over.OverMorphism.ext
  have key : (secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left = q.left ≫ 𝒢.gen.inv.left := by
    apply pullback.hom_ext
    · change ((secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left) ≫ fstG 𝒢 =
        (q.left ≫ 𝒢.gen.inv.left) ≫ fstG 𝒢
      rw [Category.assoc, mapG_fstG]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ((theta 𝒢) q).left)
        (secC_fstC τ)).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm))
    · change ((secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left) ≫ (genericFibre L 𝒢.G).hom =
        (q.left ≫ 𝒢.gen.inv.left) ≫ (genericFibre L 𝒢.G).hom
      rw [Category.assoc, mapG_snd, secC_snd, Category.assoc, Over.w 𝒢.gen.inv, Over.w q]
  unfold chi
  simp only [Over.comp_left]
  rw [← Category.assoc, key, Category.assoc, gen_inv_hom_left, Category.comp_id]

theorem theta_mul {τ : L →+* ℂ} (q₁ q₂ : CPts (A.baseChange L) τ) :
    (theta 𝒢) (q₁ * q₂) = (theta 𝒢) q₁ * (theta 𝒢) q₂ := by
  conv_lhs => rw [← (chi_theta 𝒢) q₁, ← (chi_theta 𝒢) q₂, ← chi_mul, theta_chi]

theorem theta_injective {τ : L →+* ℂ} : Function.Injective (theta 𝒢 (τ := τ)) := fun a b h => by
  rw [← (chi_theta 𝒢) a, ← (chi_theta 𝒢) b, h]

theorem theta_surjective {τ : L →+* ℂ} : Function.Surjective (theta 𝒢 (τ := τ)) :=
  fun p => ⟨(chi 𝒢) p, (theta_chi 𝒢) p⟩

theorem theta_one {τ : L →+* ℂ} : (theta 𝒢) (1 : CPts (A.baseChange L) τ) = 1 := by
  have h := theta_mul 𝒢 (τ := τ) 1 1
  rw [_root_.mul_one] at h
  exact mul_left_cancel (a := (theta 𝒢) 1) (by rw [_root_.mul_one]; exact h.symm)

theorem evalAt_theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) (U : 𝒢.G.left.Opens)
    (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt ((theta 𝒢) q) U s = cEvalAt q ((toModel 𝒢) ⁻¹ᵁ U) ((toModel 𝒢).app U s) := by
  unfold GroupModel.evalAt cEvalAt
  by_cases h : ⊤ ≤ q.left ⁻¹ᵁ ((toModel 𝒢) ⁻¹ᵁ U)
  · have h' : ⊤ ≤ ((theta 𝒢) q).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ ((theta 𝒢) q).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

end Transport

/-- **`AnalyticUniformizationOfDim` follows from leaf-push2's leaf `UniformizationExists`
(T35), proved.** Apply T35 to `A_L` over `L` at `σ = τ` (`dim A_L = dim A` by g0-dim's
`G0Dim.dim_baseChange`) and transport along `θ`. -/
theorem analyticUniformizationOfDim_of_uniformizationExists
    (hT : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.AnalyticUniformizationOfDim := by
  intro K _ A L _ _ _ 𝒢 τ g hg
  have hgL : (A.baseChange L).dim = (g : WithBot ℕ∞) := by
    rw [← hg]
    exact G0Dim.dim_baseChange L A.X.left A.X.hom
  obtain ⟨Λ, Φ₀, hd, hZ, hmul, hker, hsurj, hopen, hdiff⟩ := hT L (A.baseChange L) τ g hgL
  refine ⟨Λ, fun z => (theta 𝒢) (Φ₀ z), hd, hZ, fun z w => ?_, fun z => ?_, ?_, fun U => ?_,
    fun U s => ?_⟩
  · simp only [hmul, theta_mul]
  · rw [← hker z, ← theta_one 𝒢 (τ := τ)]
    exact (theta_injective 𝒢).eq_iff
  · exact (theta_surjective 𝒢).comp hsurj
  · exact hopen ((toModel 𝒢) ⁻¹ᵁ U)
  · have := hdiff ((toModel 𝒢) ⁻¹ᵁ U) ((toModel 𝒢).app U s)
    refine this.congr fun z _ => ?_
    exact (evalAt_theta 𝒢) (Φ₀ z) U s

end ZInQ.Metrization2

/-! ## metrization2: toward `ProductMapLocalStructure` — evaluation at complex points of schemes,
and sums of products in a pushout of commutative rings -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits Opposite

/-- The value at a complex point `q : Spec ℂ → X` of `s ∈ Γ(X, U)` (`0` if `q ∉ U(ℂ)`). Same
formula as def-faltings' `GroupModel.evalAt` (which is `ev p.left`). -/
noncomputable def ev {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (s : Γ(X, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ q ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ h s)
    else 0

section Ev

variable {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X)

theorem ev_comp (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) :
    ev (q ≫ f) U s = ev q (f ⁻¹ᵁ U) (f.app U s) := by
  unfold ev
  by_cases h : ⊤ ≤ q ⁻¹ᵁ (f ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (q ≫ f) ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (q ≫ f) ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem ev_res {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ q ⁻¹ᵁ V) (s : Γ(X, U)) :
    ev q V (X.presheaf.map i.op s) = ev q U s := by
  have hU : ⊤ ≤ q ⁻¹ᵁ U := hV.trans ((TopologicalSpace.Opens.map q.base).map i).le
  unfold ev
  rw [dif_pos hV, dif_pos hU, ← Scheme.Hom.map_appLE q hV i.op]
  rfl

theorem ev_add (U : X.Opens) (s s' : Γ(X, U)) : ev q U (s + s') = ev q U s + ev q U s' := by
  unfold ev
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem ev_mul (U : X.Opens) (s s' : Γ(X, U)) : ev q U (s * s') = ev q U s * ev q U s' := by
  unfold ev
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem ev_zero (U : X.Opens) : ev q U 0 = 0 := by
  unfold ev
  split_ifs with h
  · rw [map_zero]
    exact map_zero (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)
  · rfl

theorem ev_one (U : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U) : ev q U 1 = 1 := by
  unfold ev
  rw [dif_pos h, map_one]
  exact map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)

theorem ev_pow (U : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U) (s : Γ(X, U)) (n : ℕ) :
    ev q U (s ^ n) = ev q U s ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ev_one q U h]
  | succ n ih => rw [pow_succ, pow_succ, ev_mul, ih]

theorem ev_sum (U : X.Opens) {n : ℕ} (s : Fin n → Γ(X, U)) :
    ev q U (∑ k, s k) = ∑ k, ev q U (s k) := by
  induction n with
  | zero => simp [ev_zero]
  | succ n ih => rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ev_add, ih]

/-- A complex point in `X.basicOpen s` gives `s` a nonzero value. -/
theorem ev_ne_zero_of_mem {U : X.Opens} (s : Γ(X, U)) (h : ⊤ ≤ q ⁻¹ᵁ X.basicOpen s) :
    ev q U s ≠ 0 := by
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le s)).op s) :=
    X.toRingedSpace.isUnit_res_basicOpen s
  rw [← ev_res q (homOfLE (X.basicOpen_le s)) h]
  obtain ⟨u, hu'⟩ := hu
  intro h0
  have h1 := congrArg (ev q (X.basicOpen s)) u.mul_inv
  rw [ev_mul, ev_one q _ h, hu', h0, zero_mul] at h1
  exact zero_ne_one h1

/-- A complex point of `U` at which `s` has a nonzero value lies in `X.basicOpen s`. -/
theorem mem_basicOpen_of_ev_ne_zero {U : X.Opens} (s : Γ(X, U)) (hU : ⊤ ≤ q ⁻¹ᵁ U)
    (h : ev q U s ≠ 0) : ⊤ ≤ q ⁻¹ᵁ X.basicOpen s := by
  unfold ev at h
  rw [dif_pos hU] at h
  have hu : IsUnit (q.appLE U ⊤ hU s) := by
    have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ hU s)) :=
      isUnit_iff_ne_zero.mpr h
    have := hu'.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using this
  have hb := (Spec (CommRingCat.of ℂ)).basicOpen_of_isUnit hu
  rw [Scheme.Hom.preimage_basicOpen]
  have he : q.appLE U ⊤ hU s = (Spec (CommRingCat.of ℂ)).presheaf.map (homOfLE hU).op
      (q.app U s) := rfl
  rw [he, Scheme.basicOpen_res] at hb
  rw [← hb]
  exact inf_le_right

end Ev

/-- Finite sums of products `inl(α) · inr(β)`. -/
def IsSumProd {B C P : Type} [CommRing B] [CommRing C] [CommRing P] (inl : B →+* P)
    (inr : C →+* P) (r : P) : Prop :=
  ∃ (n : ℕ) (α : Fin n → B) (β : Fin n → C), r = ∑ k, inl (α k) * inr (β k)

theorem isSumProd_add {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r r' : P} (h : IsSumProd inl inr r) (h' : IsSumProd inl inr r') :
    IsSumProd inl inr (r + r') := by
  obtain ⟨n, α, β, rfl⟩ := h
  obtain ⟨m, α', β', rfl⟩ := h'
  refine ⟨n + m, Fin.append α α', Fin.append β β', ?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem isSumProd_mul {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r r' : P} (h : IsSumProd inl inr r) (h' : IsSumProd inl inr r') :
    IsSumProd inl inr (r * r') := by
  obtain ⟨n, α, β, rfl⟩ := h
  obtain ⟨m, α', β', rfl⟩ := h'
  refine ⟨n * m, fun k => α (finProdFinEquiv.symm k).1 * α' (finProdFinEquiv.symm k).2,
    fun k => β (finProdFinEquiv.symm k).1 * β' (finProdFinEquiv.symm k).2, ?_⟩
  rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  show _ = ∑ k, (fun p : Fin n × Fin m => inl (α p.1 * α' p.2) * inr (β p.1 * β' p.2))
    (finProdFinEquiv.symm k)
  refine Eq.trans ?_ (Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin n × Fin m => inl (α p.1 * α' p.2) * inr (β p.1 * β' p.2))).symm
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [map_mul]
  ring

theorem isSumProd_neg {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r : P} (h : IsSumProd inl inr r) : IsSumProd inl inr (-r) := by
  obtain ⟨n, α, β, rfl⟩ := h
  exact ⟨n, fun k => -α k, β, by simp [Finset.sum_neg_distrib]⟩

/-- In a pushout square of commutative rings, every element of the pushout is a finite sum of
products `inl(α) · inr(β)`. -/
theorem exists_sum_of_isPushout {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) (r : P) :
    ∃ (n : ℕ) (α : Fin n → B) (β : Fin n → C), r = ∑ k, inl (α k) * inr (β k) := by
  let T : Subring P := Subring.closure (Set.range inl.hom ∪ Set.range inr.hom)
  have hT : ∀ x ∈ T, IsSumProd inl.hom inr.hom x := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨c, rfl⟩
      · exact ⟨1, fun _ => b, fun _ => 1, by simp⟩
      · exact ⟨1, fun _ => 1, fun _ => c, by simp⟩
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    | one => exact ⟨1, fun _ => 1, fun _ => 1, by simp⟩
    | add x y _ _ hx hy => exact isSumProd_add hx hy
    | neg x _ hx => exact isSumProd_neg hx
    | mul x y _ _ hx hy => exact isSumProd_mul hx hy
  let jl : B ⟶ CommRingCat.of T := CommRingCat.ofHom
    (inl.hom.codRestrict T fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let jr : C ⟶ CommRingCat.of T := CommRingCat.ofHom
    (inr.hom.codRestrict T fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ jl = g ≫ jr := by
    ext a
    exact congrArg (fun φ => (ConcreteCategory.hom φ) a) h.w
  let ι : CommRingCat.of T ⟶ P := CommRingCat.ofHom T.subtype
  have hid : h.desc jl jr w ≫ ι = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc, Category.comp_id]; rfl
    · rw [h.inr_desc_assoc, Category.comp_id]; rfl
  have hr : r ∈ T := by
    have : ι (h.desc jl jr w r) = r := by rw [← ConcreteCategory.comp_apply, hid]; rfl
    rw [← this]
    exact ((h.desc jl jr w) r).2
  exact hT r hr

end ZInQ.Metrization2
/-! ## metrization2: `ProductMapLocalStructure`, proved

The local structure of a fibre product of schemes over an affine base at complex points
(`core_local`): affine opens `Vᵢ`, the affine scheme `Q = V₁ ×_S V₂` (an open of the product
through `j`), whose ring is the pushout `Γ(V₁) ⊗_{Γ(S)} Γ(V₂)` (`isPushout_appTop_of_isPullback`),
a basic open `D(h) ⊆ j⁻¹W` of `Q` and a fraction `t = a/h^N` on it. -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits Opposite

theorem specC_eq (z w : Spec (CommRingCat.of ℂ)) : z = w := by
  have hz : z.asIdeal = ⊥ := by
    haveI := z.isPrime; exact Ideal.eq_bot_of_prime _
  have hw : w.asIdeal = ⊥ := by
    haveI := w.isPrime; exact Ideal.eq_bot_of_prime _
  exact PrimeSpectrum.ext (hz.trans hw.symm)

theorem top_le_of_mem {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (pt : Spec (CommRingCat.of ℂ)) (h : q pt ∈ U) : ⊤ ≤ q ⁻¹ᵁ U := by
  intro z _
  rw [specC_eq z pt]
  exact h

/-- The section of `X` on `U` corresponding to a global section of `U.toScheme`. -/
noncomputable def secOf {X : Scheme.{0}} (U : X.Opens) (α : Γ(U.toScheme, ⊤)) : Γ(X, U) :=
  (inv (U.ι.appLE U ⊤ U.ι_preimage_self.ge)) α

theorem ev_secOf {X : Scheme.{0}} (U : X.Opens) (y : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (α : Γ(U.toScheme, ⊤)) : ev (y ≫ U.ι) U (secOf U α) = ev y ⊤ α := by
  have h1 : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := by
    intro z _
    show U.ι (y z) ∈ U
    exact (y z).2
  have h2 : ⊤ ≤ y ⁻¹ᵁ (⊤ : U.toScheme.Opens) := fun _ _ => trivial
  unfold ev
  rw [dif_pos h1, dif_pos h2]
  congr 1
  rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ U.ι_preimage_self.ge h2]
  unfold secOf
  rw [← ConcreteCategory.comp_apply, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

theorem ev_comp_top {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : ev (q ≫ f) ⊤ s = ev q ⊤ (f.appTop s) :=
  ev_comp q f ⊤ s

section Core

variable {S X₁ X₂ : Scheme.{0}} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)

/-- **The local structure of a fibre product over an affine base, at complex points.** -/
theorem core_local [IsAffine S] (W : (pullback f₁ f₂).Opens) (t : Γ(pullback f₁ f₂, W))
    (x₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (x₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
    (hx12 : x₁ ≫ f₁ = x₂ ≫ f₂) (hx : ⊤ ≤ (pullback.lift x₁ x₂ hx12) ⁻¹ᵁ W) :
    ∃ (V₁ : X₁.Opens) (V₂ : X₂.Opens) (n : ℕ) (a c : Fin n → Γ(X₁, V₁))
      (b d : Fin n → Γ(X₂, V₂)),
      ⊤ ≤ x₁ ⁻¹ᵁ V₁ ∧ ⊤ ≤ x₂ ⁻¹ᵁ V₂ ∧
      (∑ k, ev x₁ V₁ (c k) * ev x₂ V₂ (d k)) ≠ 0 ∧
      ∀ (y₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (y₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
        (hy : y₁ ≫ f₁ = y₂ ≫ f₂), ⊤ ≤ y₁ ⁻¹ᵁ V₁ → ⊤ ≤ y₂ ⁻¹ᵁ V₂ →
        (∑ k, ev y₁ V₁ (c k) * ev y₂ V₂ (d k)) ≠ 0 →
        ⊤ ≤ (pullback.lift y₁ y₂ hy) ⁻¹ᵁ W ∧
        ev (pullback.lift y₁ y₂ hy) W t * (∑ k, ev y₁ V₁ (c k) * ev y₂ V₂ (d k)) =
          ∑ k, ev y₁ V₁ (a k) * ev y₂ V₂ (b k) := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of ℂ)) := inferInstance
  have hpt : pt ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := trivial
  obtain ⟨V₁, hV₁, m₁, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x₁ pt ∈ (⊤ : X₁.Opens) from trivial)
  obtain ⟨V₂, hV₂, m₂, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x₂ pt ∈ (⊤ : X₂.Opens) from trivial)
  haveI : IsAffine V₁.toScheme := hV₁
  haveI : IsAffine V₂.toScheme := hV₂
  set g₁ := V₁.ι ≫ f₁ with hg₁
  set g₂ := V₂.ι ≫ f₂ with hg₂
  let j : pullback g₁ g₂ ⟶ pullback f₁ f₂ :=
    pullback.map g₁ g₂ f₁ f₂ V₁.ι V₂.ι (𝟙 S) (by simp [hg₁]) (by simp [hg₂])
  have hj1 : j ≫ pullback.fst f₁ f₂ = pullback.fst g₁ g₂ ≫ V₁.ι := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd f₁ f₂ = pullback.snd g₁ g₂ ≫ V₂.ι := pullback.lift_snd _ _ _
  -- complex points of `V₁ × V₂` lift to `Q`
  have lift_pt : ∀ (y₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (y₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
      (hy : y₁ ≫ f₁ = y₂ ≫ f₂), ⊤ ≤ y₁ ⁻¹ᵁ V₁ → ⊤ ≤ y₂ ⁻¹ᵁ V₂ →
      ∃ yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂, yQ ≫ j = pullback.lift y₁ y₂ hy ∧
        yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι = y₁ ∧ yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι = y₂ := by
    intro y₁ y₂ hy h1 h2
    have r1 : Set.range y₁ ⊆ Set.range V₁.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h1 (show z ∈ ⊤ from trivial)
    have r2 : Set.range y₂ ⊆ Set.range V₂.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h2 (show z ∈ ⊤ from trivial)
    let z₁ := IsOpenImmersion.lift V₁.ι y₁ r1
    let z₂ := IsOpenImmersion.lift V₂.ι y₂ r2
    have hz₁ : z₁ ≫ V₁.ι = y₁ := IsOpenImmersion.lift_fac _ _ _
    have hz₂ : z₂ ≫ V₂.ι = y₂ := IsOpenImmersion.lift_fac _ _ _
    have hc : z₁ ≫ g₁ = z₂ ≫ g₂ := by
      rw [hg₁, hg₂, ← Category.assoc, hz₁, ← Category.assoc, hz₂, hy]
    refine ⟨pullback.lift z₁ z₂ hc, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hj1, pullback.lift_fst, pullback.lift_fst_assoc, hz₁]
      · rw [Category.assoc, hj2, pullback.lift_snd, pullback.lift_snd_assoc, hz₂]
    · rw [pullback.lift_fst_assoc, hz₁]
    · rw [pullback.lift_snd_assoc, hz₂]
  obtain ⟨xQ, hxQ, -, -⟩ := lift_pt x₁ x₂ hx12 (top_le_of_mem _ _ pt m₁)
    (top_le_of_mem _ _ pt m₂)
  have hxQW : xQ pt ∈ j ⁻¹ᵁ W := by
    have := hx hpt
    rw [← hxQ] at this
    exact this
  obtain ⟨h, hhW, hhx⟩ := (isAffineOpen_top (pullback g₁ g₂)).exists_basicOpen_le
    (V := j ⁻¹ᵁ W) ⟨xQ pt, hxQW⟩ trivial
  -- the fraction
  set tQ : Γ(pullback g₁ g₂, (pullback g₁ g₂).basicOpen h) :=
    (pullback g₁ g₂).presheaf.map (homOfLE hhW).op (j.app W t) with htQ
  obtain ⟨⟨a0, ⟨_, N, rfl⟩⟩, heq⟩ := IsLocalization.surj (Submonoid.powers h) tQ
  have hal : ∀ r : Γ(pullback g₁ g₂, ⊤),
      algebraMap Γ(pullback g₁ g₂, ⊤) Γ(pullback g₁ g₂, (pullback g₁ g₂).basicOpen h) r =
        (pullback g₁ g₂).presheaf.map (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op r :=
    fun _ => rfl
  have heq' : tQ * (pullback g₁ g₂).presheaf.map (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op
      (h ^ (N + 1)) = (pullback g₁ g₂).presheaf.map
        (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op (a0 * h) := by
    simp only at heq
    rw [← hal, ← hal, pow_succ, map_mul, map_mul, ← mul_assoc, heq]
  -- sums of products
  have hpo := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g₁ g₂)
  obtain ⟨n₁, α, β, hα⟩ := exists_sum_of_isPushout hpo (a0 * h)
  obtain ⟨n₂, γ, δ, hγ⟩ := exists_sum_of_isPushout hpo (h ^ (N + 1))
  -- evaluation of a sum of products at a lifted point
  have key : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂) {m : ℕ}
      (u : Fin m → Γ(V₁.toScheme, ⊤)) (v : Fin m → Γ(V₂.toScheme, ⊤)),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (secOf V₁ (u k)) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (secOf V₂ (v k))) =
      ev yQ ⊤ (∑ k, (pullback.fst g₁ g₂).appTop (u k) * (pullback.snd g₁ g₂).appTop (v k)) := by
    intro yQ m u v
    rw [ev_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ev_mul, ← Category.assoc, ev_secOf, ← Category.assoc, ev_secOf, ev_comp_top,
      ev_comp_top]
  let a : Fin (n₁ + n₂) → Γ(X₁, V₁) := Fin.append (fun k => secOf V₁ (α k)) 0
  let b : Fin (n₁ + n₂) → Γ(X₂, V₂) := Fin.append (fun k => secOf V₂ (β k)) 0
  let c : Fin (n₁ + n₂) → Γ(X₁, V₁) := Fin.append 0 (fun k => secOf V₁ (γ k))
  let d : Fin (n₁ + n₂) → Γ(X₂, V₂) := Fin.append 0 (fun k => secOf V₂ (δ k))
  have hA : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (a k) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (b k)) = ev yQ ⊤ (a0 * h) := by
    intro yQ
    rw [Fin.sum_univ_add]
    simp only [a, b, Fin.append_left, Fin.append_right, Pi.zero_apply, ev_zero, mul_zero,
      Finset.sum_const_zero, add_zero]
    rw [key, hα]
  have hH : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (c k) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (d k)) = ev yQ ⊤ h ^ (N + 1) := by
    intro yQ
    rw [Fin.sum_univ_add]
    simp only [c, d, Fin.append_left, Fin.append_right, Pi.zero_apply, ev_zero, zero_mul,
      Finset.sum_const_zero, zero_add]
    rw [key, ← hγ, ev_pow yQ ⊤ (fun _ _ => trivial)]
  refine ⟨V₁, V₂, n₁ + n₂, a, c, b, d, top_le_of_mem _ _ pt m₁, top_le_of_mem _ _ pt m₂, ?_, ?_⟩
  · obtain ⟨xQ', hxQ', e1, e2⟩ := lift_pt x₁ x₂ hx12 (top_le_of_mem _ _ pt m₁)
      (top_le_of_mem _ _ pt m₂)
    have hxQ'h : ⊤ ≤ xQ' ⁻¹ᵁ (pullback g₁ g₂).basicOpen h := by
      have hjinj : xQ' = xQ := by
        apply pullback.hom_ext
        · apply (cancel_mono V₁.ι).mp
          rw [Category.assoc, Category.assoc, e1, ← hj1, ← Category.assoc, hxQ,
            pullback.lift_fst]
        · apply (cancel_mono V₂.ι).mp
          rw [Category.assoc, Category.assoc, e2, ← hj2, ← Category.assoc, hxQ,
            pullback.lift_snd]
      rw [hjinj]
      exact top_le_of_mem _ _ pt hhx
    rw [← e1, ← e2, hH]
    exact pow_ne_zero _ (ev_ne_zero_of_mem xQ' h hxQ'h)
  · intro y₁ y₂ hy h1 h2 hne
    obtain ⟨yQ, hyQ, e1, e2⟩ := lift_pt y₁ y₂ hy h1 h2
    subst e1 e2
    rw [hH] at hne ⊢
    rw [hA]
    have hev : ev yQ ⊤ h ≠ 0 := fun h0 => hne (by rw [h0, zero_pow (Nat.succ_ne_zero N)])
    have hmem : ⊤ ≤ yQ ⁻¹ᵁ (pullback g₁ g₂).basicOpen h :=
      mem_basicOpen_of_ev_ne_zero yQ h (fun _ _ => trivial) hev
    have hW : ⊤ ≤ yQ ⁻¹ᵁ (j ⁻¹ᵁ W) := hmem.trans ((TopologicalSpace.Opens.map yQ.base).map
      (homOfLE hhW)).le
    refine ⟨?_, ?_⟩
    · rw [← hyQ]; exact hW
    · rw [← hyQ, ev_comp, ← ev_res yQ (homOfLE hhW) hmem, ← htQ,
        ← ev_pow yQ ⊤ (fun _ _ => trivial),
        ← ev_res yQ (homOfLE ((pullback g₁ g₂).basicOpen_le h)) hmem (h ^ (N + 1)),
        ← ev_mul, heq', ev_res yQ _ hmem]

end Core

end ZInQ.Metrization2
/-! ## metrization2: `ProductMapLocalStructure`, hence `JacDetNondegenerate` and
`ProductLocalStructure`, proved -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)

/-- **`ProductMapLocalStructure`, proved** (from `core_local` with `S = Spec 𝓞_L`,
`W = m⁻¹(U)`, `t = m^*s`). -/
theorem productMapLocalStructure : ProductMapLocalStructure := by
  intro K _ A B C L _ _ _ ℋ 𝒢₁ 𝒢₂ m τ U s p₁ p₂ hp
  have hw : ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), p₁'.left ≫ 𝒢₁.G.hom = p₂'.left ≫ 𝒢₂.G.hom :=
    fun p₁' p₂' => (Over.w p₁').trans (Over.w p₂').symm
  obtain ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, hall⟩ :=
    core_local 𝒢₁.G.hom 𝒢₂.G.hom (m.left ⁻¹ᵁ U) (m.left.app U s) p₁.left p₂.left (hw p₁ p₂) hp
  refine ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, fun p₁' p₂' h1' h2' hne' => ?_⟩
  obtain ⟨hmem, heq⟩ := hall p₁'.left p₂'.left (hw p₁' p₂') h1' h2' hne'
  refine ⟨hmem, ?_⟩
  have hev : ℋ.evalAt (lift p₁' p₂' ≫ m) U s =
      ev (pullback.lift p₁'.left p₂'.left (hw p₁' p₂')) (m.left ⁻¹ᵁ U) (m.left.app U s) :=
    ev_comp (pullback.lift p₁'.left p₂'.left (hw p₁' p₂')) m.left U s
  rw [hev]
  exact heq

/-- **`JacDetNondegenerate`, proved** (no hypotheses). -/
theorem jacDetNondegenerate : ZInQ.Metrization.JacDetNondegenerate :=
  jacDetNondegenerate_of productMapLocalStructure

/-- **metrization's `ProductLocalStructure`, proved** (no hypotheses). -/
theorem productLocalStructure : ZInQ.Metrization.ProductLocalStructure :=
  productLocalStructure_of productMapLocalStructure

end ZInQ.Metrization2



namespace ZInQ.ProductHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings
open PkgI3 (AbVar)

/-! ## §0. Verbatim copy (from `scratch/product-height/ProductHeight.lean`) -/

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

end Points

end ZInQ.ProductHeight

namespace ZInQ.ProductUnif

section SAlg

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings ZInQ.ProductHeight
open PkgI3 (AbVar)

/-- **Glue S-alg-1 (dimensions and nonsingularity in product form).** Let `e : MP.model ≅ 𝒢₁ ⊗ 𝒢₂`
have homomorphic components, and at `τ` let the metrization `MP` (dimension `g`) be in product
form: period lattice `Λ₁ × Λ₂` and coefficient map computed by `Φ₁ × Φ₂`, for full-lattice
analytic uniformizations `Φᵢ : ℂ^{gᵢ} → 𝒢ᵢ(ℂ)_τ`, `g₁ + g₂ = g`. Then `g₁ = dim A`, `g₂ = dim B`,
and both factor Jacobians are nonsingular on some `gᵢ`-tuple of germs.

Why true (STANDARD; algebra and calculus, no AN3). Write `nᵢ` for the `L`-dimension of the
cotangent space `𝔪/𝔪²` of `𝒢ᵢ` at the generic unit. `genStalk` is the local ring of `A_L` at its
origin (regular, smooth generic fibre), so `n₁ = dim A_L = dim A` (dimension of a finite-type
scheme over a field is invariant under field extension; EGA IV 4.1.4, UNVERIFIED locator); `dim A`
is finite since `A.X.left` is nonempty. Since `cot` is an `L`-space and `L` a localization of
`𝓞_L`, `finrank_L (hodgeSpace g) = C(n, g)`. Via `e` (whose components preserve units),
`𝔪_P/𝔪_P² = 𝔪₁/𝔪₁² ⊕ 𝔪₂/𝔪₂²`, so `MP.hodge.finrank_eq_one` gives `g ∈ {0, n₁ + n₂}`.
If `g = 0`, then `g₁ = g₂ = 0`, the `Φᵢ : ℂ⁰ → 𝒢ᵢ(ℂ)_τ` are onto, so `A_τ(ℂ)`, `B_τ(ℂ)` are single
points and `dim A = dim B = 0` (a positive-dimensional variety over `ℂ` has infinitely many
points); `Fin 0` Jacobians are `1`. Otherwise: the wedges `wedge f` span `hodgeSpace` over `L`, so
`MP.hodge.coeff_ne_zero` and the coefficient formula give `f` with `jacDet (Φ₁ × Φ₂) f ≠ 0`. The map
`prodUnif ∘ cast` satisfies the analytic clauses (product-height's `ProductUnifAnalytic`,
metrization's `ProductUniformizationAnalytic`: true, from basic opens `D(h)` of affine products),
so the derivative at `0` of a germ along it depends only on its class in `cot₁ ⊕ cot₂` and the
Jacobian rows are `(D₁x, 0)`, `(0, D₂y)`; nonsingularity forces `g₁ ≤ n₁`, `g₂ ≤ n₂`, hence
equality, and nonsingular diagonal blocks. Unproved. (Reviewed: true for all instances, including
`g = 0` and an `e` incompatible with any generic-fibre product structure.) -/
def ProductUnifDims : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) →
    (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) →
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) →
    (∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
      MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    A.dim = g₁ ∧ B.dim = g₂ ∧ (∃ f₁, 𝒢₁.jacDet Φ₁ f₁ ≠ 0) ∧ (∃ f₂, 𝒢₂.jacDet Φ₂ f₂ ≠ 0)

/-- **Glue S-alg-1a (dimensions in product form).** The hypotheses of `ProductUnifDims`; the
conclusion is its dimension half: `dim A = g₁` and `dim B = g₂`. Why true: as in `ProductUnifDims`
(the nonsingularity half is not needed for it). Unproved. -/
def ProductUnifDimsEq : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) →
    (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) →
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) →
    (∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
      MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    A.dim = g₁ ∧ B.dim = g₂

/-- **`ProductUnifDims` from its dimension half and metrization's `JacDetNondegenerate`
(proved).** An alternative to proving the nonsingularity half from the product structure: it
trades that algebra for metrization's complex-geometry glue (local parameters are analytic
coordinates). -/
theorem productUnifDims_of (hE : ProductUnifDimsEq) (hN : ZInQ.Metrization.JacDetNondegenerate) :
    ProductUnifDims := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco
  obtain ⟨hA, hB⟩ := hE K A B C L 𝒢₁ 𝒢₂ g MP e τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco
  obtain ⟨hd₁, hz₁⟩ := hl₁
  obtain ⟨hd₂, hz₂⟩ := hl₂
  exact ⟨hA, hB, hN K A L 𝒢₁ τ g₁ hA Λ₁ Φ₁ hz₁ hu₁, hN K B L 𝒢₂ τ g₂ hB Λ₂ Φ₂ hz₂ hu₂⟩

end SAlg

end ZInQ.ProductUnif


/-! # unif-dims: the 2-torsion of `ℂ^g/Λ` has `4^g` elements (Mathlib only)

If `Φ : ℂ^g → G` is a surjective homomorphism onto a group with kernel a discrete full `ℤ`-lattice
`Λ`, then `#{p ∈ G | p² = 1} = 2^(2g)`. Hence the dimension `g` of such a "uniformization" is
determined by the abstract group `G`. -/

namespace ZInQ.UnifDims

open Module

variable {G : Type*} [Group G] {g : ℕ}

/-- The additive homomorphism `λ ↦ Φ(λ/2)` from the lattice to `G`. -/
noncomputable def halfHom (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ))
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) : Λ →+ Additive G :=
  AddMonoidHom.mk' (fun l => Additive.ofMul (Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)))) (by
    intro a b
    simp only [Submodule.coe_add, smul_add, hmul]
    rfl)

/-- **The 2-torsion of a uniformized group.** -/
theorem card_twoTorsion (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
    (hsurj : Function.Surjective Φ) : Nat.card {p : G // p * p = 1} = 2 ^ (2 * g) := by
  set ψ := halfHom Φ Λ hmul
  -- rank of `Λ`
  have hrank : finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ Λ hrank
  -- `Λ ⧸ ker ψ ≃ range ψ ≃ G[2]`
  have hrange : ∀ p : G, p * p = 1 ↔ Additive.ofMul p ∈ ψ.range := by
    intro p
    constructor
    · intro hp
      obtain ⟨z, rfl⟩ := hsurj p
      have h2 : (2 : ℂ) • z ∈ Λ := by
        rw [← hker, two_smul, hmul, hp]
      refine ⟨⟨_, h2⟩, ?_⟩
      show Additive.ofMul (Φ ((1 / 2 : ℂ) • (2 : ℂ) • z)) = _
      rw [smul_smul]
      norm_num
    · rintro ⟨l, hl⟩
      have hl' : Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)) = p := hl
      rw [← hl', ← hmul, ← add_smul]
      norm_num
      exact (hker _).mpr l.2
  have hker' : ψ.ker = (AddSubgroup.pi Set.univ (fun _ : Fin (2 * g) =>
      AddSubgroup.zmultiples (2 : ℤ))).comap b.equivFun.toLinearMap.toAddMonoidHom := by
    ext l
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ,
      true_implies, Int.mem_zmultiples_iff]
    show Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)) = 1 ↔ _
    rw [hker]
    constructor
    · intro h i
      set μ : Λ := ⟨_, h⟩
      have hl : l = (2 : ℤ) • μ := by
        ext1
        simp only [SetLike.val_smul, μ]
        rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        norm_num
      refine ⟨b.equivFun μ i, ?_⟩
      have := congrArg (fun x => b.equivFun x i) hl
      simp only [LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at this
      exact this
    · intro h
      choose d hd using h
      let μ : Λ := b.equivFun.symm d
      have hl : l = (2 : ℤ) • μ := by
        apply b.equivFun.injective
        ext i
        simp only [LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, μ,
          LinearEquiv.apply_symm_apply]
        exact hd i
      have : (1 / 2 : ℂ) • (l : Fin g → ℂ) = (μ : Fin g → ℂ) := by
        rw [hl, SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        norm_num
      rw [this]
      exact μ.2
  have hidx : ψ.ker.index = 2 ^ (2 * g) := by
    rw [hker', AddSubgroup.index_comap_of_surjective _ b.equivFun.surjective,
      AddSubgroup.index_pi]
    simp [Int.index_zmultiples]
  calc Nat.card {p : G // p * p = 1}
      = Nat.card ψ.range := Nat.card_congr
        (Equiv.subtypeEquiv Additive.ofMul (fun p => hrange p))
    _ = Nat.card (Λ ⧸ ψ.ker) := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv.symm
    _ = 2 ^ (2 * g) := hidx

/-- **The dimension of a uniformization is determined by the group.** -/
theorem dim_eq_of_unif {g g' : ℕ} (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g' → ℂ) → G) (Λ' : Submodule ℤ (Fin g' → ℂ))
    (hd : DiscreteTopology Λ) (hz : IsZLattice ℝ Λ) (hd' : DiscreteTopology Λ')
    (hz' : IsZLattice ℝ Λ')
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
    (hsurj : Function.Surjective Φ)
    (hmul' : ∀ z w, Φ' (z + w) = Φ' z * Φ' w) (hker' : ∀ z, Φ' z = 1 ↔ z ∈ Λ')
    (hsurj' : Function.Surjective Φ') : g = g' := by
  have h1 := card_twoTorsion Φ Λ hmul hker hsurj
  have h2 := card_twoTorsion Φ' Λ' hmul' hker' hsurj'
  rw [h1] at h2
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

end ZInQ.UnifDims


/-! ## unif-dims: `ProductUnifDims` from T35 (`UniformizationExists`)

The dimension half (`ProductUnifDimsEq`) holds because the dimension of an analytic uniformization
of `𝒢(ℂ)_τ` is determined by the group `𝒢(ℂ)_τ` (its 2-torsion has `4^g` elements,
`ZInQ.UnifDims.dim_eq_of_unif`), and T35 supplies one uniformization of dimension `dim A`
(`AnalyticUniformizationOfDim`, metrization2's transport of T35 to group models). The
nonsingularity half is metrization2's `jacDetNondegenerate` (proved, no hypotheses). The product
structure and the metrization `MP` are not used. -/

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)

/-- An abelian variety has finite dimension (copied from metrization's `abVar_dim_finite`). -/
theorem abVar_dim_finite (K : Type) [Field K] (A : AbVar K) :
    ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact G0Dim.dim_finite A.X.left A.X.hom

/-- **The dimension of an analytic uniformization is `dim A`** (from `AnalyticUniformizationOfDim`,
i.e. from T35). Any full-lattice analytic uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` has `g = dim A`. Only
the algebraic clauses (homomorphism, kernel, onto) of the two uniformizations are used. -/
theorem dim_eq_of_isAnalyticUniformization (hU : ZInQ.Metrization.AnalyticUniformizationOfDim)
    {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (hd : DiscreteTopology Λ) (hz : IsZLattice ℝ Λ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) : A.dim = (g : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := abVar_dim_finite K A
  obtain ⟨Λ', Φ', hd', hz', hΦ'⟩ := hU K A L 𝒢 τ n hn
  have := dim_eq_of_unif Φ Λ Φ' Λ' hd hz hd' hz' hΦ.1 hΦ.2.1 hΦ.2.2.1 hΦ'.1 hΦ'.2.1 hΦ'.2.2.1
  rw [hn, this]

/-- **`ProductUnifDimsEq` from `AnalyticUniformizationOfDim` (proved).** -/
theorem productUnifDimsEq_of (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.ProductUnif.ProductUnifDimsEq := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ _ _
  obtain ⟨hd₁, hz₁⟩ := hl₁
  obtain ⟨hd₂, hz₂⟩ := hl₂
  exact ⟨dim_eq_of_isAnalyticUniformization hU 𝒢₁ τ Λ₁ Φ₁ hd₁ hz₁ hu₁,
    dim_eq_of_isAnalyticUniformization hU 𝒢₂ τ Λ₂ Φ₂ hd₂ hz₂ hu₂⟩

/-- **`ProductUnifDims` from `AnalyticUniformizationOfDim` (proved).** -/
theorem productUnifDims_of_unifOfDim (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.ProductUnif.ProductUnifDims :=
  ZInQ.ProductUnif.productUnifDims_of (productUnifDimsEq_of hU)
    ZInQ.Metrization2.jacDetNondegenerate

/-- **`ProductUnifDims` from the textbook leaf T35 `UniformizationExists` (proved).** -/
theorem productUnifDims_of_uniformizationExists (hT : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.ProductUnif.ProductUnifDims :=
  productUnifDims_of_unifOfDim
    (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT)

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.dim_eq_of_unif
#print axioms ZInQ.UnifDims.dim_eq_of_isAnalyticUniformization
#print axioms ZInQ.UnifDims.productUnifDimsEq_of
#print axioms ZInQ.UnifDims.productUnifDims_of_unifOfDim
#print axioms ZInQ.UnifDims.productUnifDims_of_uniformizationExists
#print axioms ZInQ.Metrization2.jacDetNondegenerate
#print axioms ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists

/-! ## metrization: `ProductHodgeCompat` split into an algebraic and an analytic Prop

`pullGerm φ : 𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}` (pull-back of germs along a homomorphism of group models; it
needs `φ(ξ_𝒢) = ξ_ℋ`, proved from `IsMonHom`). `ProductHodgeLattice` (algebra: `s = p₁*s₁ ∧ p₂*s₂`
lies in the lattice with multiplicative index) and `ProductJacobian` (analysis: block-diagonal
Jacobian) give `ProductHodgeCompat` (with `ProductUniformization`). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

section Pull

variable {K : Type} [Field K] {A C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A homomorphism of group models maps the identity `ξ` of the generic fibre to `ξ` (proved). -/
theorem map_genericUnit_of_isMonHom {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : φ.left 𝒢.genericUnit = ℋ.genericUnit := by
  have h1 : η[𝒢.G] ≫ φ = η[ℋ.G] := IsMonHom.one_hom φ
  have h2 : (η[𝒢.G]).left ≫ φ.left = (η[ℋ.G]).left := by rw [← Over.comp_left, h1]
  show φ.left ((η[𝒢.G]).left (genericPt L)) = (η[ℋ.G]).left (genericPt L)
  rw [← h2]
  rfl

/-- Pull-back of germs at `ξ` along a homomorphism of group models: `𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}`. -/
noncomputable def pullGerm {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : ℋ.genStalk ⟶ 𝒢.genStalk :=
  ℋ.G.left.presheaf.stalkSpecializes
      ((congrArg (fun x => x ⤳ ℋ.genericUnit) (map_genericUnit_of_isMonHom φ)).mpr
        specializes_rfl) ≫
    φ.left.stalkMap 𝒢.genericUnit

end Pull

/-- **Glue (algebra: the Hodge lattice of a product).** For `e : 𝒢P ≅ M₁.model × M₂.model` with
homomorphic components: `hodgeSpace (g₁+g₂)` of `𝒢P` is a line, and there are germ tuples
`f₁, f₂` and their pull-backs `f = (p₁*f₁, p₂*f₂)`, and `a₁, a₂ ∈ L`, such that `sᵢ = aᵢ · 1⊗dfᵢ`
are nonzero elements of `⋀ω_{𝒢ᵢ}`, `s = a₁a₂ · 1⊗df` is a nonzero element of `⋀ω_{𝒢P}`, and
`[⋀ω_{𝒢P} : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]`. Why true (STANDARD): `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` and
`𝔪_ξ/𝔪_ξ² = p₁*C₁ ⊕ p₂*C₂` for a product of smooth group schemes (EGA IV 17.2.3, UNVERIFIED
locator), so `⋀^{g₁+g₂}` is the tensor product of the two lines; for invertible `𝓞_L`-modules
indices multiply (norms of ideals). Unproved (stalks and differentials of fibre products are
not in Mathlib). -/
def ProductHodgeLattice : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂)
    (e : 𝒢P.G ≅ M₁.model.G ⊗ M₂.model.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    Module.finrank L (𝒢P.hodgeSpace (g₁ + g₂)) = 1 ∧
    ∃ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal M₁.model.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal M₂.model.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk) (a₁ a₂ : L),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) ∧
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) ∧
      a₁ • M₁.model.wedge f₁ ∈ M₁.hodge.lattice ∧ a₁ • M₁.model.wedge f₁ ≠ 0 ∧
      a₂ • M₂.model.wedge f₂ ∈ M₂.hodge.lattice ∧ a₂ • M₂.model.wedge f₂ ≠ 0 ∧
      (a₁ * a₂) • 𝒢P.wedge f ∈ 𝒢P.detLattice (g₁ + g₂) ∧ (a₁ * a₂) • 𝒢P.wedge f ≠ 0 ∧
      secIndex (𝒢P.detLattice (g₁ + g₂)) ((a₁ * a₂) • 𝒢P.wedge f) =
        secIndex M₁.hodge.lattice (a₁ • M₁.model.wedge f₁) *
          secIndex M₂.hodge.lattice (a₂ • M₂.model.wedge f₂)

end ZInQ.Metrization

/-! ## unif-dims: metrization's `ProductHodgeLattice` reduced

`ProductHodgeLattice` (metrization's glue, copied verbatim above) follows from:
* `ProductCotangent` (new glue, algebraic geometry): the cotangent space at the generic unit of a
  product model is the direct sum of the factors' cotangent spaces, through the pull-backs of germs
  along the two projections, and the conormal lattice `ω` of the product is the sum of the two
  pulled-back lattices;
* `DetLatticeProd` (new glue, pure commutative algebra over `𝓞_K`, no geometry): for a direct sum
  of two modules with full lattices `ω₁, ω₂` of ranks `g₁, g₂`, the determinant lattice of
  `ω₁ ⊕ ω₂` has a section whose index is the product of the factors' indices;
* the kernel's `HodgeLattice.CotangentRank` (already reduced by hodge-lattice to
  `TangentDimAtOrigin`, with `DimBaseChange` proved below from g0-dim);
* `AnalyticUniformizationOfDim` (from T35), only to know `gᵢ = dim` for the metrizations `Mᵢ`.
The kernel's `omegaLocal` (proved) supplies finiteness and fullness of each `ω`. -/

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice TensorProduct
open PkgI3 (AbVar)

/-- **Glue (algebraic geometry: the cotangent space and conormal lattice of a product model).**
Let `e : 𝒢P ≅ 𝒢₁ ×_{𝓞_L} 𝒢₂` have homomorphic components `pᵢ`. There are `𝓞_L`-linear maps
`jᵢ : 𝔪ᵢ/𝔪ᵢ² → 𝔪_P/𝔪_P²` (at the generic units `ξ`) such that
* `jᵢ(df) = d(pᵢ* f)` for every germ `f ∈ 𝔪ᵢ` (in particular `pᵢ* f ∈ 𝔪_P`), where `pᵢ*` is
  metrization's `pullGerm`;
* `(x, y) ↦ j₁ x + j₂ y` is bijective;
* `ω_{𝒢P} = j₁(ω_{𝒢₁}) + j₂(ω_{𝒢₂})`.
Why true (STANDARD). `𝒪_{𝒢P,ξ}` is the local ring of `A_L ×_L B_L` at the origin, a localization
of `𝒪_{A_L,0} ⊗_L 𝒪_{B_L,0}`, and `𝔪/𝔪²` of a product of `L`-rational points is the direct sum
(`Ω_{X ×_S Y/S} = p₁*Ω_{X/S} ⊕ p₂*Ω_{Y/S}`; EGA IV 16.4.23 / Stacks, differentials of a fibre
product, UNVERIFIED locators). For the lattices: at every point `s` of `Spec 𝓞_L`, the ideal of the
unit section of `𝒢₁ ×_S 𝒢₂` at `e(s)` is generated by `p₁*I₁ + p₂*I₂` (the section is the
product of the two sections), so `(ω_P)_s = j₁(ω₁)_s ⊕ j₂(ω₂)_s`, and intersecting over `s` in the
direct sum gives the claim. `jᵢ` is `𝓞_L`-linear because `pᵢ` lies over `Spec 𝓞_L`. Unproved
(task infra-stalks builds the stalk infrastructure for fibre products). -/
def ProductCotangent : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    ∃ (j₁ : 𝒢₁.cotangent →ₗ[𝓞 L] 𝒢P.cotangent) (j₂ : 𝒢₂.cotangent →ₗ[𝓞 L] 𝒢P.cotangent),
      (∀ f : IsLocalRing.maximalIdeal 𝒢₁.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ fst _ _)).hom (f : 𝒢₁.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₁ (𝒢₁.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      (∀ f : IsLocalRing.maximalIdeal 𝒢₂.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ snd _ _)).hom (f : 𝒢₂.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₂ (𝒢₂.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      Function.Bijective (LinearMap.coprod j₁ j₂) ∧
      𝒢P.omega = 𝒢₁.omega.map j₁ ⊔ 𝒢₂.omega.map j₂

/-- **Glue (commutative algebra: the determinant lattice of a direct sum).** Let `K` be a number
field, `M₁, M₂, M` modules over `𝓞_K` with `M₁ × M₂ ≅ M` through `(x, y) ↦ j₁ x + j₂ y`, and
`ωᵢ ⊆ Mᵢ` finitely generated submodules spanning `K ⊗ Mᵢ`, which has `K`-rank `gᵢ`. Put
`ω = j₁ω₁ + j₂ω₂`. Then there are `xᵢ ∈ Mᵢ^{gᵢ}` and `aᵢ ∈ K` such that `sᵢ = aᵢ · 1 ⊗ ∧xᵢ` is a
nonzero element of `detLat ωᵢ gᵢ`, `s = a₁a₂ · 1 ⊗ ∧(j₁x₁, j₂x₂)` is a nonzero element of
`detLat ω (g₁+g₂)`, and `[detLat ω : 𝓞s] = [detLat ω₁ : 𝓞s₁]·[detLat ω₂ : 𝓞s₂]`.
Why true (STANDARD). `K ⊗ M = (K ⊗ M₁) ⊕ (K ⊗ M₂)` and the images `Ω̄ᵢ` of `ωᵢ` are full
`𝓞_K`-lattices (projective of rank `gᵢ`); `K ⊗ ⋀^{g₁+g₂} M = ⋀^{g₁}(K⊗M₁) ⊗ ⋀^{g₂}(K⊗M₂)` and
`det(Ω̄₁ ⊕ Ω̄₂) = det Ω̄₁ ⊗ det Ω̄₂` (Bourbaki, Algèbre III §7, UNVERIFIED locator; in coordinates,
generalized Laplace expansion along the first `g₁` columns). Identifying the lines with `K`, the
lattices become fractional ideals `I₁, I₂, I₁I₂`, and the indices multiply because
`[I : 𝓞x] = |N(x)| / N(I)` (the kernel's `secIndex_mul_absNorm`) and both norms are
multiplicative. Take `xᵢ` an `𝓞_K`-family in `ωᵢ` forming a `K`-basis and `aᵢ = 1`. Unproved. -/
def DetLatticeProd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (M₁ M₂ M : Type) [AddCommGroup M₁] [Module (𝓞 K) M₁]
    [AddCommGroup M₂] [Module (𝓞 K) M₂] [AddCommGroup M] [Module (𝓞 K) M]
    (ω₁ : Submodule (𝓞 K) M₁) (ω₂ : Submodule (𝓞 K) M₂) (j₁ : M₁ →ₗ[𝓞 K] M)
    (j₂ : M₂ →ₗ[𝓞 K] M) (g₁ g₂ : ℕ),
    Function.Bijective (LinearMap.coprod j₁ j₂) → ω₁.FG → ω₂.FG →
    Module.rank K (K ⊗[𝓞 K] M₁) = g₁ → Module.rank K (K ⊗[𝓞 K] M₂) = g₂ →
    Submodule.span K (Set.range fun x : ω₁ => (1 : K) ⊗ₜ[𝓞 K] (x : M₁)) = ⊤ →
    Submodule.span K (Set.range fun x : ω₂ => (1 : K) ⊗ₜ[𝓞 K] (x : M₂)) = ⊤ →
    ∃ (x₁ : Fin g₁ → M₁) (x₂ : Fin g₂ → M₂) (a₁ a₂ : K),
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ∈ detLat ω₁ g₁ ∧
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ≠ 0 ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ∈ detLat ω₂ g₂ ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ≠ 0 ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ∈ detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂) ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ≠ 0 ∧
      secIndex (detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂))
          ((a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
            (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂)))) =
        secIndex (detLat ω₁ g₁) (a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁)) *
          secIndex (detLat ω₂ g₂) (a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂))

/-- hodge-lattice's `DimBaseChange`, proved (g0-dim's `G0Dim.dim_baseChange`). -/
theorem dimBaseChange : DimBaseChange := fun _ _ A L _ _ =>
  G0Dim.dim_baseChange L A.X.left A.X.hom

/-- `K ⊗ -` turns a direct sum decomposition into a sum of ranks. -/
theorem rank_tensor_of_bijective {K : Type} [Field K] [NumberField K] {M₁ M₂ M : Type}
    [AddCommGroup M₁] [Module (𝓞 K) M₁] [AddCommGroup M₂] [Module (𝓞 K) M₂] [AddCommGroup M]
    [Module (𝓞 K) M] (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) {g₁ g₂ : ℕ}
    (h₁ : Module.rank K (K ⊗[𝓞 K] M₁) = g₁) (h₂ : Module.rank K (K ⊗[𝓞 K] M₂) = g₂) :
    Module.rank K (K ⊗[𝓞 K] M) = ((g₁ + g₂ : ℕ) : Cardinal) := by
  let E : (M₁ × M₂) ≃ₗ[𝓞 K] M := LinearEquiv.ofBijective _ hbij
  rw [← (LinearEquiv.baseChange (𝓞 K) K _ _ E).rank_eq,
    (TensorProduct.prodRight (𝓞 K) K K M₁ M₂).rank_eq, rank_prod', h₁, h₂]
  push_cast
  rfl

/-- **`ProductHodgeLattice` from `ProductCotangent`, `DetLatticeProd`, `CotangentRank` and
`AnalyticUniformizationOfDim` (proved).** -/
theorem productHodgeLattice_of (hPC : ProductCotangent) (hDL : DetLatticeProd)
    (hCR : CotangentRank) (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.Metrization.ProductHodgeLattice := by
  intro K _ A B C L _ _ _ 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  obtain ⟨j₁, j₂, hc₁, hc₂, hbij, hom⟩ := hPC K A B C L 𝒢P M₁.model M₂.model e hfst hsnd
  obtain ⟨τ⟩ := (inferInstance : Nonempty (L →+* ℂ))
  have hg : ∀ {X : AbVar K} {g : ℕ} (M : MetrizedModel X L g), X.dim = (g : WithBot ℕ∞) := by
    intro X g M
    obtain ⟨Φ, hΦ, -⟩ := M.arch τ
    exact dim_eq_of_isAnalyticUniformization hU M.model τ _ Φ (M.hodge.periods_discrete τ)
      (M.hodge.periods_isZLattice τ) hΦ
  have hr₁ := hCR K A L M₁.model g₁ (hg M₁)
  have hr₂ := hCR K B L M₂.model g₂ (hg M₂)
  have hfg : ∀ {X : AbVar K} (𝒢 : GroupModel X L), 𝒢.omega.FG := fun 𝒢 =>
    omegaFG_of_omegaLocal omegaLocal K _ L 𝒢
  have hsp : ∀ {X : AbVar K} (𝒢 : GroupModel X L), Submodule.span L
      (Set.range fun x : 𝒢.omega => (1 : L) ⊗ₜ[𝓞 L] (x : 𝒢.cotangent)) = ⊤ := fun 𝒢 =>
    omegaSpans_of_omegaLocal omegaLocal K _ L 𝒢
  have hrP := rank_tensor_of_bijective j₁ j₂ hbij hr₁ hr₂
  refine ⟨(hodgeLattice_of_lattice 𝒢P.omega (hfg 𝒢P) hrP (hsp 𝒢P)).1, ?_⟩
  obtain ⟨x₁, x₂, a₁, a₂, h₁, h₁', h₂, h₂', hP, hP', hidx⟩ :=
    hDL L M₁.model.cotangent M₂.model.cotangent 𝒢P.cotangent M₁.model.omega M₂.model.omega
      j₁ j₂ g₁ g₂ hbij (hfg _) (hfg _) hr₁ hr₂ (hsp _) (hsp _)
  choose f₁ hf₁ using fun i => (IsLocalRing.maximalIdeal M₁.model.genStalk).toCotangent_surjective
    (x₁ i)
  choose f₂ hf₂ using fun i => (IsLocalRing.maximalIdeal M₂.model.genStalk).toCotangent_surjective
    (x₂ i)
  choose m₁ hm₁ using fun i => hc₁ (f₁ i)
  choose m₂ hm₂ using fun i => hc₂ (f₂ i)
  let f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk :=
    Fin.append (fun i => ⟨_, m₁ i⟩) (fun j => ⟨_, m₂ j⟩)
  have hw₁ : M₁.model.wedge f₁ = (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g₁ x₁ := by
    unfold GroupModel.wedge
    congr 2
    funext i
    exact hf₁ i
  have hw₂ : M₂.model.wedge f₂ = (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g₂ x₂ := by
    unfold GroupModel.wedge
    congr 2
    funext i
    exact hf₂ i
  have hw : 𝒢P.wedge f = (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) (g₁ + g₂)
      (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂)) := by
    unfold GroupModel.wedge
    congr 2
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [f, Fin.append_left, Function.comp_apply]
      rw [← hm₁ i, ← hf₁ i]
      rfl
    · simp only [f, Fin.append_right, Function.comp_apply]
      rw [← hm₂ j, ← hf₂ j]
      rfl
  have hL₁ : M₁.hodge.lattice = detLat M₁.model.omega g₁ := M₁.lattice_eq
  have hL₂ : M₂.hodge.lattice = detLat M₂.model.omega g₂ := M₂.lattice_eq
  have hLP : 𝒢P.detLattice (g₁ + g₂) =
      detLat (M₁.model.omega.map j₁ ⊔ M₂.model.omega.map j₂) (g₁ + g₂) := by
    rw [detLattice_eq, hom]
  refine ⟨f₁, f₂, f, a₁, a₂, fun i => ?_, fun j => ?_, ?_⟩
  · simp only [f, Fin.append_left]
  · simp only [f, Fin.append_right]
  rw [hw₁, hw₂, hw, hL₁, hL₂, hLP]
  exact ⟨h₁, h₁', h₂, h₂', hP, hP', hidx⟩

/-- **`ProductHodgeLattice` from `ProductCotangent`, `DetLatticeProd`, hodge-lattice's
`TangentDimAtOrigin` and T35 (proved).** -/
theorem productHodgeLattice_of_tangent (hPC : ProductCotangent) (hDL : DetLatticeProd)
    (hT : TangentDimAtOrigin) (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.Metrization.ProductHodgeLattice :=
  productHodgeLattice_of hPC hDL
    (cotangentRank_of_tangentDim (tangentDim_of_abVar hT dimBaseChange))
    (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35)

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.dimBaseChange
#print axioms ZInQ.UnifDims.rank_tensor_of_bijective
#print axioms ZInQ.UnifDims.productHodgeLattice_of
#print axioms ZInQ.UnifDims.productHodgeLattice_of_tangent
