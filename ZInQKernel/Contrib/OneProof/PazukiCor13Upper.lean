import ZInQKernel.OneProof.H.TailY
import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.OneProof.H.TailZ24

/-!
# pazuki-dict: `pazukiCor13Upper` from Pazuki's corollary for algebraic `(A, L)`

Task pazuki-dict (2026-11-16), docs/research/pazuki-dict.md.

The field `pazukiCor13Upper : ZInQ.HeightSplit.PazukiCor13Upper` (`ZInQKernel/OneProof/H/TailY.lean`) quantifies
over *analytic* data: a weak uniformization `Φ : ℂ² → A(ℂ)_σ` (leaf-push2's `IsUniformization`: a surjective analytic
homomorphism with kernel `Λ`) and a Siegel period matrix `Ω` of `Λ` (an analytic principal polarization of `ℂ²/Λ`).
Pazuki's Cor. 1.3(2) speaks of an algebraic principally polarized abelian surface `(A, L)` over `ℚ̄`.

This file
* states Pazuki's corollary (upper half) over algebraic `(A_{K'}, L)`: `L` an ample, symmetric line bundle with
  `h⁰(L) = 1` on the base change `A_{K'}` to a number field `K'`, and `Ω` the period matrix of `(A_σ, L)` for a
  biholomorphic uniformization (bp-analytic's strong `IsUniformization` of `A ×_{K,σ} ℂ`): the divisor of the
  section of `L` is, through the uniformization, the zero set of Riemann's theta function `θ(T w + c, Ω)`
  (`PazukiCor13UpperPP`, the new printed-form leaf);
* isolates the analytic-to-algebraic step as one named Prop (`AnalyticPPAlgebraic`: every analytic principal
  polarization of `A_σ(ℂ)`, `A` over a number field, is the period matrix of an algebraic symmetric principal
  `(A_{K'}, L)`; Appell–Humbert / Riemann's theta divisor, GAGA, `NS(A_ℚ̄) = NS(A_ℂ)`), rated GLUE (composite);
* proves the step from leaf-push2's weak uniformization to the biholomorphic one in Lean (`exists_strong_of_weak`,
  from the existing field `UniformizationLeafAll`, av-split's base change `ptE` and homlattice's linear lifting);
* proves `ZInQ.HeightSplit.PazukiCor13Upper` from the three (`pazukiCor13Upper_of_printed`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace PazukiDict

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open ZInQ.LeafPush2 (CPts IsSiegel IsPeriodMatrix Char2 thetaConst pazukiC2)
open ZInQ.HeightSplit (IsStableFaltingsHeight absLogHeightL2)
open AvSplit.HomLatticeAN3 (bcC ptE)
open BPAnalytic (Torus proj)

/-! ## §1. Genuine definitions -/

/-- **Riemann's theta function** `θ(z, Ω) = ∑_{n ∈ ℤ²} exp(πi nᵀΩn + 2πi nᵀz)` (Mumford, *Tata Lectures on Theta I*,
II §1; UNVERIFIED numbering). Absolutely convergent for `Ω ∈ 𝔥₂`; the `tsum` junk value `0` occurs only outside
`𝔥₂`. -/
def riemannTheta (Ω : Matrix (Fin 2) (Fin 2) ℂ) (z : Fin 2 → ℂ) : ℂ :=
  ∑' n : Fin 2 → ℤ,
    Complex.exp (Real.pi * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ Ω.mulVec (fun i => (n i : ℂ))) +
      2 * Real.pi * Complex.I * ((fun i => (n i : ℂ)) ⬝ᵥ z))

variable {K K' : Type} [Field K] [Field K'] [Algebra K K']

/-- `Spec ℂ → Spec K` through `σ = σ' ∘ (K → K')` factors through `Spec K'`. -/
theorem specMap_comp_eq (σ : K →+* ℂ) (σ' : K' →+* ℂ) (hσ : σ'.comp (algebraMap K K') = σ) :
    Spec.map (CommRingCat.ofHom σ') ≫ Spec.map (CommRingCat.ofHom (algebraMap K K')) =
      Spec.map (CommRingCat.ofHom σ) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσ]

/-- **The complex point of `A_{K'}` over `σ'` lying over a complex point `p` of `A` over `σ = σ' ∘ (K → K')`**:
`(p, Spec σ') : Spec ℂ → A ×_K K'`. -/
def liftPt (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ) (hσ : σ'.comp (algebraMap K K') = σ)
    (p : CPts A σ) : Spec (CommRingCat.of ℂ) ⟶ (A.baseChange K').X.left :=
  pullback.lift p.left (Spec.map (CommRingCat.ofHom σ')) (by
    rw [specMap_comp_eq σ σ' hσ]
    exact Over.w p)

/-- **A complex point lies on the divisor of a section** `s` of an invertible sheaf `ℳ` on `X`: its image lies in
the support of the zero scheme `Z(s)` (the vendored `Scheme.Modules.Hom.zeroLocus`). -/
def OnZeroLocus {X : Scheme.{0}} {M : X.Modules} [M.IsInvertible] (s : 𝟙_ X.Modules ⟶ M)
    (q : Spec (CommRingCat.of ℂ) ⟶ X) : Prop :=
  ∀ x, q.base x ∈ (Scheme.Modules.Hom.zeroLocus s).support

/-- **`L` is a symmetric principal polarization of `B`**: `L` is ample (t09-pic's `IsAmple`, Stacks 01PS),
symmetric (`[-1]^* L ≅ L`, the pullback along the inverse of the group scheme) and `h⁰(L) = 1` (the space of global
sections is one-dimensional over `Γ(B, 𝒪) = K'`). For ample `L`, `h⁰(L)² = deg φ_L` (Mumford, *Abelian varieties*,
§16, Riemann–Roch and the vanishing theorem; UNVERIFIED numbering), so `h⁰(L) = 1` says that `φ_L` is an isomorphism:
`L` defines a principal polarization. -/
def IsSymmPrincipal (B : PkgI3.AbVar K') (L : B.X.left.Pic) : Prop :=
  T09Pic.IsAmple B.X.left L ∧ Scheme.Pic.map (GrpObj.inv (X := B.X)).left L = L ∧
    Module.finrank Γ(B.X.left, ⊤) Γ((fromSkeleton B.X.left.Modules).obj L.val, ⊤) = 1

/-- **`Ω` is the period matrix of `(A_σ, L)` in a symplectic basis, through the uniformization `φ`.** `A` is over
`K`, `L` is a line bundle on `A_{K'}`, `σ = σ' ∘ (K → K')`, and `φ : ℂ^g ⧸ Λ ≃ A_ℂ(ℂ)` (with `A_ℂ = A ×_{K,σ} ℂ`,
`A_ℂ(ℂ) = A(ℂ)_σ` by `ptE`). There are a `ℂ`-linear isomorphism `T : ℂ^g ≃ ℂ²` carrying `Λ` onto `Ωℤ² + ℤ²`, a vector
`c ∈ ℂ²` and a global section `s` of `L` such that a point `φ(w)` lies on the divisor of `s` exactly when
`θ(T w + c, Ω) = 0`. By Riemann's theorem on the theta divisor this says that the Riemann form of `L` is the standard
symplectic form of `Ωℤ² + ℤ²` (transported by `T`), i.e. `Ω` is the period matrix of `(A_σ, L)` for the symplectic
basis given by `T` (Mumford, *Tata Lectures on Theta I*, II §1; Birkenhake–Lange, *Complex abelian varieties*, §8.1
and §8.5; UNVERIFIED numbering): for `h⁰(L) = 1`, the divisor of `s` is the theta divisor, which is reduced. -/
def IsThetaPeriodMatrix (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    (hσ : σ'.comp (algebraMap K K') = σ) (L : (A.baseChange K').X.left.Pic) {g : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ)) (φ : Torus Λ ≃+ Additive (CPts (bcC A σ) (RingHom.id ℂ)))
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)) (c : Fin 2 → ℂ)
    (s : 𝟙_ (A.baseChange K').X.left.Modules ⟶
      (fromSkeleton (A.baseChange K').X.left.Modules).obj L.val),
    (∀ w, w ∈ Λ ↔ ∃ m n : Fin 2 → ℤ, T w = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ)) ∧
    ∀ w : Fin g → ℂ, OnZeroLocus s (liftPt A σ σ' hσ (ptE A σ (Additive.toMul (φ (proj Λ w))))) ↔
      riemannTheta Ω (T w + c) = 0

/-! ## §2. The new leaf and the remaining named Prop -/

/-- **LEAF (printed form): Pazuki's Cor. 1.3(2), upper half, for algebraic `(A, L)`** (F. Pazuki, *Theta height and
Faltings height*, Bull. SMF 140 (2012), Cor. 1.3(2), pp. 21-22, `g = r = 2`; Deligne's metric p. 26; theta height
p. 30; arXiv:0907.1458v2 Cor. 1.3(2) p. 3, Def. 2.1 pp. 6-7, Def. 2.6 p. 9; read by the locator audit,
docs/research/locators.md item 5; the upper half of the display, as `ZInQ.HeightSplit.PazukiCor13Upper`).

For a principally polarized abelian surface `(A, L)` over `ℚ̄` with `H_Θ = max(1, h_Θ(A, L))`, `H_D = max(1, h_D(A))`:
`H_Θ − H_D/2 ≤ C₂(2,2) log(min(H_Θ, H_D) + 2)`, `C₂(2,2) = 1000·2⁴·(log 2⁴)⁵`.

Lean reading. `(A, L)` over `ℚ̄` is given by a model: `A` an abelian surface over a number field `K`, `L` a
symmetric principal polarization (`IsSymmPrincipal`) of the base change `A_{K'}` to a number field `K'` (`(A, L)` over
`ℚ̄` is `(A_{K'}, L) ⊗ ℚ̄`). `x` is the stable Faltings height of `A` (Faltings' normalization), so `h_D = x + log π`
(Deligne's metric, `g = 2`, locators.md item 5). The theta height: for a complex embedding `σ' : K' → ℂ`
(`σ = σ' ∘ (K → K')`), the biholomorphic uniformization `φ : ℂ^g ⧸ Λ ≃ A_ℂ(ℂ)` (bp-analytic's strong
`IsUniformization`: regular functions holomorphic, local coordinates by regular functions, `φ⁻¹` continuous) and the
period matrix `Ω ∈ 𝔥₂` of `(A_σ, L)` in a symplectic basis (`IsThetaPeriodMatrix`), `h_Θ` is the `ℓ²`-height of
the theta-null point `[θ[a;b](0, Ω)]_{a,b ∈ {0,½}²}` (any algebraic representative `z`, up to the factor `c`).
Reading steps: the identification of Pazuki's level-2 theta coordinates (Def. 2.6) with the classical
`θ[a;b](0, Ω)` is UNVERIFIED (locators.md, leaf-review-b premise 3; the review risk of 11-14: if Pazuki's coordinates
are `θ[a;0](0, 2Ω)`, Riemann's quadratic relation gives only `h(classical) ≤ h_Θ + log 4`); the theta-null point
does not depend on the symplectic basis (theta transformation formula); `h⁰(L) = 1` with `L` ample is "principal"
(Riemann–Roch). Unlike `PazukiCor13Upper`, the polarization is algebraic and the uniformization is the biholomorphic
one, as in the print. -/
def PazukiCor13UpperPP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, IsStableFaltingsHeight A x →
    ∀ (σ : K →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
      (φ : Torus Λ ≃+ Additive (CPts (bcC A σ) (RingHom.id ℂ))),
      BPAnalytic.Uniformization.IsUniformization (bcC A σ) Λ φ →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (σ' : K' →+* ℂ)
      (hσ : σ'.comp (algebraMap K K') = σ) (L : (A.baseChange K').X.left.Pic),
      IsSymmPrincipal (A.baseChange K') L →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsThetaPeriodMatrix A σ σ' hσ L Λ φ Ω →
    ∀ (F : Type) [Field F] [NumberField F] (emb : F →+* ℂ) (z : Char2 → F) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * thetaConst Ω m) →
      max 1 (absLogHeightL2 z) - max 1 (x + Real.log Real.pi) / 2 ≤
        pazukiC2 * Real.log (min (max 1 (absLogHeightL2 z)) (max 1 (x + Real.log Real.pi)) + 2)

/-- **GLUE (composite of published results): every analytic principal polarization of `A_σ(ℂ)` is algebraic and
defined over `ℚ̄`.** For an abelian variety `A` over a number field `K`, a complex embedding `σ`, the biholomorphic
uniformization `φ : ℂ^g ⧸ Λ ≃ A_ℂ(ℂ)` and any `Ω ∈ 𝔥₂` with a `ℂ`-linear `T : ℂ^g ≃ ℂ²` carrying `Λ` onto
`Ωℤ² + ℤ²` (an analytic principal polarization `T^*(Im Ω)⁻¹` with a symplectic basis): there are a number field
`K' ⊇ K`, an embedding `σ' : K' → ℂ` over `σ` and a symmetric principal polarization `L` of `A_{K'}` whose period
matrix is `Ω` (`IsThetaPeriodMatrix`).

Why true (published pieces, all locators UNVERIFIED): Riemann's theta function `θ(·, Ω)` is a section of the line
bundle of the principal Riemann form of `Ωℤ² + ℤ²` (Appell–Humbert, Mumford, *Abelian varieties*, §2; Frobenius'
theorem, `h⁰ = 1`, §3); the analytic theta divisor `{θ(T w, Ω) = 0}` is symmetric and, by Chow's theorem / GAGA
(Serre 1956; SGA 1 XII 4.4), it is an effective divisor `D` on `A_ℂ`, with `𝒪(D)` ample (Mumford §6, Application 1)
and `h⁰ = 1`; since `NS(A_ℚ̄) = NS(A_ℂ)` (the Néron–Severi group does not change under extension of algebraically
closed fields; e.g. Maulik–Poonen, Prop. 3.1) and the symmetric line bundles in a class differ by the finite group
`Pic⁰[2]` of `ℚ̄`-points, `𝒪(D)` is the base change of a symmetric `L` on `A_{K'}` for a number field `K' ⊂ ℂ`, whose
section has divisor `D` after base change (flat base change of `H⁰`). Not one printed theorem, so GLUE. -/
def AnalyticPPAlgebraic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ)) (φ : Torus Λ ≃+ Additive (CPts (bcC A σ) (RingHom.id ℂ))),
    BPAnalytic.Uniformization.IsUniformization (bcC A σ) Λ φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → ∀ T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ),
      (∀ w, w ∈ Λ ↔ ∃ m n : Fin 2 → ℤ, T w = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ)) →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (σ' : K' →+* ℂ)
      (hσ : σ'.comp (algebraMap K K') = σ) (L : (A.baseChange K').X.left.Pic),
      IsSymmPrincipal (A.baseChange K') L ∧ IsThetaPeriodMatrix A σ σ' hσ L Λ φ Ω

/-! ## §3. Glue (proved): weak uniformization → biholomorphic one, and the main theorem -/

/-- If every complex multiple of `v` lies in a lattice `Λ` with `T(Λ) = Ωℤ² + ℤ²` (`T` a `ℂ`-linear isomorphism),
then `v = 0` (`Ωℤ² + ℤ²` is countable, a complex line is not). -/
theorem eq_zero_of_smul_mem {Λ : Submodule ℤ (Fin 2 → ℂ)} {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (T : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hT : ∀ z, z ∈ Λ ↔ ∃ m n : Fin 2 → ℤ, T z = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ))
    {v : Fin 2 → ℂ} (hv : ∀ t : ℂ, t • v ∈ Λ) : v = 0 := by
  by_contra h
  have hTv : T v ≠ 0 := (LinearEquiv.map_ne_zero_iff T).mpr h
  apply not_countable_complex
  set S : Set (Fin 2 → ℂ) := Set.range (fun p : (Fin 2 → ℤ) × (Fin 2 → ℤ) =>
    Ω.mulVec (fun i => (p.1 i : ℂ)) + fun i => (p.2 i : ℂ)) with hSdef
  have hS : S.Countable := Set.countable_range _
  have hinj : Function.Injective (fun t : ℂ => t • T v) := smul_left_injective ℂ hTv
  have hsub : (Set.univ : Set ℂ) ⊆ (fun t : ℂ => t • T v) ⁻¹' S := by
    intro t _
    obtain ⟨m, n, hmn⟩ := (hT _).1 (hv t)
    refine ⟨(m, n), ?_⟩
    simp only [map_smul] at hmn
    exact hmn.symm
  exact Set.countable_univ_iff.mp ((hS.preimage hinj).mono hsub)

variable {K : Type} [Field K]

/-- `toMul (φ (proj Λ w)) = 1 ↔ w ∈ Λ` for a group isomorphism `φ` out of `ℂ^g ⧸ Λ`. -/
theorem toMul_proj_eq_one_iff {G : Type*} [Group G] {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    (φ : Torus Λ ≃+ Additive G) (w : Fin g → ℂ) :
    Additive.toMul (φ (proj Λ w)) = 1 ↔ w ∈ Λ := by
  rw [toMul_eq_one, AddEquivClass.map_eq_zero_iff]
  exact QuotientAddGroup.eq_zero_iff w

/-- **Glue (proved): leaf-push2's weak uniformization factors through the biholomorphic one.** Let
`Φ : ℂ² → A(ℂ)_σ` be a surjective analytic homomorphism with kernel `Λ` (leaf-push2's `IsUniformization`), and
suppose `Λ` contains no complex line. Then, for the biholomorphic uniformization `φ : ℂ^g ⧸ Λ_B ≃ A_ℂ(ℂ)` of
`A_ℂ = A ×_{K,σ} ℂ` (from `UniformizationLeafAll`), `Φ = ptE ∘ φ ∘ proj ∘ D` for a `ℂ`-linear **isomorphism**
`D : ℂ² ≃ ℂ^g`, and `Λ = D⁻¹(Λ_B)`. Linear lifting: homlattice's `exists_complexLinear_of_analytic` with av-split's
`isAnalyticHom_ptE_symm`; `D` onto: `surjective_of_proj_comp_surjective`; `D` one-to-one: its kernel is a complex
subspace of `Λ`. -/
theorem exists_strong_of_weak (hU : BPAnalytic.Uniformization.UniformizationLeafAll) {A : PkgI3.AbVar K}
    {σ : K →+* ℂ} {Λ : Submodule ℤ (Fin 2 → ℂ)} {Φ : (Fin 2 → ℂ) → CPts A σ}
    (hΦ : ZInQ.LeafPush2.IsUniformization σ Λ Φ)
    (hline : ∀ v : Fin 2 → ℂ, (∀ t : ℂ, t • v ∈ Λ) → v = 0) :
    ∃ (g : ℕ) (ΛB : Submodule ℤ (Fin g → ℂ)) (φ : Torus ΛB ≃+ Additive (CPts (bcC A σ) (RingHom.id ℂ))),
      BPAnalytic.Uniformization.IsUniformization (bcC A σ) ΛB φ ∧
      ∃ D : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
        (∀ v, ptE A σ (Additive.toMul (φ (proj ΛB (D v)))) = Φ v) ∧
        ∀ w, w ∈ ΛB ↔ D.symm w ∈ Λ := by
  obtain ⟨g, ΛB, hd, -, φ, hφ⟩ := hU (bcC A σ)
  haveI := hd
  have hψ : ZInQ.HomLattice.IsAnalyticHom (RingHom.id ℂ) (fun v => (ptE A σ).symm (Φ v)) :=
    AvSplit.HomLatticeAN3.isAnalyticHom_ptE_symm A σ (ZInQ.HomLattice.isAnalyticHom_of_unif hΦ)
  obtain ⟨D, hD⟩ := ZInQ.HomLattice.exists_complexLinear_of_analytic hφ hψ
  have hD' : ∀ v, ptE A σ (Additive.toMul (φ (proj ΛB (D v)))) = Φ v := by
    intro v; rw [hD v]; exact (ptE A σ).apply_symm_apply _
  have hker : ∀ v, D v ∈ ΛB ↔ v ∈ Λ := by
    intro v
    rw [← toMul_proj_eq_one_iff φ, ← hΦ.2.1 v, ← hD' v]
    constructor
    · intro h; rw [h, map_one]
    · intro h; exact (ptE A σ).injective (h.trans (map_one _).symm)
  have hinj : Function.Injective D := by
    intro a b hab
    have h0 : a - b = 0 := by
      refine hline _ fun t => (hker _).1 ?_
      rw [map_smul, map_sub, hab, sub_self, smul_zero]
      exact ΛB.zero_mem
    exact sub_eq_zero.mp h0
  have hsurj : Function.Surjective D := by
    have := ZInQ.HomLattice.surjective_of_proj_comp_surjective (Λ' := ΛB)
      (D : (Fin 2 → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (by
        intro t
        obtain ⟨v, hv⟩ := hΦ.2.2.1 (ptE A σ (Additive.toMul (φ t)))
        refine ⟨v, φ.injective (Additive.toMul.injective ((ptE A σ).injective ?_))⟩
        simp only [ContinuousLinearMap.coe_coe]
        rw [hD' v, hv])
    simpa using this
  let De : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.ofBijective (D : (Fin 2 → ℂ) →ₗ[ℂ] (Fin g → ℂ)) ⟨hinj, hsurj⟩
  refine ⟨g, ΛB, φ, hφ, De, fun v => hD' v, fun w => ?_⟩
  have hw : D (De.symm w) = w := De.apply_symm_apply w
  conv_lhs => rw [← hw]
  exact hker _

/-- **Main theorem: `pazukiCor13Upper` from the printed leaf, the analytic-to-algebraic glue and the existing field
`UniformizationLeafAll`.** Given the weak uniformization `Φ` with kernel `Λ` and `T(Λ) = Ωℤ² + ℤ²`: `Λ` contains no
complex line, so `Φ` factors through the biholomorphic `φ` by a linear isomorphism `D` (`exists_strong_of_weak`);
`T ∘ D⁻¹` carries `Λ_B` onto `Ωℤ² + ℤ²`; `AnalyticPPAlgebraic` gives the algebraic `(A_{K'}, L)` with period matrix
`Ω`; `PazukiCor13UpperPP` gives the bound, for the same `Ω`, `z` and `x`. -/
theorem pazukiCor13Upper_of_printed (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hA : AnalyticPPAlgebraic) (hP : PazukiCor13UpperPP) : ZInQ.HeightSplit.PazukiCor13Upper := by
  intro K _ _ A hA2 x hx σ Λ Φ hΦ Ω hΩ hPer F _ _ emb z c hc hz
  obtain ⟨T, hT⟩ := hPer
  obtain ⟨g, ΛB, φ, hφ, D, -, hΛB⟩ := exists_strong_of_weak hU hΦ (fun v hv => eq_zero_of_smul_mem T hT hv)
  have hTB : ∀ w, w ∈ ΛB ↔ ∃ m n : Fin 2 → ℤ,
      (D.symm.trans T) w = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ) := by
    intro w
    rw [hΛB w, hT]
    rfl
  obtain ⟨K', _, _, _, σ', hσ, L, hL, hθ⟩ := hA K A σ g ΛB φ hφ Ω hΩ (D.symm.trans T) hTB
  exact hP K A hA2 x hx σ g ΛB φ hφ K' σ' hσ L hL Ω hΩ hθ F emb z c hc hz

end PazukiDict
