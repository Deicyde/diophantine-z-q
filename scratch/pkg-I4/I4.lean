import Mathlib

/-!
# Package I4 (modularity): leaves statable over Mathlib today

Draft for `docs/research/pkg-I4.md` (task pkg-I4, 2026-11-11). Check with
`lake env lean scratch/pkg-I4/I4.lean`.

* §0 Galois side over `ℚ̄`: copied, with small changes, from `scratch/hdec-faithful/Leaves.lean`
  §0 (places as valuation subrings, inertia, arithmetic Frobenius, complex conjugation,
  continuous `GL_n(ℚ̄_ℓ)`-representations, characters).
* §1 **new**: the local Galois group `G_{ℚ_p}`, its action on Mathlib's `ℂ_[p]`, the
  `p`-adic cyclotomic character, and **Hodge–Tate multiplicities** (Tate–Sen definition through
  `(ℂ_p(i) ⊗ V)^{G_{ℚ_p}}`, written as a space of equivariant `ℚ_p`-linear maps `V → ℂ_p`).
* §2 modular side: cusp forms on `Γ₁(N)`, nebentypus, normalized eigenforms (Hecke recursion of
  the q-coefficients, as hdec-faithful), representations attached to eigenforms (trace form),
  and **new**: the old space and newforms.
* §3 the leaves of I4 that are statable now, as `def … : Prop` (none proved).
* §4 the leaves that are not statable now, as *templates*: functions of the missing predicate
  (`IsPst`, the conductor exponent). A template is **not** a leaf: `PanFor P` says nothing until
  `P` is the genuine potentially-semistable predicate.
* §5 small glue facts, proved.
-/

noncomputable section

namespace PkgI4

open scoped MatrixGroups ModularForm

/-! ## §0. Galois side over `ℚ̄` -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- A continuous `n`-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` (`PadicAlgCl ℓ` with its
spectral norm). As in Pan's paper, the coefficients are `ℚ̄_ℓ`. -/
structure GaloisRep (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) where
  toHom : GQ →* GL (Fin n) (PadicAlgCl ℓ)
  continuous_toHom : Continuous toHom

/-- A continuous character `G_ℚ → ℚ̄_ℓ^×`. -/
structure GaloisChar (ℓ : ℕ) [Fact ℓ.Prime] where
  toHom : GQ →* (PadicAlgCl ℓ)ˣ
  continuous_toHom : Continuous toHom

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- The matrix of `ρ(σ)`. -/
def GaloisRep.mat (ρ : GaloisRep ℓ n) (σ : GQ) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) :=
  (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))

/-- `ρ` is unramified at `p`: every inertia group above `p` acts trivially. -/
def GaloisRep.UnramifiedAt (ρ : GaloisRep ℓ n) (p : ℕ) : Prop :=
  ∀ v : ValuationSubring Qbar, LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ρ.toHom ((σ : v.decompositionSubgroup ℚ) : GQ) = 1

/-- `ρ` is ramified at only finitely many primes. -/
def GaloisRep.FinitelyRamified (ρ : GaloisRep ℓ n) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ρ.UnramifiedAt p

/-- `c` is a complex conjugation: it is `z ↦ z̄` through some embedding `ℚ̄ → ℂ`. -/
def IsComplexConj (c : GQ) : Prop :=
  ∃ ι : Qbar →ₐ[ℚ] ℂ, ∀ x, ι (c x) = starRingEnd ℂ (ι x)

/-- `ρ` is odd: `det ρ(c) = −1` for every complex conjugation `c` (Pan, Conj. 1.0.1). -/
def GaloisRep.IsOdd (ρ : GaloisRep ℓ 2) : Prop :=
  ∀ c, IsComplexConj c → (ρ.mat c).det = -1

/-- `ρ` is irreducible over the algebraically closed `ℚ̄_ℓ`, in Burnside's form: the image spans
`M_n(ℚ̄_ℓ)`. -/
def GaloisRep.IsIrreducible (ρ : GaloisRep ℓ n) : Prop :=
  Algebra.adjoin (PadicAlgCl ℓ) (Set.range ρ.mat) = ⊤

/-- `ρ` is semisimple: every invariant subspace has an invariant complement. -/
def GaloisRep.IsSemisimple (ρ : GaloisRep ℓ n) : Prop :=
  ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
    (∀ σ, W.map (Matrix.toLin' (ρ.mat σ)) ≤ W) →
    ∃ W', IsCompl W W' ∧ ∀ σ, W'.map (Matrix.toLin' (ρ.mat σ)) ≤ W'

/-! ## §1. The local Galois group, `ℂ_p`, and Hodge–Tate multiplicities -/

section Local

variable (p : ℕ) [Fact p.Prime]

/-- `G_{ℚ_p} = Gal(ℚ̄_p/ℚ_p)`, with `ℚ̄_p = PadicAlgCl p`; this is Mathlib's
`Field.absoluteGaloisGroup ℚ_[p]`. -/
abbrev GQp := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

/-- The decomposition map `G_{ℚ_p} → G_ℚ` (restriction along an embedding `ℚ̄ → ℚ̄_p`, Mathlib's
`Field.absoluteGaloisGroup.map`). Its image is a decomposition group at a place above `p`; the
choice of embedding changes it by conjugation, which no property below depends on. -/
def decomp : GQp p →* GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p]) :
    Field.absoluteGaloisGroup ℚ_[p] →* Field.absoluteGaloisGroup ℚ)

/-- `ρ|_{G_{ℚ_p}}`. -/
def GaloisRep.restrictLocal (ρ : GaloisRep ℓ n) : GQp p →* GL (Fin n) (PadicAlgCl ℓ) :=
  ρ.toHom.comp (decomp p)

/-- Every `σ ∈ G_{ℚ_p}` is an isometry of `ℚ̄_p` (Mathlib: `spectralNorm_eq_of_equiv`). -/
theorem norm_gqp_apply (σ : GQp p) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem continuous_gqp (σ : GQp p) : Continuous σ :=
  (AddMonoidHomClass.isometry_of_norm σ (norm_gqp_apply p σ)).continuous

/-- `σ ∈ G_{ℚ_p}` as a continuous ring endomorphism of `ℚ̄_p`. -/
def gqpRingHom (σ : GQp p) : PadicAlgCl p →+* PadicAlgCl p := σ.toAlgHom.toRingHom

theorem continuous_gqpRingHom (σ : GQp p) : Continuous (gqpRingHom p σ) :=
  continuous_gqp p σ

/-- The action of `σ ∈ G_{ℚ_p}` on `ℂ_p = ℂ_[p]`: the extension of `σ` to the completion. -/
def cpAct (σ : GQp p) : ℂ_[p] →+* ℂ_[p] :=
  UniformSpace.Completion.mapRingHom (gqpRingHom p σ) (continuous_gqpRingHom p σ)

theorem cpAct_coe (σ : GQp p) (x : PadicAlgCl p) :
    cpAct p σ (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem cpAct_algebraMap (σ : GQp p) (c : ℚ_[p]) :
    cpAct p σ (algebraMap ℚ_[p] ℂ_[p] c) = algebraMap ℚ_[p] ℂ_[p] c := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    cpAct_coe, AlgEquiv.commutes]

/-- The `p`-adic cyclotomic character `χ : G_{ℚ_p} → ℤ_p^×` (Mathlib's `cyclotomicCharacter`
on `ℚ̄_p`, which contains all `p`-power roots of unity). -/
def cyc (σ : GQp p) : ℤ_[p]ˣ :=
  cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv

/-- `χ(σ)^i ∈ ℚ_p` for `i ∈ ℤ`. -/
def cycPow (σ : GQp p) (i : ℤ) : ℚ_[p] :=
  ((((cyc p σ) ^ i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]

/-- For an `E`-linear representation `ρ` of `G_{ℚ_p}` on `V = E^n` (`E/ℚ_p` finite), the space
`H_i(ρ) = { φ : V →ₗ[ℚ_p] ℂ_p | φ(ρ(σ)v) = χ(σ)^i · σ(φ(v)) }`. It is
`(ℂ_p(i) ⊗_{ℚ_p} V^∨)^{G_{ℚ_p}}` written as equivariant maps. -/
def htSpace (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    Submodule ℚ_[p] ((Fin n → E) →ₗ[ℚ_[p]] ℂ_[p]) where
  carrier := {φ | ∀ (σ : GQp p) (v : Fin n → E),
    φ (Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v) = cycPow p σ i • cpAct p σ (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add, smul_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v]
    rw [Algebra.smul_def c (φ v), map_mul, cpAct_algebraMap, ← Algebra.smul_def, smul_comm]

/-- **Hodge–Tate multiplicity** of the weight `w`, in the convention of N5 and Pan: the
cyclotomic character has weight `−1`. It is `dim_E (ℂ_p(−w) ⊗ V^∨)^{G}` =
`dim_E (ℂ_p(w) ⊗ V)^{G}`·, computed as `dim_{ℚ_p} H_{−w}(ρ) / [E : ℚ_p]`. (Check: for `V = ℚ_p(1)`,
`H_i ≠ 0` iff `ℂ_p(1−i)^G ≠ 0` iff `i = 1`, i.e. weight `−1`, by Tate's theorem.) -/
def htMult (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : ℕ :=
  Module.finrank ℚ_[p] (htSpace p ρ (-w)) / Module.finrank ℚ_[p] E

/-- `ρ` is Hodge–Tate with weight multiset `S` (`card S = n` makes it Hodge–Tate). -/
def HasHTWeights (ρ : GQp p →* GL (Fin n) E) (S : Multiset ℤ) : Prop :=
  ∀ w : ℤ, htMult p ρ w = S.count w

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` has Hodge–Tate weights `S`: it takes values in
`GL_n(E)` for a finite `E/ℚ_p` inside `ℚ̄_p`, and the `E`-representation has weights `S`. (The
multiplicities do not depend on `E`, by base change; STANDARD.) -/
def LocalHasHTWeights (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) (S : Multiset ℤ) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    HasHTWeights p ρE S

/-- `ρ|_{G_{ℚ_p}}` has Hodge–Tate weights `S` (for `ρ` with `ℚ̄_p` coefficients). -/
def GaloisRep.HasHTWeightsAtSelf (ρ : GaloisRep p n) (S : Multiset ℤ) : Prop :=
  LocalHasHTWeights p (ρ.restrictLocal p) S

/-- `ρ|_{G_{ℚ_p}}` has distinct Hodge–Tate weights (2-dimensional case). -/
def GaloisRep.DistinctHTWeights (ρ : GaloisRep p 2) : Prop :=
  ∃ a b : ℤ, a ≠ b ∧ ρ.HasHTWeightsAtSelf p {a, b}

end Local

/-! ## §2. Modular side -/

/-- Cusp forms of weight `k` on `Γ₁(N)` (Mathlib). -/
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k

/-- The `m`-th q-expansion coefficient `a_m(f)` (period 1). -/
def coeff {N : ℕ} {k : ℤ} (f : CF N k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff m

/-- `f` has nebentypus `χ`: `f|_k γ = χ(d) f` for `γ = (a b; c d) ∈ Γ₀(N)`. -/
def HasNebentypus {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) • ⇑f

/-- `f` is a normalized eigenform of all Hecke operators `T_n` with nebentypus `χ`, through its
coefficients: `a₁ = 1` and `a_m a_n = Σ_{d ∣ (m,n)} χ(d) d^{k−1} a_{mn/d²}`. Equivalent to the
Hecke definition for forms with nebentypus `χ` (Diamond–Shurman Prop. 5.3.1 and §5.8; locator
UNVERIFIED). Same as hdec-faithful. -/
def IsNormalizedEigenform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  HasNebentypus f χ ∧ coeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      coeff f m * coeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * coeff f (m * n / d ^ 2)

/-- `τ ↦ dτ` on `ℍ`, for `d ≥ 1`. -/
def scaleH (d : ℕ+) (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(d : ℂ) * (τ : ℂ), by
    have h := τ.coe_im_pos
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast d.pos) h⟩

/-- The **old space** of level `N`, weight `k`: the span of the functions `τ ↦ f(dτ)` with
`f ∈ S_k(Γ₁(M))`, `M ∣ N`, `M < N`, `d ∣ N/M` (Atkin–Lehner, Li 1975 §1). -/
def oldSpace (N : ℕ) (k : ℤ) : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ {F | ∃ (M : ℕ) (d : ℕ+) (f : CF M k), 0 < M ∧ M ∣ N ∧ M < N ∧
    (d : ℕ) * M ∣ N ∧ F = fun τ => f (scaleH d τ)}

/-- `f` is a **newform** of level `N`: a normalized eigenform of all `T_n` not lying in the old
space. For an eigenform of all `T_n` this is equivalent to Li's definition (orthogonal to the
old space for the Petersson product): the new and old spaces are stable under all `T_n` and, by
strong multiplicity one, share no eigensystem away from `N` (Li 1975, Thms 3 and 5;
Diamond–Shurman Thm 5.8.2; locators UNVERIFIED). The Petersson definition needs the Petersson
integral over `Γ₁(N)\ℍ`, which Mathlib lacks (it has the integrand, `petersson`). -/
def IsNewform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  IsNormalizedEigenform f χ ∧ (⇑f : UpperHalfPlane → ℂ) ∉ oldSpace N k

/-- `ρ` is attached to the eigenform `g` (through `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`), in the
Tate-module normalization (arithmetic Frobenius, `tr = a_p`): for `p ∤ Nℓ`, `ρ` is unramified at
`p` and every arithmetic Frobenius above `p` has trace `ιL(α)` with `ιC(α) = a_p(g)`. -/
def GaloisRep.AttachedTo (ρ : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} {k : ℤ} (g : CF N k) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧
      ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
        (ρ.mat σ).trace = ιL α

/-- `ρ` is attached to `g` **up to the twist** `ψ`, outside a finite set `S`: Pan's conclusion
"comes from a cuspidal eigenform up to twist", in trace form (see `PanFor`). -/
def GaloisRep.AttachedUpToTwist (ρ : GaloisRep ℓ 2) (ψ : GaloisChar ℓ) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} (g : CF N k) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧
      ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
        (ρ.mat σ).trace = (ψ.toHom σ : PadicAlgCl ℓ) * ιL α

/-! ## §3. Leaves of I4 statable now (statements only; none is proved) -/

/-- **I4-L1. Galois representations of eigenforms** (Eichler–Shimura and Shimura 1971 Thm 7.14
for `k = 2`; Deligne 1971 for `k ≥ 2`; Deligne–Serre 1974 Thm 6.1 for `k = 1`; theorem numbers
UNVERIFIED). Consequence form (the published statements also give the determinant
`ε_g χ^{k−1}`). Same as hdec-faithful L27(a). -/
def EigenformRepExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g

/-- **I4-L2. Hodge–Tate weights of eigenform representations, every level** (Faltings, Math.
Ann. 278 (1987) for `k ≥ 2` (level `ℓ ∣ N` UNVERIFIED there); Saito, Invent. Math. 129 (1997)
(pst at `ℓ`, every level); Kato, Astérisque 295 (2004) §9.4 (de Rham, every level); Scholl 1990
with Scholze 2013 and Fontaine's closure). A semisimple `ρ` attached to a normalized eigenform of
weight `k ≥ 2` and any level `N` (including `ℓ ∣ N`) is Hodge–Tate at `ℓ` with weights
`{0, 1 − k}` in the Tate normalization (cyclotomic weight `−1`; h-trust C8). Consequence form
(the published theorems give de Rham or pst, which imply Hodge–Tate with the same weights). -/
def EigenformHT : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

/-- **I4-L3. Deligne–Serre** (Ann. Sci. ÉNS 7 (1974), Thm 4.1, with Chebotarev and
Brauer–Nesbitt): a semisimple `ρ` attached to a weight-one eigenform has finite image.
Consequence form. Same as hdec-faithful L27(b). -/
def DeligneSerreFinite : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ρ : GaloisRep ℓ 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1),
    0 < N → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    (Set.range ρ.toHom).Finite

/-- **I4-L4. Twisting an eigenform** (Shimura 1971 Prop. 3.64; Atkin–Li, Invent. Math. 48 (1978)
Prop. 3.1; locators UNVERIFIED). Consequence form. Same as hdec-faithful L28(a). -/
def EigenformTwist : Prop :=
  ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
    0 < N → 0 < m → IsNormalizedEigenform g χ →
    ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
      IsNormalizedEigenform g' χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p

/-- **I4-L5. Newform attached to an eigensystem** (Li, Math. Ann. 212 (1975), Thm 5 (strong
multiplicity one) with the decomposition `S_k = S_k^new ⊕ S_k^old`; Miyake Thm 4.6.19; locators
UNVERIFIED). Every normalized eigenform of level `M` has the Hecke eigenvalues away from `M` of a
newform of level dividing `M`. Consequence form. -/
def NewformOfEigenform : Prop :=
  ∀ (M : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ M) (g : CF M k),
    0 < M → IsNormalizedEigenform g χ →
    ∃ (N : ℕ) (χ' : DirichletCharacter ℂ N) (f : CF N k), 0 < N ∧ N ∣ M ∧ IsNewform f χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → coeff f p = coeff g p

/-- **I4-L6. Carayol at unramified primes** (Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A), the
case "conductor exponent 0"; theorem letter VERIFIED from N5 L9778's locator, content
UNVERIFIED). For a newform `f` of weight 2 and level `N` and a semisimple `ρ` attached to it, a
prime `p ≠ ℓ` at which `ρ` is unramified does not divide `N`. Consequence form (Théorème (A)
gives `v_p(N) =` the conductor exponent, which is 0 exactly when `ρ` is unramified). -/
def CarayolUnramified : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ),
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    p.Prime → p ≠ ℓ → ρ.UnramifiedAt p → ¬ p ∣ N

/-! ## §4. Templates (not leaves): the missing predicates are arguments

`PanFor IsPst` is Pan's theorem once `IsPst` is the genuine "potentially semistable in the sense
of Fontaine" predicate on `ℚ̄_p`-representations of `G_{ℚ_p}`; for any other argument it means
nothing. Likewise for `BergerFor`, `CarayolFor`. -/

/-- A predicate on `ℚ̄_p`-valued representations of `G_{ℚ_p}`, for every `p` and `n`. -/
abbrev LocalPred := ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), (GQp p →* GL (Fin n) (PadicAlgCl p)) → Prop

/-- **Template for I4-L7, Pan's theorem** (Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169,
Thm 1.0.4 = arXiv:1901.07166v2 Thm 1.0.4 (statement VERIFIED in h-a011 §1.1 from the arXiv
source; JAMS numbering UNVERIFIED)), for `p ≥ 5` (which drops the `p = 3` residual clause):
a continuous irreducible `ρ : G_ℚ → GL₂(ℚ̄_p)`, ramified at finitely many primes, potentially
semistable at `p`, odd, with distinct Hodge–Tate weights at `p`, comes from a cuspidal eigenform
up to twist. The conclusion is in trace form: some normalized eigenform `g`, continuous `ψ` and
embeddings with `tr ρ(Frob_q) = ψ(Frob_q) ι(a_q(g))` for almost all `q`. Every reading of
"comes from … up to twist" implies it, in either Frobenius normalization, since
`U^∨ ≅ U ⊗ det U⁻¹` in dimension 2 (h-trust C8; pkg-I4 note §2.1). -/
def PanFor (IsPst : LocalPred) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ρ : GaloisRep p 2,
    ρ.IsIrreducible → ρ.FinitelyRamified → IsPst p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    ρ.DistinctHTWeights p →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl p) (S : Finset ℕ),
        ρ.AttachedUpToTwist ψ ιC ιL g S

/-- **Template for I4-L8, Berger's theorem** (Invent. Math. 148 (2002), Théorème 0.7 in the
published numbering (ASTRA-READ), = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3 (VERIFIED by
rv-h-a011)): de Rham ⇒ potentially semistable. -/
def BergerFor (IsDR IsPst : LocalPred) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    Continuous ρ → IsDR p n ρ → IsPst p n ρ

/-- A conductor-exponent function: `a ℓ ρ p` is the Artin conductor exponent at `p ≠ ℓ` of the
`ℓ`-adic representation `ρ` (Weil–Deligne / Serre's definition). Missing in every library. -/
abbrev CondExp := ∀ (ℓ : ℕ) [Fact ℓ.Prime], GaloisRep ℓ 2 → ℕ → ℕ

/-- **Template for I4-L9, Carayol's Théorème (A)** at `F = ℚ`, weight 2 (the case N5 uses):
for a newform `f` of level `N` and a semisimple `ρ` attached to it, `v_p(N) = a(ρ, p)` for every
prime `p ≠ ℓ`. -/
def CarayolFor (a : CondExp) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ),
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    p.Prime → p ≠ ℓ → a ℓ ρ p = N.factorization p

/-! ## §5. Glue facts, proved -/

/-- **C8 weight comparison** (Tate normalization). If `ρ ≅ ρ_g ⊗ ψ` with `ψ` Hodge–Tate of
weight `n`, the weights of `ρ` are `{n, n + 1 − k}`; if they are `{0, −1}` and `k ≥ 1`, then
`n = 0` and `k = 2`. Stated on multisets. -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : ({n, n + 1 - k} : Multiset ℤ) = {0, -1}) : n = 0 ∧ k = 2 := by
  have h0 : (0 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1
  omega

/-- The same comparison in Pan's cohomological normalization (weights of `ρ_g` are `{0, k−1}`):
`{n, n + k − 1} = {0, −1}` with `k ≥ 1` forces `k = 2`, `n = −1` (twist by `χ¹`; h-trust C8,
rv-h-c8 `weights.py`). -/
theorem weight_match_coh (n k : ℤ) (hk : 1 ≤ k)
    (h : ({n, n + k - 1} : Multiset ℤ) = {0, -1}) : n = -1 ∧ k = 2 := by
  have h0 : (0 : ℤ) ∈ ({n, n + k - 1} : Multiset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + k - 1} : Multiset ℤ) := by rw [h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1
  omega

end PkgI4

end

#print axioms PkgI4.weight_match
#print axioms PkgI4.weight_match_coh
#print axioms PkgI4.cpAct_algebraMap
