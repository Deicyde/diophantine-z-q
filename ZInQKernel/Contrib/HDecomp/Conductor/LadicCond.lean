import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/def-ladic-cond/LadicCond.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# def-ladic-cond: the conductor exponent of an ℓ-adic representation of `G_{ℚ_p}`, `ℓ ≠ p`

Check with `lake env lean scratch/def-ladic-cond/LadicCond.lean`.

* Part A (copied from `scratch/pkg-I4/I4.lean` §0, §1 start, §2, unchanged): `G_ℚ`, places,
  Frobenius, `GaloisRep`, `G_{ℚ_p}` (`PkgI4.GQp`), `restrictLocal`, cusp forms, newforms,
  `AttachedTo`.
* Part B (**new**): on `G_{ℚ_p} = Gal(ℚ̄_p/ℚ_p)` (Mathlib's `PadicAlgCl p` with its spectral norm):
  inertia, wild inertia, the lower ramification groups of a finite Galois `L/ℚ_p` inside `ℚ̄_p`
  (as subsets of `G_{ℚ_p}`, preimages of Serre's `G_i(L/ℚ_p)`), their orders, Herbrand's `φ`,
  the upper numbering, the absolute upper filtration; invariants and codimensions; the Swan
  conductor at a level `L` adapted to `ρ` (wild inertia acts through `Gal(L/ℚ_p)`), and the
  conductor exponent `a(ρ) = codim V^I + Sw(ρ)` (Serre–Tate 1968 §2; Serre, *Corps locaux* VI §2).
* Part C: sanity facts (proved): unramified ⇒ `a = 0`; agreement with the finite-level Artin
  conductor (Serre's `∑ (g_i/g_0) codim V^{G_i}`, the formula of pkg-I6's `artinConductor`) when
  `ρ` factors through `Gal(L/ℚ_p)`, given restriction of (wild) inertia is onto (stated);
  independence of `L` reduced to one Prop.
* Part D: the leaves R17 (Carayol 1986, Théorème (A)) and L8 (Swan = integral over the upper
  filtration) stated over Part B.
-/

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Part A. Copied from pkg-I4 -/

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

end PkgI4

/-! ## Part B. Inertia, ramification groups and the conductor exponent on `G_{ℚ_p}` -/

namespace LadicCond

open PkgI4

variable {p : ℕ} [Fact p.Prime]

/-- `ℚ̄_p` (Mathlib's `PadicAlgCl p`, normed by the unique extension of `|·|_p`). -/
abbrev Kbar (p : ℕ) [Fact p.Prime] := PadicAlgCl p

/-- A finite Galois extension `L/ℚ_p` inside `ℚ̄_p`. -/
abbrev Fld (p : ℕ) [Fact p.Prime] := IntermediateField ℚ_[p] (Kbar p)

/-- **Inertia** `I_p ⊂ G_{ℚ_p}`: the `σ` acting trivially on the residue field of `ℚ̄_p`,
i.e. `|σx − x| < 1` for all `|x| ≤ 1` (Serre, *Corps locaux* I §7 / IV §1). -/
def inertiaSet : Set (GQp p) := {σ | ∀ x : Kbar p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}

/-- **Wild inertia** `P_p ⊂ G_{ℚ_p}`: the `σ` with `σx/x ≡ 1` modulo the maximal ideal for all
`x ≠ 0`, i.e. `|σx − x| < |x|` (Serre, *Corps locaux* IV §2, Cor. 1 of Prop. 7, at every finite
level; UNVERIFIED numbering). -/
def wildSet : Set (GQp p) := {σ | ∀ x : Kbar p, x ≠ 0 → ‖σ x - x‖ < ‖x‖}

/-- `G_L ⊂ G_{ℚ_p}`: the `σ` fixing `L` pointwise. -/
def fixSet (L : Fld p) : Set (GQp p) := {σ | ∀ x ∈ L, σ x = x}

/-- `ϖ` is a uniformizer of `L`: an element of `L` of maximal absolute value `< 1`. -/
def IsUnif (L : Fld p) (ϖ : Kbar p) : Prop :=
  ϖ ∈ L ∧ ‖ϖ‖ < 1 ∧ ∀ y ∈ L, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖

/-- **Lower ramification groups** of `L/ℚ_p` (Serre, *Corps locaux* IV §1), pulled back to
`G_{ℚ_p}`: `σ ∈ ramSet L i` iff `v_L(σx − x) ≥ i + 1` for every `x ∈ 𝓞_L`. It contains `G_L`, and
its image under `σ ↦ σ|_L` is `G_i(L/ℚ_p)` (for `L/ℚ_p` Galois). -/
def ramSet (L : Fld p) (i : ℕ) : Set (GQp p) :=
  {σ | ∃ ϖ, IsUnif L ϖ ∧ ∀ x ∈ L, ‖x‖ ≤ 1 → ‖σ x - x‖ ≤ ‖ϖ‖ ^ (i + 1)}

/-- `σ ↦ σ|_L`, as a function `L → ℚ̄_p`. -/
def restr (L : Fld p) (σ : GQp p) : L → Kbar p := fun x => σ x

/-- `g_i = |G_i(L/ℚ_p)|`: the number of restrictions to `L` of elements of `ramSet L i`. -/
def ramCard (L : Fld p) (i : ℕ) : ℕ := Nat.card (restr L '' ramSet L i)

/-- `L/ℚ_p` is finite Galois. -/
def IsFinGal (L : Fld p) : Prop := FiniteDimensional ℚ_[p] L ∧ IsGalois ℚ_[p] L

variable {k : Type*} [Field k] {n : ℕ}

/-- `V^S` for `V = kⁿ` and a set `S ⊆ G_{ℚ_p}` acting through `ρ`. -/
def invariants (ρ : GQp p →* GL (Fin n) k) (S : Set (GQp p)) : Submodule k (Fin n → k) where
  carrier := {v | ∀ σ ∈ S, (ρ σ : Matrix (Fin n) (Fin n) k).mulVec v = v}
  zero_mem' := by intro σ _; simp
  add_mem' := by
    intro v w hv hw σ hσ
    simp only [Set.mem_ofPred_eq] at hv hw
    rw [Matrix.mulVec_add, hv σ hσ, hw σ hσ]
  smul_mem' := by
    intro c v hv σ hσ
    simp only [Set.mem_ofPred_eq] at hv
    rw [Matrix.mulVec_smul, hv σ hσ]

/-- `codim V^S = n − dim V^S`. -/
def codimInv (ρ : GQp p →* GL (Fin n) k) (S : Set (GQp p)) : ℕ :=
  n - Module.finrank k (invariants ρ S)

/-- `L` is **adapted** to `ρ`: `L/ℚ_p` is finite Galois and `ρ` is trivial on `P_p ∩ G_L`, so
that `ρ|_{P_p}` factors through `Gal(L/ℚ_p)`. For `ρ` continuous with values in `GL_n(E)`,
`E/ℚ_ℓ` finite, `ℓ ≠ p`, such an `L` exists, since `ρ(P_p)` is finite (`AdaptedExists`). -/
def IsAdapted (L : Fld p) (ρ : GQp p →* GL (Fin n) k) : Prop :=
  IsFinGal L ∧ ∀ σ ∈ wildSet ∩ fixSet L, ρ σ = 1

/-- **The Swan conductor at level `L`** (Serre–Tate 1968 §2; Serre, *Corps locaux* VI §2):
`Sw_L(ρ) = ∑_{i ≥ 1} (g_i/g_0) · codim V^{G_i ∩ P}`. For `L` adapted, `G_i ∩ P` acts through
`G_i(L/ℚ_p)` (for `i ≥ 1`, `G_i(L/ℚ_p)` is the image of `P ∩ ramSet L i`). -/
def swanAt (L : Fld p) (ρ : GQp p →* GL (Fin n) k) : ℚ :=
  ∑ᶠ i : ℕ, ((ramCard L (i + 1) : ℚ) / ramCard L 0) * (codimInv ρ (ramSet L (i + 1) ∩ wildSet) : ℚ)

open Classical in
/-- **The Swan conductor** `Sw(ρ)`: `swanAt L ρ` at a chosen adapted `L` (`0` if none exists,
which does not happen for continuous ℓ-adic `ρ`). Independent of `L`: `SwanIndependent`. -/
def swan (ρ : GQp p →* GL (Fin n) k) : ℚ :=
  if h : ∃ L : Fld p, IsAdapted L ρ then swanAt h.choose ρ else 0

/-- **The conductor exponent** `a(ρ) = codim V^{I_p} + Sw(ρ)` (Serre–Tate 1968 §2; equal to the
conductor of the Weil–Deligne representation, `codim (ker N)^{I}` + Swan, since
`V^{ρ(I)} = (ker N)^{I}` by Grothendieck's monodromy theorem). -/
def condExp (ρ : GQp p →* GL (Fin n) k) : ℚ :=
  codimInv ρ inertiaSet + swan ρ

/-- The conductor exponent computed at a level `L`. -/
def condAt (L : Fld p) (ρ : GQp p →* GL (Fin n) k) : ℚ :=
  codimInv ρ inertiaSet + swanAt L ρ

/-- **Finite-level Artin conductor** (Serre, *Corps locaux* VI §2):
  `∑_{i ≥ 0} (g_i/g_0) codim V^{G_i}`.
For `ρ` trivial on `G_L` this is pkg-I6's `PkgI6.artinConductor` of the induced representation of
`Gal(L/ℚ_p)` (same formula, with `G_i(L/ℚ_p)` = image of `ramSet L i`). -/
def artinAt (L : Fld p) (ρ : GQp p →* GL (Fin n) k) : ℚ :=
  ∑ᶠ i : ℕ, ((ramCard L i : ℚ) / ramCard L 0) * (codimInv ρ (ramSet L i) : ℚ)

/-! ### Herbrand's function and the upper numbering (for L8) -/

/-- Lower numbering for real `t`: `G_t = G_{⌈t⌉}` for `t > −1`, `G_t = G` for `t ≤ −1`. -/
def ramSetR (L : Fld p) (t : ℝ) : Set (GQp p) :=
  if t ≤ -1 then Set.univ else ramSet L ⌈t⌉.toNat

/-- `|G_t(L/ℚ_p)|` for real `t`. -/
def ramCardR (L : Fld p) (t : ℝ) : ℕ := Nat.card (restr L '' ramSetR L t)

/-- **Herbrand's function** `φ_{L/ℚ_p}(u) = ∫₀ᵘ g_t/g_0 dt` (Serre IV §3). -/
def phiAt (L : Fld p) (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, (ramCardR L t : ℝ) / (ramCard L 0 : ℝ)

/-- **Upper numbering** `G^v(L/ℚ_p) = G_{ψ(v)}`, `ψ = φ⁻¹` (Serre IV §3), pulled back to `G_{ℚ_p}`.
  -/
def upperSet (L : Fld p) (v : ℝ) : Set (GQp p) :=
  ramSetR L (sInf {u : ℝ | -1 ≤ u ∧ v ≤ phiAt L u})

/-- **The upper ramification filtration of `G_{ℚ_p}`**: `σ ∈ G^v` iff `σ|_L ∈ G^v(L/ℚ_p)` for
every finite Galois `L` (Serre IV §3, remark after Prop. 14; well defined by Herbrand's theorem). -/
def upperAbs (p : ℕ) [Fact p.Prime] (v : ℝ) : Set (GQp p) :=
  {σ | ∀ L : Fld p, IsFinGal L → σ ∈ upperSet L v}

/-! ## Part C. Sanity facts -/

theorem wildSet_subset_inertiaSet : (wildSet : Set (GQp p)) ⊆ inertiaSet := by
  intro σ hσ x hx
  by_cases h0 : x = 0
  · subst h0; simp
  · exact lt_of_lt_of_le (hσ x h0) hx

theorem invariants_eq_top {ρ : GQp p →* GL (Fin n) k} {S : Set (GQp p)}
    (h : ∀ σ ∈ S, ρ σ = 1) : invariants ρ S = ⊤ := by
  ext v
  simp only [Submodule.mem_top, iff_true]
  intro σ hσ
  rw [h σ hσ]
  simp

theorem codimInv_eq_zero {ρ : GQp p →* GL (Fin n) k} {S : Set (GQp p)}
    (h : ∀ σ ∈ S, ρ σ = 1) : codimInv ρ S = 0 := by
  rw [codimInv, invariants_eq_top h, finrank_top, Module.finrank_fin_fun, Nat.sub_self]

/-- **Sanity (a1).** If `ρ` is unramified (trivial on `I_p`), `Sw_L(ρ) = 0` at every level. -/
theorem swanAt_eq_zero_of_unramified {ρ : GQp p →* GL (Fin n) k}
    (h : ∀ σ ∈ inertiaSet, ρ σ = 1) (L : Fld p) : swanAt L ρ = 0 := by
  rw [swanAt]
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  rw [codimInv_eq_zero (fun σ hσ => h σ (wildSet_subset_inertiaSet hσ.2))]
  simp

/-- **Sanity (a).** Unramified ⇒ conductor exponent `0` (whatever `L` the definition picks). -/
theorem condExp_eq_zero_of_unramified {ρ : GQp p →* GL (Fin n) k}
    (h : ∀ σ ∈ inertiaSet, ρ σ = 1) : condExp ρ = 0 := by
  rw [condExp, codimInv_eq_zero h, swan]
  split_ifs with hL
  · rw [swanAt_eq_zero_of_unramified h]; simp
  · simp

theorem condAt_eq_zero_of_unramified {ρ : GQp p →* GL (Fin n) k}
    (h : ∀ σ ∈ inertiaSet, ρ σ = 1) (L : Fld p) : condAt L ρ = 0 := by
  rw [condAt, codimInv_eq_zero h, swanAt_eq_zero_of_unramified h]; simp

/-- `V^S = V^T` when `S ⊆ T` and every element of `T` agrees on `L` with one of `S`, and `ρ` is
trivial on `G_L`. -/
theorem invariants_eq_of_cover {ρ : GQp p →* GL (Fin n) k} {L : Fld p} {S T : Set (GQp p)}
    (hfix : ∀ σ ∈ fixSet L, ρ σ = 1) (hST : S ⊆ T)
    (hcov : ∀ σ ∈ T, ∃ τ ∈ S, ∀ x ∈ L, τ x = σ x) : invariants ρ S = invariants ρ T := by
  apply le_antisymm
  · intro v hv σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := hcov σ hσ
    have h1 : τ⁻¹ * σ ∈ fixSet L := by
      intro x hx
      change τ⁻¹ (σ x) = x
      rw [← hτσ x hx]
      exact τ.symm_apply_apply x
    have h2 : ρ σ = ρ τ * ρ (τ⁻¹ * σ) := by rw [← map_mul, mul_inv_cancel_left]
    rw [h2, hfix _ h1, mul_one]
    exact hv τ hτ
  · intro v hv σ hσ
    exact hv σ (hST hσ)

/-- **Restriction of inertia is onto** `G_0(L/ℚ_p)` and of wild inertia onto `G_i(L/ℚ_p)`,
`i ≥ 1`, together with `I_p ⊆ ramSet L 0` (Serre, *Corps locaux* I §7 Prop. 21 and IV §1–2;
UNVERIFIED numbering). STANDARD; stated, not proved here. -/
def InertiaRestriction (L : Fld p) : Prop :=
  inertiaSet ⊆ ramSet L 0 ∧
  (∀ σ ∈ ramSet L 0, ∃ τ ∈ inertiaSet, ∀ x ∈ L, τ x = σ x) ∧
  (∀ i : ℕ, ∀ σ ∈ ramSet L (i + 1), ∃ τ ∈ ramSet L (i + 1) ∩ wildSet, ∀ x ∈ L, τ x = σ x)

/-- `G_i(L/ℚ_p) = 1` for `i ≥ N` (Serre IV §1; holds for every finite `L`). -/
def EventuallyTrivial (L : Fld p) (N : ℕ) : Prop := ∀ i, N ≤ i → ramSet L i ⊆ fixSet L

/-- **Sanity (b). Agreement with the Artin conductor on finite image.** If `ρ` factors through
`Gal(L/ℚ_p)` (trivial on `G_L`), then `codim V^I + Sw_L(ρ)` equals the finite-level Artin
conductor `∑_{i≥0} (g_i/g_0) codim V^{G_i}` (pkg-I6's `artinConductor` formula), given the
restriction facts `InertiaRestriction L`, `G_i(L/ℚ_p) = 1` for large `i`, and `g_0 ≠ 0`. -/
theorem condAt_eq_artinAt {ρ : GQp p →* GL (Fin n) k} {L : Fld p}
    (hfix : ∀ σ ∈ fixSet L, ρ σ = 1) (hR : InertiaRestriction L) {N : ℕ}
    (hN : EventuallyTrivial L N) (hg0 : ramCard L 0 ≠ 0) :
    condAt L ρ = artinAt L ρ := by
  obtain ⟨hI, hIc, hW⟩ := hR
  have e0 : codimInv ρ inertiaSet = codimInv ρ (ramSet L 0) := by
    rw [codimInv, codimInv, invariants_eq_of_cover hfix hI hIc]
  have ei : ∀ i, codimInv ρ (ramSet L (i + 1) ∩ wildSet) = codimInv ρ (ramSet L (i + 1)) := by
    intro i
    rw [codimInv, codimInv, invariants_eq_of_cover hfix Set.inter_subset_left (hW i)]
  have hz : ∀ i, N ≤ i → codimInv ρ (ramSet L i) = 0 := fun i hi =>
    codimInv_eq_zero fun σ hσ => hfix σ (hN i hi hσ)
  set f : ℕ → ℚ := fun i => ((ramCard L i : ℚ) / ramCard L 0) * (codimInv ρ (ramSet L i) : ℚ)
    with hf
  have hsupp : Function.support f ⊆ ↑(Finset.range (N + 1)) := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hi (by simp [f, hz i (by omega)])
  have hsupp' : Function.support (fun i => f (i + 1)) ⊆ ↑(Finset.range N) := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    exact hi (by simp [f, hz (i + 1) (by omega)])
  have hA : artinAt L ρ = ∑ i ∈ Finset.range (N + 1), f i :=
    finsum_eq_sum_of_support_subset f hsupp
  have hS : swanAt L ρ = ∑ i ∈ Finset.range N, f (i + 1) := by
    rw [swanAt]
    simp_rw [ei]
    exact finsum_eq_sum_of_support_subset (fun i => f (i + 1)) hsupp'
  rw [condAt, hA, hS, Finset.sum_range_succ', e0, add_comm]
  congr 1
  simp only [f]
  rw [div_self (by exact_mod_cast hg0), one_mul]

/-- **Independence of the level** (Serre–Tate 1968 §2; a consequence of Herbrand's theorem,
pkg-I6 leaf I6.8, and the transitivity I6.9). GLUE, not proved here. -/
def SwanIndependent : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (ρ : GQp p →* GL (Fin n) k) (L L' : Fld p),
    IsAdapted L ρ → IsAdapted L' ρ → swanAt L ρ = swanAt L' ρ

/-- Under `SwanIndependent`, the conductor exponent is computed at any adapted level. -/
theorem condExp_eq_condAt (hI : SwanIndependent (p := p)) {k : Type} [Field k]
    {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsAdapted L ρ) : condExp ρ = condAt L ρ := by
  have h : ∃ L : Fld p, IsAdapted L ρ := ⟨L, hL⟩
  rw [condExp, condAt, swan, dite_cond_eq_true (eq_true h), hI k n ρ _ L h.choose_spec hL]

/-- **Existence of an adapted level** (Serre–Tate 1968 §2, after Grothendieck: `ρ(P_p)` is finite
for `ℓ ≠ p` since `P_p` is pro-`p` and the kernel of `GL_n(𝓞_E) → GL_n(𝓞_E/λ)` is pro-`ℓ`; a
continuous `ρ` into `GL_n(ℚ̄_ℓ)` takes values in `GL_n(E)`, `E/ℚ_ℓ` finite). GLUE (elementary
profinite group theory plus Baire), not proved here. -/
def AdaptedExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)),
    Continuous ρ → ∃ L : Fld p, IsAdapted L ρ

/-! ## Part D. The leaves -/

/-- **R17 = glue-conductor's L10: Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A)** at `F = ℚ`,
weight 2, pp. 409-411 and §0.8 p. 411 (read by the locator audit: all finite `p` and every
`ℓ ≠ p`, including `p ∣ N` and `ℓ = 2`; the finite discrete-series hypothesis concerns only totally
real `F` of even degree), with `a(π_p) = v_p(N)` for newforms (Casselman 1973, locator
UNVERIFIED). Do not replace it by Théorème (B) or by the `Γ₀` elliptic-curve corollary.
*2026-11-12 (loc-fix, applying rv-loc-leaves (f)):* this replaces "content and coverage of
`p ∣ N` UNVERIFIED"; the Lean statement is unchanged. This form, at every adapted level, is a
consequence of the published form `CarayolR17'` plus the glue `SwanIndependent`
(`carayolR17_of_R17'`); it is not a separate published statement. For a newform `f` of weight 2,
level `N`, and a semisimple `ρ` attached to
`f` (pkg-I4's trace form), and a prime `p ≠ ℓ`, the conductor exponent of `ρ|_{G_{ℚ_p}}` is
`v_p(N)`; stated at every adapted level (equivalent to the published form by `SwanIndependent`). -/
def CarayolR17 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ) [Fact p.Prime],
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → p ≠ ℓ →
    ∀ L : Fld p, IsAdapted L (ρ.restrictLocal p) →
      condAt L (ρ.restrictLocal p) = (N.factorization p : ℚ)

/-- **R17, published form**, with the canonical `condExp` (choice of level inside): Carayol,
Théorème (A), coverage as above (every `ℓ`, including 2; every `p ≠ ℓ`, including `p ∣ N`; read by
the locator audit, adopted 2026-11-12 by loc-fix). `condExp` is the Serre–Tate conductor, which
does not change under duals, so the Tate normalization of `AttachedTo` is harmless. -/
def CarayolR17' : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ) [Fact p.Prime],
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → p ≠ ℓ →
      condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

/-- The two forms of R17 agree given the glue `SwanIndependent` and `AdaptedExists`. -/
theorem carayolR17_of_R17' (hI : ∀ (p : ℕ) [Fact p.Prime], SwanIndependent (p := p))
    (h : CarayolR17') : CarayolR17 := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hs ha hp L hL
  rw [← condExp_eq_condAt (hI p) hL]
  exact h ℓ ιC ιL N χ f ρ p hN hf hs ha hp

theorem carayolR17'_of_R17 (hE : ∀ (p : ℕ) [Fact p.Prime], AdaptedExists (p := p))
    (hI : ∀ (p : ℕ) [Fact p.Prime], SwanIndependent (p := p))
    (h : CarayolR17) : CarayolR17' := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hs ha hp
  obtain ⟨L, hL⟩ := hE p ℓ hp.symm 2 (ρ.restrictLocal p)
    (ρ.continuous_toHom.comp
      (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous_toFun)
  rw [condExp_eq_condAt (hI p) hL]
  exact h ℓ ιC ιL N χ f ρ p hN hf hs ha hp L hL

/-- **L8 (glue-conductor): the Swan conductor is the integral of the upper filtration**,
`Sw(ρ) = ∫₀^∞ codim V^{G^u} du` (Serre, *Corps locaux* VI §2 and IV §3 for finite image;
Serre–Tate 1968 §2 for ℓ-adic `ρ`; UNVERIFIED numbering). With `condAt = codim V^I + swanAt`
this is glue-conductor's `a = codim V^I + ∫₀^∞ codim V^{G^u} du`. A change of variables in
Herbrand's `φ` plus Herbrand's theorem: provable glue over Part B. -/
def SwanIntegral : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime], p ≠ ℓ →
    ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)), Continuous ρ →
    ∀ L : Fld p, IsAdapted L ρ →
      (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ)

/-! ### Consumer: glue-conductor's D4(i) from L8 (GLUE, proved) -/

theorem codimInv_le (ρ : GQp p →* GL (Fin n) k) (S : Set (GQp p)) : codimInv ρ S ≤ n :=
  Nat.sub_le _ _

open MeasureTheory in
/-- If `ρ` is trivial on `G^u` for every `u > U ≥ 0`, the right side of L8 is `≤ n·U`. (If the
integrand is not integrable, Mathlib's integral is `0` and the bound is trivial.) -/
theorem integral_codim_le (ρ : GQp p →* GL (Fin n) k) (U : ℝ) (hU : 0 ≤ U)
    (h : ∀ u : ℝ, U < u → ∀ σ ∈ upperAbs p u, ρ σ = 1) :
    ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ) ≤ n * U := by
  set f : ℝ → ℝ := fun u => (codimInv ρ (upperAbs p u) : ℝ) with hf
  set g : ℝ → ℝ := (Set.Ioc 0 U).indicator (fun _ => (n : ℝ)) with hg
  have hle : ∀ u ∈ Set.Ioi (0 : ℝ), f u ≤ g u := by
    intro u hu
    by_cases huU : u ≤ U
    · have : u ∈ Set.Ioc 0 U := ⟨hu, huU⟩
      simp only [hf, hg, Set.indicator_of_mem this]
      exact_mod_cast codimInv_le ρ _
    · have h0 : codimInv ρ (upperAbs p u) = 0 := codimInv_eq_zero (h u (lt_of_not_ge huU))
      simp only [hf, h0, Nat.cast_zero]
      exact Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg n) u
  have hgi : ∫ u in Set.Ioi (0 : ℝ), g u = n * U := by
    rw [hg, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self, setIntegral_const]
    simp [Real.volume_real_Ioc_of_le hU, mul_comm]
  have hgint : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    rw [IntegrableOn, hg, integrable_indicator_iff measurableSet_Ioc]
    refine IntegrableOn.restrict ?_
    exact integrableOn_const (by simp [Real.volume_Ioc])
  by_cases hfi : IntegrableOn f (Set.Ioi (0 : ℝ))
  · rw [← hgi]
    exact setIntegral_mono_on hfi hgint measurableSet_Ioi hle
  · rw [integral_undef hfi]
    positivity

/-- **D4(i) from L8 (GLUE, proved).** For continuous ℓ-adic `ρ`, `ℓ ≠ p`, trivial on `G^u` for
`u > U ≥ 0`, and `L` adapted: `a(ρ) = codim V^I + Sw_L(ρ) ≤ n(1 + U)`. -/
theorem condAt_le_of_upper (hL8 : SwanIntegral) (ℓ : ℕ) [Fact ℓ.Prime] (hp : p ≠ ℓ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)) (hc : Continuous ρ) (L : Fld p)
    (hL : IsAdapted L ρ) (U : ℝ) (hU : 0 ≤ U)
    (h : ∀ u : ℝ, U < u → ∀ σ ∈ upperAbs p u, ρ σ = 1) :
    (condAt L ρ : ℝ) ≤ n * (1 + U) := by
  have h1 : ((codimInv ρ inertiaSet : ℕ) : ℝ) ≤ n := by exact_mod_cast codimInv_le ρ _
  have h2 := integral_codim_le ρ U hU h
  rw [← hL8 ℓ p hp n ρ hc L hL] at h2
  rw [condAt, Rat.cast_add, Rat.cast_natCast]
  linarith

/-! ### Non-degeneracy checks -/

/-- `G_L ⊆ G_i(L)` (preimage) as soon as `L` has a uniformizer. -/
theorem fixSet_subset_ramSet {L : Fld p} {ϖ : Kbar p} (hϖ : IsUnif L ϖ) (i : ℕ) :
    fixSet L ⊆ ramSet L i := by
  intro σ hσ
  refine ⟨ϖ, hϖ, fun x hx _ => ?_⟩
  rw [hσ x hx, sub_self, norm_zero]
  positivity

/-- The trivial representation is adapted to every finite Galois `L`, and has conductor `0`. -/
theorem isAdapted_one {L : Fld p} (hL : IsFinGal L) :
    IsAdapted L (1 : GQp p →* GL (Fin n) k) :=
  ⟨hL, fun _ _ => rfl⟩

theorem condExp_one : condExp (1 : GQp p →* GL (Fin n) k) = 0 :=
  condExp_eq_zero_of_unramified fun _ _ => rfl

/-- Wild inertia contains `1`. -/
theorem one_mem_wildSet : (1 : GQp p) ∈ wildSet := by
  intro x hx
  simp only [AlgEquiv.one_apply, sub_self, norm_zero]
  exact norm_pos_iff.mpr hx

/-- Galois conjugates of elements of a finite Galois `L ⊆ ℚ̄_p` lie in `L`. -/
theorem apply_mem {L : Fld p} (hL : IsFinGal L) (σ : GQp p) {x : Kbar p} (hx : x ∈ L) :
    σ x ∈ L := by
  have : IsGalois ℚ_[p] L := hL.2
  have hn : Normal ℚ_[p] L := inferInstance
  exact (IntermediateField.normal_iff_forall_map_le'.1 hn σ) ⟨x, hx, rfl⟩

/-- **First clause of `InertiaRestriction` (proved):** `I_p ⊆ ramSet L 0` for finite Galois `L`
with a uniformizer. -/
theorem inertiaSet_subset_ramSet_zero {L : Fld p} (hL : IsFinGal L) {ϖ : Kbar p}
    (hϖ : IsUnif L ϖ) : inertiaSet ⊆ ramSet L 0 := by
  intro σ hσ
  refine ⟨ϖ, hϖ, fun x hx hx1 => ?_⟩
  rw [zero_add, pow_one]
  exact hϖ.2.2 _ (L.sub_mem (apply_mem hL σ hx) hx) (hσ x hx1)

theorem norm_p_kbar : ‖(p : Kbar p)‖ = (p : ℝ)⁻¹ := by
  have h := PadicAlgCl.norm_extends p (p : ℚ_[p])
  have e : ((p : ℚ_[p]) : PadicAlgCl p) = (p : Kbar p) := map_natCast (algebraMap ℚ_[p] _) p
  rw [e, Padic.norm_p] at h
  exact h

/-- **Non-vacuity of `IsUnif`:** `p` is a uniformizer of `L = ℚ_p`. -/
theorem isUnif_bot : IsUnif (⊥ : Fld p) (p : Kbar p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  · rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
  · intro y hy hy1
    obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.1 hy
    have hq : ‖algebraMap ℚ_[p] (Kbar p) q‖ = ‖q‖ := PadicAlgCl.norm_extends p q
    rw [hq] at hy1 ⊢
    rw [norm_p_kbar]
    have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one q (-1)).2 (by simpa using hy1)
    simpa [zpow_neg_one] using this

/-- The restrictions to a finite `L` of elements of `G_{ℚ_p}` form a finite set. -/
theorem finite_restr {L : Fld p} (hL : IsFinGal L) (S : Set (GQp p)) :
    (restr L '' S).Finite := by
  have : FiniteDimensional ℚ_[p] L := hL.1
  refine (Set.finite_range (fun f : L →ₐ[ℚ_[p]] Kbar p => (f : L → Kbar p))).subset ?_
  rintro _ ⟨σ, -, rfl⟩
  exact ⟨σ.toAlgHom.comp L.val, rfl⟩

/-- **`g_0 ≠ 0` (proved)** for a finite Galois `L` with a uniformizer. -/
theorem ramCard_ne_zero {L : Fld p} (hL : IsFinGal L) {ϖ : Kbar p} (hϖ : IsUnif L ϖ) (i : ℕ) :
    ramCard L i ≠ 0 := by
  have hne : (restr L '' ramSet L i).Nonempty :=
    ⟨restr L 1, 1, fixSet_subset_ramSet hϖ i (fun x _ => rfl), rfl⟩
  have hfin := finite_restr hL (ramSet L i)
  have : Finite (restr L '' ramSet L i) := hfin.to_subtype
  have : Nonempty (restr L '' ramSet L i) := hne.to_subtype
  exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩

/-- **Sanity (b), reduced hypotheses.** For `L` finite Galois with a uniformizer and `ρ` trivial on
`G_L`: `codim V^I + Sw_L = ∑_{i≥0}(g_i/g_0) codim V^{G_i}`, assuming only the two surjectivity
statements (restriction of `I_p` onto `G_0(L)`, of `P_p ∩ G_i` onto `G_i(L)` for `i ≥ 1`) and
`G_i(L) = 1` for `i ≥ N`. -/
theorem condAt_eq_artinAt' {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsFinGal L)
    {ϖ : Kbar p} (hϖ : IsUnif L ϖ) (hfix : ∀ σ ∈ fixSet L, ρ σ = 1)
    (hI : ∀ σ ∈ ramSet L 0, ∃ τ ∈ inertiaSet, ∀ x ∈ L, τ x = σ x)
    (hW : ∀ i : ℕ, ∀ σ ∈ ramSet L (i + 1), ∃ τ ∈ ramSet L (i + 1) ∩ wildSet, ∀ x ∈ L, τ x = σ x)
    {N : ℕ} (hN : EventuallyTrivial L N) :
    condAt L ρ = artinAt L ρ :=
  condAt_eq_artinAt hfix ⟨inertiaSet_subset_ramSet_zero hL hϖ, hI, hW⟩ hN
    (ramCard_ne_zero hL hϖ 0)

/-- Two uniformizers of `L` have the same absolute value. -/
theorem IsUnif.norm_eq {L : Fld p} {ϖ ϖ' : Kbar p} (h : IsUnif L ϖ) (h' : IsUnif L ϖ') :
    ‖ϖ'‖ = ‖ϖ‖ :=
  le_antisymm (h.2.2 _ h'.1 h'.2.1) (h'.2.2 _ h.1 h.2.1)

/-- If `σ₀` moves `L`, then for large `i` no element of `ramSet L i` restricts to `σ₀|_L`. -/
theorem eventually_not_restr {L : Fld p} {ϖ : Kbar p} (hϖ : IsUnif L ϖ) {σ₀ : GQp p}
    (h₀ : σ₀ ∉ fixSet L) :
    ∃ N : ℕ, ∀ i, N ≤ i → ∀ σ ∈ ramSet L i, restr L σ ≠ restr L σ₀ := by
  simp only [fixSet, Set.mem_setOf_eq, not_forall] at h₀
  obtain ⟨y, hy, hσy⟩ := h₀
  have hpn : ‖(p : Kbar p)‖ < 1 := by
    rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖y‖ + 1) by positivity) hpn
  set x₀ : Kbar p := (p : Kbar p) ^ k * y with hx₀
  have hpk : (p : Kbar p) ^ k = algebraMap ℚ_[p] (Kbar p) ((p : ℚ_[p]) ^ k) := by simp
  have hx₀L : x₀ ∈ L := L.mul_mem (hpk ▸ IntermediateField.algebraMap_mem _ _) hy
  have hx₀1 : ‖x₀‖ ≤ 1 := by
    rw [hx₀, norm_mul, norm_pow]
    have h1 : ‖(p : Kbar p)‖ ^ k * (‖y‖ + 1) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at hk
    nlinarith [norm_nonneg y, pow_nonneg (norm_nonneg (p : Kbar p)) k]
  have hσx₀ : σ₀ x₀ - x₀ = (p : Kbar p) ^ k * (σ₀ y - y) := by
    rw [hx₀, map_mul, map_pow, map_natCast]; ring
  have hε : 0 < ‖σ₀ x₀ - x₀‖ := by
    rw [hσx₀, norm_pos_iff]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
      (sub_ne_zero.2 hσy)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hϖ.2.1
  refine ⟨N, fun i hi σ hσ heq => ?_⟩
  obtain ⟨ϖ', hϖ', hb⟩ := hσ
  have e : σ x₀ = σ₀ x₀ := congrFun heq ⟨x₀, hx₀L⟩
  have h1 := hb x₀ hx₀L hx₀1
  rw [e, hϖ.norm_eq hϖ'] at h1
  have h2 : ‖ϖ‖ ^ (i + 1) ≤ ‖ϖ‖ ^ N :=
    pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega)
  linarith

/-- **`G_i(L/ℚ_p) = 1` for large `i` (proved)**, for finite Galois `L` with a uniformizer. -/
theorem eventuallyTrivial {L : Fld p} (hL : IsFinGal L) {ϖ : Kbar p} (hϖ : IsUnif L ϖ) :
    ∃ N, EventuallyTrivial L N := by
  have key : ∀ T : Set (L → Kbar p), T.Finite → T ⊆ restr L '' (fixSet L)ᶜ →
      ∃ N : ℕ, ∀ i, N ≤ i → ∀ σ ∈ ramSet L i, restr L σ ∉ T := by
    intro T hT
    induction T, hT using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨0, fun _ _ _ _ h => h⟩
    | @insert f T' _ _ ih =>
      intro hsub
      obtain ⟨N₁, hN₁⟩ := ih (fun g hg => hsub (Set.mem_insert_of_mem _ hg))
      obtain ⟨σ₀, h₀, rfl⟩ := hsub (Set.mem_insert _ _)
      obtain ⟨N₀, hN₀⟩ := eventually_not_restr hϖ h₀
      refine ⟨max N₀ N₁, fun i hi σ hσ hmem => ?_⟩
      rcases hmem with h | h
      · exact hN₀ i (le_of_max_le_left hi) σ hσ h
      · exact hN₁ i (le_of_max_le_right hi) σ hσ h
  obtain ⟨N, hN⟩ := key _ (finite_restr hL _) le_rfl
  refine ⟨N, fun i hi σ hσ => ?_⟩
  by_contra hfix
  exact hN i hi σ hσ ⟨σ, hfix, rfl⟩

/-- **Sanity (b), final form.** For `L` finite Galois with a uniformizer and `ρ` trivial on `G_L`,
`codim V^I + Sw_L = ∑_{i≥0}(g_i/g_0) codim V^{G_i}`, given only the two surjectivity facts. -/
theorem condAt_eq_artinAt'' {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsFinGal L)
    {ϖ : Kbar p} (hϖ : IsUnif L ϖ) (hfix : ∀ σ ∈ fixSet L, ρ σ = 1)
    (hI : ∀ σ ∈ ramSet L 0, ∃ τ ∈ inertiaSet, ∀ x ∈ L, τ x = σ x)
    (hW : ∀ i : ℕ, ∀ σ ∈ ramSet L (i + 1), ∃ τ ∈ ramSet L (i + 1) ∩ wildSet, ∀ x ∈ L, τ x = σ x) :
    condAt L ρ = artinAt L ρ :=
  let ⟨_, hN⟩ := eventuallyTrivial hL hϖ
  condAt_eq_artinAt' hL hϖ hfix hI hW hN

/-- For `y ≠ 0` in a finite `L/ℚ_p`, `‖y‖^{[L:ℚ_p]!}` is an integral power of `p` (from Mathlib's
`spectralNorm_eq_norm_coeff_zero_rpow`: `‖y‖ = ‖a_0‖^{1/deg}` for the minimal polynomial). -/
theorem norm_pow_factorial {L : Fld p} (hL : FiniteDimensional ℚ_[p] L) {y : Kbar p}
    (hy : y ∈ L) (hy0 : y ≠ 0) :
    ∃ j : ℤ, ‖y‖ ^ (Module.finrank ℚ_[p] L).factorial = (p : ℝ) ^ j := by
  have hint : IsIntegral ℚ_[p] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  set m := (minpoly ℚ_[p] y).natDegree with hm
  have hm_le : m ≤ Module.finrank ℚ_[p] L := by
    have := minpoly.natDegree_le (A := ℚ_[p]) (⟨y, hy⟩ : L)
    rwa [IntermediateField.minpoly_eq] at this
  have hm_pos : 0 < m := minpoly.natDegree_pos hint
  obtain ⟨t, ht⟩ := Nat.dvd_factorial hm_pos hm_le
  set c := (minpoly ℚ_[p] y).coeff 0 with hc
  have hc0 : c ≠ 0 := minpoly.coeff_zero_ne_zero hint hy0
  have hnorm : ‖y‖ = ‖c‖ ^ (1 / m : ℝ) := by
    rw [← PadicAlgCl.spectralNorm_eq]
    exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (L := Kbar p) y
  have hym : ‖y‖ ^ m = ‖c‖ := by
    rw [hnorm, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    have : (1 / (m : ℝ)) * (m : ℝ) = 1 := by
      field_simp
    rw [this, Real.rpow_one]
  refine ⟨-c.valuation * t, ?_⟩
  rw [ht, pow_mul, hym, Padic.norm_eq_zpow_neg_valuation hc0, ← zpow_natCast, ← zpow_mul]

/-- **Every finite `L/ℚ_p` inside `ℚ̄_p` has a uniformizer (proved).** -/
theorem exists_isUnif {L : Fld p} (hL : FiniteDimensional ℚ_[p] L) : ∃ ϖ, IsUnif L ϖ := by
  classical
  set D := (Module.finrank ℚ_[p] L).factorial with hDdef
  have hD : 0 < D := Nat.factorial_pos _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpL : (p : Kbar p) ∈ L := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hex : ∃ n : ℕ, ∃ y ∈ L, ‖y‖ < 1 ∧ ‖y‖ ^ D = (p : ℝ) ^ (-(n : ℤ)) :=
    ⟨D, p, hpL, isUnif_bot.2.1, by rw [norm_p_kbar, zpow_neg, zpow_natCast, inv_pow]⟩
  obtain ⟨ϖ, hϖL, hϖ1, hϖD⟩ := Nat.find_spec hex
  refine ⟨ϖ, hϖL, hϖ1, fun y hy hy1 => ?_⟩
  by_cases hy0 : y = 0
  · rw [hy0, norm_zero]; exact norm_nonneg _
  obtain ⟨j, hj⟩ := norm_pow_factorial hL hy hy0
  have hjneg : j < 0 := by
    have h1 : ‖y‖ ^ D < 1 := pow_lt_one₀ (norm_nonneg _) hy1 hD.ne'
    rw [hj] at h1
    by_contra h
    rw [not_lt] at h
    exact absurd h1 (not_lt.2 (one_le_zpow₀ hp1.le h))
  have hle : Nat.find hex ≤ (-j).toNat :=
    Nat.find_min' hex ⟨y, hy, hy1, by rw [hj]; congr 1; omega⟩
  have hDle : ‖y‖ ^ D ≤ ‖ϖ‖ ^ D := by
    rw [hj, hϖD]
    exact zpow_le_zpow_right₀ hp1.le (by omega)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hD.ne').1 hDle

/-- **Sanity (b), with no structural hypotheses.** For `L/ℚ_p` finite Galois and `ρ` trivial on
`G_L`: `codim V^I + Sw_L = ∑_{i≥0}(g_i/g_0) codim V^{G_i}`, given the two surjectivity facts. -/
theorem condAt_eq_artinAt_of_surj {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsFinGal L)
    (hfix : ∀ σ ∈ fixSet L, ρ σ = 1)
    (hI : ∀ σ ∈ ramSet L 0, ∃ τ ∈ inertiaSet, ∀ x ∈ L, τ x = σ x)
    (hW : ∀ i : ℕ, ∀ σ ∈ ramSet L (i + 1), ∃ τ ∈ ramSet L (i + 1) ∩ wildSet, ∀ x ∈ L, τ x = σ x) :
    condAt L ρ = artinAt L ρ :=
  let ⟨_, hϖ⟩ := exists_isUnif hL.1
  condAt_eq_artinAt'' hL hϖ hfix hI hW

end LadicCond

end

