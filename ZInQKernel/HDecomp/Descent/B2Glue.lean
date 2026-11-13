import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-descent/B2Glue.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-descent: the deduction of B2 from its literature inputs (N5 L665-700)

An abstract but universally quantified form: `G` is any topological group (for the application,
`G_ℚ` with the Krull topology), `ι` any index type (the finite primes), `Gv v` any topological
groups with continuous homomorphisms `r v : Gv v →* G` (the decomposition groups
`G_{ℚ_p} → G_ℚ` along a chosen embedding `ℚ̄ → ℚ̄_p`), and `U` any commutative group (`ℂ^×`).
"Continuous with values in a discrete group" is `IsLocallyConstant`.

A sign 2-cocycle `η` is *trivial* (`SignCob`) if `η = dγ` for a locally constant sign cochain
`γ`. The hypotheses are exactly the inputs of N5's argument:

* `hasse` (leaf L-B2a): a locally constant sign 2-cocycle on `G` that is trivial at every finite
  place is trivial (injectivity of `H²(G_ℚ, ±1) → ∏_{p<∞} H²(G_{ℚ_p}, ±1)`: Kummer theory
  with Hilbert 90, Albert–Brauer–Hasse–Noether and reciprocity, with `Br(ℝ)[2] = ℤ/2`);
* `local_two` (leaf L-B2b): `H²(G_{ℚ_p}, ±1)` has at most two elements (`Br(ℚ_p)[2] = ℤ/2`);
* `agree` (the local analysis of B2, leaves L-B2c, L-B2d): at every finite place, `[ε]` and
  `δχ = [dβ₀]` are both trivial or both nontrivial.

Conclusion: a locally constant `β` with `β² = χ` and `β σ β τ = ε(σ,τ) β(στ)`.
-/

namespace GlueDescent.B2

variable {U : Type*} [CommGroup U]

/-- `d β (σ, τ) = β σ β τ / β (στ)`. -/
def dB {Γ : Type*} [Mul Γ] (β : Γ → U) (x y : Γ) : U := β x * β y * (β (x * y))⁻¹

/-- `η` is a locally constant sign 2-cocycle (trivial action). -/
def IsSignCocycle {Γ : Type*} [Mul Γ] [TopologicalSpace Γ] (η : Γ → Γ → U) : Prop :=
  IsLocallyConstant (Function.uncurry η) ∧ (∀ x y, η x y ^ 2 = 1) ∧
    ∀ x y z, η (x * y) z * η x y = η y z * η x (y * z)

/-- `η` is the coboundary of a locally constant sign cochain. -/
def SignCob {Γ : Type*} [Mul Γ] [TopologicalSpace Γ] (η : Γ → Γ → U) : Prop :=
  ∃ γ : Γ → U, IsLocallyConstant γ ∧ (∀ x, γ x ^ 2 = 1) ∧ ∀ x y, η x y = dB γ x y

section Pullback

variable {Γ Δ : Type*} [Group Γ] [Group Δ] [TopologicalSpace Γ] [TopologicalSpace Δ]

/-- Pull back a 2-cochain along a homomorphism. -/
def pull (r : Δ →* Γ) (η : Γ → Γ → U) : Δ → Δ → U := fun x y => η (r x) (r y)

theorem pull_dB (r : Δ →* Γ) (β : Γ → U) : pull r (dB β) = dB (β ∘ r) := by
  funext x y; simp [pull, dB, map_mul]

theorem isSignCocycle_pull (r : Δ →* Γ) (hr : Continuous r) {η : Γ → Γ → U}
    (hη : IsSignCocycle η) : IsSignCocycle (pull r η) := by
  refine ⟨?_, fun x y => hη.2.1 _ _, fun x y z => by simp only [pull, map_mul]; exact hη.2.2 _ _ _⟩
  have : Function.uncurry (pull r η) = Function.uncurry η ∘ (Prod.map r r) := by
    funext ⟨x, y⟩; rfl
  rw [this]
  exact hη.1.comp_continuous (hr.prodMap hr)

end Pullback

section Algebra

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

theorem dB_mul (β γ : Γ → U) : dB (fun x => β x * γ x) = fun x y => dB β x y * dB γ x y := by
  funext x y; simp only [dB, mul_inv]; ac_rfl

theorem dB_inv (γ : Γ → U) : dB (fun x => (γ x)⁻¹) = fun x y => (dB γ x y)⁻¹ := by
  funext x y; simp only [dB, mul_inv, inv_inv]

theorem signCob_mul {η₁ η₂ : Γ → Γ → U} (h₁ : SignCob η₁) (h₂ : SignCob η₂) :
    SignCob (fun x y => η₁ x y * η₂ x y) := by
  obtain ⟨γ₁, hl₁, hs₁, he₁⟩ := h₁
  obtain ⟨γ₂, hl₂, hs₂, he₂⟩ := h₂
  refine ⟨fun x => γ₁ x * γ₂ x, hl₁.mul hl₂, fun x => by rw [mul_pow, hs₁, hs₂, mul_one], ?_⟩
  intro x y
  show η₁ x y * η₂ x y = _
  rw [he₁, he₂, dB_mul]

theorem signCob_inv {η : Γ → Γ → U} (h : SignCob η) : SignCob (fun x y => (η x y)⁻¹) := by
  obtain ⟨γ, hl, hs, he⟩ := h
  refine ⟨fun x => (γ x)⁻¹, hl.inv, fun x => by rw [inv_pow, hs, inv_one], ?_⟩
  intro x y
  show (η x y)⁻¹ = _
  rw [he, dB_inv]

theorem isSignCocycle_mul {η₁ η₂ : Γ → Γ → U} (h₁ : IsSignCocycle η₁) (h₂ : IsSignCocycle η₂) :
    IsSignCocycle (fun x y => η₁ x y * η₂ x y) := by
  refine ⟨?_, fun x y => by rw [mul_pow, h₁.2.1, h₂.2.1, mul_one], fun x y z => ?_⟩
  · have : Function.uncurry (fun x y => η₁ x y * η₂ x y) =
        Function.uncurry η₁ * Function.uncurry η₂ := by funext ⟨x, y⟩; rfl
    rw [this]; exact h₁.1.mul h₂.1
  · have e1 := h₁.2.2 x y z
    have e2 := h₂.2.2 x y z
    show η₁ (x * y) z * η₂ (x * y) z * (η₁ x y * η₂ x y) =
      η₁ y z * η₂ y z * (η₁ x (y * z) * η₂ x (y * z))
    calc η₁ (x * y) z * η₂ (x * y) z * (η₁ x y * η₂ x y)
        = (η₁ (x * y) z * η₁ x y) * (η₂ (x * y) z * η₂ x y) := by ac_rfl
      _ = (η₁ y z * η₁ x (y * z)) * (η₂ y z * η₂ x (y * z)) := by rw [e1, e2]
      _ = _ := by ac_rfl

theorem isSignCocycle_inv {η : Γ → Γ → U} (h : IsSignCocycle η) :
    IsSignCocycle (fun x y => (η x y)⁻¹) := by
  refine ⟨?_, fun x y => by rw [inv_pow, h.2.1, inv_one], fun x y z => ?_⟩
  · have : Function.uncurry (fun x y => (η x y)⁻¹) = (Function.uncurry η)⁻¹ := by
      funext ⟨x, y⟩; rfl
    rw [this]; exact h.1.inv
  · show (η (x * y) z)⁻¹ * (η x y)⁻¹ = (η y z)⁻¹ * (η x (y * z))⁻¹
    rw [← mul_inv, ← mul_inv, h.2.2 x y z]

/-- The coboundary of a locally constant pointwise square root of a locally constant
character is a sign 2-cocycle. -/
theorem isSignCocycle_dB [IsTopologicalGroup Γ] (χ : Γ →* U) (β₀ : Γ → U)
    (hβ₀ : ∀ x, β₀ x ^ 2 = χ x) (hl : IsLocallyConstant β₀) : IsSignCocycle (dB β₀) := by
  refine ⟨?_, fun x y => ?_, fun x y z => ?_⟩
  · have hm : Continuous (fun p : Γ × Γ => p.1 * p.2) := continuous_mul
    have h1 : IsLocallyConstant (fun p : Γ × Γ => β₀ p.1) := hl.comp_continuous continuous_fst
    have h2 : IsLocallyConstant (fun p : Γ × Γ => β₀ p.2) := hl.comp_continuous continuous_snd
    have h3 : IsLocallyConstant (fun p : Γ × Γ => (β₀ (p.1 * p.2))⁻¹) :=
      (hl.comp_continuous hm).inv
    have : Function.uncurry (dB β₀) = ((fun p : Γ × Γ => β₀ p.1) * fun p => β₀ p.2) *
        fun p => (β₀ (p.1 * p.2))⁻¹ := by funext ⟨x, y⟩; rfl
    rw [this]; exact (h1.mul h2).mul h3
  · simp only [dB, mul_pow, inv_pow, hβ₀, map_mul, mul_inv_cancel]
  · simp only [dB]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, mul_assoc]
    abel

end Algebra

/-- **B2, the deduction** (N5 L665-700). See the module docstring for the hypotheses. -/
theorem exists_beta {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : Type*} (Gv : ι → Type*) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
    (r : ∀ v, Gv v →* G) (hr : ∀ v, Continuous (r v))
    (hasse : ∀ η : G → G → U, IsSignCocycle η → (∀ v, SignCob (pull (r v) η)) → SignCob η)
    (local_two : ∀ v, ∀ η₁ η₂ : Gv v → Gv v → U, IsSignCocycle η₁ → IsSignCocycle η₂ →
      ¬ SignCob η₁ → ¬ SignCob η₂ → SignCob (fun x y => η₁ x y * (η₂ x y)⁻¹))
    (ε : G → G → U) (hε : IsSignCocycle ε)
    (χ : G →* U) (β₀ : G → U) (hβ₀ : ∀ x, β₀ x ^ 2 = χ x) (hl : IsLocallyConstant β₀)
    (agree : ∀ v, SignCob (pull (r v) ε) ↔ SignCob (pull (r v) (dB β₀))) :
    ∃ β : G → U, IsLocallyConstant β ∧ (∀ x, β x ^ 2 = χ x) ∧
      ∀ x y, β x * β y = ε x y * β (x * y) := by
  have hd : IsSignCocycle (dB β₀) := isSignCocycle_dB χ β₀ hβ₀ hl
  -- η = ε · (dβ₀)⁻¹
  set η : G → G → U := fun x y => ε x y * (dB β₀ x y)⁻¹ with hηdef
  have hη : IsSignCocycle η := isSignCocycle_mul hε (isSignCocycle_inv hd)
  have hloc : ∀ v, SignCob (pull (r v) η) := by
    intro v
    have hpε := isSignCocycle_pull (r v) (hr v) hε
    have hpd := isSignCocycle_pull (r v) (hr v) hd
    have e : pull (r v) η = fun x y => pull (r v) ε x y * (pull (r v) (dB β₀) x y)⁻¹ := rfl
    rw [e]
    by_cases h : SignCob (pull (r v) ε)
    · exact signCob_mul h (signCob_inv ((agree v).mp h))
    · exact local_two v _ _ hpε hpd h (fun h' => h ((agree v).mpr h'))
  obtain ⟨γ, hγl, hγs, hγe⟩ := hasse η hη hloc
  -- β = β₀ γ
  refine ⟨fun x => β₀ x * γ x, hl.mul hγl, fun x => by rw [mul_pow, hβ₀, hγs, mul_one], ?_⟩
  intro x y
  have hxy := hγe x y
  simp only [hηdef, dB] at hxy
  -- from ε · (dβ₀)⁻¹ = dγ:  β₀x γx β₀y γy = ε (β₀ (xy) γ (xy))
  have key : ε x y = (β₀ x * β₀ y * (β₀ (x * y))⁻¹) * (γ x * γ y * (γ (x * y))⁻¹) := by
    rw [← hxy]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  show β₀ x * γ x * (β₀ y * γ y) = ε x y * (β₀ (x * y) * γ (x * y))
  rw [key]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel


/-- **B2, the cohomological form of the square-root criterion** (N5 L680-683, the exact sequence
`1 → ±1 → μ_∞ → μ_∞ → 1`). For a character `ψ` with a locally constant pointwise square root
`β₀`, the boundary `δψ = [dβ₀]` is trivial iff `ψ` has a locally constant square-root
character. (Which characters of `G_{ℚ_p}` have square roots is local class field theory:
leaf L-B2c.) -/
theorem signCob_dB_iff {Γ : Type*} [Group Γ] [TopologicalSpace Γ] (ψ : Γ →* U) (β₀ : Γ → U)
    (hβ₀ : ∀ x, β₀ x ^ 2 = ψ x) (hl : IsLocallyConstant β₀) :
    SignCob (dB β₀) ↔ ∃ φ : Γ →* U, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = ψ x := by
  constructor
  · rintro ⟨γ, hγl, hγs, hγe⟩
    refine ⟨{ toFun := fun x => β₀ x * (γ x)⁻¹, map_one' := ?_, map_mul' := ?_ },
      hl.mul hγl.inv, fun x => ?_⟩
    · have h := hγe 1 1
      simp only [dB, one_mul] at h
      have h' : β₀ 1 * (γ 1)⁻¹ * (β₀ 1 * (γ 1)⁻¹) = β₀ 1 * (γ 1)⁻¹ := by
        have : β₀ 1 * β₀ 1 * (β₀ 1)⁻¹ * (γ 1 * γ 1 * (γ 1)⁻¹)⁻¹ = 1 := by
          rw [h, mul_inv_cancel]
        apply Additive.ofMul.injective
        have := congrArg Additive.ofMul this
        simp only [ofMul_mul, ofMul_inv, ofMul_one] at this ⊢
        rw [← sub_eq_zero]; rw [← this]; abel
      exact mul_eq_left.mp h'
    · intro x y
      have h := hγe x y
      simp only [dB] at h
      have : β₀ x * β₀ y * (β₀ (x * y))⁻¹ * (γ x * γ y * (γ (x * y))⁻¹)⁻¹ = 1 := by
        rw [h, mul_inv_cancel]
      show β₀ (x * y) * (γ (x * y))⁻¹ = β₀ x * (γ x)⁻¹ * (β₀ y * (γ y)⁻¹)
      apply Additive.ofMul.injective
      have := congrArg Additive.ofMul this
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at this ⊢
      rw [← sub_eq_zero, ← neg_eq_zero, ← this]; abel
    · show (β₀ x * (γ x)⁻¹) ^ 2 = ψ x
      rw [mul_pow, hβ₀, inv_pow, hγs, inv_one, mul_one]
  · rintro ⟨φ, hφl, hφs⟩
    refine ⟨fun x => β₀ x * (φ x)⁻¹, hl.mul hφl.inv, fun x => ?_, fun x y => ?_⟩
    · rw [mul_pow, hβ₀, inv_pow, hφs, mul_inv_cancel]
    · simp only [dB, map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel

end GlueDescent.B2

/-!
## The leaves of B2 over genuine Mathlib objects

`G_ℚ = Field.absoluteGaloisGroup ℚ` and `G_{ℚ_p} = Field.absoluteGaloisGroup ℚ_[p]` with their
Krull topologies; `resp p : G_{ℚ_p} →* G_ℚ` is Mathlib's `absoluteGaloisGroup.map` along
`ℚ → ℚ_p` (it depends on a choice of embedding `ℚ̄ → ℚ̄_p`; the vanishing of a class does not).
Sign-valued cochains are `ℂ^×`-valued with square `1`. `cyc N : G_ℚ →* (ℤ/N)^×` is Mathlib's
`modularCyclotomicCharacter` on `ℚ̄`.
-/

namespace GlueDescent.B2Q

open GlueDescent.B2 NumberField

/-- `G_ℚ`. -/
abbrev GQ := Field.absoluteGaloisGroup ℚ

instance : IsTopologicalGroup GQ :=
  inferInstanceAs (IsTopologicalGroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- `G_{ℚ_p}`. -/
abbrev GQp (p : Nat.Primes) := Field.absoluteGaloisGroup ℚ_[p]

/-- The decomposition-group map `G_{ℚ_p} → G_ℚ`. -/
noncomputable def resp (p : Nat.Primes) : GQp p →* GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).toMonoidHom

theorem resp_continuous (p : Nat.Primes) : Continuous (resp p) :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous

/-- The forgetful map `Gal(ℚ̄/ℚ) → Aut(ℚ̄)` as a monoid homomorphism. -/
noncomputable def toRingAut : GQ →* (AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The cyclotomic character `G_ℚ → (ℤ/N)^×`. -/
noncomputable def cyc (N : ℕ) [NeZero N] : GQ →* (ZMod N)ˣ :=
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  (modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)).comp toRingAut

/-- A Dirichlet character as a character of `G_ℚ`. -/
noncomputable def galChar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : GQ →* ℂˣ :=
  χ.toUnitHom.comp (cyc N)

/-- **Leaf L-B2a** (Hasse principle for `H²(G_ℚ, ±1)` at the finite places). A continuous sign
2-cocycle of `G_ℚ` whose restriction to every `G_{ℚ_p}` is a coboundary is a coboundary.
Consequence of: `H²(G_K, μ₂) = Br(K)[2]` (Kummer theory, Hilbert 90), the
Albert–Brauer–Hasse–Noether theorem `Br(ℚ) ↪ ⊕_v Br(ℚ_v)` with `∑_v inv_v = 0`, and
`Br(ℝ) = ℤ/2` (so a class trivial at all finite places is trivial at `∞`). -/
def LeafHasse : Prop :=
  ∀ η : GQ → GQ → ℂˣ, IsSignCocycle η →
    (∀ p : Nat.Primes, SignCob (pull (resp p) η)) → SignCob η

/-- **Leaf L-B2b** (`H²(G_{ℚ_p}, ±1)` has at most two elements). Consequence of
`H²(G_{ℚ_p}, μ₂) = Br(ℚ_p)[2] ≅ ℤ/2` (local class field theory). -/
def LeafLocalTwo : Prop :=
  ∀ p : Nat.Primes, ∀ η₁ η₂ : GQp p → GQp p → ℂˣ, IsSignCocycle η₁ → IsSignCocycle η₂ →
    ¬ SignCob η₁ → ¬ SignCob η₂ → SignCob (fun x y => η₁ x y * (η₂ x y)⁻¹)

/-- **Leaf L-B2c** (explicit local square-root criterion for Dirichlet characters). For a
Dirichlet character `χ` mod `N` and a prime `p` with `N = p^k N'`, `p ∤ N'`, let `u ∈ (ℤ/N)^×`
be `≡ -1 mod p^k` and `≡ 1 mod N'`. Then `χ|_{G_{ℚ_p}}` has a continuous square-root
character iff `χ(u) = 1`. Consequence of local class field theory for `ℚ_p` with its explicit
(Lubin–Tate / cyclotomic) reciprocity law — the local Artin map sends `-1 ∈ ℤ_p^×` to an element
acting on `μ_N` through `u^{±1} = u` — together with the structure of `ℚ_p^×` (N5 L683-689: a
finite-order character of `ℚ_p^×` has a square root iff its value at `-1` is `1`). -/
def LeafSqrtCrit : Prop :=
  ∀ (p : Nat.Primes) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ),
    ((u : ZMod N).cast : ZMod ((p : ℕ) ^ N.factorization p)) = -1 →
    ((u : ZMod N).cast : ZMod (N / (p : ℕ) ^ N.factorization p)) = 1 →
    ((∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = galChar χ (resp p x)) ↔
      χ.toUnitHom u = 1)

/-- An element of `G_ℚ` as an automorphism of `ℚ̄`. -/
def act (σ : GQ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ

/-- `ε : G_ℚ × G_ℚ → ℂ^×` is inflated from `Gal(L/ℚ)`. -/
def InflatedFrom (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (ε : GQ → GQ → ℂˣ) : Prop :=
  ∀ σ σ' τ τ' : GQ, (∀ x ∈ L, act σ x = act σ' x) → (∀ x ∈ L, act τ x = act τ' x) → ε σ τ = ε σ' τ'

/-- `L` is unramified at `p`: every prime of `𝓞 L` above `p` has ramification index `1`. -/
def UnramifiedAt (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 L), P.IsPrime → ((p : ℤ) : 𝓞 L) ∈ P →
    P.ramificationIdx ℤ = 1

/-- **Leaf L-B2d** (unramified classes vanish locally). If `ε` is inflated from `Gal(L/ℚ)` for
a finite Galois `L` unramified at `p`, its restriction to `G_{ℚ_p}` is a coboundary.
Consequence of: the restriction is inflated from `Gal(ℚ_p^{ur}/ℚ_p) ≅ ℤ̂`, and
`H²(ℤ̂, ℤ/2) = 0` (`cd ℤ̂ = 1`). -/
def LeafUnramified : Prop :=
  ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ), IsSignCocycle ε → InflatedFrom L ε →
    ∀ p : Nat.Primes, UnramifiedAt L p → SignCob (pull (resp p) ε)

end GlueDescent.B2Q

/-!
## Toward the assembly of B2 over `G_ℚ`: continuity of the cyclotomic character
-/

namespace GlueDescent.B2Q

open GlueDescent.B2 NumberField

/-- A function on a topological group that is invariant under right translation by an open
subgroup is locally constant. -/
theorem isLocallyConstant_of_openSubgroup {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (f : G → X)
    (hf : ∀ g, ∀ k ∈ U, f (g * k) = f g) : IsLocallyConstant f := by
  refine IsLocallyConstant.iff_isOpen_fiber.2 fun y => isOpen_iff_forall_mem_open.2 fun x hx =>
    ⟨(x * ·) '' U, ?_, isOpenMap_mul_left x _ hU, ⟨1, U.one_mem, mul_one x⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  rw [hf x k hk, hx]

theorem act_mul (σ τ : GQ) (x : AlgebraicClosure ℚ) : act (σ * τ) x = act σ (act τ x) := rfl

/-- `cyc N σ` depends only on the action of `σ` on the `N`-th roots of unity. -/
theorem cyc_eq_of_agree (N : ℕ) [NeZero N] (σ τ : GQ)
    (h : ∀ t ∈ rootsOfUnity N (AlgebraicClosure ℚ),
      act σ (t : AlgebraicClosure ℚ) = act τ (t : AlgebraicClosure ℚ)) :
    cyc N σ = cyc N τ := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N
  apply Units.ext
  show ((modularCyclotomicCharacter (AlgebraicClosure ℚ) hn (toRingAut σ) : (ZMod N)ˣ) : ZMod N) =
    ((modularCyclotomicCharacter (AlgebraicClosure ℚ) hn (toRingAut τ) : (ZMod N)ˣ) : ZMod N)
  apply modularCyclotomicCharacter.unique _ hn
  intro t ht
  rw [← modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) hn (toRingAut σ) ht]
  exact (h t ht).symm

/-- **The cyclotomic character is continuous** (locally constant): it is invariant under the
open subgroup fixing `ℚ(μ_N)`. -/
theorem cyc_isLocallyConstant (N : ℕ) [NeZero N] : IsLocallyConstant (cyc N) := by
  let S : Set (AlgebraicClosure ℚ) :=
    (fun t : (AlgebraicClosure ℚ)ˣ => (t : AlgebraicClosure ℚ)) ''
      (rootsOfUnity N (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ)
  have hfin : Finite (rootsOfUnity N (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ) :=
    (inferInstance : Finite (rootsOfUnity N (AlgebraicClosure ℚ)))
  haveI : Finite S := ((Set.toFinite _).image _).to_subtype
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ S
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  refine isLocallyConstant_of_openSubgroup (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    K.fixingSubgroup K.fixingSubgroup_isOpen (fun g => cyc N g) ?_
  intro g k hk
  apply cyc_eq_of_agree
  intro t ht
  have hfix : act k (t : AlgebraicClosure ℚ) = t :=
    (IntermediateField.mem_fixingSubgroup_iff K k).mp hk _
      (IntermediateField.subset_adjoin ℚ S ⟨t, ht, rfl⟩)
  show g (k (t : AlgebraicClosure ℚ)) = g (t : AlgebraicClosure ℚ)
  exact congrArg g hfix

theorem galChar_isLocallyConstant {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    IsLocallyConstant (galChar χ) :=
  show IsLocallyConstant (χ.toUnitHom ∘ cyc N) from (cyc_isLocallyConstant N).comp _

/-- A square-root choice function on `ℂ^×`. -/
noncomputable def sqrtU (z : ℂˣ) : ℂˣ :=
  have h : ∃ w : ℂ, w ^ 2 = z := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (by norm_num)
  Units.mk0 (Classical.choose h) (by
    intro h0
    have := Classical.choose_spec h
    rw [h0] at this
    exact z.ne_zero (by rw [← this]; ring))

theorem sqrtU_sq (z : ℂˣ) : sqrtU z ^ 2 = z := by
  apply Units.ext
  simp only [sqrtU, Units.val_pow_eq_pow_val, Units.val_mk0]
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (z : ℂ) (by norm_num : 0 < 2))

end GlueDescent.B2Q
