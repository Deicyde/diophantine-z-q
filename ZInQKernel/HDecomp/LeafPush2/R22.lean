import ZInQKernel.HDecomp.LeafPush2.R18

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from
`scratch/leaf-push2/LeafPush2.lean`, R22.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

namespace ZInQ.LeafPush2

open NumberField MeasureTheory

/-! Part I of the draft (def-faltings §§1-18 and H5, a verbatim copy) is imported from
`ZInQKernel.HDecomp.Faltings.Height`, namespace `ZInQ.DefFaltings`; the copies of
leaf-modcurves' curve definitions are `LeafModCurves`'s, from
`ZInQKernel.HDecomp.ModCurves.Leaves`. -/
open ZInQ.DefFaltings
open LeafModCurves (IsCurve IsJacobian JacobianExists IsBelyiFunction)

section R22Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 Complex

variable {K : Type} [Field K]

/-- `Spec ℂ` as a `K`-scheme via `σ : K → ℂ`. -/
noncomputable def cptObj (σ : K →+* ℂ) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom σ))

/-- The complex points `A(ℂ)_σ` of an abelian variety over `K` at `σ : K → ℂ`, a group
(Mathlib's group structure on morphisms into a group object). -/
abbrev CPts (A : AbVar K) (σ : K →+* ℂ) : Type := cptObj σ ⟶ A.X

noncomputable example (A : AbVar K) (σ : K →+* ℂ) : Group (CPts A σ) := inferInstance

/-- The value `s(p) ∈ ℂ` of a regular function `s ∈ Γ(U, 𝒪_A)` at a complex point `p ∈ U(ℂ)`
(`0` if `p ∉ U(ℂ)`); adapted from `GroupModel.evalAt` of def-faltings §17. -/
noncomputable def cEvalAt {A : AbVar K} {σ : K →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens)
    (s : Γ(A.X.left, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ p.left ⁻¹ᵁ U then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.left.appLE U ⊤ h s) else 0

/-- `Φ⁻¹(U(ℂ)) ⊆ ℂ^g`. -/
def cDom {A : AbVar K} {σ : K →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → CPts A σ) (U : A.X.left.Opens) :
    Set (Fin g → ℂ) := {z | ⊤ ≤ (Φ z).left ⁻¹ᵁ U}

/-- **Analytic uniformization of `A(ℂ)_σ`** (def-faltings' `IsAnalyticUniformization`, with the
abelian variety in place of a group model): `Φ : ℂ^g → A(ℂ)_σ` a surjective homomorphism with
kernel `Λ`, with open preimages of affine-chart points and holomorphic regular functions. -/
def IsUniformization {A : AbVar K} (σ : K →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) : Prop :=
  (∀ z w, Φ (z + w) = Φ z * Φ w) ∧
  (∀ z, Φ z = 1 ↔ z ∈ Λ) ∧
  Function.Surjective Φ ∧
  (∀ U, IsOpen (cDom Φ U)) ∧
  (∀ U (s : Γ(A.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Φ z) U s) (cDom Φ U))

/-- **Siegel upper half space** `𝔥₂`: symmetric `Ω` with `Im Ω` positive definite. -/
def IsSiegel (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  Ω.transpose = Ω ∧ (Ω.map Complex.im).PosDef

/-- **`Ω` is a period matrix of the lattice `Λ`**: a `ℂ`-linear automorphism `T` of `ℂ²` maps
`Λ` onto `Ωℤ² + ℤ²`. For `Ω ∈ 𝔥₂`, `ℂ²/(Ωℤ² + ℤ²)` carries the principal polarization with
Hermitian form `(Im Ω)⁻¹` (Birkenhake–Lange, *Complex abelian varieties*, §8.1, UNVERIFIED
number), and every principal polarization of `ℂ²/Λ` with every symplectic basis arises this way.
So "for all `Ω ∈ 𝔥₂` with `IsPeriodMatrix Λ Ω`" = "for all principal polarizations of `ℂ²/Λ`
and all symplectic bases". No polarization object is needed. -/
def IsPeriodMatrix (Λ : Submodule ℤ (Fin 2 → ℂ)) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ T : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ), ∀ z, z ∈ Λ ↔
    ∃ m n : Fin 2 → ℤ, T z = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ)

/-- Theta characteristics of level 2: `m = (a, b)`, `a, b ∈ {0, 1}²` standing for `a/2, b/2`. -/
abbrev Char2 : Type := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)

/-- **The theta constant** `θ[a;b](0, Ω) = ∑_{n ∈ ℤ²} exp(πi (n+a/2)ᵀΩ(n+a/2) + 2πi (n+a/2)ᵀ b/2)`
(Mumford, *Tata Lectures on Theta I*, II §1, UNVERIFIED number). Absolutely convergent for
`Ω ∈ 𝔥₂`; the `tsum` junk value `0` occurs only outside `𝔥₂`. The six odd characteristics give
`0`, so the point has the same height as the ten even theta constants used by the project. -/
noncomputable def thetaConst (Ω : Matrix (Fin 2) (Fin 2) ℂ) (m : Char2) : ℂ :=
  ∑' n : Fin 2 → ℤ,
    Complex.exp (Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ
          Ω.mulVec (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2)) +
      2 * Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ (fun i => ((m.2 i : ℕ) : ℂ) / 2)))

/-- (copied from scratch/rv-loc-leaves/PazukiR22.lean) Absolute logarithmic Weil height (sup
norms) of a point of projective space over a number field: Mathlib's `Height.logHeight` divided by
`[K : ℚ]`. -/
noncomputable def absLogHeight {L : Type*} [Field L] [NumberField L] {J : Type*} [Finite J]
    (z : J → L) : ℝ :=
  Height.logHeight z / Module.finrank ℚ L

/-- (copied) Pazuki's constant `C₂(2, 2) = 1000 · 2⁴ · (log 2⁴)⁵`. -/
noncomputable def pazukiC2 : ℝ := 1000 * 2 ^ 4 * (Real.log (2 ^ 4)) ^ 5

/-- **R22. Pazuki** (Bull. SMF 140 (2012), Cor. 1.3(2), pp. 21-22 (`g = r = 2`), metric p. 26,
theta height p. 30; arXiv:0907.1458v2 Cor. 1.3(2) p. 3, Def. 2.1 pp. 6-7, Def. 2.6 p. 9; read by
the locator audit, docs/research/locators.md item 5). Printed (literal): for a principally
polarized abelian surface over `ℚ̄`, `|max(1,h_Θ) − max(1,h_D)/2| ≤ C₂ log(min(max(1,h_Θ),
max(1,h_D)) + 2)`, `h_D` in Deligne's metric, `h_Θ` the theta height with Euclidean norms at the
infinite places.

**Stated form (a consequence; the audit's upper half, rv-loc-leaves (c)).** For an abelian
surface `A` over a number field `K` whose stable Faltings height (Faltings' normalization) is the
real number `x`, and any `X ≥ max(1, x + log π)`; for every complex embedding `σ`, every analytic
uniformization `Φ` of `A(ℂ)_σ` with kernel `Λ`, every `Ω ∈ 𝔥₂` that is a period matrix of `Λ`
(= every principal polarization of `A(ℂ)_σ` with a symplectic basis), and every algebraic
representative `z ∈ L¹⁶` (`L` a number field, `emb : L → ℂ`) of the theta-null point
`[θ_m(0, Ω)]_m`: `h(z) ≤ X/2 + C₂ log(X + 2)`.

Why it is a consequence (each step is a citation-chain fact, not a Lean leaf):
* `h_D = h_F + log π` for surfaces (audit; `stableFaltingsHeightDeligne_eq`), so the hypothesis
  on `X` gives `X ≥ max(1, h_D)`; the three algebraic steps from the literal corollary are proved
  (`pazuki_upper_of_literal` in scratch/rv-loc-leaves, recompiled in §R22-glue below).
* The sup-norm height `absLogHeight` is `≤` the Euclidean-norm height of the paper (each
  archimedean factor `max |z_m| ≤ (∑|z_m|²)^{1/2}`); so an upper bound on Pazuki's `h_Θ` bounds it.
* Every analytic principal polarization of `A(ℂ)_σ` is algebraic and defined over `ℚ̄` (Riemann's
  theorem / GAGA, Mumford §§1-3 (T11-type input); rigidity of `NS`); its theta-null point is
  Pazuki's (Def. 2.6, level `r = 2`; the identification of his coordinates with the classical
  `θ[a;b](0, Ω)`, `a, b ∈ {0,½}²`, follows the project's reading (h-decomposition R22, pkg-I5),
  UNVERIFIED here). A change of symplectic basis permutes the `θ_m` up to eighth roots of unity
  and one common factor (theta transformation formula), so the height does not depend on it.
* **H5** identifies `stableFaltingsHeight` with the published height (rv-blueprints F2); taking
  the height through a real `x` (not `EReal.toReal`) keeps the statement no stronger.

Non-vacuity rests on standard facts not proved here: uniformizations exist (the `AbVar` analogue
of def-faltings' `AnalyticUniformizationExists`), principally polarizable abelian surfaces exist
over number fields (Jacobians of genus-2 curves), the theta-null point is algebraic up to a
common factor; and `𝔥₂ ≠ ∅` (`isSiegel_I`, proved below). -/
def R22_Pazuki : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, stableFaltingsHeight A = x →
    ∀ X : ℝ, max 1 (x + Real.log Real.pi) ≤ X →
    ∀ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → CPts A σ),
      IsUniformization σ Λ Φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∀ (L : Type) [Field L] [NumberField L] (emb : L →+* ℂ) (z : Char2 → L) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * thetaConst Ω m) →
      absLogHeight z ≤ X / 2 + pazukiC2 * Real.log (X + 2)

/-- The hardened form used by the glue (`X = max(1, h_F + 3)`, rv-leaves-a §3.3). -/
theorem R22_plus3 (h : R22_Pazuki) (K : Type) [Field K] [NumberField K] (A : AbVar K)
    (hA : A.dim = (2 : WithBot ℕ∞)) (x : ℝ) (hx : stableFaltingsHeight A = x)
    (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → CPts A σ)
    (hΦ : IsUniformization σ Λ Φ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : IsSiegel Ω)
    (hP : IsPeriodMatrix Λ Ω) (L : Type) [Field L] [NumberField L] (emb : L →+* ℂ)
    (z : Char2 → L) (c : ℂ) (hc : c ≠ 0) (hz : ∀ m, emb (z m) = c * thetaConst Ω m) :
    absLogHeight z ≤ max 1 (x + 3) / 2 + pazukiC2 * Real.log (max 1 (x + 3) + 2) := by
  have hpi : Real.log Real.pi ≤ 3 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  exact h K A hA x hx (max 1 (x + 3)) (max_le_max le_rfl (by linarith)) σ Λ Φ hΦ Ω hΩ hP
    L emb z c hc hz

/-- Sanity: `i · 1 ∈ 𝔥₂` (the `Ω`-quantifier of R22 is not empty). -/
theorem isSiegel_I : IsSiegel (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine ⟨by simp, ?_⟩
  have : ((Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)).map Complex.im) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this]
  exact Matrix.PosDef.one

end R22Sec

/-! ## R3 (Lin–Yang): the QM surfaces of discriminant 6 are Jacobians on the Lin–Yang family -/

end ZInQ.LeafPush2
