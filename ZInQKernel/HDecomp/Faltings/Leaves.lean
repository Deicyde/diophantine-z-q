import ZInQKernel.HDecomp.Faltings.Height

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/def-faltings/Faltings.lean`, §21-§22.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

namespace ZInQ.DefFaltings

open NumberField MeasureTheory

section ModelsSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ExteriorAlgebra
open PkgI3 (AbVar)

/-! ## 21. The leaves R19-R21 over `stableFaltingsHeight`

Normalizations (docs/research/locators.md): Gaudron-Rémond (R19) and Faltings (R20) use the
stable height in Faltings' original normalization, which is `stableFaltingsHeight`; Bost's bound
(R21) is used in the form `h_F ≥ −(3/2) dim A` printed by Gaudron-Rémond §9; Pazuki (R22) uses
Deligne's metric, `stableFaltingsHeightDeligne = stableFaltingsHeight + (g/2) log π`
(`stableFaltingsHeightDeligne_eq`).

Where the height is an input of an upper bound (R19, R20), it is taken through a real `x` with
`stableFaltingsHeight A = x`, never through `EReal.toReal` (whose junk value `0` at `⊤` would
make the statement stronger than the published one). Isogenies: homomorphisms of group schemes
that are finite and surjective (project's `IsIsogenyMor`); the degree is the order of the kernel
on `K̄`-points, which equals the degree in characteristic `0` (STANDARD). -/

section Leaves

open MonObj

/-- `Spec L` as a `K`-scheme (copied from `ZInQKernel/HDecomp/Objects.lean`). -/
noncomputable def ptObj (K L : Type) [Field K] [Field L] [Algebra K L] :
    Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

variable {K : Type} [Field K]

/-- An isogeny: a homomorphism of group schemes, finite and surjective. -/
def IsIsogeny {A B : AbVar K} (φ : A.X ⟶ B.X) : Prop :=
  IsMonHom φ ∧ IsFinite φ.left ∧ Surjective φ.left

/-- The degree of an isogeny in characteristic `0`: `# ker(φ)(K̄)`. -/
noncomputable def isogDeg {A B : AbVar K} (φ : A.X ⟶ B.X) : ℕ :=
  Nat.card {P : ptObj K (AlgebraicClosure K) ⟶ A.X // P ≫ φ = 1}

/-- Gaudron-Rémond's `κ(A) = ((14g)^{64g²} [k:ℚ] max(h_F(A), log[k:ℚ], 1)²)^{1024g³}`. -/
noncomputable def grKappa (g d : ℕ) (x : ℝ) : ℝ :=
  ((14 * g : ℝ) ^ (64 * g ^ 2) * d * (max (max x (Real.log d)) 1) ^ 2) ^ (1024 * g ^ 3)

/-- **R19. Gaudron-Rémond**, Duke Math. J. 163 (2014), Thm 1.4 (p. 2060; `κ` and
`α(g) = 1024g³`, p. 2058), specialized to `k = K` (locators read by the audit, locators.md).
Isogenous abelian varieties over a number field admit isogenies in both directions of degree
`≤ κ(A)`. -/
def R19_GaudronRemond : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → stableFaltingsHeight A = x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **R20. Faltings' height lemma** (Faltings 1983, Lemma 5; Raynaud, Astérisque 127, VII
Cor. 2.1.3): for an isogeny `φ : A → B`, `|h_F(A) − h_F(B)| ≤ ½ log deg φ`. Locator audit: Lemma 5
unread, UNVERIFIED (including direction and the stable/semistable hypotheses). -/
def R20_FaltingsLemma5 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbVar K) (φ : A.X ⟶ B.X), IsIsogeny φ →
    ∀ x y : ℝ, stableFaltingsHeight A = x → stableFaltingsHeight B = y →
      |x - y| ≤ (1 / 2) * Real.log (isogDeg φ)

/-- **R21. Bost's lower bound**, in the form printed by Gaudron-Rémond 2014 §9 (proof of
Lemma 9.1, p. 2098): `h_F(A) ≥ −(3/2) dim A`. Bost's own display UNVERIFIED (locators.md). -/
def R21_Bost : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ((-(3 / 2) * g : ℝ) : EReal) ≤ stableFaltingsHeight A

/-- R21 excludes `h = ⊥`. -/
theorem stableFaltingsHeight_ne_bot_of_R21 (h : R21_Bost) {K : Type} [Field K] [NumberField K]
    (A : AbVar K) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) : stableFaltingsHeight A ≠ ⊥ := by
  intro hb
  have := h K A g hg
  rw [hb] at this
  exact EReal.coe_ne_bot _ (le_bot_iff.mp this)

end Leaves

/-! ## 22. R18 and R22: not stated

* **R22 (Pazuki, Bull. SMF 140 (2012), Cor. 1.3(2)).** The height side is available:
  `stableFaltingsHeightDeligne` and `stableFaltingsHeightDeligne_eq` give
  `h_D = h_F + log π` for surfaces, so the condition `X_D ≥ max(1, h_D(A))` of the consequence
  form is expressible. Missing: principal polarizations, level-2 theta structures and the theta
  (Fubini-Study) height `h_Θ(A)` of a principally polarized abelian surface (the theta constants
  need the period matrix, i.e. AN3 together with the Riemann form). The genus-2 special case over
  `faltingsHeightGood` is `PkgI5.PazukiGoodGenus2Literal` (scratch/rv-loc-leaves).
* **R18 (Javanpeykar, ANT 8 (2014), Thm 1.1.1).** Missing: the genus of a smooth projective
  curve over `ℚ̄` (differentials or `H¹`), Belyi maps (finite morphisms to `ℙ¹` unramified outside
  `{0, 1, ∞}`, with their degree) and the Jacobian as an `AbVar` (node AV7). -/

end ModelsSec

end ZInQ.DefFaltings
