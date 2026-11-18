import ZInQKernel.Contrib.OneProof.R16Split
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Fricke.Matrix

/-! # r16-shimura73: `r16CoreY` along the manuscript's own sources (Li 1975, Shimura 1973 Thm 1)

Task r16-shimura73 (2026-11-17), report `docs/research/r16-shimura73.md`, scratch `scratch/r16-shimura73/`.

The manuscript (diophantine_zq.tex, the paragraph "Modularity and a uniform conductor bound") takes the
primitive newform `f`, applies Li's Fricke formula (Li, Math. Ann. 212 (1975), p. 296, before Lemma 6) to make the
span of the coefficient conjugates of `f` Fricke-stable, and then uses Shimura's quotient construction and
Euler-factor identity (Shimura, J. Math. Soc. Japan 25 (1973), Thm 1) to conclude that `r_5` is a constituent of the
Tate module of `A_f`. This file states the two cited theorems as printed-form leaves over the kernel's objects
and derives from them exactly what they give:

* `LiFrickePrinted` (LEAF, printed form, weight 2): for a newform `g` of level `N`, `g ∣₂ W_N = λ · g^ρ`, where `g^ρ`
  is the cusp form with coefficients `conj(a_n(g))`.
* `ShimuraThm1Printed` (LEAF, printed form, existential): for a newform `f` of weight 2 on `Γ₁(N)` and `J = J₁(N)`,
  `K_f` is finite over `ℚ`, and there are `A` over `ℚ`, a surjection `π : J → A` and `θ : K_f → End⁰(A)` with
  `dim A = [K_f : ℚ]`; if the span of the conjugates of `f` is Fricke-stable, the Euler factors of `A` are the
  products over the conjugates: the characteristic polynomial of Frobenius at `p` on `V_ℓ(A)` is
  `∏_{ι : K_f → ℂ} (X² − ι(a_p) X + ι(χ(p)) p)` (for all but finitely many `p`).
* `ConjNewform` (step not covered by the two citations): the Galois conjugates of a newform are newforms (needed to
  apply Li to every conjugate).
* `r16CoreYTotal_of_shimura_li`: from the three, `R16CoreYTotal` (= `R16Split.R16CoreY` with the per-embedding
  trace/determinant clause replaced by Shimura's total Euler-factor identity). Proved.
* **Known issue.** `R16CoreYTotal` does not give `R16CoreY`: the total identity does not mention `θ`, so it cannot
  say which `ι`-component of `V_ℓ(A)` carries which conjugate (it is invariant under `θ ↦ θ ∘ τ` for
  `τ ∈ Aut(K_f)`, while the per-embedding clause is not). `ShimuraTotalToComponents` names the statement the chain
  would need; it is neither in the manuscript nor in the two cited prints (it is the gap a review recorded at the
  manuscript's inference). `r16CoreY_of_total` composes. This file does not repair the gap.

No `sorry`, no `axiom`, no build-time code. -/

noncomputable section

namespace R16ShimuraLi

open scoped MatrixGroups ModularForm
open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH
  oldSpace IsNewform)
open LeafModCurves
open WeierstrassCurve AlgebraicGeometry
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar

/-! ## 1. Definitions: conjugates, Fricke-stability, the Euler-factor identity -/

/-- `g` is a Galois conjugate `f^σ` of `f`: its `q`-expansion coefficients are `σ(a_n(f))` for one field
embedding `σ : K_f → ℂ`. -/
def IsConjOf {N : ℕ} (f g : CF N 2) : Prop :=
  ∃ σ : coeffField f →+* ℂ, ∀ n : ℕ, coeff g n = σ ⟨coeff f n, coeff_mem_coeffField f n⟩

/-- The `ℂ`-span of the conjugates of `f` (as functions on `ℍ`). -/
def conjSpan {N : ℕ} (f : CF N 2) : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ {F | ∃ g : CF N 2, IsConjOf f g ∧ F = ⇑g}

/-- **The span of the conjugates of `f` is Fricke-stable** (generator form: the slash operator by
`W_N = (0 −1; N 0)` is `ℂ`-linear, so this is stability of the span): every conjugate `g` has
`g ∣₂ W_N ∈ span{f^σ}`. The premise of Shimura 1973 Thm 1's Euler-factor clause as the manuscript uses it. -/
def FrickeStable (N : ℕ) (hN : 0 < N) (f : CF N 2) : Prop :=
  letI : NeZero N := ⟨hN.ne'⟩
  ∀ g : CF N 2, IsConjOf f g → (⇑g ∣[(2 : ℤ)] TauCeti.frickeGL ℝ N) ∈ conjSpan f

/-- **Shimura's Euler-factor identity for `A`** (in characteristic-polynomial form): for every prime `ℓ` (with
`V_ℓ(A)` finite-dimensional, the print's presupposition) there is a finite set `S` of primes such that, for every
prime `p ∉ S`, `p ∤ Nℓ`, and every arithmetic Frobenius `σ` at `p`, the characteristic polynomial over `ℚ_ℓ` of `σ`
on `V_ℓ(A)` is the rational polynomial `Q` with `Q = ∏_{ι : K_f → ℂ} (X² − ι(a_p) X + ι(χ(p)) p)` in `ℂ[X]`.
(Equality of the Euler factors at `p` of `ζ(s, A/ℚ)` and `∏_ι L(s, f^ι)`, after `X ↦` reciprocal polynomial.) -/
def EulerIdentity (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (A : AbVar ℚ) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] [FiniteDimensional ℚ_[ℓ] (A.V ℓ)],
    ∃ S : Finset ℕ, ∀ (p : ℕ), p.Prime → p ∉ S → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
      ∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
        ∃ Q : Polynomial ℚ,
          Q.map (algebraMap ℚ ℂ) =
            (∏ᶠ io : coeffField f →+* ℂ,
              (Polynomial.X ^ 2 - Polynomial.C (io ⟨coeff f p, coeff_mem_coeffField f p⟩) * Polynomial.X + Polynomial.C (io c * (p : ℂ)))) ∧
          LinearMap.charpoly (A.galRep ℓ σ) = Q.map (algebraMap ℚ ℚ_[ℓ])

/-! ## 2. The two cited theorems (printed-form leaves) -/

/-- **LEAF (Li's Fricke formula), printed form at weight 2.** W.-C. W. Li, *Newforms and functional equations*,
Math. Ann. 212 (1975), 285–315, p. 296 (before Lemma 6; the manuscript's locator, UNVERIFIED: not read here, no
network): for a newform `g ∈ S_k(N, χ)`, `g ∣_k W_N = λ_N(g) · ḡ`, where `ḡ(z) = conj(g(−z̄))` is the newform with
coefficients `conj(a_n(g))`. Stated at `k = 2` (a specialization), with `ḡ` given as an element of
`S₂(Γ₁(N))` by its coefficients, and without `|λ| = 1` (a weakening); the normalization of `W_N` and of the slash
operator only rescales `λ`, which is existential. `IsNewform` is the kernel's (normalized eigenform outside the old
space; its docstring gives the dictionary to Li's definition). -/
def LiFrickePrinted : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (χ : DirichletCharacter ℂ N) (g : CF N 2), IsNewform g χ →
    letI : NeZero N := ⟨hN.ne'⟩
    ∃ (lam : ℂ) (h : CF N 2), (∀ n : ℕ, coeff h n = starRingEnd ℂ (coeff g n)) ∧
      (⇑g ∣[(2 : ℤ)] TauCeti.frickeGL ℝ N) = lam • ⇑h

/-- **LEAF (Shimura 1973, Theorem 1), printed form, existential.** G. Shimura, *On the factors of the jacobian
variety of a modular function field*, J. Math. Soc. Japan 25 (1973), 523–544, Theorem 1 (pp. 526–527 per the
locator audit, row R16 of `docs/research/locators.md`; page and clause wording UNVERIFIED here, no network). For a
newform `f ∈ S₂(Γ₁(N))` with nebentypus `χ` and `J = J₁(N)` (`IsJ1`: the Jacobian of a model of `X₁(N)` over `ℚ`):
`K_f` is a number field, and there are an abelian variety `A = A_f` over `ℚ`, a surjective homomorphism
`π : J → A` (Shimura's quotient) and `θ : K_f → End⁰_ℚ(A)` with `dim A = [K_f : ℚ]` (the unconditional clauses);
and if the span of the conjugates of `f` is stable under the Fricke involution, the zeta function of `A` over `ℚ`
is `∏_ι L(s, f^ι)` up to finitely many Euler factors (`EulerIdentity`; the Euler factor of `ζ(s, A/ℚ)` at a good
prime read on `V_ℓ(A)`). Weakenings against the print: `A` existential (the print constructs it as `J/I_f J` with `θ`
the Hecke action; the kernel has no non-Diamond–Shurman Hecke operators on `J₁(N)`), and the exceptional set of the
Euler identity is an unspecified finite set (the print's set, presumably the primes dividing `N`, UNVERIFIED). -/
def ShimuraThm1Printed : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ) (hN : 0 < N),
    IsNewform f χ → IsJ1 N J →
    FiniteDimensional ℚ (coeffField f) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (_θ : coeffField f →+* A.End0),
      Surjective π.hom.left ∧
      A.dim = ((Module.finrank ℚ (coeffField f) : ℕ) : WithBot ℕ∞) ∧
      (FrickeStable N hN f → EulerIdentity N χ f A)

/-! ## 3. The step the two citations do not cover, and the known issue -/

/-- **Conjugates of newforms are newforms** (step not covered by the manuscript's two citations: Li's formula is
applied to every conjugate `f^σ`). For a newform `f` of weight 2 and level `N`, every `g ∈ S₂(Γ₁(N))` with
coefficients `σ(a_n(f))` is a newform (for the character `σ ∘ χ`, left existential). Sources: Shimura 1971,
*Introduction to the arithmetic theory of automorphic functions*, Thm 3.52 (`f^σ ∈ S_k(N, χ^σ)`, eigenform) and the
Galois stability of the new subspace (Li 1975 / Atkin–Lehner); numbers UNVERIFIED. Not cited at the manuscript's
step: GLUE until a reader attaches a print. -/
def ConjNewform : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f g : CF N 2), 0 < N → IsNewform f χ → IsConjOf f g →
    ∃ χ' : DirichletCharacter ℂ N, IsNewform g χ'

/-- **What Li and Shimura 1973 Thm 1 give** (`R16Split.R16CoreY` with the per-embedding trace/determinant clause
replaced by the total Euler-factor identity). -/
def R16CoreYTotal : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    FiniteDimensional ℚ (coeffField f) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (_θ : coeffField f →+* A.End0),
      Surjective π.hom.left ∧
      A.dim = ((Module.finrank ℚ (coeffField f) : ℕ) : WithBot ℕ∞) ∧
      EulerIdentity N χ f A

/-- **KNOWN ISSUE: the statement the chain would need after Shimura's Euler-factor identity** (not a leaf, not in
the manuscript, not in the two cited prints). For a quotient `π : J₁(N) ↠ A` of dimension `[K_f : ℚ]` with a
`K_f`-action whose Euler factors are `∏_ι (X² − ι(a_p) X + ι(χ(p)) p)`, some action `θ'` of `K_f` makes every
`ι`-component of `V_ℓ(A)` carry trace `ι(a_p)` and determinant `ι(χ(p)) p` at every `p ∤ Nℓ`. The manuscript passes
from the Euler-factor identity (a divisibility/equality of total characteristic polynomials) directly to "`r_5` is a
constituent of the Tate module of `A_f`"; that inference needs this statement or the Eichler–Shimura relation
`Frob_p + χ(p) p Frob_p⁻¹ = T_p` on `A_f` with `θ` the Hecke action (Shimura 1971 Thm 7.9 / Diamond–Shurman
Thm 9.6.5 at `k = 2`, the Diamond–Shurman route this task replaces). With `∀ θ` in place of `∃ θ'` the statement is
false whenever `Aut(K_f) ≠ 1` (replace a good `θ` by `θ ∘ τ`); with `S` ≠ ∅ it also needs every `p ∤ Nℓ` outside
`S` (good reduction of `A` outside `N` and Chebotarev). Raised with the owner as a source issue; not repaired. -/
def ShimuraTotalToComponents : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J → FiniteDimensional ℚ (coeffField f) →
    ∀ (A : AbVar ℚ) (π : Hom J A) (_θ : coeffField f →+* A.End0),
      Surjective π.hom.left →
      A.dim = ((Module.finrank ℚ (coeffField f) : ℕ) : WithBot ℕ∞) →
      EulerIdentity N χ f A →
      ∃ θ' : coeffField f →+* A.End0,
        ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
          ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
            (∀ a : coeffField f, (a : ℂ) = coeff f p →
                LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ' emb σ) = emb a) ∧
            (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
                LinearMap.det (frobOn ℓ A θ' emb σ) = emb c * p)

/-! ## 4. Glue (proved) -/

/-- **Li's formula makes the span of the conjugates Fricke-stable** (the manuscript's first sentence; glue, proved,
given that conjugates are newforms). For a conjugate `g = f^σ`, Li gives `g ∣₂ W_N = λ ḡ`, and `ḡ` has coefficients
`conj(σ(a_n(f)))`, so it is the conjugate `f^{c ∘ σ}`. -/
theorem frickeStable_of_li (hL : LiFrickePrinted) (hC : ConjNewform) {N : ℕ} (hN : 0 < N)
    {χ : DirichletCharacter ℂ N} {f : CF N 2} (hf : IsNewform f χ) : FrickeStable N hN f := by
  intro g hg
  obtain ⟨χ', hg'⟩ := hC N χ f g hN hf hg
  obtain ⟨σ, hσ⟩ := hg
  obtain ⟨lam, h, hcoeff, heq⟩ := hL N hN χ' g hg'
  rw [heq]
  refine Submodule.smul_mem _ lam (Submodule.subset_span ⟨h, ⟨(starRingEnd ℂ).comp σ, fun n => ?_⟩, rfl⟩)
  rw [hcoeff n, hσ n]
  rfl

/-- **`R16CoreYTotal` from the two cited theorems** and `ConjNewform` (glue, proved). -/
theorem r16CoreYTotal_of_shimura_li (hS : ShimuraThm1Printed) (hL : LiFrickePrinted) (hC : ConjNewform) :
    R16CoreYTotal := by
  intro N χ f J hN hf hJ
  obtain ⟨hfin, A, π, θ, hs, hdim, hE⟩ := hS N χ f J hN hf hJ
  exact ⟨hfin, A, π, θ, hs, hdim, hE (frickeStable_of_li hL hC hN hf)⟩

/-- **`r16CoreY` from `R16CoreYTotal` and the known-issue statement** (composition). -/
theorem r16CoreY_of_total (hT : R16CoreYTotal) (hG : ShimuraTotalToComponents) : R16Split.R16CoreY := by
  intro N χ f J hN hf hJ
  obtain ⟨hfin, A, π, θ, hs, hdim, hE⟩ := hT N χ f J hN hf hJ
  obtain ⟨θ', hθ'⟩ := hG N χ f J hN hf hJ hfin A π θ hs hdim hE
  exact ⟨hfin, A, π, θ', hs, hdim, hθ'⟩

/-- **`r16CoreY` along the manuscript's sources**: Li's Fricke formula, Shimura 1973 Thm 1, the uncited step
`ConjNewform`, and the known-issue statement `ShimuraTotalToComponents`. -/
theorem r16CoreY_of_shimura_li (hS : ShimuraThm1Printed) (hL : LiFrickePrinted) (hC : ConjNewform)
    (hG : ShimuraTotalToComponents) : R16Split.R16CoreY :=
  r16CoreY_of_total (r16CoreYTotal_of_shimura_li hS hL hC) hG

end R16ShimuraLi

end
