import ZInQKernel.Contrib.OneProof.R16ShimuraLi
import ZInQKernel.Contrib.OneProof.R16CoreYDS965

/-! # r16-thm1: Shimura 1973 Theorem 1 as read, in place of the Diamond–Shurman rows `afShimura`, `heckeJ1DS`

Task r16-thm1 (round 2 of r16-shimura73, 2026-11-17), report `docs/research/r16-thm1.md`, scratch
`scratch/r16-thm1/`.

Input: an AI page read of Shimura 1973 Theorem 1 (counts as a reading under the owner's ruling; cited as
"AI page read"). Theorem 1 prints, unconditionally, (i) a `ℚ`-rational quotient `ν : J ↠ A` of `J`, (ii) `θ : K_f →
End(A) ⊗ ℚ` with `ν ∘ ξ_n = θ(a_n) ∘ ν`, (iii) `dim A = [K_f : ℚ]`, (iv) the cotangent space is spanned by the
`f_σ`, and uniqueness; and, under the proviso "`Γ = Γ₀(N)`, or `span{f_σ}` stable under `h(z) ↦ h(−1/Nz)/z²`", the
total Euler-factor clause (a product over all embeddings). The curve is Shimura's standard model (Shimura 1971
§7.3, not cited in 1973).

This file:
* `ShimuraThm1Printed` (LEAF, printed form at `Γ = Γ₁(N)`, `n` prime and `n = p²`): (i)–(iii) and the Euler
  clause with the Fricke proviso; (iv) and uniqueness are dropped (weakenings, unused).
* `BShStandardModel` (ON THE SPOT): Shimura's standard model with `ξ_p` and `⟨d⟩` is the kernel's `IsX1Gen` model
  with `IsHeckeT`, `IsDiamond` operators over `ℚ`. Its Lean content is the existence of those operators,
  which is the statement of `AfTateLam.HeckeJ1DS`: `heckeJ1DS_of_bSh`.
* `ShimuraQuotientIsAf` (GLUE): Shimura's quotient is Diamond–Shurman's `J/I_f J` (kills `I_f J`, universal).
  Not in the print as read; proof sketch ON THE SPOT in its docstring.
* `afShimura_of_shimura73` (proved): `AfTateLam.AfShimura` from the leaf and the glue. The action clause
  `IsAfAction` is derived in Lean from (ii): `T_p` directly, `⟨d⟩` from `ξ_{p²} = T_p² − p⟨p⟩` at a prime
  `p ≡ d (mod N)` (Dirichlet's theorem, Mathlib) and `a_p² − a_{p²} = χ(p) p`.
* `euler_of_shimura73_li` (proved): Li's Fricke formula (with `ConjNewform`) supplies the proviso, so the total
  Euler identity holds for the leaf's `A`. It does not give the per-embedding characteristic polynomial
  (round 1, Known issue 1): `afCharpolyDS965` stays.

No `sorry`, no `axiom`. -/

noncomputable section

namespace R16Thm1

open scoped TensorProduct MatrixGroups ModularForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (Qbar GQ CF coeff IsNewform IsNormalizedEigenform)
open AfTateLam (IsX1Gen IsHeckeT IsDiamond HeckeFree evF heckeJ KillsIf IsAfQuotient IsAfAction)
open R16ShimuraLi (FrickeStable EulerIdentity LiFrickePrinted ConjNewform)

/-! ## 1. Definitions -/

/-- The composite `f ≫ g` of homomorphisms of abelian varieties. -/
def comp {A B C : AbVar ℚ} (f : AbVar.Hom A B) (g : AbVar.Hom B C) : AbVar.Hom A C :=
  Hom.mk' (f.hom ≫ g.hom)

@[simp] theorem comp_hom {A B C : AbVar ℚ} (f : AbVar.Hom A B) (g : AbVar.Hom B C) :
    (comp f g).hom = f.hom ≫ g.hom := rfl

/-- **`ν ∘ t = x ∘ ν` in `Hom(J, A) ⊗ ℚ`** for `x ∈ End(A) ⊗ ℚ`, in integral form: for some `m > 0` and
`e ∈ End(A)` with `m x = 1 ⊗ e`, `m (ν ∘ t) = e ∘ ν` in `Hom(J, A)`. (Equivalent to the equation in
`Hom⁰(J, A)`, since `Hom(J, A)` is torsion-free; the integral form is the weaker one.) -/
def HeckeCompat {J A : AbVar ℚ} (ν : AbVar.Hom J A) (t : AbVar.End J) (x : A.End0) : Prop :=
  ∃ (m : ℕ) (e : AbVar.End A), 0 < m ∧ m • x = (1 : ℚ) ⊗ₜ e ∧ m • comp t ν = comp ν e

/-- **`ker ν` is connected** (`A = J/B` for an abelian subvariety `B`): `ν` admits no factorization
`J ↠ B → A` through an isogeny `B → A` other than an isomorphism. (`J/(ker ν)⁰ → J/ker ν` is an isogeny of
degree `[ker ν : (ker ν)⁰]`.) -/
def KerConnected {J A : AbVar ℚ} (ν : AbVar.Hom J A) : Prop :=
  ∀ (B : AbVar ℚ) (φ : AbVar.Hom J B) (ψ : AbVar.Hom B A), Surjective φ.hom.left →
    IsIsogenyMor ψ.hom → φ.hom ≫ ψ.hom = ν.hom → IsIso ψ.hom

/-- The class of a prime `p ∤ N` in `(ℤ/N)ˣ`. -/
def unitOf (N : ℕ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) : (ZMod N)ˣ :=
  ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)

/-- Shimura's `ξ_{p²}` for `p ∤ N` in terms of `T_p` and `⟨p⟩`: `T_p² − p ⟨p⟩` (the Hecke relation
`T(p)² = T(p²) + p T(p, p)`: a theorem step, not a definition; flagged on the round-3 row
`R16Thm1b.ShimuraThm1Af`). -/
def xiSq {N : ℕ} {J : AbVar ℚ} (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J)
    (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N) : AbVar.End J :=
  tp p * tp p - ((p : ℕ) : AbVar.End J) * δ (unitOf N p.2 hpN)

/-- Clauses (i)–(iii) of Shimura 1973 Thm 1 for `(A, ν, θ)` (with `ξ_n` at `n = p` and `n = p²`, `p ∤ N`). -/
def ShimuraClauses {N : ℕ} (f : CF N 2) {J : AbVar ℚ} (tp : Nat.Primes → AbVar.End J)
    (δ : (ZMod N)ˣ → AbVar.End J) (A : AbVar ℚ) (ν : AbVar.Hom J A) (θ : coeffField f →+* A.End0) :
    Prop :=
  (Surjective ν.hom.left ∧ KerConnected ν) ∧
  ((∀ p : Nat.Primes, HeckeCompat ν (tp p) (θ ⟨coeff f p, coeff_mem_coeffField f p⟩)) ∧
    (∀ (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N),
      HeckeCompat ν (xiSq tp δ p hpN) (θ ⟨coeff f ((p : ℕ) * p), coeff_mem_coeffField f _⟩))) ∧
  A.dim = ((Module.finrank ℚ (coeffField f) : ℕ) : WithBot ℕ∞)

/-! ## 2. The leaf, the bridge, the glue -/

/-- **LEAF (Shimura 1973, Theorem 1), printed form, as read.** G. Shimura, *On the factors of the jacobian
variety of a modular function field*, J. Math. Soc. Japan 25 (1973), 523–544, Theorem 1 (AI page read;
pp. 526–527 per the locator audit). At `Γ = Γ₁(N)`, for a newform `f ∈ S₂(Γ₁(N))` with nebentypus `χ`, the
model `X` of `X₁(N)` with its Jacobian `J` and the Hecke operators `T_p = ξ_p`, `⟨d⟩` (transported from Shimura's
standard model by `BShStandardModel`): `K_f` is finite over `ℚ`, and there are `A` over `ℚ`, `ν : J → A`, `θ :
K_f → End⁰(A)` with
(i) `ν` surjective, `A` a quotient of `J` (`ker ν` connected);
(ii) `ν ∘ ξ_n = θ(a_n) ∘ ν` (`HeckeCompat`) at `n = p` prime and at `n = p²`, `p ∤ N`, with
     `ξ_{p²} = T_p² − p⟨p⟩` (`xiSq`; B-Sh);
(iii) `dim A = [K_f : ℚ]`;
and the Euler-factor clause, under its proviso in the Fricke branch: if `span{f_σ}` is stable under
`h ↦ h ∣₂ W_N` (`FrickeStable`), the zeta function of `A` is `∏_σ L(s, f_σ)` up to finitely many Euler factors
(`EulerIdentity`: total, a product over all embeddings `K_f → ℂ`).
Weakenings against the print (each makes the leaf a consequence): (ii) only at `n = p, p²`; (iv) (cotangent
space spanned by the `f_σ`) dropped: the kernel has no cotangent/q-expansion dictionary for `J₁(N)`, and no
consumer reads it; the uniqueness clause dropped (its exact wording is not in the read note); the proviso's
`Γ = Γ₀(N)` branch dropped (this instance is `Γ = Γ₁(N)`); the exceptional set of the Euler clause unspecified.
Reading-dependent: "quotient" rendered as `ker ν` connected (`KerConnected`), the reading under which the
printed uniqueness can hold (clauses (ii)–(iv) are invariant under composing `ν` with an isogeny). Misprint
(corrected in round 3, r16-thm1b): in the sentence on `f_σ` before (iv) on p. 526, "`f_σ | T_n = a_n^σ f`" for
"`f_σ | T_n = a_n^σ f_σ`" (not in the Euler clause); Known issues 1 of `docs/research/r16-thm1b.md`. Round 3
supersedes this row in the fold by `R16Thm1b.ShimuraThm1Af` (one row with `C = I_f J` and uniqueness). -/
def ShimuraThm1Printed : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (h2 : 2 ≤ N), IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
      FiniteDimensional ℚ (coeffField f) ∧
        ∃ (A : AbVar ℚ) (ν : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
          ShimuraClauses f tp δ A ν θ ∧
          (FrickeStable N (lt_of_lt_of_le two_pos h2) f → EulerIdentity N χ f A)

/-- **ON THE SPOT: the bridge B-Sh** (not printed in Shimura 1973, which defines its curve only by citing
Shimura 1971 §7.3, uncited by the manuscript). Shimura's standard model of `X₁(N)` over `ℚ`, with its
`ℚ`-rational Hecke correspondences `ξ_p` and diamond operators `⟨d⟩` acting on the Jacobian, is the kernel's
model: for every model `X` with `IsX1Gen` (function field `ℚ(j, f₁)` with the relations of `(j(τ), f₁(τ))`), a
rational point and Jacobian `J`, `ξ_p` and `⟨d⟩` induce endomorphisms of `J` over `ℚ` acting on the classes of
the points `x_τ` by the double-coset formulas `IsHeckeT`, `IsDiamond` (those pin them:
`AfTateLam.HeckePin.isHeckeT_unique`, `isDiamond_unique`). The Lean statement is the existence of such operators.
Sources the bridge would rest on: Shimura 1971 §7.2–7.3 (canonical model, rationality of `T(n)` over `ℚ`;
numbers UNVERIFIED, unread); its Lean form is the statement of `AfTateLam.HeckeJ1DS`. -/
def BShStandardModel : Prop :=
  ∀ (N : ℕ), 2 ≤ N → ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
      ∃ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
        (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) ∧
        (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d))

/-- **GLUE: Shimura's quotient is Diamond–Shurman's `J/I_f J`.** For `(A, ν, θ)` with Shimura's clauses
(i)–(iii), `ν` kills `I_f J` and every homomorphism killing `I_f J` factors uniquely through `ν`. Not a
statement of the print as read (the kernel's `AfCharpolyDS965` is phrased over DS's `J/I_f J`, the manuscript
uses Shimura's `A` directly). Proof sketch, ON THE SPOT, not formalized: (a) `ν` kills `I_f J`: by (ii),
`ν ∘ h = θ(evF h) ∘ ν` in `Hom⁰(J, A)` for `h` in the Hecke algebra (diamonds via `ξ_{p²}` and Dirichlet, as in
`isAfAction_of`), so `ν ∘ h = 0` if `evF h = 0` (`Hom(J, A)` torsion-free); (b) `I_f J ⊆ ker ν` are abelian
subvarieties (by (i)) of the same dimension: `dim J/I_f J ≤ [K_f : ℚ] = dim A` by multiplicity one (the
pulled-back cotangent space of `J/I_f J` lies in `S₂(Γ₁(N))[I_f] = span{f_σ}`, of dimension `[K_f : ℚ]`;
printed in Shimura 1973 itself, `m = 1` from `q`-expansions, p. 527, per the round-3 AI page read), so
`ker ν = I_f J`; (c) `J → J/B` is universal among
homomorphisms killing `B` (Mumford §7, Milne AV §8). -/
def ShimuraQuotientIsAf : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
    ∀ (A : AbVar ℚ) (ν : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
      ShimuraClauses f tp δ A ν θ →
      KillsIf χ f tp δ ν ∧
        ∀ (B : AbVar ℚ) (φ : AbVar.Hom J B), KillsIf χ f tp δ φ →
          ∃! ψ : AbVar.Hom A B, ν.hom ≫ ψ.hom = φ.hom

/-! ## 3. `heckeJ1DS` from B-Sh -/

/-- **`heckeJ1DS` from the bridge B-Sh** (same statement; the supplier changes from Diamond–Shurman §6.3/§7.9
to Shimura's standard model). -/
theorem heckeJ1DS_of_bSh (h : BShStandardModel) : AfTateLam.HeckeJ1DS := h

/-! ## 4. Glue lemmas on `Hom`, `End`, `End⁰` -/

section Glue

variable {J A : AbVar ℚ}

/-- `e ↦ e ∘ ν` is additive. -/
def postC (ν : AbVar.Hom J A) : AbVar.End A →+ AbVar.Hom J A where
  toFun e := comp ν e
  map_zero' := Hom.ext' (by simp)
  map_add' e e' := Hom.ext' (by simp [MonObj.comp_mul])

/-- `t ↦ ν ∘ t` is additive. -/
def preC (ν : AbVar.Hom J A) : AbVar.End J →+ AbVar.Hom J A where
  toFun t := comp t ν
  map_zero' := Hom.ext' (by simp)
  map_add' t t' := Hom.ext' (by simp [MonObj.mul_comp])

theorem comp_nsmul_right (ν : AbVar.Hom J A) (m : ℕ) (e : AbVar.End A) :
    comp ν (m • e) = m • comp ν e := map_nsmul (postC ν) m e

/-- `ν ∘ t = e ∘ ν`. -/
def Rel (ν : AbVar.Hom J A) (t : AbVar.End J) (e : AbVar.End A) : Prop := comp t ν = comp ν e

theorem rel_one (ν : AbVar.Hom J A) : Rel ν 1 1 := Hom.ext' (by
  change 𝟙 _ ≫ ν.hom = ν.hom ≫ 𝟙 _
  simp)

theorem rel_mul {ν : AbVar.Hom J A} {s t : AbVar.End J} {es et : AbVar.End A} (hs : Rel ν s es)
    (ht : Rel ν t et) : Rel ν (s * t) (es * et) := Hom.ext' (by
  have hs' := congrArg Hom.hom hs
  have ht' := congrArg Hom.hom ht
  simp only [comp_hom] at hs' ht'
  change (t.hom ≫ s.hom) ≫ ν.hom = ν.hom ≫ (et.hom ≫ es.hom)
  rw [Category.assoc, hs', ← Category.assoc, ht', Category.assoc])

theorem rel_sub {ν : AbVar.Hom J A} {s t : AbVar.End J} {es et : AbVar.End A} (hs : Rel ν s es)
    (ht : Rel ν t et) : Rel ν (s - t) (es - et) := by
  have h1 : comp (s - t) ν = comp s ν - comp t ν := map_sub (preC ν) s t
  have h2 : comp ν (es - et) = comp ν es - comp ν et := map_sub (postC ν) es et
  unfold Rel at *
  rw [h1, h2, hs, ht]

theorem rel_natCast (ν : AbVar.Hom J A) (n : ℕ) : Rel ν (n : AbVar.End J) (n : AbVar.End A) := by
  have h1 : comp (n : AbVar.End J) ν = n • comp 1 ν := by
    rw [← nsmul_one]; exact map_nsmul (preC ν) n 1
  have h2 : comp ν (n : AbVar.End A) = n • comp ν 1 := by
    rw [← nsmul_one]; exact map_nsmul (postC ν) n 1
  unfold Rel
  rw [h1, h2, show comp 1 ν = comp ν 1 from rel_one ν]

/-- Cancellation of a positive integer in `End⁰(A) = ℚ ⊗ End(A)`. -/
theorem nsmul_cancel {m : ℕ} (hm : 0 < m) {x y : A.End0} (h : m • x = m • y) : x = y := by
  have hq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h' : (m : ℚ) • x = (m : ℚ) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h]
  have := congrArg (fun z => (m : ℚ)⁻¹ • z) h'
  simpa [smul_smul, inv_mul_cancel₀ hq] using this

theorem tmul_nsmul' (m : ℕ) (e : AbVar.End A) :
    (1 : ℚ) ⊗ₜ[ℤ] (m • e) = m • ((1 : ℚ) ⊗ₜ[ℤ] e) :=
  map_nsmul (TensorProduct.mk ℤ ℚ (AbVar.End A) (1 : ℚ)) m e

end Glue

/-! ## 5. `IsAfQuotient` and `IsAfAction` from the clauses -/

section Action

variable {N : ℕ} {χ : DirichletCharacter ℂ N} {f : CF N 2} {J : AbVar ℚ}
  {tp : Nat.Primes → AbVar.End J} {δ : (ZMod N)ˣ → AbVar.End J} {A : AbVar ℚ} {ν : AbVar.Hom J A}

theorem killsIf_comp_heckeJ (hK : KillsIf χ f tp δ ν) (g : HeckeFree N) :
    KillsIf χ f tp δ (comp (heckeJ tp δ g) ν) := by
  intro h hh
  have := hK (g * h) (by rw [map_mul, hh, mul_zero])
  rw [map_mul] at this
  change ((heckeJ tp δ h).hom ≫ (heckeJ tp δ g).hom) ≫ ν.hom = _ at this
  rw [comp_hom, ← Category.assoc]
  exact this

theorem killsIf_comp_right (hK : KillsIf χ f tp δ ν) {B : AbVar ℚ} (e : AbVar.Hom A B) :
    KillsIf χ f tp δ (comp ν e) := by
  intro h hh
  have := hK h hh
  simp only [comp_hom, Hom.hom_zero] at this ⊢
  rw [← Category.assoc, this, MonObj.one_comp]

theorem hom_ext_of_isAfQuotient (hQ : IsAfQuotient χ f tp δ A ν) {B : AbVar ℚ} (e e' : AbVar.Hom A B)
    (h : comp ν e = comp ν e') : e = e' := by
  obtain ⟨-, hK, hU⟩ := hQ
  obtain ⟨ψ, -, hψ⟩ := hU B (comp ν e) (killsIf_comp_right hK e)
  exact (hψ e rfl).trans (hψ e' (by change ν.hom ≫ e'.hom = (comp ν e).hom; rw [h]; rfl)).symm

theorem exists_rel (hQ : IsAfQuotient χ f tp δ A ν) (g : HeckeFree N) :
    ∃ e : AbVar.End A, Rel ν (heckeJ tp δ g) e := by
  obtain ⟨e, he, -⟩ := hQ.2.2 A (comp (heckeJ tp δ g) ν) (killsIf_comp_heckeJ hQ.2.1 g)
  exact ⟨e, Hom.ext' he.symm⟩

theorem tp_eq (p : Nat.Primes) : tp p = heckeJ tp δ (FreeAlgebra.ι ℤ (Sum.inl p)) := by
  simp [heckeJ]

theorem δ_eq (d : (ZMod N)ˣ) : δ d = heckeJ tp δ (FreeAlgebra.ι ℤ (Sum.inr d)) := by
  simp [heckeJ]

/-- From `HeckeCompat` and an integral `Rel`, `x = 1 ⊗ e`. -/
theorem eq_tmul_of_compat (hQ : IsAfQuotient χ f tp δ A ν) {t : AbVar.End J} {e : AbVar.End A}
    {x : A.End0} (hR : Rel ν t e) (hC : HeckeCompat ν t x) : x = (1 : ℚ) ⊗ₜ e := by
  obtain ⟨m, e', hm, hx, hc⟩ := hC
  have hee : m • e = e' := hom_ext_of_isAfQuotient hQ _ _ (by
    rw [comp_nsmul_right, ← hR, hc])
  apply nsmul_cancel hm
  rw [hx, ← hee, tmul_nsmul']

/-- `a_p² − a_{p²} = χ(p) p` for a normalized eigenform of weight 2. -/
theorem coeff_sq_relation (hf : IsNormalizedEigenform f χ) {p : ℕ} (hp : p.Prime) :
    coeff f p * coeff f p - coeff f (p * p) = χ (p : ZMod N) * (p : ℂ) := by
  have key := hf.2.2 p p hp.pos hp.pos
  have e2 : p * p / p ^ 2 = 1 := by rw [← pow_two, Nat.div_self (pow_pos hp.pos 2)]
  rw [Nat.gcd_self, hp.divisors, Finset.sum_pair hp.one_lt.ne, one_pow, Nat.div_one, e2,
    hf.2.1] at key
  norm_num at key
  linear_combination key

/-- **`IsAfAction` from Shimura's clause (ii) and the universal property** (glue, proved). `T_p`: the
endomorphism `e_p` induced by `T_p` on `A` satisfies `θ(a_p) = 1 ⊗ e_p` by (ii) at `n = p`. `⟨d⟩`: take a prime
`p ≡ d (mod N)`, `p > N` (Dirichlet); (ii) at `n = p²` with `ξ_{p²} = T_p² − p⟨p⟩` gives
`θ(a_{p²}) = θ(a_p)² − p (1 ⊗ e_d)`, and `a_p² − a_{p²} = χ(p) p`, so `θ(χ(d)) = 1 ⊗ e_d`. -/
theorem isAfAction_of (h2 : 2 ≤ N) (hf : IsNormalizedEigenform f χ) (hQ : IsAfQuotient χ f tp δ A ν)
    {θ : coeffField f →+* A.End0}
    (hT : ∀ p : Nat.Primes, HeckeCompat ν (tp p) (θ ⟨coeff f p, coeff_mem_coeffField f p⟩))
    (hS : ∀ (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N),
      HeckeCompat ν (xiSq tp δ p hpN) (θ ⟨coeff f ((p : ℕ) * p), coeff_mem_coeffField f _⟩)) :
    IsAfAction χ f tp δ ν θ := by
  have hTp : ∀ p : Nat.Primes, ∃ e : AbVar.End A, Rel ν (tp p) e ∧
      θ ⟨coeff f p, coeff_mem_coeffField f p⟩ = (1 : ℚ) ⊗ₜ e := by
    intro p
    obtain ⟨e, he⟩ := exists_rel hQ (δ := δ) (FreeAlgebra.ι ℤ (Sum.inl p))
    rw [← tp_eq] at he
    exact ⟨e, he, eq_tmul_of_compat hQ he (hT p)⟩
  refine ⟨fun p => ?_, fun d => ?_⟩
  · obtain ⟨e, he, hθ⟩ := hTp p
    exact ⟨e, by simpa using congrArg Hom.hom he, hθ⟩
  · have : NeZero N := ⟨by omega⟩
    obtain ⟨p, hpN', hp, hpd⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := N) d.isUnit N
    have hpN : ¬ p ∣ N := fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      omega
    set P : Nat.Primes := ⟨p, hp⟩ with hP
    have hu : unitOf N P.2 hpN = d := Units.ext (by
      simp [unitOf, ZMod.coe_unitOfCoprime, hP, hpd])
    obtain ⟨ep, hep, hθp⟩ := hTp P
    obtain ⟨ed, hed⟩ := exists_rel hQ (tp := tp) (FreeAlgebra.ι ℤ (Sum.inr d))
    rw [← δ_eq] at hed
    have hR : Rel ν (xiSq tp δ P hpN) (ep * ep - (p : AbVar.End A) * ed) := by
      unfold xiSq
      rw [hu]
      exact rel_sub (rel_mul hep hep) (rel_mul (rel_natCast ν p) hed)
    have hθsq := eq_tmul_of_compat hQ hR (hS P hpN)
    -- the element `c = (a_p² − a_{p²})/p` of `K_f`, equal to `χ(d)`
    set ap : coeffField f := ⟨coeff f p, coeff_mem_coeffField f p⟩ with hap
    set app : coeffField f := ⟨coeff f (p * p), coeff_mem_coeffField f _⟩ with happ
    have hp0 : (p : coeffField f) ≠ 0 := by
      have : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
      intro h; apply this; exact_mod_cast congrArg Subtype.val h
    set c : coeffField f := (ap * ap - app) / (p : coeffField f) with hc
    have hpc : (p : coeffField f) * c = ap * ap - app := by
      rw [hc, mul_div_cancel₀ _ hp0]
    have hcv : (c : ℂ) = χ (d : ZMod N) := by
      have h1 : ((p : coeffField f) * c : ℂ) = ((ap * ap - app : coeffField f) : ℂ) :=
        congrArg Subtype.val hpc
      push_cast at h1
      rw [hap, happ] at h1
      simp only at h1
      rw [coeff_sq_relation hf hp, hpd] at h1
      have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
      apply mul_left_cancel₀ hpC
      rw [h1, mul_comm]
    have hθc : θ c = (1 : ℚ) ⊗ₜ ed := by
      have h1 := congrArg θ hpc
      rw [map_mul, map_sub, map_mul, map_natCast] at h1
      have hθp' : θ ap = (1 : ℚ) ⊗ₜ ep := hθp
      have hθsq' : θ app = (1 : ℚ) ⊗ₜ (ep * ep - (p : AbVar.End A) * ed) := hθsq
      rw [hθp', hθsq'] at h1
      have h3 : ((1 : ℚ) ⊗ₜ[ℤ] (ep * ep - (p : AbVar.End A) * ed) : A.End0) =
          (1 : ℚ) ⊗ₜ ep * (1 : ℚ) ⊗ₜ ep - (p : A.End0) * ((1 : ℚ) ⊗ₜ ed) := by
        have := map_sub (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := AbVar.End A))
          (ep * ep) ((p : AbVar.End A) * ed)
        simpa [Algebra.TensorProduct.includeRight_apply, map_mul, map_natCast] using this
      rw [h3, sub_sub_cancel] at h1
      apply nsmul_cancel hp.pos
      rw [nsmul_eq_mul, nsmul_eq_mul, h1]
    exact ⟨c, ed, hcv, by simpa using congrArg Hom.hom hed, hθc⟩

end Action

/-! ## 6. `afShimura` from Shimura 1973 Thm 1 -/

/-- **`afShimura` from Shimura 1973 Theorem 1 (as read) and the glue `ShimuraQuotientIsAf`.** -/
theorem afShimura_of_shimura73 (hS : ShimuraThm1Printed) (hG : ShimuraQuotientIsAf) :
    AfTateLam.AfShimura := by
  intro N χ f h2 hf X _ jX tX hC hX P₀ J aj hJ tp δ htp hδ
  obtain ⟨hfin, A, ν, θ, hcl, -⟩ := hS N χ f h2 hf X jX tX hC hX P₀ J aj hJ tp δ htp hδ
  obtain ⟨hK, hU⟩ := hG N χ f h2 hf X jX tX hC hX P₀ J aj hJ tp δ htp hδ A ν θ hcl
  have hQ : IsAfQuotient χ f tp δ A ν := ⟨hcl.1.1, hK, hU⟩
  exact ⟨hfin, A, ν, θ, hQ, isAfAction_of h2 hf.1 hQ hcl.2.1.1 hcl.2.1.2⟩

/-- **Li supplies the proviso** (with `ConjNewform`): the leaf's `A` satisfies the total Euler identity. This is
everything Li and Shimura 1973 Thm 1 give on Frobenius; it is a statement about the total characteristic
polynomial on `V_ℓ(A)` and does not see `θ` (round 1, Known issue 1), so `afCharpolyDS965` is not replaced. -/
theorem euler_of_shimura73_li (hS : ShimuraThm1Printed) (hL : LiFrickePrinted) (hC : ConjNewform) :
    ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (_ : 2 ≤ N), IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
      FiniteDimensional ℚ (coeffField f) ∧
        ∃ (A : AbVar ℚ) (ν : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
          ShimuraClauses f tp δ A ν θ ∧ EulerIdentity N χ f A := by
  intro N χ f h2 hf X _ jX tX hCv hX P₀ J aj hJ tp δ htp hδ
  obtain ⟨hfin, A, ν, θ, hcl, hE⟩ := hS N χ f h2 hf X jX tX hCv hX P₀ J aj hJ tp δ htp hδ
  exact ⟨hfin, A, ν, θ, hcl, hE (R16ShimuraLi.frickeStable_of_li hL hC _ hf)⟩

/-- **`r16CoreY` with the new suppliers**: B-Sh for `heckeJ1DS`, Shimura 1973 Thm 1 with the glue
`ShimuraQuotientIsAf` for `afShimura`; `afCharpolyDS965` (DS 9.6.5, flagged) and Diamond–Shurman 7.6.3 as before. -/
theorem r16CoreY_of_shimura73 (hB : BShStandardModel) (hS : ShimuraThm1Printed) (hG : ShimuraQuotientIsAf)
    (h3 : AfTateLam.AfCharpolyDS965) (hI : X1Igusa.IgusaGL2DS) (hM : AvSplit.MumfordTorsionAlgClosed) :
    R16Split.R16CoreY :=
  AfTateLam.r16CoreY_of_ds965 (heckeJ1DS_of_bSh hB) (afShimura_of_shimura73 hS hG) h3 hI hM

end R16Thm1

end
