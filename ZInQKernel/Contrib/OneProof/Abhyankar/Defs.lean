import ZInQKernel.Contrib.OneProof.SGRDirectNVLocal

/-!
# abhyankar: the named steps of `TameBranchNormal`

`SGRDirect.NVLocal.TameBranchNormal` (nv-local) is proved from the following Props (all of them proved in the
other files of `Abhyankar/`), each a step of the proof of the dimension-two case of Abhyankar's lemma (SGA 1 XIII 5.2–5.3; Grothendieck–Murre, LNM 208, §2.3;
locators UNVERIFIED):

* `TBNLocal` — the statement over the local ring `A = R_m` (`tameBranchNormal_of_local`);
* `KummerBase` — `A[t, u]`, `t^a = f`, `u^b = g`, is regular local of dimension 2 with maximal ideal `(t, u)`;
* `KummerUnram` — the integral closure of `A[t, u]` in `Ω = L(t, u)`, `a = b = [L : K]`, is finite over
  `A[t, u]` and unramified at its height-one primes (Abhyankar's lemma for DVRs, `t2_proved`, at `(t)` and
  `(u)`; base change elsewhere);
* `EtaleBranch` — over a two-dimensional regular local ring with maximal ideal `(t, u)`, a finite étale domain
  has, at each maximal ideal, a unique branch of `t = 0`, and it is normal (`S'/tS'` is étale over the DVR
  `B/t`);
* `BranchDescent` — unique normal branches descend along `S ⊆ S'` (going down; trace as Reynolds operator,
  `[Ω : L]` invertible).
-/

open IsLocalRing HDec

set_option linter.all false

noncomputable section

namespace Abhyankar

/-- The conclusion of `TameBranchNormal` for a ring `S`, a maximal ideal `𝔓`, a prime `Q ≤ 𝔓` over `𝔮`. -/
def BranchConcl {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (𝔮 : Ideal A) (𝔓 Q : Ideal S) : Prop :=
  (∀ Q' : Ideal S, Q'.IsPrime → Q'.under A = 𝔮 → Q' ≤ 𝔓 → Q' = Q) ∧
  (∀ (F : Type) [CommRing F] [Algebra (S ⧸ Q) F] [IsFractionRing (S ⧸ Q) F] (z : F),
    IsIntegral (S ⧸ Q) z →
    ∃ a s : S, s ∉ 𝔓 ∧ algebraMap _ F (Ideal.Quotient.mk Q s) * z = algebraMap _ F (Ideal.Quotient.mk Q a))

/-- **GLUE (step 0: `TameBranchNormal` over the local ring).** `TameBranchNormal` with `R = A` a regular local
ring of dimension 2 and `m` its maximal ideal; `S` is the integral closure of `A` in `L`. -/
def TBNLocal : Prop :=
  ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L], ringKrullDim A = 2 →
    ∀ f g : A, maximalIdeal A = Ideal.span {f, g} → (Ideal.span {f}).IsPrime →
    ∀ p : ℕ, p.Prime → (p : A) ∈ maximalIdeal A → Module.finrank K L < p →
    (∀ P : Ideal A, P.IsPrime → P.height = 1 → f ∉ P → g ∉ P →
      ∀ P' : Ideal (integralClosure A L), P'.IsPrime → P'.under A = P →
        P'.ramificationIdx A = 1) →
    ∀ 𝔓 : Ideal (integralClosure A L), 𝔓.IsMaximal →
    ∀ Q : Ideal (integralClosure A L), Q.IsPrime → Q.under A = Ideal.span {f} → Q ≤ 𝔓 →
      BranchConcl (Ideal.span {f}) 𝔓 Q

/-- **GLUE (step 1: the Kummer base).** If `A` is a regular local ring of dimension 2 with maximal ideal
`(f, g)` inside a field `Ω`, and `t^a = f`, `u^b = g` in `Ω` (`a, b > 0`), then `A[t, u] ⊆ Ω` is a regular local
ring of dimension 2 with maximal ideal `(t, u)` (it is finite over `A` and `(t, u) ⊇ (f, g)`). -/
def KummerBase : Prop :=
  ∀ (A Ω : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field Ω] [Algebra A Ω],
    Function.Injective (algebraMap A Ω) → ringKrullDim A = 2 →
    ∀ f g : A, maximalIdeal A = Ideal.span {f, g} →
    ∀ a b : ℕ, 0 < a → 0 < b → ∀ t u : Ω, t ^ a = algebraMap A Ω f → u ^ b = algebraMap A Ω g →
      IsRegularLocalRing (Algebra.adjoin A {t, u}) ∧ ringKrullDim (Algebra.adjoin A {t, u}) = 2 ∧
      (Ideal.span {(⟨t, Algebra.subset_adjoin (by simp)⟩ : Algebra.adjoin A {t, u}),
        ⟨u, Algebra.subset_adjoin (by simp)⟩}).IsMaximal

/-- **GLUE (step 2: unramified in codimension one after the Kummer base change).** In the setting of
`TameBranchNormal` over a local `A`, with `N = [L : K]`, `Ω ⊇ L` finite with `t^N = f`, `u^N = g`,
`Ω = L(t, u)`: the integral closure `S'` of `A[t, u]` in `Ω` is finite over `A[t, u]` and unramified at every
height-one prime. At primes over `(t)` and `(u)` this is Abhyankar's lemma for DVRs (SGA 1 X 3.6, UNVERIFIED;
the kernel's T2, proved as `HDec.HSyn.t2_proved`); at the others it is base change of the unramified
`L/K` (`TsKummer.unramBaseChange`). -/
def KummerUnram : Prop :=
  ∀ (A K L Ω : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field K] [Field L] [Field Ω]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra L Ω] [Algebra K Ω] [Algebra A Ω]
    [IsScalarTower A K Ω] [IsScalarTower K L Ω] [FiniteDimensional L Ω], ringKrullDim A = 2 →
    ∀ f g : A, maximalIdeal A = Ideal.span {f, g} → (Ideal.span {f}).IsPrime →
    ∀ p : ℕ, p.Prime → (p : A) ∈ maximalIdeal A → Module.finrank K L < p →
    (∀ P : Ideal A, P.IsPrime → P.height = 1 → f ∉ P → g ∉ P →
      ∀ P' : Ideal (integralClosure A L), P'.IsPrime → P'.under A = P →
        P'.ramificationIdx A = 1) →
    ∀ t u : Ω, t ^ Module.finrank K L = algebraMap A Ω f → u ^ Module.finrank K L = algebraMap A Ω g →
    IntermediateField.adjoin L {t, u} = ⊤ →
      Module.Finite (Algebra.adjoin A {t, u}) (integralClosure (Algebra.adjoin A {t, u}) Ω) ∧
      ∀ Q : Ideal (integralClosure (Algebra.adjoin A {t, u}) Ω), [Q.IsPrime] → Q.height = 1 →
        Algebra.IsUnramifiedAt (Algebra.adjoin A {t, u}) Q

/-- **GLUE (step 3: branches of a finite étale cover of a regular surface germ).** `B` regular local of
dimension 2 with maximal ideal `(t, u)`, `S'` a finite étale `B`-algebra which is a domain. At a maximal
ideal `𝔓'` of `S'` all primes `Q' ⊊ 𝔓'` containing `t` coincide, and `(S'/Q')_{𝔓'}` is integrally closed:
`S'_{𝔓'}` is regular local of dimension `≤ 2` with maximal ideal `(t, u)`, so `S'_{𝔓'}/t` is a DVR. -/
def EtaleBranch : Prop :=
  ∀ (B S' : Type) [CommRing B] [IsDomain B] [IsRegularLocalRing B] [CommRing S'] [IsDomain S']
    [Algebra B S'], ringKrullDim B = 2 → ∀ t u : B, maximalIdeal B = Ideal.span {t, u} → t ≠ 0 →
    Algebra.Etale B S' → Module.Finite B S' → Function.Injective (algebraMap B S') →
    ∀ 𝔓' : Ideal S', 𝔓'.IsMaximal →
    ∀ Q' : Ideal S', Q'.IsPrime → algebraMap B S' t ∈ Q' → Q' ≤ 𝔓' → Q' ≠ 𝔓' →
      (∀ Q'' : Ideal S', Q''.IsPrime → algebraMap B S' t ∈ Q'' → Q'' ≤ 𝔓' → Q'' ≠ 𝔓' → Q'' = Q') ∧
      (∀ (F : Type) [CommRing F] [Algebra (S' ⧸ Q') F] [IsFractionRing (S' ⧸ Q') F] (z : F),
        IsIntegral (S' ⧸ Q') z →
        ∃ a s : S', s ∉ 𝔓' ∧
          algebraMap _ F (Ideal.Quotient.mk Q' s) * z = algebraMap _ F (Ideal.Quotient.mk Q' a))

/-- **GLUE (step 4: descent of unique normal branches).** `A` integrally closed, `L/K` and `Ω/L` finite
separable, `A'' ⊆ Ω` integral over `A`, `S = A^L ⊆ S' = (A'')^Ω`, `S'` noetherian. If at every maximal
ideal of `S'` the primes over `𝔮` form a unique normal branch, the same holds at a maximal `𝔓` of `S` with
`[Ω : L] ∉ 𝔓`. Proof: going down for `S ⊆ S'` gives uniqueness; for normality, the trace `Tr_{Ω/L}` is an
`S`-linear map `S' → S` sending the radical of `QS'` into `Q` (trace as the sum of the conjugates), so it
is a Reynolds operator for `S/Q ⊆ S'/√(QS')`. -/
def BranchDescent : Prop :=
  ∀ (A K L Ω : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L] [Field Ω]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Algebra L Ω] [Algebra K Ω] [Algebra A Ω]
    [IsScalarTower A K Ω] [IsScalarTower K L Ω] [FiniteDimensional L Ω] [Algebra.IsSeparable L Ω]
    (A'' : Subalgebra A Ω), Algebra.IsIntegral A A'' → IsNoetherianRing (integralClosure A'' Ω) →
    ∀ 𝔮 : Ideal A, 𝔮.IsPrime →
    (∀ 𝔓' : Ideal (integralClosure A'' Ω), 𝔓'.IsMaximal →
      ∀ Q' : Ideal (integralClosure A'' Ω), Q'.IsPrime → Q'.under A = 𝔮 → Q' ≤ 𝔓' →
        BranchConcl 𝔮 𝔓' Q') →
    ∀ 𝔓 : Ideal (integralClosure A L), 𝔓.IsMaximal →
    ∀ Q : Ideal (integralClosure A L), Q.IsPrime → Q.under A = 𝔮 → Q ≤ 𝔓 →
      ((Module.finrank L Ω : ℕ) : integralClosure A L) ∉ 𝔓 → BranchConcl 𝔮 𝔓 Q

end Abhyankar
