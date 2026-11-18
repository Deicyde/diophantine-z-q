import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Inflation
import ZInQKernel.Contrib.TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic

/-!
# `kummer`: the statements of the stages

Manuscript `diophantine_zq.tex`, tex 4482–4492: "Kummer theory gives the exact sequence
`0 → 𝒪_{K,S_T}^×/(𝒪_{K,S_T}^×)² → H¹(G_{K,S_T}, 𝔽₂) → Cl(𝒪_{K,S_T})[2] → 0` … The unit term has
dimension `1 + |S_T|`." RC6's field `kummer` records the resulting dimension count. Stages:

* `SelmerCount` (count): for an imaginary quadratic field and a finite `S`, the Selmer group
  `K(S,2) ⊆ K^×/K^{×2}` (Mathlib's `IsDedekindDomain.selmerGroup`) has `2^{1 + |S| + rk₂ Cl_S}`
  elements (Tau Ceti's exact sequence `1 → 𝒪_S^×/2 → K(S,2) → Cl_S[2] → 1` and the `S`-unit rank);
* `SqrtMemOfSelmer` (`⊇`): if `a ∈ K(S,2)` and `S` contains the primes above `2`, then `√a ∈ K_S`;
* `SelmerOfSqrtMem` (`⊆`): if `√a ∈ K_S` then `a ∈ K(S,2)`.

Here `K_S = unramifiedOutside K S` (`GlobalPrints`), the square root taken in `AlgebraicClosure K`.
Kinds: definitions only.
-/

noncomputable section

open NumberField IsDedekindDomain

namespace ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS

/-- The class of `a` in `K^×/K^{×2}`. -/
abbrev sqClass {K : Type} [Field K] (a : Kˣ) : Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range :=
  QuotientGroup.mk a

/-- **Count**: `|K(S,2)| = 2^{1 + |S| + rk₂ Cl(𝒪_{K,S})}` for imaginary quadratic `K`, finite `S`. -/
def SelmerCount : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite →
      Nat.card (IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := S) (n := 2)) =
        2 ^ (1 + S.ncard + TauCeti.twoRank (ClassGroup (S.integer K)))

/-- **`⊇`**: a square root of a Selmer class lies in `K_S` (`S` containing the primes above `2`). -/
def SqrtMemOfSelmer : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))),
    (∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ (a : Kˣ) (x : AlgebraicClosure K), x ^ 2 = algebraMap K _ a →
      sqClass a ∈ IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := S) (n := 2) →
      x ∈ unramifiedOutside K S

/-- **`⊆`**: if a square root of `a` lies in `K_S`, then `a` is a Selmer class. -/
def SelmerOfSqrtMem : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))),
    ∀ (a : Kˣ) (x : AlgebraicClosure K), x ^ 2 = algebraMap K _ a →
      x ∈ unramifiedOutside K S →
      sqClass a ∈ IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := S) (n := 2)

end ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS
