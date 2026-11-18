import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.SupportChange
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Inflation
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.LocalConditions

/-!
# Lane RC26: the genuine Galois groups — `G_{K,S}`, `G_{K_v}`, localization and inflation

Manuscript `diophantine_zq.tex`, (4.3) at tex 3455–3463 and the support comparisons at tex
3480–3496; Nekovář, *Selmer complexes*, 5.1 (p. 113): `G_{K,S} = Gal(K_S/K)`, and for every
`v ∈ S` an embedding `K^sep ↪ K_v^sep` is fixed, giving `p_v : G_v → G_{K,S}`.

The genuine objects already in the tree are used:
* `GaloisGroupS K S = Gal(K_S/K)` (`K_S` the maximal extension of `K` unramified outside `S`
  inside `AlgebraicClosure K`), the restriction `resAbs`, and `resUnrCont K h : G_{K,S'} → G_{K,S}`
  for `S ⊆ S'` (`CloudB3RC53/RankCounts/GlobalPrints.lean`, `Inflation.lean`);
* `Field.absoluteGaloisGroup (v.adicCompletion K)` (Mathlib) for `G_{K_v}`, with Mathlib's
  continuous `Field.absoluteGaloisGroup.map` along `K → K_v` (an embedding of algebraic closures
  is chosen, as in Nekovář 5.1);
* `GUr K w = Gal(K_w^{ur}/K_w)` (Tau Ceti's maximal unramified extension inside
  `AlgebraicClosure K_w`, `RankCounts/LocalConditions.lean`).

Definitions (genuine): `resAbsCont`, `decompMap`, `locMap K S v : G_{K_v} → G_{K,S}` (Nekovář's
`p_v`), `urRes K q : G_{K_q} → Gal(K_q^{ur}/K_q)`; `galoisSelData` — the genuine Selmer data of
(4.3) for a finite set `S` of finite primes, a coefficient ring `k` and a topological
`k[G_{K,S}]`-module `M`; `galoisSupportData` — the genuine support change from `S` to `S' ⊇ S`
with unramified conditions at `S' − S`.

PROVED: `locMap_compat` (`infl ∘ p'_v = p_v`, the localization maps for `S'` and `S` are
compatible with the restriction `G_{K,S'} → G_{K,S}`).

GLUE (standard fact, not proved here): `UnramifiedAtFactorization K S` — for `q ∉ S` the
localization `G_{K_q} → G_{K,S}` factors through `Gal(K_q^{ur}/K_q)` (`K_S/K` is unramified at
`q`). The genuine support data take such a factorization as input.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open NumberField IsDedekindDomain CategoryTheory ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable (K : Type) [Field K] [NumberField K]

/-- **`G_{K,S}`**, the tree's `GaloisGroupS K S = Gal(K_S/K)` (Krull topology), as a type synonym
whose group and topology instances are frozen (so that instance unification does not unfold the
Galois group structure of `K_S`). -/
def GKS (S : Set (HeightOneSpectrum (𝓞 K))) : Type := GaloisGroupS K S

instance (S : Set (HeightOneSpectrum (𝓞 K))) : Group (GKS K S) :=
  inferInstanceAs (Group (GaloisGroupS K S))

instance (S : Set (HeightOneSpectrum (𝓞 K))) : TopologicalSpace (GKS K S) :=
  inferInstanceAs (TopologicalSpace (GaloisGroupS K S))

instance (S : Set (HeightOneSpectrum (𝓞 K))) : IsTopologicalGroup (GKS K S) :=
  inferInstanceAs (IsTopologicalGroup (GaloisGroupS K S))

/-- The restriction `Gal(K̄/K) → G_{K,S} = Gal(K_S/K)` as a continuous homomorphism. -/
def resAbsCont (S : Set (HeightOneSpectrum (𝓞 K))) :
    Field.absoluteGaloisGroup K →ₜ* GKS K S :=
  { resAbs K S with
    continuous_toFun := InfiniteGalois.restrictNormalHom_continuous (unramifiedOutside K S) }

/-- The decomposition map `G_{K_v} → G_K` along `K → K_v` (Mathlib's
`Field.absoluteGaloisGroup.map`, for a chosen embedding of algebraic closures). -/
abbrev decompMap (v : HeightOneSpectrum (𝓞 K)) :
    Field.absoluteGaloisGroup (v.adicCompletion K) →ₜ* Field.absoluteGaloisGroup K :=
  Field.absoluteGaloisGroup.map (algebraMap K (v.adicCompletion K))

/-- **The localization map** `p_v : G_{K_v} → G_{K,S}` (Nekovář 5.1, p. 113): the decomposition
map followed by restriction to `K_S`. -/
def locMap (S : Set (HeightOneSpectrum (𝓞 K))) (v : HeightOneSpectrum (𝓞 K)) :
    Field.absoluteGaloisGroup (v.adicCompletion K) →ₜ* GKS K S :=
  (resAbsCont K S).comp (decompMap K v)

/-- The restriction `G_{K,S'} → G_{K,S}` for `S ⊆ S'` (the tree's `resUnrCont`). -/
def inflMap {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') : GKS K S' →ₜ* GKS K S :=
  resUnrCont K h

/-- **The localization maps are compatible with the restriction `G_{K,S'} → G_{K,S}`** for
`S ⊆ S'`: `infl ∘ p'_v = p_v`. PROVED (`resUnr_comp`). -/
theorem locMap_compat {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S')
    (v : HeightOneSpectrum (𝓞 K)) (g : Field.absoluteGaloisGroup (v.adicCompletion K)) :
    inflMap K h (locMap K S' v g) = locMap K S v g :=
  resUnr_comp K h (decompMap K v g)

/-- The restriction `G_{K_q} → Gal(K_q^{ur}/K_q)` onto the unramified quotient `G_q/I_q`. -/
def urRes (q : HeightOneSpectrum (𝓞 K)) :
    Field.absoluteGaloisGroup (q.adicCompletion K) →ₜ* GUr K q :=
  { AlgEquiv.restrictNormalHom (TauCeti.maximalUnramifiedExtension (q.adicCompletion K)
      (AlgebraicClosure (q.adicCompletion K))) with
    continuous_toFun := InfiniteGalois.restrictNormalHom_continuous _ }

/-- **GLUE (standard): `K_S/K` is unramified at every `q ∉ S`**, in local Galois terms: the
localization `p_q : G_{K_q} → G_{K,S}` factors through the unramified quotient
`Gal(K_q^{ur}/K_q)` (the inertia group `I_q` acts trivially on `K_S`). Not proved here (it relates
the global definition of `K_S` through ramification indices to the local inertia groups). -/
def UnramifiedAtFactorization (S : Set (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ q : HeightOneSpectrum (𝓞 K), q ∉ S →
    ∃ ψ : GUr K q →ₜ* GKS K S, ∀ g, locMap K S q g = ψ (urRes K q g)

/-- The places of a set `S` of finite primes, as an index type (the elements of `S`). -/
abbrev Places (S : Set (HeightOneSpectrum (𝓞 K))) : Type := ↥S

/-- The local Galois group `G_{K_v}`. -/
abbrev Gloc (v : HeightOneSpectrum (𝓞 K)) : Type := Field.absoluteGaloisGroup (v.adicCompletion K)

section Genuine

variable (S : Set (HeightOneSpectrum (𝓞 K))) (k : Type) [CommRing k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- Local conditions for the genuine Galois data at the places of `S`. -/
abbrev GaloisLocalConditions : Type 1 :=
  LocalConditions k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M

/-- **The genuine Selmer data of (4.3)** (Nekovář 6.1.2), for a (finite, in the applications) set
`S` of finite primes:
`C^•_cont(G_{K,S}, M) --res_S--> ∏_{v ∈ S} C^•_cont(G_{K_v}, M) <--i_S-- ∏_{v ∈ S} U_v`. Its Selmer
complex `selCx (galoisSelData K S k M Δ)` is
`C_U = Cone(RΓ(G_{K,S}, M) ⊕ ⊕_{v∈S} U_v → ⊕_{v∈S} RΓ(K_v, M))[−1]` (for finite `S` the product
is the direct sum). -/
def galoisSelData (Δ : GaloisLocalConditions K S k M) : SelData k :=
  selData k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) M Δ

/-- Non-vacuity: the genuine Selmer data exist for every `M` (strict conditions). -/
example : SelData k :=
  galoisSelData K S k M (strictConditions k _ _ _ M)

end Genuine

section GenuineSupport

variable {S S' : Set (HeightOneSpectrum (𝓞 K))} (hS : S ⊆ S') (k : Type) [CommRing k]
  (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M] [ContinuousAdd M]
  [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]

/-- The new places `S' − S`. -/
abbrev NewPlaces (S S' : Set (HeightOneSpectrum (𝓞 K))) : Type := ↥(S' \ S)

/-- **The genuine support change** (Nekovář 7.8.8(ii), tex 3470–3499) from `S` to `S' ⊇ S`:
inflation `C^•_cont(G_{K,S}, M) → C^•_cont(G_{K,S'}, M)` along `G_{K,S'} → G_{K,S}`, the old
local conditions at `v ∈ S` and the unramified conditions
`C^•_cont(Gal(K_q^{ur}/K_q), M) → C^•_cont(G_{K_q}, M)` at `q ∈ S' − S`, for factorizations
`ψ_q` of the localization through the unramified quotient (`UnramifiedAtFactorization`). An
instance of the abstract `SupportChangeData`. -/
def galoisSupportData (ψ : ∀ q : NewPlaces K S S', GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ (q : NewPlaces K S S') g, locMap K S q.1 g = ψ q (urRes K q.1 g))
    (Δ : GaloisLocalConditions K S k M) : SupportChangeData k :=
  supportData k (GKS K S) (GKS K S') (inflMap K hS) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (fun v => locMap K S' v.1) (fun q : NewPlaces K S S' => Gloc K q.1)
    (fun q => locMap K S' q.1) (fun q : NewPlaces K S S' => GUr K q.1) (fun q => urRes K q.1) ψ M
    (fun v g => locMap_compat K hS v.1 g)
    (fun q g => (locMap_compat K hS q.1 g).trans (hψ q g)) Δ

/-- Non-vacuity of the hypotheses of `galoisSupportData`: for `S' = S` there are no new places,
so the factorization hypothesis is empty. PROVED. -/
example (Δ : GaloisLocalConditions K S k M) : SupportChangeData k :=
  galoisSupportData K (subset_refl S) k M (fun q => absurd q.2.1 q.2.2)
    (fun q => absurd q.2.1 q.2.2) Δ

end GenuineSupport

end ZInQ.Manuscript.RC.SelmerComplex
