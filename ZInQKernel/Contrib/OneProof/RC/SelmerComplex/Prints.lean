import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Galois
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.DualQuasiIso

/-!
# Lane RC26: Nekovář's duality and support-change theorems as PRINTs about genuine complexes

The Selmer-duality files state three inputs for *abstract* models (`SelData`, `SelPairData`,
`SupportChangeData`) and leave their identification with Galois cochains open:
`GlobalDualityInput`, `LocalOrthogonalityInput` (`SelmerDuality/Duality.lean`) and
`SupportChangeInput` (`SelmerDuality/SupportChange.lean`). With the genuine complexes of this
lane they become statements about the actual continuous cochains of `G_{K,S}`, `G_{K_v}`:

* `NekovarProp543` (PRINT; Nekovář, *Selmer complexes*, Astérisque 310, 2006, Proposition 5.4.3,
  p. 127, case (i) with `J = I[0] = R`): for the genuine data, the global duality map
  `C(G_{K,S}, M) → Hom_R(C_c(G_{K,S}, M'), R)[−3]` built from the genuine cup product `∪_c` and a
  global trace is a quasi-isomorphism. `globalDualityInput_of_print`: it *is*
  `GlobalDualityInput` for the genuine `SelPairData` (no identification left).
* `NekovarProp541` (PRINT; Nekovář 5.4.1, pp. 125–126, with 5.1.5): a global trace inducing
  `H³_c(G_{K,S}, R(1)) ≅ R` exists (non-vacuity of the trace hypothesis).
* `NekovarProp524` (PRINT; Nekovář 5.2.4, p. 116, case (i) with `J = R`): local duality for the
  genuine local complexes, `C(G_{K_v}, M) ≃ Hom_R(C(G_{K_v}, M'), R)[−2]` via the local cup
  product and a local trace inducing `H²(G_{K_v}, R(1)) ≅ R`.
* `OrthogonalComplements` (Nekovář 6.2.7, p. 140, "orthogonal complements with respect to π and
  h_v"): the definition, for genuine local conditions with isotropy homotopies;
  `localOrthogonalityInput_iff`: it *is* `LocalOrthogonalityInput` for the genuine data.
  `orthogonal_relaxed_strict` (PROVED): the full condition is orthogonal to the zero condition
  (tex 2813–2814: "A full condition is paired with the zero condition").
* `genuineSelmerDuality` (PROVED from `NekovarProp543` and `OrthogonalComplements`; this is
  Nekovář 6.3.4, p. 143, for the genuine complexes, by the cochain-level five lemma of
  `finiteSelmerDualityNode_proof`): `C_U(M) ≃ RHom_R(C_{U⊥}(M'), R)[−3]`, Lemma
  `ex:arith-conjugate-duality` (tex 2761–2830) and (4.3) for genuine complexes.
* `NekovarProp788ii` (PRINT; Nekovář 7.8.8(ii), pp. 186–187): the genuine support comparison
  `supportMap (galoisSupportData …)` is a quasi-isomorphism — the conclusion of
  `SupportChangeInput` for the genuine `SupportChangeData` (`supportChange_of_print`).

The PRINT hypotheses are Nekovář's (5.1, p. 113; 5.2.3/6.2.5 (A) with `J = R`): `K` a number
field, `p` a prime, `S` a finite set of finite primes containing those above `p` (the archimedean
places are implicit; under (P) they do not enter `C_c` or the Selmer complexes), condition (P):
`p = 2 → K` totally complex; `R` a finite local ring with nilpotent `p` (residue characteristic
`p`) which is self-injective (`R = I`, an injective hull of the residue field: `J = I[0]`);
finite discrete coefficient modules with continuous action (admissible, of finite type over `R`),
a perfect `G_{K,S}`-equivariant pairing `β : M × M' → T` with `T ≅ R(1)` (`IsCyclotomicTwist`).
Traces are quantified over all traces inducing an isomorphism on `H³_c` (resp. `H²` locally):
Nekovář's `r_S` is one of them, and any two differ, up to homotopy, by a unit of `R`
(Hom from a complex with `H^{>3} = 0` to the injective `R[−3]` is `Hom(H³, R)`), which does not
change quasi-isomorphy. Locators are those of the printed edition (read through the Numdam scan;
see the lane report for the reading notes).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.SelmerComplex

open NumberField IsDedekindDomain CategoryTheory ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable (K : Type) [Field K] [NumberField K]

/-- An element of `G_{K,S}` as an automorphism of `K_S`. -/
abbrev toGal {S : Set (HeightOneSpectrum (𝓞 K))} (g : GKS K S) : GaloisGroupS K S := g

/-- **`T ≅ R(1)`** as `R[G_{K,S}]`-modules: `T` is free of rank one over `R` and `G_{K,S}` acts
through the cyclotomic character modulo `N`, where `N > 0` kills `R` and `K_S` contains `N`
distinct `N`-th roots of unity: there are `e : T ≃ R` and `c : G_{K,S} → ℕ` with
`g ζ = ζ ^ c(g)` for every `N`-th root of unity `ζ ∈ K_S` and `e (g • t) = c(g) · e t`. -/
def IsCyclotomicTwist (S : Set (HeightOneSpectrum (𝓞 K))) (R T : Type) [CommRing R]
    [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (e : T ≃ₗ[R] R) (c : GKS K S → ℕ),
    (N : R) = 0 ∧
    Nat.card {ζ : unramifiedOutside K S // ζ ^ N = 1} = N ∧
    (∀ (g : GKS K S) (ζ : unramifiedOutside K S), ζ ^ N = 1 → toGal K g ζ = ζ ^ c g) ∧
    ∀ (g : GKS K S) (t : T), e (g • t) = (c g : R) * e t

/-- The finite standing hypotheses of Nekovář §5–§7 used here (5.1, p. 113; 5.2.3 and 6.2.5
(A) with `J = I[0] = R`). -/
structure NekovarFiniteSetting (S : Set (HeightOneSpectrum (𝓞 K))) (p : ℕ) (R : Type)
    [CommRing R] [IsLocalRing R] : Prop where
  prime : p.Prime
  finite_S : S.Finite
  above_p : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S
  condP : p = 2 → IsTotallyComplex K
  finite_R : Finite R
  nilpotent_p : IsNilpotent (p : R)
  selfInjective : Module.Injective R R

/-- A degree-three trace `tr : C³ → R` killing coboundaries **induces an isomorphism**
`H³(C) ≅ R`: a cocycle with `tr = 0` is a coboundary, and some cocycle has trace `1`. -/
def InducesIsoH3 {R : Type} [CommRing R] {C : GCx R} (tr : C.X 3 →ₗ[R] R) : Prop :=
  (∀ z : C.X 3, C.d 3 4 rfl z = 0 → tr z = 0 → ∃ y, C.d 2 3 rfl y = z) ∧
    ∃ z : C.X 3, C.d 3 4 rfl z = 0 ∧ tr z = 1

/-- A bilinear pairing of discrete modules is jointly continuous. -/
theorem continuous_pairing {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [TopologicalSpace A]
    [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace C]
    (β : A →ₗ[R] B →ₗ[R] C) : Continuous fun x : A × B => β x.1 x.2 :=
  continuous_of_discreteTopology

section Data

variable (S : Set (HeightOneSpectrum (𝓞 K))) (R : Type) [CommRing R]
  {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)


/-- Genuine isotropy data for the Galois Selmer data (Nekovář 6.2.1.3). -/
abbrev GaloisIsotropyData (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M') :
    Type :=
  IsotropyData R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
    (continuous_pairing β) ΔA ΔB

/-- **The genuine cup-product data** on the Galois Selmer data (`genuinePairData`). -/
abbrev galoisPairData (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
    (I : GaloisIsotropyData K S R β hβ ΔA ΔB) :
    SelPairData (galoisSelData K S R M ΔA) (galoisSelData K S R M' ΔB) :=
  genuinePairData R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
    (continuous_pairing β) ΔA ΔB I

/-- The genuine compactly supported cochains with coefficients `T`,
`C_c(G_{K,S}, T) = Cone(C(G_{K,S}, T) → ⊕_v C(G_v, T))[−1]` (Nekovář 5.3.1.1). -/
abbrev galoisCompactT (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
    (I : GaloisIsotropyData K S R β hβ ΔA ΔB) : GCx R :=
  coneCx (galoisPairData K S R β hβ ΔA ΔB I).resE

end Data

/-- A degree-two local trace `tr : C² → R` killing coboundaries **induces an isomorphism**
`H²(C) ≅ R` (as `inv_v` does for `C = C^•_cont(G_{K_v}, R(1))`, Nekovář 5.1.3, 5.2.1). -/
def InducesIsoH2 {R : Type} [CommRing R] {C : GCx R} (tr : C.X 2 →ₗ[R] R) : Prop :=
  (∀ z : C.X 2, C.d 2 3 rfl z = 0 → tr z = 0 → ∃ y, C.d 1 2 rfl y = z) ∧
    ∃ z : C.X 2, C.d 2 3 rfl z = 0 ∧ tr z = 1

/-! ### The PRINT statements -/

/-- **PRINT — Nekovář, *Selmer complexes*, Proposition 5.2.4, p. 116, case (i) with
`J = I[0] = R`** (local duality, cited at tex 3455), for the genuine local complexes: under the
finite standing hypotheses, for finite discrete modules `M`, `M'` with a perfect equivariant
pairing `β : M × M' → T`, `T ≅ R(1)`, at every place `v ∈ S` and for every local trace
`tr_v : C²_cont(G_{K_v}, T) → R` killing coboundaries and inducing `H²(G_{K_v}, T) ≅ R`, the map
`C^•_cont(G_{K_v}, M) → Hom_R(C^•_cont(G_{K_v}, M'), R)[−2]`, `a ↦ (b ↦ tr_v(a ∪ b))`
(Nekovář's `α_{J,X}` of 5.2.2), is a quasi-isomorphism. -/
def NekovarProp524 : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (p : ℕ) (R : Type) [CommRing R] [IsLocalRing R],
    NekovarFiniteSetting K S p R →
    ∀ (M M' T : Type)
      [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
      [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
      [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M']
      [SMulCommClass (GKS K S) R M'] [TopologicalSpace M'] [DiscreteTopology M']
      [ContinuousSMul (GKS K S) M'] [Finite M']
      [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
      [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
      (β : M →ₗ[R] M' →ₗ[R] T)
      (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b),
      Function.Bijective β → Function.Bijective β.flip → IsCyclotomicTwist K S R T →
      ∀ (v : Places K S)
        (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
          T v).X 2 →ₗ[R] R)
        (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T v).d (2 - 1) 2 (by omega) z) = 0),
        InducesIsoH2 trv →
        QuasiIso (GHom.toCC (adjHom (localPair R (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) β hβ (continuous_pairing β) v) 2 trv htrv))

/-- **PRINT — Nekovář, *Selmer complexes* (Astérisque 310, 2006), Proposition 5.4.3, p. 127,
case (i) with `J = I[0] = R`** ("a variant of the Poitou–Tate global duality theorem", cited at
tex 3455, with 5.1 and 5.4 for the trace), stated for the genuine continuous cochains: under
the finite standing hypotheses, for finite discrete `R[G_{K,S}]`-modules `M`, `M'` with a perfect
equivariant pairing `β : M × M' → T`, `T ≅ R(1)`, any genuine local conditions and isotropy data,
and any global trace `tr : C³_c(G_{K,S}, T) → R` killing coboundaries and inducing
`H³_c(G_{K,S}, T) ≅ R`, the global duality map
`C(G_{K,S}, M) → Hom_R(C_c(G_{K,S}, M'), R)[−3]`, `a ↦ ((b, y) ↦ tr(a ∪ b, (−1)^i res a ∪ y))`
(Nekovář's `cβ_{J,X}` of 5.4.2, induced by `∪_c` of 5.3.3.3), is a quasi-isomorphism. -/
def NekovarProp543 : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (p : ℕ) (R : Type) [CommRing R] [IsLocalRing R],
    NekovarFiniteSetting K S p R →
    ∀ (M M' T : Type)
      [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
      [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M] [Finite M]
      [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M']
      [SMulCommClass (GKS K S) R M'] [TopologicalSpace M'] [DiscreteTopology M']
      [ContinuousSMul (GKS K S) M'] [Finite M']
      [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
      [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
      (β : M →ₗ[R] M' →ₗ[R] T)
      (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b),
      Function.Bijective β → Function.Bijective β.flip → IsCyclotomicTwist K S R T →
      ∀ (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
        (I : GaloisIsotropyData K S R β hβ ΔA ΔB)
        (tr : (galoisCompactT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
        (htr : ∀ z, tr ((galoisCompactT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0),
        InducesIsoH3 tr →
        QuasiIso (GHom.toCC (globalDualityMap (galoisPairData K S R β hβ ΔA ΔB I) tr htr))

/-- **PRINT — Nekovář 5.4.1 (pp. 125–126) with 5.1.5**: `H³_c(G_{K,S}, R(1)) ≅ R` through a
cochain-level trace: for genuine data as in `NekovarProp543`, a global trace killing coboundaries
and inducing `H³_c(G_{K,S}, T) ≅ R` exists. (Non-vacuity of the trace hypothesis of
`NekovarProp543`.) -/
def NekovarProp541 : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (p : ℕ) (R : Type) [CommRing R] [IsLocalRing R],
    NekovarFiniteSetting K S p R →
    ∀ (M M' T : Type)
      [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
      [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
      [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M']
      [SMulCommClass (GKS K S) R M'] [TopologicalSpace M'] [DiscreteTopology M']
      [ContinuousSMul (GKS K S) M']
      [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
      [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
      (β : M →ₗ[R] M' →ₗ[R] T)
      (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b),
      IsCyclotomicTwist K S R T →
      ∀ (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
        (I : GaloisIsotropyData K S R β hβ ΔA ΔB),
        ∃ (tr : (galoisCompactT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
          (_ : ∀ z, tr ((galoisCompactT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0), InducesIsoH3 tr

/-- **PRINT — Nekovář 7.8.8(ii) (pp. 186–187)**, cited at tex 3483: for `S ⊆ S'` finite (with
the standing hypotheses for `S`), a finite discrete `R[G_{K,S}]`-module `M`, arbitrary local
conditions at `S`, and the unramified conditions `C^•_cont(G_q/I_q, M)` at `q ∈ S' − S` (with any
factorizations `ψ_q` of the localization through `G_q/I_q`), the genuine support comparison
`C_f(G_{K,S}, M; Δ) → C_f(G_{K,S'}, M; Δ ∪ ur)` (inflation, `galoisSupportData`) is a
quasi-isomorphism. -/
def NekovarProp788ii : Prop :=
  ∀ (S S' : Set (HeightOneSpectrum (𝓞 K))) (hS : S ⊆ S') (p : ℕ) (R : Type) [CommRing R]
    [IsLocalRing R], NekovarFiniteSetting K S p R → S'.Finite →
    ∀ (M : Type) [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M]
      [SMulCommClass (GKS K S) R M] [TopologicalSpace M] [DiscreteTopology M]
      [ContinuousSMul (GKS K S) M] [Finite M]
      (ψ : ∀ q : NewPlaces K S S', GUr K q.1 →ₜ* GKS K S)
      (hψ : ∀ (q : NewPlaces K S S') g, locMap K S q.1 g = ψ q (urRes K q.1 g))
      (Δ : GaloisLocalConditions K S R M),
      QuasiIso (GHom.toCC (supportMap (galoisSupportData K hS R M ψ hψ Δ)))

/-! ### The abstract inputs, for the genuine data -/

section Inputs

variable {S : Set (HeightOneSpectrum (𝓞 K))} {R : Type} [CommRing R]
  {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
  (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
  (I : GaloisIsotropyData K S R β hβ ΔA ΔB)
  (tr : (galoisCompactT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
  (htr : ∀ z, tr ((galoisCompactT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0)

/-- **`GlobalDualityInput` for the genuine data, from the PRINT** `NekovarProp543`: the GLUE
input of `SelmerDuality/Duality.lean` holds for the genuine `SelPairData` (for every coefficient
pairing argument `P`, which the input does not use). PROVED. -/
theorem globalDualityInput_of_print (h : NekovarProp543 K) (p : ℕ) [IsLocalRing R]
    (hset : NekovarFiniteSetting K S p R) [Finite M] [Finite M'] (hb : Function.Bijective β)
    (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S R T) (htr3 : InducesIsoH3 tr)
    (P : PerfectCoefficientPairing R) :
    GlobalDualityInput (galoisPairData K S R β hβ ΔA ΔB I) tr htr P :=
  h S p R hset M M' T β hβ hb hb' hT ΔA ΔB I tr htr htr3

/-- **Orthogonal complements** (Nekovář 6.2.7, p. 140): the genuine local conditions `ΔA`, `ΔB`
with isotropy homotopies `I` are orthogonal complements of each other with respect to the
pairing and the (local part of the) trace: the map
`U⁻_S(M)[−1] = Cone(U_S → ⊕_v C(G_v, M))[−1] → Hom_R(U_S(M'), R)[−3]`,
`(u, x) ↦ (v ↦ tr(0, x ∪ i' v + h(u, v)))` (Nekovář's `u⁻_{π,h_v}`, 6.2.2) is a
quasi-isomorphism. (Under the perfect duality of 6.2.6 this is equivalent to the same for
`u⁺`, Nekovář 6.2.7.) -/
def OrthogonalComplements : Prop :=
  QuasiIso (GHom.toCC (localDualityMap (galoisPairData K S R β hβ ΔA ΔB I) tr htr))

/-- **`LocalOrthogonalityInput` for the genuine data is Nekovář's orthogonality** of the genuine
local conditions (the abstract-model identification disappears). PROVED (definitional). -/
theorem localOrthogonalityInput_iff (P : PerfectCoefficientPairing R) :
    LocalOrthogonalityInput (galoisPairData K S R β hβ ΔA ΔB I) tr htr P ↔
      OrthogonalComplements K β hβ ΔA ΔB I tr htr :=
  Iff.rfl

/-- **The genuine support change from the PRINT** (`NekovarProp788ii`): the conclusion of
`SupportChangeInput` — `QuasiIso (GHom.toCC (supportMap T))` — holds for the genuine
`T = galoisSupportData …`. PROVED. -/
theorem supportChange_of_print (h : NekovarProp788ii K) {S' : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S ⊆ S') (p : ℕ) [IsLocalRing R] (hset : NekovarFiniteSetting K S p R)
    (hS' : S'.Finite) [Finite M] (ψ : ∀ q : NewPlaces K S S', GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ (q : NewPlaces K S S') g, locMap K S q.1 g = ψ q (urRes K q.1 g))
    (Δ : GaloisLocalConditions K S R M) :
    QuasiIso (GHom.toCC (supportMap (galoisSupportData K hS R M ψ hψ Δ))) :=
  h S S' hS p R hset hS' M ψ hψ Δ

/-- For the genuine support data, `SupportChangeInput` (whatever its auxiliary hypothesis) is the
conclusion of `NekovarProp788ii`. PROVED. -/
theorem supportChangeInput_of_print (h : NekovarProp788ii K) {S' : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S ⊆ S') (p : ℕ) [IsLocalRing R] (hset : NekovarFiniteSetting K S p R)
    (hS' : S'.Finite) [Finite M] (ψ : ∀ q : NewPlaces K S S', GUr K q.1 →ₜ* GKS K S)
    (hψ : ∀ (q : NewPlaces K S S') g, locMap K S q.1 g = ψ q (urRes K q.1 g))
    (Δ : GaloisLocalConditions K S R M)
    (H : SupportChangeUnramified (galoisSupportData K hS R M ψ hψ Δ)) :
    SupportChangeInput (galoisSupportData K hS R M ψ hψ Δ) H :=
  supportChange_of_print K h hS p hset hS' ψ hψ Δ

/-- The perfect coefficient pairing `M × M' → R` obtained from `β` and `T ≅ R`. -/
def perfectOfTwist (e : T ≃ₗ[R] R) (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) :
    PerfectCoefficientPairing R where
  M := ModuleCat.of R M
  M' := ModuleCat.of R M'
  pair := β.compr₂ e.toLinearMap
  perfect_left := by
    have h : ⇑(β.compr₂ e.toLinearMap) =
        ⇑((LinearEquiv.refl R M').arrowCongr e) ∘ ⇑β := by
      funext m
      ext m'
      rfl
    change Function.Bijective ⇑(β.compr₂ e.toLinearMap)
    rw [h]
    exact (LinearEquiv.bijective _).comp hb
  perfect_right := by
    have h : ⇑(β.compr₂ e.toLinearMap).flip =
        ⇑((LinearEquiv.refl R M).arrowCongr e) ∘ ⇑β.flip := by
      funext m'
      ext m
      rfl
    change Function.Bijective ⇑(β.compr₂ e.toLinearMap).flip
    rw [h]
    exact (LinearEquiv.bijective _).comp hb'

/-- **Finite Selmer duality for the genuine complexes** (Lemma `ex:arith-conjugate-duality`,
tex 2761–2830, and (4.3), tex 3455–3463; Nekovář 6.3.4, p. 143): from the PRINT
`NekovarProp543` and the orthogonality of the genuine local conditions (Nekovář 6.2.7; for the
text's Kummer conditions this is Lemma `ex:arith-local-kummer`), the genuine Selmer duality map
`C_U(M) → Hom_R(C_{U⊥}(M'), R)[−3] = RHom_R(C_{U⊥}(M'), R)[−3]` is a quasi-isomorphism. PROVED
(by `finiteSelmerDualityNode_proof`, the cochain-level form of Nekovář's proof of 6.3.4). -/
theorem genuineSelmerDuality (h : NekovarProp543 K) (p : ℕ) [IsLocalRing R]
    (hset : NekovarFiniteSetting K S p R) [Finite M] [Finite M'] (hb : Function.Bijective β)
    (hb' : Function.Bijective β.flip) (hT : IsCyclotomicTwist K S R T) (htr3 : InducesIsoH3 tr)
    (horth : OrthogonalComplements K β hβ ΔA ΔB I tr htr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairData K S R β hβ ΔA ΔB I) tr htr)) := by
  have hT' := hT
  obtain ⟨N, -, e, -⟩ := hT'
  exact finiteSelmerDualityNode_proof R _ _ (galoisPairData K S R β hβ ΔA ΔB I) tr htr
    (perfectOfTwist β e hb hb') (Or.inl hset.selfInjective)
    (globalDualityInput_of_print K β hβ ΔA ΔB I tr htr h p hset hb hb' hT htr3 _) horth

end Inputs

/-! ### The full condition is orthogonal to the zero condition -/

section RelaxedStrict

variable {S : Set (HeightOneSpectrum (𝓞 K))} {R : Type} [CommRing R]
  {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[R] M' →ₗ[R] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- The isotropy data of the pair (full condition, zero condition): zero homotopies (the local
product `i u ∪ i' v` vanishes since `U' = 0`). -/
def relaxedStrictIsotropy :
    GaloisIsotropyData K S R β hβ (relaxedConditions R _ _ _ M) (strictConditions R _ _ _ M') where
  h _ _ _ _ _ := 0
  isotropy v i i₁ j j₁ l l₁ hh hi hj hl x y := by
    have hy : ((strictConditions R (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) M').i v).f j j rfl y = 0 := rfl
    rw [hy, map_zero]
    simp

/-- On the full condition the local condition map is the identity: `−ι = −id`. -/
theorem toCC_negι_relaxed :
    GHom.toCC (negι (galoisSelData K S R M (relaxedConditions R _ _ _ M))) = -𝟙 _ := by
  ext i x
  rfl

/-- **The full local condition is the orthogonal complement of the zero condition** (tex
2813–2816: "A full condition is paired with the zero condition"): for every trace, the local
duality map `Cone(id)[−1] → Hom_R(0, R)[−3]` is a quasi-isomorphism (both sides are acyclic).
PROVED. -/
theorem orthogonal_relaxed_strict
    (tr : (galoisCompactT K S R β hβ _ _ (relaxedStrictIsotropy K β hβ)).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactT K S R β hβ _ _ (relaxedStrictIsotropy K β hβ)).d 2 3 rfl z) = 0) :
    OrthogonalComplements K β hβ _ _ (relaxedStrictIsotropy K β hβ) tr htr := by
  unfold OrthogonalComplements
  apply quasiIso_of_acyclic
  · rw [acyclic_toCC_iff]
    exact relaxed_locCx_acyclic (k := R) (GS := GKS K S) (Gv := fun v : Places K S => Gloc K v.1)
      (loc := fun v => locMap K S v.1) (M := M)
  · rw [acyclic_toCC_iff]
    intro i j l hij hjl φ _
    refine ⟨0, dualCx_ext fun x => ?_⟩
    have hx : x = 0 := funext fun _ => rfl
    rw [hx, map_zero, map_zero]

end RelaxedStrict

/-! ### Non-vacuity of the PRINT hypotheses -/

section NonVacuity

/-- A module with the trivial action of `G` (a type synonym of `V`). -/
def TrivMod (_G V : Type) : Type := V

variable (G V : Type) [Group G]

instance [AddCommGroup V] : AddCommGroup (TrivMod G V) := inferInstanceAs (AddCommGroup V)
instance {R : Type} [Semiring R] [AddCommGroup V] [Module R V] : Module R (TrivMod G V) :=
  inferInstanceAs (Module R V)
instance [TopologicalSpace V] : TopologicalSpace (TrivMod G V) :=
  inferInstanceAs (TopologicalSpace V)
instance [TopologicalSpace V] [DiscreteTopology V] : DiscreteTopology (TrivMod G V) :=
  inferInstanceAs (DiscreteTopology V)
instance [AddCommGroup V] : DistribMulAction G (TrivMod G V) where
  smul _ v := v
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
instance {R : Type} [Semiring R] [AddCommGroup V] [Module R V] : SMulCommClass G R (TrivMod G V) where
  smul_comm _ _ _ := rfl
instance [AddCommGroup V] [TopologicalSpace G] [TopologicalSpace V] :
    ContinuousSMul G (TrivMod G V) where
  continuous_smul := continuous_snd

/-- **Non-vacuity of `IsCyclotomicTwist`**: `ℤ/2` with the trivial action is `(ℤ/2)(1)`
(`μ₂ = {±1} ⊂ K ⊂ K_S`). PROVED. -/
theorem isCyclotomicTwist_example (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsCyclotomicTwist K S (ZMod 2) (TrivMod (GKS K S) (ZMod 2)) := by
  have hne : (1 : unramifiedOutside K S) ≠ -1 := by
    intro h
    have h2 : (2 : unramifiedOutside K S) = 0 := by
      calc (2 : unramifiedOutside K S) = 1 + 1 := by norm_num
        _ = -1 + 1 := by rw [← h]
        _ = 0 := by ring
    exact two_ne_zero h2
  refine ⟨2, two_pos, LinearEquiv.refl _ _, fun _ => 1, by decide, ?_, ?_, ?_⟩
  · have hset : {ζ : unramifiedOutside K S | ζ ^ 2 = 1} = {1, -1} := by
      ext ζ
      simp [sq_eq_one_iff]
    rw [show Nat.card {ζ : unramifiedOutside K S // ζ ^ 2 = 1} =
        Nat.card ({ζ : unramifiedOutside K S | ζ ^ 2 = 1} : Set _) from rfl, hset,
      Nat.card_coe_set_eq, Set.ncard_pair hne]
  · intro g ζ hζ
    rcases (sq_eq_one_iff).1 hζ with rfl | rfl
    · simp
    · simp
  · intro g t
    simp
    rfl

/-- **Non-vacuity of `NekovarFiniteSetting`**: for a totally complex number field `K` (condition
(P) at `p = 2`), the primes above `2` and the coefficient ring `ℤ/2` satisfy the finite standing
hypotheses. PROVED. -/
theorem nekovarFiniteSetting_example (hK : IsTotallyComplex K) :
    NekovarFiniteSetting K {v : HeightOneSpectrum (𝓞 K) | (2 : 𝓞 K) ∈ v.asIdeal} 2 (ZMod 2) where
  prime := Nat.prime_two
  finite_S := primesAboveTwo_finite K
  above_p v hv := by simpa using hv
  condP _ := hK
  finite_R := inferInstance
  nilpotent_p := ⟨1, by decide⟩
  selfInjective := Module.injective_of_isSemisimpleRing (ZMod 2) (ZMod 2)

end NonVacuity

end ZInQ.Manuscript.RC.SelmerComplex

