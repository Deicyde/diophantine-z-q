import ZInQKernel.Contrib.OneProof.RC.KummerMaps.ConjKummer
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Collapse

/-!
# Lane RC29, round 2, item (5): the transported dual conditions for the inflated `M_i`

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830), tex
2810–2813, for the actual coefficient module of lane RC28: `M_i = (E[2^i] ⊗ A_i)(α)` is built over
`G_{K,S₀}` (`S₀` the ramification support of the coefficients) and inflated to the Selmer support
`S ⊇ S₀` (lane RC28's `MinS hS W i α`, tex 3479–3498). This removes the departure D6 of
`ConjTransport.lean` (there the module was built directly over `G_{K,S}`).

* `conjInflConj`: the actual conjugation `C` of `G_{K,S}` restricts to one of `G_{K,S₀}` for a
  `κ`-stable `S₀` (same `ι, τ, κ`); `conjInfl_inflMap_conj`: **the inflation intertwines the two
  conjugations** (lane RC28's `inflMap_conjGKS`).
* `conjInflPullEquiv`: `τ^*(Infl M₀) = Infl(τ^*M₀)` as `G_{K,S}`-modules (the identity map; the
  two actions agree by `conjInfl_inflMap_conj`); `conjInflMapEquiv`: inflation of an equivariant
  isomorphism.
* `conjInflDualEquiv : τ^*M_i ≃ Infl(M_{i,0}^*(1))` (`M_{i,0}` the module over `G_{K,S₀}`):
  lane RC28's `conjDualEquiv` over `S₀`, inflated; equivariant (`conjInflDualEquiv_smul`) when
  `α_i^τ = α_i^{-1}`.
* `conjInflTransportDual`: **the transported dual condition for the inflated module**: a local
  condition at `τv` for `M_i = MinS` gives a condition at `v` for `Infl(M_{i,0}^*(1))`; it preserves
  injectivity, zero and full (`conjInflTransportDual_isInjective`, `_zeroAt`,
  `_fullAt_bijective`).
* `conjInflKummerIso`, `conjInflDualKummerIso`: **the Kummer conditions at `2N` for the inflated
  module are preserved** (tex 2812–2813): the transported actual Kummer condition at `τv`
  (`actualKummerAtS`) is isomorphic, compatibly with the cochain isomorphism, to the Kummer
  condition of `B_v = localTwist W h v` at `v` through the transported coefficient map, and its
  dual version through `conjInflDualEquiv`; the `H¹` images are the spans of the transported
  Kummer images (`conjInflDualKummer_range_H1`).
* `conjInflDualAt`, `conjInflDualConditions`, `conjInflDual_isGaloisSelData`: the assembled dual
  conditions at the old places `S₀` (split: from `τv ∈ S₀`; fixed: from `v` through the local
  representative), with lane RC28's unramified conditions at the new places `S − S₀`, are genuine
  Galois Selmer data.
* Non-vacuity of the one new hypothesis (`κ`-stability of `S₀`): `conjInflStable_self`,
  `conjInflStable_empty`.

Kinds: DEF and PROVED; no PRINT. Hypotheses (each also flagged at the declarations):
* `hS : S₀ ⊆ S`: DEF (lane RC28's `MinS`).
* `hS₀`: `S₀` is stable under the conjugate-place map: ELLIOT (tex 3479–3498: `S₀` consists of
  the primes above `2N`, the moving prime and the twist data, a set of primes of `K` lying over a
  set of rational primes, hence stable under `κ`; cf. lane RC28's `isStable_comap_int`);
  non-vacuous (`conjInflStable_self`, `conjInflStable_empty`).
* `hα₀ : α(c₀ σ) = α(σ)⁻¹` on `G_{K,S₀}`: ELLIOT (tex 2786–2795), as `hα` of `ConjTransport.lean`.
* The other hypotheses are those of `ConjTransport.lean` and `ConjKummer.lean`.

DEPARTURE (form): the dual module of the inflated `M_i` is taken to be the inflation of the
`G_{K,S₀}`-dual `M_{i,0}^*(1)` (as in the other lane RC29 files, e.g. `OrthActual.lean`), not the
`G_{K,S}`-dual of `Infl M_{i,0}` (the two agree when `A_i(1)` over `G_{K,S}` is the inflation of
`A_i(1)` over `G_{K,S₀}`; that identification is not formalized here). DEPARTURE D4 of
`ConjTransport.lean` (orthogonality `U^⊥` not proved) applies unchanged.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (GHom.toCC)

/-! ### The conjugation of `G_{K,S₀}` and the inflation -/

section InflConj

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (hS : S₀ ⊆ S)
  (hS₀ : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ S₀ ↔ w ∈ S₀))

/-- **The actual conjugation over `S₀`**: the same `ι, τ, κ` as `C`, for the `κ`-stable `S₀`.
Hypothesis `hS₀`: ELLIOT (tex 3479–3498), non-vacuous (`conjInflStable_self`). -/
def conjInflConj : ActualConj K S₀ where
  ι := C.ι
  τ := C.τ
  κ := C.κ
  hτ := C.hτ
  hι := C.hι
  hinv := C.hinv
  hS := hS₀

/-- PROVED (lane RC28's `inflMap_conjGKS`). **The inflation intertwines the conjugations**:
`infl(c σ) = c₀(infl σ)`. -/
theorem conjInfl_inflMap_conj (σ : GKS K S) :
    inflMap K hS (C.conj σ) = (conjInflConj C hS₀).conj (inflMap K hS σ) :=
  inflMap_conjGKS K C.κ C.τ C.hτ hS hS₀ C.hS σ

variable (k : Type) [CommRing k] (M₀ : Type) [AddCommGroup M₀] [Module k M₀]
  [DistribMulAction (GKS K S₀) M₀] [SMulCommClass (GKS K S₀) k M₀]

/-- DEF. **`τ^*(Infl M₀) = Infl(τ^*M₀)`**: the identity of the underlying module. -/
def conjInflPullEquiv :
    PullMod C.conj (InflMod hS M₀) ≃ₗ[k] InflMod hS (PullMod (conjInflConj C hS₀).conj M₀) :=
  LinearEquiv.refl k M₀

omit [SMulCommClass (GKS K S₀) k M₀] in
/-- PROVED. `conjInflPullEquiv` is `G_{K,S}`-equivariant: both actions are
`σ ↦ c₀(infl σ) = infl(c σ)` (`conjInfl_inflMap_conj`). -/
theorem conjInflPullEquiv_smul (σ : GKS K S) (m : PullMod C.conj (InflMod hS M₀)) :
    conjInflPullEquiv C hS hS₀ k M₀ (σ • m) = σ • conjInflPullEquiv C hS hS₀ k M₀ m := by
  change inflMap K hS (C.conj σ) • (show M₀ from m) =
    (conjInflConj C hS₀).conj (inflMap K hS σ) • (show M₀ from m)
  rw [conjInfl_inflMap_conj]

variable {k} (N₀ : Type) [AddCommGroup N₀] [Module k N₀] [DistribMulAction (GKS K S₀) N₀]
  [SMulCommClass (GKS K S₀) k N₀]

/-- DEF. The inflation of a `k`-linear isomorphism of `G_{K,S₀}`-modules. -/
def conjInflMapEquiv (ψ : M₀ ≃ₗ[k] N₀) : InflMod hS M₀ ≃ₗ[k] InflMod hS N₀ :=
  ψ

omit [SMulCommClass (GKS K S₀) k M₀] [SMulCommClass (GKS K S₀) k N₀] in
/-- PROVED. The inflation of an equivariant isomorphism is equivariant. Hypothesis `hψ`: the
equivariance over `G_{K,S₀}`. -/
theorem conjInflMapEquiv_smul (ψ : M₀ ≃ₗ[k] N₀)
    (hψ : ∀ (σ : GKS K S₀) (m : M₀), ψ (σ • m) = σ • ψ m) (σ : GKS K S) (m : InflMod hS M₀) :
    conjInflMapEquiv hS M₀ N₀ ψ (σ • m) = σ • conjInflMapEquiv hS M₀ N₀ ψ m :=
  hψ (inflMap K hS σ) m

end InflConj

/-- PROVED. Non-vacuity of `hS₀`: `S` itself is stable (`S₀ = S`). -/
theorem conjInflStable_self {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (C : ActualConj K S) :
    ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) →
        (v ∈ S ↔ w ∈ S) :=
  C.hS

/-- PROVED. Non-vacuity of `hS₀`: the empty set is stable. -/
theorem conjInflStable_empty {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (C : ActualConj K S) :
    ∀ v w : HeightOneSpectrum (𝓞 K),
      w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) →
        (v ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))) ↔ w ∈ (∅ : Set (HeightOneSpectrum (𝓞 K)))) :=
  fun _ _ _ => Iff.rfl

/-! ### The coefficient identification `τ^*M_i ≃ Infl(M_{i,0}^*(1))` -/

section InflDual

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (hS : S₀ ⊆ S)
  (hS₀ : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ S₀ ↔ w ∈ S₀))
  (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.map (C.κ : K →+* K) = W) (i : ℕ)
  (α : GKS K S₀ →* (Acoef i)ˣ) (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (hFull₀ : FullTorsion K S₀ W (2 ^ i))

/-- DEF (tex 2765, 2805, inflated). **`τ^*M_i ≃ Infl(M_{i,0}^*(1))`** for the inflated
`M_i = MinS`: `conjInflPullEquiv` followed by the inflation of lane RC28's `conjDualEquiv` over
`S₀`. Hypotheses: `hW` (RC28 DEPARTURE 3), `hFull₀` (GLUE, RC28), `hS₀` (ELLIOT). -/
def conjInflDualEquiv :
    PullMod C.conj (MinS hS W i α) ≃ₗ[Acoef i] InflMod hS (DualM W hμ₀ (Acoef i) α) :=
  (conjInflPullEquiv C hS hS₀ (Acoef i) (Mcoef K S₀ W i α)).trans
    (conjInflMapEquiv hS _ _ (conjDualEquiv (conjInflConj C hS₀) W hW hμ₀ (Acoef i) α hFull₀))

/-- PROVED. **`τ^*M_i ≃ Infl(M_{i,0}^*(1))` is `G_{K,S}`-equivariant** when `α_i^τ = α_i^{-1}`
(hypothesis `hα₀`: ELLIOT, tex 2786–2795). -/
theorem conjInflDualEquiv_smul (hα₀ : ∀ σ, α ((conjInflConj C hS₀).conj σ) = (α σ)⁻¹)
    (σ : GKS K S) (m : PullMod C.conj (MinS hS W i α)) :
    conjInflDualEquiv C hS hS₀ W hW i α hμ₀ hFull₀ (σ • m) =
      σ • conjInflDualEquiv C hS hS₀ W hW i α hμ₀ hFull₀ m := by
  change conjInflMapEquiv hS _ _ (conjDualEquiv (conjInflConj C hS₀) W hW hμ₀ (Acoef i) α hFull₀)
      (conjInflPullEquiv C hS hS₀ (Acoef i) (Mcoef K S₀ W i α) (σ • m)) =
    σ • conjInflMapEquiv hS _ _ (conjDualEquiv (conjInflConj C hS₀) W hW hμ₀ (Acoef i) α hFull₀)
      (conjInflPullEquiv C hS hS₀ (Acoef i) (Mcoef K S₀ W i α) m)
  rw [conjInflPullEquiv_smul, conjInflMapEquiv_smul hS _ _ _
    (conjDualEquiv_smul (conjInflConj C hS₀) W hW hμ₀ (Acoef i) α hFull₀ hα₀)]

/-! ### The transported dual condition for the inflated module -/

variable [IsOpenKer α] [ContinuousSMul (GKS K S₀) (DualM W hμ₀ (Acoef i) α)]
  (hα₀ : ∀ σ, α ((conjInflConj C hS₀).conj σ) = (α σ)⁻¹)
  (g : GKS K S) {v w : Places K S}
  (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
  (hg : ∀ σ : Gloc K v.1,
    locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹)

/-- DEF (tex 2810–2812 for the inflated `M_i`). **The dual condition at `v` transported from the
condition `c` at `τv`** for `M_i = MinS hS W i α`: `conjTransport` followed by the coefficient
change along `conjInflDualEquiv`. Hypotheses as in `conjTransportDual`, with `hS₀`, `hα₀`
(ELLIOT). DEPARTURE D4: the orthogonality `U^⊥` is not proved. -/
def conjInflTransportDual (c : CondAt K S (Acoef i) (MinS hS W i α) w) :
    CondAt K S (Acoef i) (InflMod hS (DualM W hμ₀ (Acoef i) α)) v :=
  conjTransportCoef (conjInflDualEquiv C hS hS₀ W hW i α hμ₀ hFull₀)
    (conjInflDualEquiv_smul C hS hS₀ W hW i α hμ₀ hFull₀ hα₀) (conjTransport C g hvw hg c)

/-- PROVED. The transported dual condition is a subcomplex when `c` is. -/
theorem conjInflTransportDual_isInjective (c : CondAt K S (Acoef i) (MinS hS W i α) w)
    (hc : c.IsInjective) :
    (conjInflTransportDual C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ g hvw hg c).IsInjective :=
  conjTransportCoef_isInjective _ _ _ (conjTransport_isInjective C g hvw hg c hc)

/-- PROVED. The dual of the zero condition at `τv` is the zero condition at `v`. -/
theorem conjInflTransportDual_zeroAt :
    conjInflTransportDual C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ g hvw hg (zeroAt K S (Acoef i) _ w) =
      zeroAt K S (Acoef i) (InflMod hS (DualM W hμ₀ (Acoef i) α)) v := by
  unfold conjInflTransportDual
  rw [conjTransport_zeroAt, conjTransportCoef_zeroAt]

/-- PROVED. The dual of the full condition at `τv` maps isomorphically onto the full local complex
at `v`. -/
theorem conjInflTransportDual_fullAt_bijective (n : ℤ) :
    Function.Bijective ((conjInflTransportDual C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ g hvw hg
      (fullAt K S (Acoef i) _ w)).i.f n n rfl) :=
  (locConjNatHom_bijective (conjTransportCoefIso (conjInflDualEquiv C hS hS₀ W hW i α hμ₀ hFull₀)
    (conjInflDualEquiv_smul C hS hS₀ W hW i α hμ₀ hFull₀ hα₀) v.1) n).comp
    (conjTransport_fullAt_bijective C g hvw hg n)

/-! ### The Kummer conditions at `2N` for the inflated module -/

variable (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hκh : C.κ h = h) (hαw : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) w.1)

/-- DEF. **The transported coefficient map for the inflated module** at `v`:
`t ↦ g⁻¹ · ι_{τv}(Ē_* t)` (`conjKIotaAt`) with `ι_{τv}` lane RC29's `kummerIotaS`. Hypotheses
`hW`, `hκh` (`κ h = h`: ELLIOT, the twist is defined over the fixed field, as `hW`). -/
def conjInflIota :
    TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) →+
      ResMod (locMap K S v.1) (PullMod C.conj (MinS hS W i α)) :=
  conjKIotaAt C (Acoef i) g hvw (localTwist W h v.1) (localTwist W h w.1)
    (conjK_localTwist_map C.κ hvw W hW hκh) (2 ^ i) (kummerIotaS hS W i s hs hs0 α hFull₀ w)

omit [IsOpenKer α] [ContinuousSMul (GKS K S₀) (DualM W hμ₀ (Acoef i) α)] in
include hg hαw in
/-- PROVED. The transported coefficient map is `G_{K_v}`-equivariant. -/
theorem conjInflIota_smul (σ : Gloc K v.1)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    conjInflIota C hS W hW i α hFull₀ g hvw s hs hs0 hκh (σ • t) =
      σ • conjInflIota C hS W hW i α hFull₀ g hvw s hs hs0 hκh t :=
  conjKIotaAt_smul C (Acoef i) g hvw hg _ _ _ _ _
    (kummerIotaS_smul hS W i s hs hs0 α hFull₀ w hαw) σ t

open scoped Classical in
/-- PROVED (tex 2812–2813: "Kummer conditions at `2N` are preserved by this transport", for the
inflated `M_i`). **The transported actual Kummer condition at `τv` is isomorphic, compatibly with
the cochain isomorphism, to the Kummer condition of `B_v` at `v` through the transported
coefficient map** (`conjKTransportKummerIso` at `ι_{τv} = kummerIotaS`). -/
def conjInflKummerIso :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    ConjKCondIso (conjTransport C g hvw hg (actualKummerAtS hS W i s hs hs0 α hFull₀ w hαw))
      (kummerAt v (localTwist W h v.1) (2 ^ i)
        (conjInflIota C hS W hW i α hFull₀ g hvw s hs hs0 hκh)
        (conjInflIota_smul C hS W hW i α hFull₀ g hvw hg s hs hs0 hκh hαw)) :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) w.1
  conjKTransportKummerIso C (Acoef i) g hvw hg (localTwist W h v.1) (localTwist W h w.1)
    (conjK_localTwist_map C.κ hvw W hW hκh) (2 ^ i) (kummerIotaS hS W i s hs hs0 α hFull₀ w)
    (kummerIotaS_smul hS W i s hs hs0 α hFull₀ w hαw)

/-- DEF. **The dual transported coefficient map** into `Infl(M_{i,0}^*(1))`:
`conjInflDualEquiv ∘ conjInflIota`. -/
def conjInflDualIota :
    TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) →+
      ResMod (locMap K S v.1) (InflMod hS (DualM W hμ₀ (Acoef i) α)) :=
  (conjTransportCoefEquiv (S := S) (conjInflDualEquiv C hS hS₀ W hW i α hμ₀ hFull₀)
    v.1).toLinearMap.toAddMonoidHom.comp (conjInflIota C hS W hW i α hFull₀ g hvw s hs hs0 hκh)

omit [IsOpenKer α] [ContinuousSMul (GKS K S₀) (DualM W hμ₀ (Acoef i) α)] in
include hα₀ hg hαw in
/-- PROVED. The dual transported coefficient map is `G_{K_v}`-equivariant. -/
theorem conjInflDualIota_smul (σ : Gloc K v.1)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    conjInflDualIota C hS hS₀ W hW i α hμ₀ hFull₀ g hvw s hs hs0 hκh (σ • t) =
      σ • conjInflDualIota C hS hS₀ W hW i α hμ₀ hFull₀ g hvw s hs hs0 hκh t :=
  conjKCoefIota_smul (conjInflDualEquiv C hS hS₀ W hW i α hμ₀ hFull₀)
    (conjInflDualEquiv_smul C hS hS₀ W hW i α hμ₀ hFull₀ hα₀) (localTwist W h v.1) (2 ^ i)
    (conjInflIota C hS W hW i α hFull₀ g hvw s hs hs0 hκh)
    (conjInflIota_smul C hS W hW i α hFull₀ g hvw hg s hs hs0 hκh hαw) σ t

open scoped Classical in
/-- PROVED (tex 2810–2813, inflated `M_i`). **The transported dual Kummer condition**: the dual
condition `conjInflTransportDual` of the actual Kummer condition at `τv` is isomorphic,
compatibly with the cochain isomorphisms, to the Kummer condition of `B_v` at `v` with
coefficients in `Infl(M_{i,0}^*(1))` through `conjInflDualIota`. -/
def conjInflDualKummerIso :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    ConjKCondIso (conjInflTransportDual C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ g hvw hg
        (actualKummerAtS hS W i s hs hs0 α hFull₀ w hαw))
      (kummerAt v (localTwist W h v.1) (2 ^ i)
        (conjInflDualIota C hS hS₀ W hW i α hμ₀ hFull₀ g hvw s hs hs0 hκh)
        (conjInflDualIota_smul C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ g hvw hg s hs hs0 hκh hαw)) :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  ((conjInflKummerIso C hS W hW i α hFull₀ g hvw hg s hs hs0 hκh hαw).coef
    (conjInflDualEquiv C hS hS₀ W hW i α hμ₀ hFull₀)
    (conjInflDualEquiv_smul C hS hS₀ W hW i α hμ₀ hFull₀ hα₀)).trans
    (conjKCoefKummerIso (conjInflDualEquiv C hS hS₀ W hW i α hμ₀ hFull₀)
      (conjInflDualEquiv_smul C hS hS₀ W hW i α hμ₀ hFull₀ hα₀) (localTwist W h v.1) (2 ^ i)
      (conjInflIota C hS W hW i α hFull₀ g hvw s hs hs0 hκh)
      (conjInflIota_smul C hS W hW i α hFull₀ g hvw hg s hs hs0 hκh hαw))

open scoped Classical in
/-- PROVED. **The `H¹` image of the transported dual Kummer condition** is the `A_i`-span of the
Kummer image of `B_v(K_v)` through `conjInflDualIota`. -/
theorem conjInflDualKummer_range_H1 :
    haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
    LinearMap.range (HomologicalComplex.homologyMap (GHom.toCC (conjInflTransportDual C hS hS₀ W hW
      i α hμ₀ hFull₀ hα₀ g hvw hg (actualKummerAtS hS W i s hs hs0 α hFull₀ w hαw)).i) 1).hom =
      Submodule.span (Acoef i) (Set.range (kummerMapIn (Acoef i)
        (conjInflDualIota C hS hS₀ W hW i α hμ₀ hFull₀ g hvw s hs hs0 hκh)
        (conjInflDualIota_smul C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ g hvw hg s hs hs0 hκh hαw))) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v.1
  exact ((conjInflDualKummerIso C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ g hvw hg s hs hs0 hκh
    hαw).range_homology 1).trans (range_homologyMap_kummerConditionIn (Acoef i) _ _)

end InflDual

/-! ### The dual conditions at all places -/

section InflAssembly

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (hS : S₀ ⊆ S)
  (hS₀ : ∀ v w : HeightOneSpectrum (𝓞 K),
    w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) → (v ∈ S₀ ↔ w ∈ S₀))
  (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.map (C.κ : K →+* K) = W) (i : ℕ)
  (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  (hFull₀ : FullTorsion K S₀ W (2 ^ i)) [ContinuousSMul (GKS K S₀) (DualM W hμ₀ (Acoef i) α)]
  (hα₀ : ∀ σ, α ((conjInflConj C hS₀).conj σ) = (α σ)⁻¹)

include hS₀ in
/-- PROVED. The conjugate place of an old place is old (`hS₀`). -/
theorem conjInfl_conjPlace_mem {v : Places K S} (hv : v.1 ∈ S₀) : (locConjPlaceS C v).1 ∈ S₀ :=
  (hS₀ v.1 (conjPlace C.κ v.1) rfl).1 hv

open Classical in
/-- DEF (tex 2810–2812 at the old places). **The transported condition at an old place `v ∈ S₀`**
for `τ^*M_i`: at a fixed place, the transport by the local representative of conjugation
(`conjTransportFixed`); at a split place, the transport from `τv ∈ S₀`
(`conjTransportConjPlace`). The case split fixed/split: ELLIOT (tex 2810–2812). -/
def conjInflTransportAt (Δ : ∀ w : Places K S, w.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) w)
    (v : Places K S) (hv : v.1 ∈ S₀) : CondAt K S (Acoef i) (PullMod C.conj (MinS hS W i α)) v :=
  if hfix : conjPlace C.κ v.1 = v.1 then conjTransportFixed C v hfix (Δ v hv)
  else conjTransportConjPlace C v (Δ (locConjPlaceS C v) (conjInfl_conjPlace_mem C hS₀ hv))

omit [W.IsElliptic] in
/-- PROVED. The transported conditions at the old places are subcomplexes. -/
theorem conjInflTransportAt_isInjective
    (Δ : ∀ w : Places K S, w.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) w)
    (hΔ : ∀ w hw, (Δ w hw).IsInjective) (v : Places K S) (hv : v.1 ∈ S₀) :
    (conjInflTransportAt C hS hS₀ W i α Δ v hv).IsInjective := by
  unfold conjInflTransportAt
  split_ifs with hfix
  · exact conjTransport_isInjective C _ _ _ _ (hΔ v hv)
  · exact conjTransport_isInjective C _ _ _ _ (hΔ _ _)

/-- DEF (tex 2810–2812). **The dual condition at an old place `v ∈ S₀`** on `Infl(M_{i,0}^*(1))`:
`conjInflTransportAt` pushed along `conjInflDualEquiv`. DEPARTURE D4 (orthogonality not proved). -/
def conjInflDualAt (Δ : ∀ w : Places K S, w.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) w)
    (v : Places K S) (hv : v.1 ∈ S₀) :
    CondAt K S (Acoef i) (InflMod hS (DualM W hμ₀ (Acoef i) α)) v :=
  conjTransportCoef (conjInflDualEquiv C hS hS₀ W hW i α hμ₀ hFull₀)
    (conjInflDualEquiv_smul C hS hS₀ W hW i α hμ₀ hFull₀ hα₀)
    (conjInflTransportAt C hS hS₀ W i α Δ v hv)

/-- DEF (tex 2810–2812 with tex 3483–3498). **The dual local conditions on `Infl(M_{i,0}^*(1))`
at all places of `S`**, in lane RC26's format: the transported dual conditions at the old places
`S₀` and lane RC28's unramified conditions at the new places `S − S₀` (`urOutside`; stated with a
discrete topology on `A_i`, as lane RC28's `actualConditions`). -/
def conjInflDualConditions [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
    (Δ : ∀ w : Places K S, w.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) w) :
    GaloisLocalConditions K S (Acoef i) (InflMod hS (DualM W hμ₀ (Acoef i) α)) :=
  ofCondAt K S (Acoef i) _
    (urOutside hS (Acoef i) (DualM W hμ₀ (Acoef i) α)
      (conjInflDualAt C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ Δ))

/-- DEF. **The dual Selmer data `C_{U^⊥}(Infl M_{i,0}^*(1))`** (lane RC26's `galoisSelData`, with
the discrete topology on `A_i` as in lane RC28's `actualSelData`). -/
def conjInflDualSelData
    (Δ : ∀ w : Places K S, w.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) w) :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (Acoef i) :=
  letI := acoefTop i
  haveI := acoefTop_discrete i
  galoisSelData K S (Acoef i) (InflMod hS (DualM W hμ₀ (Acoef i) α))
    (conjInflDualConditions C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ Δ)

/-- PROVED. **The dual Selmer data for the inflated `M_i` are genuine Galois Selmer data** (lane
RC0's `IsGaloisSelData`), for finite `S` and injective conditions at the old places. -/
theorem conjInflDual_isGaloisSelData (hSfin : S.Finite)
    (Δ : ∀ w : Places K S, w.1 ∈ S₀ → CondAt K S (Acoef i) (MinS hS W i α) w)
    (hΔ : ∀ w hw, (Δ w hw).IsInjective) :
    ZInQ.Manuscript.RC.Wiring.IsGaloisSelData
      (conjInflDualSelData C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ Δ) := by
  let _ : TopologicalSpace (Acoef i) := acoefTop i
  have : DiscreteTopology (Acoef i) := acoefTop_discrete i
  exact ⟨K, inferInstance, inferInstance, S, InflMod hS (DualM W hμ₀ (Acoef i) α), inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, conjInflDualConditions C hS hS₀ W hW i α hμ₀ hFull₀ hα₀ Δ, hSfin,
    ofCondAt_injective K S _ _ _ (urOutside_isInjective hS (Acoef i) (DualM W hμ₀ (Acoef i) α) _
      (fun w hw => conjTransportCoef_isInjective _ _ _
        (conjInflTransportAt_isInjective C hS hS₀ W i α Δ hΔ w hw))), rfl⟩

end InflAssembly

end ZInQ.Manuscript.RC.KummerMaps
