import ZInQKernel.Contrib.OneProof.RC.CoefModules.Conjugate
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.UnramifiedFactorization
import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport

/-!
# Lane RC29, item 5 (part 1): the local conjugation `G_{K_v} ≃ G_{K_{τv}}`

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830), proof,
tex 2810–2812:

> At a split place `v`, the dual local condition is transported from the conjugate place `τv`.
> At a fixed place it is transported by the actual local representative of conjugation.

and tex 2767, 2823 ("the conjugate places", "the conjugate local places"). The actual complex
conjugation is lane RC28's `ActualConj` (tex 2778: "Fix an actual complex conjugation
`τ ∈ G_ℚ`, so that `τ² = 1`"): a ring automorphism `τ` of `K̄` restricting to `κ` on `K`, with
`S` stable under `κ`, and `c = C.conj : σ ↦ τστ⁻¹` on `G_{K,S}`. The conjugate place `τv` is
RC28's `conjPlace κ v` (the image of the prime `v` under `κ`).

This file builds the local transport needed for the sentence above. Throughout, `v, w` are
finite places with `w = κ(v)` as prime ideals (`hvw`); the split case is `w = conjPlace κ v`
(`hvw` is `rfl`), the fixed case is `w = v` (`locConjFixed_asIdeal`). No cast along an
equality of places is needed.

* (a) `locConjCompletion`: **`e : K_v ≃+* K_w`**, the continuous extension of `κ`; `κ` carries
  the `v`-adic valuation to the `w`-adic one (`locConj_valuation`, `locConjCompletion_valued`);
  `e` extends `κ` (`locConjCompletion_algebraMap`), is continuous
  (`locConjCompletion_continuous`) and is the only continuous ring map extending `κ`
  (`locConjCompletion_unique`).
* (b) `locConjBar`: **`Ē : K̄_v ≃+* K̄_w` over `e`** (`locConjBar_algebraMap`), and
  `locConjGal`: **`φ_v : G_{K_v} ≃ₜ* G_{K_w}`**, `φ_v(σ) = Ē σ Ē⁻¹` (`locConjGal_apply`).
* (c) `locConj_locMap`: **`p_w(φ_v σ) = g · c(p_v σ) · g⁻¹`** for one `g ∈ G_{K,S}` and all
  `σ`, where `p_v = locMap K S v` (lane RC26). The exact form is `locConj_locMap_rep`:
  `p_w(φ_v σ) = τ' p_v(σ) τ'⁻¹` for the representative `τ' = τ ∘ h⁻¹` (`h ∈ Gal(K̄/K)`),
  which is the restriction of `Ē` to `K̄`: `Ē ∘ j_v = j_w ∘ τ'` for the decomposition
  embeddings `j_v = decompLift K v` (lane RC26); and `conjGKS_locConjRep`: conjugation by `τ'`
  on `G_{K,S}` is `x ↦ g c(x) g⁻¹` with `g = c(h|_{K_S})⁻¹`.
* (e) `locConj_fixed`: at a fixed place (`conjPlace κ v = v`) the same construction is the
  local representative of conjugation: `e_v ∈ Aut_cont(K_v)` extends `κ`, `Ē_v ∈ Aut(K̄_v)`
  lies over `e_v`, `φ_v = Ē_v (·) Ē_v⁻¹`, and `Ē_v` restricts on `K̄` to the representative
  `τ_v = τ ∘ h⁻¹` of conjugation, with `p_v(φ_v σ) = τ_v p_v(σ) τ_v⁻¹` exactly.

Kinds: definitions (DEF) and PROVED theorems. No PRINT or GLUE hypothesis is used in this file.
The only hypotheses are lane RC28's structure `ActualConj` (non-vacuous:
`actualConj_nonempty_gaussian`), the equation `hvw` (non-vacuous: `rfl` at `w = conjPlace κ v`)
and, in (e), `conjPlace κ v = v` (non-vacuous: `conjTransportNV_fixedPlace`, the place above `2`
of `ℚ(i)`, in `ConjTransport.lean`).

DEPARTURES (form; each also flagged at the declaration):
* D1. The local conjugation `φ_v` and the decomposition maps use Mathlib's arbitrary embeddings
  of algebraic closures (`IsAlgClosed.lift`, inside `Field.absoluteGaloisGroup.map`; lane RC26's
  `decompMap`; Nekovář, *Selmer complexes*, 5.1 also fixes embeddings, locator as cited by lane
  RC26, UNVERIFIED here). Hence the compatibility
  of `φ_v` with the global conjugation `c` holds up to the inner automorphism by `g` (c); the
  text does not mention it. Decomposition groups are only defined up to conjugacy, so this is
  the exact form of "transported from the conjugate place".
* D2. "The actual local representative of conjugation" (tex 2812) is realized as the
  automorphism `Ē_v` of `K̄_v` over the continuous automorphism `e_v` of `K_v` extending `κ`,
  and its restriction `τ_v = τ ∘ h⁻¹` to `K̄`; `τ_v` is not claimed to be an involution, and it is
  not presented as an element of a decomposition group inside `G_ℚ` (no `ℚ_p`-structure on
  `K_v` is used).
* D3. `τ ∈ G_ℚ` of the text is RC28's ring automorphism `τ` of `K̄ = AlgebraicClosure K` over
  `κ = τ|_K`; places are height-one primes of `𝓞_K`, and `τv` is `conjPlace κ v`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside GaloisGroupS resAbs resAbs_apply_coe
  resAbs_surjective)

variable {K : Type} [Field K] [NumberField K]

/-! ### (a) The conjugate completion `K_v ≃+* K_{κv}` -/

/-- The automorphism of `K` induced by `κ` on the fraction field of `𝓞_K` is `κ`.
Kind: PROVED. -/
theorem locConj_fractionRing (κ : K ≃+* K) :
    (IsFractionRing.ringEquivOfRingEquiv (RingOfIntegers.mapRingEquiv κ) : K ≃+* K) = κ := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 K)) (S := K) (RingHom.ext fun r ↦ ?_)
  simp [RingOfIntegers.mapRingEquiv_apply]

/-- **`κ` carries the `v`-adic valuation to the `κv`-adic valuation**: for `w = κ(v)` (as prime
ideals of `𝓞_K`), `|κ x|_w = |x|_v`. Kind: PROVED (Tau Ceti's transport of adic valuations
along ring isomorphisms of Dedekind domains, `valuation_ringEquivOfRingEquiv`).

Hypothesis `hvw` (kind DEF): the defining equation of the conjugate place; it is `rfl` for
`w = conjPlace κ v` (tex 2810: "the conjugate place `τv`"), and it holds for `w = v` at a fixed
place (`locConjFixed_asIdeal`). -/
theorem locConj_valuation (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) (x : K) :
    w.valuation K (κ x) = v.valuation K x := by
  have h := valuation_ringEquivOfRingEquiv (K := K) (K' := K) (RingOfIntegers.mapRingEquiv κ)
    (v := v) (w := w) hvw x
  rwa [locConj_fractionRing] at h

/-- **(a) The ring isomorphism of completions `e : K_v ≃+* K_{κv}` induced by `κ`**: the
continuous extension of the isometry `κ : (K, |·|_v) → (K, |·|_w)` (Tau Ceti's
`adicCompletionCongr`). Hypothesis `hvw`: kind DEF, see `locConj_valuation`. -/
def locConjCompletion (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    v.adicCompletion K ≃+* w.adicCompletion K :=
  adicCompletionCongr v w κ (locConj_valuation κ hvw)

/-- **`e` is compatible with `K → K_v` and `K → K_{κv}`**: `e(x) = κ(x)` for `x ∈ K`.
Kind: PROVED. -/
theorem locConjCompletion_algebraMap (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) (x : K) :
    locConjCompletion κ hvw (algebraMap K (v.adicCompletion K) x) =
      algebraMap K (w.adicCompletion K) (κ x) :=
  adicCompletionCongr_algebraMap _ x

/-- `e⁻¹(κ c) = c` on `K`. Kind: PROVED. -/
theorem locConjCompletion_symm_algebraMap (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) (c : K) :
    (locConjCompletion κ hvw).symm (algebraMap K (w.adicCompletion K) (κ c)) =
      algebraMap K (v.adicCompletion K) c := by
  rw [RingEquiv.symm_apply_eq, locConjCompletion_algebraMap]

/-- `e` is continuous. Kind: PROVED. -/
theorem locConjCompletion_continuous (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    Continuous (locConjCompletion κ hvw) :=
  continuous_adicCompletionCongr _

/-- `e` carries the valuation of `K_v` to that of `K_{κv}`. Kind: PROVED. -/
theorem locConjCompletion_valued (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (x : v.adicCompletion K) :
    Valued.v (locConjCompletion κ hvw x) = Valued.v x :=
  valued_adicCompletionCongr (locConj_valuation κ hvw) x

/-- **`e` is induced by `κ`**: it is the only continuous ring homomorphism `K_v → K_{κv}`
extending `κ`. Kind: PROVED. -/
theorem locConjCompletion_unique (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    {f : v.adicCompletion K →+* w.adicCompletion K} (hf : Continuous f)
    (hfK : ∀ x : K, f (algebraMap K _ x) = algebraMap K (w.adicCompletion K) (κ x)) :
    f = (locConjCompletion κ hvw).toRingHom :=
  eq_adicCompletionCongr_of_continuous (locConj_valuation κ hvw) hf hfK

/-! ### (b) The local conjugation `φ_v : G_{K_v} ≃ₜ* G_{K_{κv}}` -/

/-- The embedding of algebraic closures `J : K̄_{κv} → K̄_v` over `e⁻¹ : K_{κv} → K_v` chosen by
Mathlib's `Field.absoluteGaloisGroup.map` along `e⁻¹` (`IsAlgClosed.lift`). DEPARTURE D1: an
arbitrary choice, as in lane RC26's decomposition maps. -/
def locConjLift (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    AlgebraicClosure (w.adicCompletion K) →+* AlgebraicClosure (v.adicCompletion K) :=
  letI : Algebra (w.adicCompletion K) (v.adicCompletion K) :=
    (locConjCompletion κ hvw).symm.toRingHom.toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure (w.adicCompletion K) →ₐ[w.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)).toRingHom

/-- **(b) The local conjugation `φ_v : G_{K_v} ≃ₜ* G_{K_{κv}}`**: Mathlib's continuous map of
absolute Galois groups along the field isomorphism `e⁻¹ : K_{κv} ≃+* K_v`, an isomorphism of
topological groups (Tau Ceti's `absoluteGaloisGroupMapEquiv`). By `locConjGal_apply` it is
`σ ↦ Ē σ Ē⁻¹` for the extension `Ē = locConjBar` of `e` to the algebraic closures. -/
def locConjGal (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    Gloc K v ≃ₜ* Gloc K w :=
  TauCeti.absoluteGaloisGroupMapEquiv (locConjCompletion κ hvw).symm

/-- `J (φ_v(σ) x) = σ (J x)`. Kind: PROVED. -/
theorem locConjLift_locConjGal (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (σ : Gloc K v) (x : AlgebraicClosure (w.adicCompletion K)) :
    locConjLift κ hvw (@id (AlgebraicClosure (w.adicCompletion K) ≃ₐ[w.adicCompletion K]
        AlgebraicClosure (w.adicCompletion K)) (locConjGal κ hvw σ) x) =
      @id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
        AlgebraicClosure (v.adicCompletion K)) σ (locConjLift κ hvw x) := by
  let _ : Algebra (w.adicCompletion K) (v.adicCompletion K) :=
    (locConjCompletion κ hvw).symm.toRingHom.toAlgebra
  let g : AlgebraicClosure (w.adicCompletion K) →ₐ[w.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K) := IsAlgClosed.lift
  let _ : Algebra (AlgebraicClosure (w.adicCompletion K)) (AlgebraicClosure (v.adicCompletion K)) :=
    g.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalarsHom (w.adicCompletion K)
    (@id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K)) σ)) (AlgebraicClosure (w.adicCompletion K)) x

/-- `J` lies over `e⁻¹`. Kind: PROVED. -/
theorem locConjLift_algebraMap (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (a : w.adicCompletion K) :
    locConjLift κ hvw (algebraMap (w.adicCompletion K) (AlgebraicClosure (w.adicCompletion K)) a) =
      algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        ((locConjCompletion κ hvw).symm a) := by
  let _ : Algebra (w.adicCompletion K) (v.adicCompletion K) :=
    (locConjCompletion κ hvw).symm.toRingHom.toAlgebra
  exact (IsAlgClosed.lift : AlgebraicClosure (w.adicCompletion K) →ₐ[w.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K)).commutes a

/-- `J` is bijective (`K̄_v` is algebraic over the image of `K_{κv}`, and `K̄_{κv}` is
algebraically closed). Kind: PROVED. -/
theorem locConjLift_bijective (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    Function.Bijective (locConjLift κ hvw) := by
  let _ : Algebra (w.adicCompletion K) (v.adicCompletion K) :=
    (locConjCompletion κ hvw).symm.toRingHom.toAlgebra
  let g : AlgebraicClosure (w.adicCompletion K) →ₐ[w.adicCompletion K]
    AlgebraicClosure (v.adicCompletion K) := IsAlgClosed.lift
  let _ : Algebra (AlgebraicClosure (w.adicCompletion K)) (AlgebraicClosure (v.adicCompletion K)) :=
    g.toAlgebra
  have : IsScalarTower (w.adicCompletion K) (AlgebraicClosure (w.adicCompletion K))
      (AlgebraicClosure (v.adicCompletion K)) :=
    IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  have h : Function.Bijective (algebraMap (w.adicCompletion K) (v.adicCompletion K)) :=
    (locConjCompletion κ hvw).symm.bijective
  have : Algebra.IsIntegral (w.adicCompletion K) (v.adicCompletion K) :=
    Algebra.isIntegral_of_surjective h.2
  have : Algebra.IsIntegral (w.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) :=
    Algebra.IsIntegral.trans (v.adicCompletion K)
  have : Algebra.IsIntegral (AlgebraicClosure (w.adicCompletion K))
      (AlgebraicClosure (v.adicCompletion K)) :=
    Algebra.IsIntegral.tower_top (w.adicCompletion K)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- **(b) The extension `Ē : K̄_v ≃+* K̄_{κv}` of `e` to the algebraic closures**: the inverse
of `J`. -/
def locConjBar (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    AlgebraicClosure (v.adicCompletion K) ≃+* AlgebraicClosure (w.adicCompletion K) :=
  (RingEquiv.ofBijective (locConjLift κ hvw) (locConjLift_bijective κ hvw)).symm

/-- `J ∘ Ē = id`. Kind: PROVED. -/
theorem locConjLift_locConjBar (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (y : AlgebraicClosure (v.adicCompletion K)) :
    locConjLift κ hvw (locConjBar κ hvw y) = y :=
  (RingEquiv.ofBijective (locConjLift κ hvw) (locConjLift_bijective κ hvw)).apply_symm_apply y

/-- `Ē ∘ J = id`. Kind: PROVED. -/
theorem locConjBar_locConjLift (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (x : AlgebraicClosure (w.adicCompletion K)) :
    locConjBar κ hvw (locConjLift κ hvw x) = x :=
  (RingEquiv.ofBijective (locConjLift κ hvw) (locConjLift_bijective κ hvw)).symm_apply_apply x

/-- **`Ē` extends `e`**: `Ē(a) = e(a)` for `a ∈ K_v`. Kind: PROVED. -/
theorem locConjBar_algebraMap (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (a : v.adicCompletion K) :
    locConjBar κ hvw (algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) a) =
      algebraMap (w.adicCompletion K) (AlgebraicClosure (w.adicCompletion K))
        (locConjCompletion κ hvw a) := by
  apply (locConjLift_bijective κ hvw).1
  rw [locConjLift_locConjBar, locConjLift_algebraMap, RingEquiv.symm_apply_apply]

/-- **`φ_v` is conjugation by `Ē`**: `φ_v(σ)(y) = Ē (σ (Ē⁻¹ y))`. Kind: PROVED. -/
theorem locConjGal_apply (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (σ : Gloc K v) (y : AlgebraicClosure (w.adicCompletion K)) :
    @id (AlgebraicClosure (w.adicCompletion K) ≃ₐ[w.adicCompletion K]
        AlgebraicClosure (w.adicCompletion K)) (locConjGal κ hvw σ) y =
      locConjBar κ hvw (@id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
        AlgebraicClosure (v.adicCompletion K)) σ ((locConjBar κ hvw).symm y)) := by
  apply (locConjLift_bijective κ hvw).1
  rw [locConjLift_locConjGal, locConjLift_locConjBar]
  congr 1

/-! ### (c) Compatibility with the global conjugation, up to an inner automorphism -/

/-- Lane RC26's decomposition embedding `j_v : K̄ → K̄_v` (`decompLift`) as a `K`-algebra map. -/
def locConjDecompAlg (v : HeightOneSpectrum (𝓞 K)) :
    AlgebraicClosure K →ₐ[K] AlgebraicClosure (v.adicCompletion K) :=
  ⟨decompLift K v, decompLift_algebraMap K v⟩

/-- The second `K`-embedding `J ∘ j_{κv} ∘ τ : K̄ → K̄_v` (it is `K`-linear because `τ` lies over
`κ`, `j_{κv}` over `K → K_{κv}`, and `J` over `e⁻¹`). -/
def locConjAlg (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (κ x))
    {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    AlgebraicClosure K →ₐ[K] AlgebraicClosure (v.adicCompletion K) :=
  ⟨(locConjLift κ hvw).comp ((decompLift K w).comp (τ : AlgebraicClosure K →+* AlgebraicClosure K)),
    fun c => by
      change locConjLift κ hvw (decompLift K w (τ (algebraMap K (AlgebraicClosure K) c))) = _
      rw [hτ, decompLift_algebraMap,
        IsScalarTower.algebraMap_apply K (w.adicCompletion K)
          (AlgebraicClosure (w.adicCompletion K)),
        locConjLift_algebraMap, locConjCompletion_symm_algebraMap,
        ← IsScalarTower.algebraMap_apply]⟩

/-- **The two embeddings differ by an element of `Gal(K̄/K)`**: there is `h` with
`j_v ∘ h = J ∘ j_{κv} ∘ τ` (two `K`-embeddings of the normal extension `K̄/K` into `K̄_v`; Tau
Ceti's `AlgHom.exists_comp_eq_of_normal`). Kind: PROVED. -/
theorem locConj_exists_comp (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (κ x))
    {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    ∃ h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ x : AlgebraicClosure K,
      decompLift K v (h x) = locConjLift κ hvw (decompLift K w (τ x)) := by
  obtain ⟨h, hh⟩ := AlgHom.exists_comp_eq_of_normal (locConjDecompAlg v) (locConjAlg κ τ hτ hvw)
  exact ⟨h, fun x => DFunLike.congr_fun hh x⟩

/-- **The comparison element `h ∈ Gal(K̄/K)`**, `j_v ∘ h = J ∘ j_{κv} ∘ τ`; it is unique
(`locConjElt_unique`), so this choice is canonical. -/
def locConjElt (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (κ x))
    {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  Classical.choose (locConj_exists_comp κ τ hτ hvw)

/-- The defining property of `locConjElt`. Kind: PROVED. -/
theorem locConjElt_spec (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (κ x))
    {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (x : AlgebraicClosure K) :
    decompLift K v (locConjElt κ τ hτ hvw x) = locConjLift κ hvw (decompLift K w (τ x)) :=
  Classical.choose_spec (locConj_exists_comp κ τ hτ hvw) x

/-- `locConjElt` is the only element with its defining property (`j_v` is injective).
Kind: PROVED. -/
theorem locConjElt_unique (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (κ x))
    {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hh : ∀ x, decompLift K v (h x) = locConjLift κ hvw (decompLift K w (τ x))) :
    h = locConjElt κ τ hτ hvw :=
  AlgEquiv.ext fun x =>
    (decompLift K v).injective ((hh x).trans (locConjElt_spec κ τ hτ hvw x).symm)

/-- **The decomposition maps**: `d_{κv}(φ_v σ) = τ (h⁻¹ d_v(σ) h) τ⁻¹` in `Gal(K̄/K)`, for
`d_v = decompMap K v` (lane RC26) and the comparison element `h`. Kind: PROVED. -/
theorem locConj_decompMap (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (κ x))
    {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hh : ∀ x, decompLift K v (h x) = locConjLift κ hvw (decompLift K w (τ x))) (σ : Gloc K v) :
    decompMap K w (locConjGal κ hvw σ) =
      conjAbs K κ τ hτ (h⁻¹ * @id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (decompMap K v σ) * h) := by
  apply AlgEquiv.ext
  intro y
  apply (decompLift K w).injective
  apply (locConjLift κ hvw).injective
  set s := @id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K v σ) with hs
  have e1 : locConjLift κ hvw (decompLift K w
      (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K w (locConjGal κ hvw σ)) y)) =
      @id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
        AlgebraicClosure (v.adicCompletion K)) σ (locConjLift κ hvw (decompLift K w y)) := by
    rw [decompLift_decompMap, locConjLift_locConjGal]
  have e2 : (conjAbs K κ τ hτ (h⁻¹ * s * h)) y = τ (h.symm (s (h (τ.symm y)))) := rfl
  have e3 : decompLift K v (s (h (τ.symm y))) =
      @id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
        AlgebraicClosure (v.adicCompletion K)) σ (decompLift K v (h (τ.symm y))) :=
    decompLift_decompMap K v σ _
  change locConjLift κ hvw (decompLift K w
      (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K w (locConjGal κ hvw σ)) y)) =
    locConjLift κ hvw (decompLift K w ((conjAbs K κ τ hτ (h⁻¹ * s * h)) y))
  rw [e1, e2, ← hh, AlgEquiv.apply_symm_apply, e3, hh, RingEquiv.apply_symm_apply]

/-- **The representative of conjugation `τ' = τ ∘ h⁻¹`** attached to `h ∈ Gal(K̄/K)`; it lies
over `κ` (`locConjRep_algebraMap`) and lies in the coset `τ · Gal(K̄/K)`. -/
def locConjRep (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : AlgebraicClosure K ≃+* AlgebraicClosure K :=
  h.symm.toRingEquiv.trans τ

omit [NumberField K] in
/-- `τ' x = τ (h⁻¹ x)`. Kind: PROVED. -/
theorem locConjRep_apply (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K) :
    locConjRep τ h x = τ (h.symm x) := rfl

omit [NumberField K] in
/-- `τ'⁻¹ x = h (τ⁻¹ x)`. Kind: PROVED. -/
theorem locConjRep_symm_apply (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K) :
    (locConjRep τ h).symm x = h (τ.symm x) := rfl

omit [NumberField K] in
/-- `τ'` lies over `κ`. Kind: PROVED. -/
theorem locConjRep_algebraMap (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (κ x))
    (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : K) :
    locConjRep τ h (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (κ x) := by
  rw [locConjRep_apply, AlgEquiv.commutes, hτ]

omit [NumberField K] in
/-- Conjugation by `τ' = τ ∘ h⁻¹` on `Gal(K̄/K)` is `y ↦ τ (h⁻¹ y h) τ⁻¹`. Kind: PROVED. -/
theorem conjAbs_locConjRep (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (κ x))
    (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (y : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    conjAbs K κ (locConjRep τ h) (locConjRep_algebraMap κ τ hτ h) y =
      conjAbs K κ τ hτ (h⁻¹ * y * h) := by
  apply AlgEquiv.ext
  intro x
  rfl

/-- **The exact form at the level of `Gal(K̄/K)`**: for the comparison element `h`, the
representative `τ' = τ ∘ h⁻¹` is the restriction of `Ē` to `K̄` (`Ē ∘ j_v = j_{κv} ∘ τ'`), and
`d_{κv}(φ_v σ) = τ' d_v(σ) τ'⁻¹` for all `σ`. Kind: PROVED. -/
theorem locConj_rep (κ : K ≃+* K) (τ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (κ x))
    {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K)) :
    ∃ h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (∀ x, locConjBar κ hvw (decompLift K v x) = decompLift K w (locConjRep τ h x)) ∧
      ∀ σ : Gloc K v, decompMap K w (locConjGal κ hvw σ) =
        conjAbs K κ (locConjRep τ h) (locConjRep_algebraMap κ τ hτ h)
          (@id (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (decompMap K v σ)) := by
  obtain ⟨h, hh⟩ := locConj_exists_comp κ τ hτ hvw
  refine ⟨h, fun x => ?_, fun σ => ?_⟩
  · have : locConjLift κ hvw (decompLift K w (locConjRep τ h x)) = decompLift K v x := by
      rw [locConjRep_apply, ← hh, AlgEquiv.apply_symm_apply]
    rw [← this, locConjBar_locConjLift]
  · rw [conjAbs_locConjRep, locConj_decompMap κ τ hτ hvw h hh σ]

/-- The representative is determined by `Ē`: a ring automorphism `τ''` of `K̄` with
`Ē ∘ j_v = j_{κv} ∘ τ''` equals `τ'` (`j_{κv}` is injective). Kind: PROVED. -/
theorem locConjRep_eq_of_bar (κ : K ≃+* K) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K))
    (τ₁ τ₂ : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (h₁ : ∀ x, locConjBar κ hvw (decompLift K v x) = decompLift K w (τ₁ x))
    (h₂ : ∀ x, locConjBar κ hvw (decompLift K v x) = decompLift K w (τ₂ x)) : τ₁ = τ₂ :=
  RingEquiv.ext fun x => (decompLift K w).injective ((h₁ x).symm.trans (h₂ x))

variable {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **(c), for a given comparison element `h`**: with `g = c(h|_{K_S})⁻¹ ∈ G_{K,S}`,
`p_{κv}(φ_v σ) = g · c(p_v σ) · g⁻¹` for all `σ ∈ G_{K_v}`, where `p_v = locMap K S v`
(lane RC26) and `c = C.conj` (lane RC28). Kind: PROVED. DEPARTURE D1 (the inner automorphism by
`g`). -/
theorem locConj_locMap_of (C : ActualConj K S) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hh : ∀ x, decompLift K v (h x) = locConjLift C.κ hvw (decompLift K w (C.τ x)))
    (σ : Gloc K v) :
    locMap K S w (locConjGal C.κ hvw σ) =
      (C.conj (resAbs K S h))⁻¹ * C.conj (locMap K S v σ) * (C.conj (resAbs K S h))⁻¹⁻¹ := by
  have e1 : locMap K S w (locConjGal C.κ hvw σ) =
      resAbs K S (decompMap K w (locConjGal C.κ hvw σ)) := rfl
  have e2 : locMap K S v σ = resAbs K S (decompMap K v σ) := rfl
  rw [e1, locConj_decompMap C.κ C.τ C.hτ hvw h hh σ, resAbs_conjAbs K C.κ C.τ C.hτ S C.hS, e2,
    inv_inv]
  rw [map_mul (resAbs K S), map_mul (resAbs K S), map_inv (resAbs K S)]
  show C.conj ((@id (GKS K S) (resAbs K S h))⁻¹ * @id (GKS K S) (resAbs K S (decompMap K v σ)) *
    @id (GKS K S) (resAbs K S h)) = _
  rw [map_mul, map_mul, map_inv]
  rfl

/-- **(c) The compatibility of the local conjugation with the global conjugation of `G_{K,S}`**:
there is `g ∈ G_{K,S}` with `p_{κv}(φ_v σ) = g · c(p_v σ) · g⁻¹` for all `σ ∈ G_{K_v}`
(`g = c(h|_{K_S})⁻¹` for the comparison element `h`, `locConj_locMap_of`). Since the embeddings
at `v` and `κv` are chosen independently, this is the true statement (DEPARTURE D1); the exact
form without `g`, through the representative `τ' = τ ∘ h⁻¹`, is `locConj_locMap_rep`.
Hypotheses: `C` (lane RC28's `ActualConj`, non-vacuous), `hvw` (DEF, see `locConj_valuation`).
Kind: PROVED. -/
theorem locConj_locMap (C : ActualConj K S) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K)) :
    ∃ g : GKS K S, ∀ σ : Gloc K v,
      locMap K S w (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v σ) * g⁻¹ :=
  ⟨_, locConj_locMap_of C hvw (locConjElt C.κ C.τ C.hτ hvw) (locConjElt_spec C.κ C.τ C.hτ hvw)⟩

/-- (c) at the conjugate place itself: `w = conjPlace κ v` (tex 2810, "the conjugate place
`τv`"). Kind: PROVED. -/
theorem locConj_locMap_conjPlace (C : ActualConj K S) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ g : GKS K S, ∀ σ : Gloc K v,
      locMap K S (conjPlace C.κ v) (locConjGal C.κ (v := v) (w := conjPlace C.κ v) rfl σ) =
        g * C.conj (locMap K S v σ) * g⁻¹ :=
  locConj_locMap C rfl

/-- **(c), exact form**: for the comparison element `h` and the representative
`τ' = τ ∘ h⁻¹` (the restriction of `Ē` to `K̄`), `p_{κv}(φ_v σ) = τ' p_v(σ) τ'⁻¹` in `G_{K,S}`
(conjugation by `τ'` is RC28's `conjGKS` for `τ'`). Kind: PROVED. -/
theorem locConj_locMap_rep (C : ActualConj K S) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K)) :
    ∃ h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (∀ x, locConjBar C.κ hvw (decompLift K v x) = decompLift K w (locConjRep C.τ h x)) ∧
      ∀ σ : Gloc K v, locMap K S w (locConjGal C.κ hvw σ) =
        conjGKS K C.κ (locConjRep C.τ h) (locConjRep_algebraMap C.κ C.τ C.hτ h) S C.hS
          (locMap K S v σ) := by
  obtain ⟨h, hbar, hdec⟩ := locConj_rep C.κ C.τ C.hτ hvw
  refine ⟨h, hbar, fun σ => ?_⟩
  have e1 : locMap K S w (locConjGal C.κ hvw σ) =
      resAbs K S (decompMap K w (locConjGal C.κ hvw σ)) := rfl
  rw [e1, hdec σ, resAbs_conjAbs K C.κ (locConjRep C.τ h) (locConjRep_algebraMap C.κ C.τ C.hτ h) S
    C.hS]
  rfl

/-- **Conjugation by the representative is conjugation by `τ` up to an inner automorphism**:
for `τ' = τ ∘ h⁻¹` and `g = c(h|_{K_S})⁻¹`, `τ' x τ'⁻¹ = g · c(x) · g⁻¹` on `G_{K,S}`.
Kind: PROVED. -/
theorem conjGKS_locConjRep (C : ActualConj K S) (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : GKS K S) :
    conjGKS K C.κ (locConjRep C.τ h) (locConjRep_algebraMap C.κ C.τ C.hτ h) S C.hS x =
      (C.conj (resAbs K S h))⁻¹ * C.conj x * (C.conj (resAbs K S h))⁻¹⁻¹ := by
  obtain ⟨y, rfl⟩ := resAbs_surjective K S x
  rw [← resAbs_conjAbs K C.κ (locConjRep C.τ h) (locConjRep_algebraMap C.κ C.τ C.hτ h) S C.hS,
    conjAbs_locConjRep C.κ C.τ C.hτ h, resAbs_conjAbs K C.κ C.τ C.hτ S C.hS, inv_inv,
    map_mul (resAbs K S), map_mul (resAbs K S), map_inv (resAbs K S)]
  show C.conj ((@id (GKS K S) (resAbs K S h))⁻¹ * @id (GKS K S) (resAbs K S y) *
    @id (GKS K S) (resAbs K S h)) = _
  rw [map_mul, map_mul, map_inv]
  rfl

/-! ### (e) Fixed places: the actual local representative of conjugation -/

omit [NumberField K] in
/-- **A fixed place** (`conjPlace κ v = v`, tex 2811–2812: "At a fixed place") satisfies the
hypothesis `hvw` with `w = v`. Hypothesis `hfix`: kind ELLIOT (the case distinction of
tex 2810–2812); non-vacuous (`conjTransportNV_fixedPlace`). Kind: PROVED. -/
theorem locConjFixed_asIdeal (κ : K ≃+* K) {v : HeightOneSpectrum (𝓞 K)}
    (hfix : conjPlace κ v = v) :
    v.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv κ : 𝓞 K →+* 𝓞 K) :=
  (congrArg HeightOneSpectrum.asIdeal hfix).symm

/-- **(e) At a fixed place the construction is the actual local representative of
conjugation** (tex 2811–2812). For `conjPlace κ v = v`:
* `e_v : K_v ≃+* K_v` is a continuous automorphism extending `κ`;
* `Ē_v : K̄_v ≃+* K̄_v` lies over `e_v`, and `φ_v(σ) = Ē_v σ Ē_v⁻¹`;
* for the comparison element `h`, `Ē_v` restricts on `K̄` (through `j_v`) to the representative
  `τ_v = τ ∘ h⁻¹` of conjugation, `p_v(φ_v σ) = τ_v p_v(σ) τ_v⁻¹` exactly, and conjugation by
  `τ_v` is `x ↦ g c(x) g⁻¹` with `g = c(h|_{K_S})⁻¹`.
Hypothesis `hfix`: ELLIOT, non-vacuous (see `locConjFixed_asIdeal`). DEPARTURE D2. Kind: PROVED. -/
theorem locConj_fixed (C : ActualConj K S) {v : HeightOneSpectrum (𝓞 K)}
    (hfix : conjPlace C.κ v = v) :
    Continuous (locConjCompletion C.κ (locConjFixed_asIdeal C.κ hfix)) ∧
    (∀ x : K, locConjCompletion C.κ (locConjFixed_asIdeal C.κ hfix)
        (algebraMap K (v.adicCompletion K) x) = algebraMap K (v.adicCompletion K) (C.κ x)) ∧
    (∀ a : v.adicCompletion K, locConjBar C.κ (locConjFixed_asIdeal C.κ hfix)
        (algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) a) =
      algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (locConjCompletion C.κ (locConjFixed_asIdeal C.κ hfix) a)) ∧
    (∀ (σ : Gloc K v) (y : AlgebraicClosure (v.adicCompletion K)),
      @id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
          AlgebraicClosure (v.adicCompletion K))
          (locConjGal C.κ (locConjFixed_asIdeal C.κ hfix) σ) y =
        locConjBar C.κ (locConjFixed_asIdeal C.κ hfix)
          (@id (AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
            AlgebraicClosure (v.adicCompletion K)) σ
              ((locConjBar C.κ (locConjFixed_asIdeal C.κ hfix)).symm y))) ∧
    ∃ h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (∀ x, locConjBar C.κ (locConjFixed_asIdeal C.κ hfix) (decompLift K v x) =
        decompLift K v (locConjRep C.τ h x)) ∧
      (∀ σ : Gloc K v, locMap K S v (locConjGal C.κ (locConjFixed_asIdeal C.κ hfix) σ) =
        conjGKS K C.κ (locConjRep C.τ h) (locConjRep_algebraMap C.κ C.τ C.hτ h) S C.hS
          (locMap K S v σ)) ∧
      ∀ x : GKS K S,
        conjGKS K C.κ (locConjRep C.τ h) (locConjRep_algebraMap C.κ C.τ C.hτ h) S C.hS x =
          (C.conj (resAbs K S h))⁻¹ * C.conj x * (C.conj (resAbs K S h))⁻¹⁻¹ := by
  obtain ⟨h, h1, h2⟩ := locConj_locMap_rep C (locConjFixed_asIdeal C.κ hfix)
  exact ⟨locConjCompletion_continuous _ _, locConjCompletion_algebraMap _ _,
    locConjBar_algebraMap _ _, locConjGal_apply _ _, h, h1, h2, conjGKS_locConjRep C h⟩

end ZInQ.Manuscript.RC.KummerMaps
