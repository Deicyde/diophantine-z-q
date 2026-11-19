import ZInQKernel.Contrib.OneProof.RC.KummerMaps.LocalConj
import ZInQKernel.Contrib.OneProof.RC.CoefModules.LocalConditions
import ZInQKernel.Contrib.OneProof.RC.CoefModules.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchLeaf

/-!
# Lane RC29, item 5 (part 2): transport of local conditions from the conjugate place

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-conjugate-duality` (tex 2761–2830), proof,
tex 2810–2812:

> At a split place `v`, the dual local condition is transported from the conjugate place `τv`.
> At a fixed place it is transported by the actual local representative of conjugation.

with the coefficient identification `τ^*M_i ≃ M_i^*(1)` of tex 2765, 2805 (lane RC28's
`conjDualEquiv`) and "the conjugate places" of tex 2767, 2823.

* (d) `conjTransportIso`: **the cochain isomorphism**
  `C^•_cont(G_{K_{κv}}, M) ≅ C^•_cont(G_{K_v}, τ^*M)`, `c ↦ g⁻¹ · c ∘ φ_vⁿ`, induced by the local
  conjugation `φ_v` (`LocalConj.lean`) and `m ↦ g⁻¹m`, for any `g` with
  `p_{κv}(φ_v σ) = g c(p_v σ) g⁻¹` (`locConj_locMap`). `conjTransport`: **a local condition at
  `κv` for `M` gives one at `v` for `τ^*M = PullMod C.conj M`**; it preserves injectivity
  (`conjTransport_isInjective`), sends zero to zero (`conjTransport_zeroAt`, an equality) and
  full to full (`conjTransport_fullAt_apply`, `conjTransport_fullAt_bijective`: the transported
  full condition is the full local complex at `κv`, mapped isomorphically onto the full local
  complex at `v`).
* The split case (tex 2810–2811), `conjTransportConjPlace`, at `w = conjPlace κ v`; the fixed case
  (tex 2811–2812), `conjTransportFixed`, at `w = v`; the canonical `g` is `conjTransportElt`.
* (e) `conjTransport_eq_rep`, `conjTransportFixed_rep`: **the same construction is the transport
  by the representative of conjugation**: it factors as `c ↦ c ∘ φ_v` into
  `C^•(G_{K_v}, τ'^*M)` (no inner automorphism: `p_{κv}(φ_v σ) = τ' p_v(σ) τ'⁻¹`) followed by the
  coefficient comparison `τ'^*M ≅ τ^*M`, `m ↦ g⁻¹m`; at a fixed place `τ' = τ_v` is the
  restriction of the local automorphism `Ē_v` of `K̄_v` to `K̄` (`locConj_fixed`), the actual local
  representative of conjugation.
* **Conjugate transport to the coefficient dual `M_i^*(1)` (tex 2810–2812)**: `conjTransportDual`
  composes `conjTransport` with the coefficient change `conjTransportCoef` along RC28's
  `conjDualEquiv : τ^*M_i ≃ M_i^*(1)`: from the condition `U_{τv}` at `τv` for `M_i` it gives a
  condition at `v` for `M_i^*(1)`. `conjTransportDualAt` does this at every place of `S` (split:
  from `τv`; fixed: from `v` itself through the local representative), and
  `conjTransportDualConditions` assembles lane RC26's local conditions for `M_i^*(1)`; the
  resulting Selmer data on `M_i^*(1)` are genuine (`conjTransportDual_isGaloisSelData`). These are
  transported conditions on the coefficient dual, not the orthogonal complement `U^⊥`: zero goes to
  zero and full to full. To represent `U^⊥`, first supply the actual orthogonal system (Kummer at
  `2N`, zero against full, tex 2813–2815) and transport that system; lane RC29's round-3
  `conjActualLocalComplements` (`ConjComplements.lean`) proves that the transport of the actual
  orthogonal system is the orthogonal complement of the actual conditions.
* (f) Non-vacuity: `conjTransportNV_unique`, `conjTransportNV_fixedPlace` (the place above `2` of
  `ℚ(i)` is the only one and is fixed by every automorphism), `conjTransportNV_actualConj`,
  `conjTransportDual_nonvacuous` and `conjTransportNV_isGaloisSelData`: every hypothesis of
  `conjTransportDual` and of the assembled data is discharged at once for `K = ℚ(i)`, `S` the
  places above `2`, `E = E_1 : y² = x(x−1)(x+3)` (RC28's `curveEll 1`), `N = 2`, `A = ℤ/2`,
  `α = 1`.

Kinds: definitions (DEF) and PROVED theorems; no PRINT. Hypotheses, with their kinds (each is
also flagged at the declarations):
* `C : ActualConj K S`: lane RC28's actual complex conjugation (tex 2778); non-vacuous
  (`actualConj_nonempty_gaussian`).
* `hvw : w = κ(v)` as prime ideals: DEF (`rfl` at `w = conjPlace κ v`; `locConjFixed_asIdeal` at a
  fixed place `w = v`).
* `hg : p_{κv}(φ_v σ) = g c(p_v σ) g⁻¹`: PROVED satisfiable (`locConj_locMap`); the canonical
  choice is `conjTransportElt`. `hrep`, `hτg` (the factorization through a representative):
  PROVED satisfiable (`locConj_locMap_rep`, `conjGKS_locConjRep`).
* `hfix : conjPlace κ v = v`: ELLIOT (the case "fixed place", tex 2811); non-vacuous.
* `hFull : FullTorsion K S W N`: GLUE (lane RC28: Néron–Ogg–Shafarevich, Silverman AEC VII.7.1,
  reference as given by lane RC28); non-vacuous (`fullTorsion_two_curveEll`).
* `hα : α(c σ) = α(σ)⁻¹`: ELLIOT (tex 2786–2795, `α_i^τ = α_i^{-1}`), PROVED by RC28 for the actual
  `α_i` (`alphaChar_conj`); non-vacuous (`α = 1`).
* `hW : W.map κ = W`: lane RC28's DEPARTURE 3 (`E` over the fixed field of `κ`); non-vacuous.
* `[ContinuousSMul …]` on `M_i` and `M_i^*(1)`: discrete modules; non-vacuous through RC28's
  instances (`IsOpenKer α`, finiteness).

DEPARTURES (form):
* D1 (as in `LocalConj.lean`): the transport uses Mathlib's chosen embeddings, so the coefficient
  map is `m ↦ g⁻¹m` for the inner element `g` of `locConj_locMap`; the text does not mention `g`.
* D4. "The dual local condition is transported from the conjugate place": formalized as the
  transport of the given condition `U_{τv}` (for `M_i` at `τv`) to a condition at `v` for
  `τ^*M_i ≃ M_i^*(1)`. That this transported condition is the orthogonal complement `U_v^⊥` of
  `U_v` under local Tate duality is NOT proved here (the orthogonality inputs, lane RC28 "What
  remains" item 2; ELLIOT). For the pair full/zero it is consistent with tex 2813–2815: if
  `U_{τv}` is zero, the transported condition is zero, and if it is full, the transported
  condition is full.
* D5. The coefficient modules are discrete (`DiscreteTopology`), as the text's finite `M_i`.
* D6. `conjTransportDual` is stated for `M_i = (E(K_S)[N] ⊗ A)(α)` over `G_{K,S}` itself (RC28's
  `conjDualEquiv`), not for the inflation `MinS` from a smaller support `S₀`.
* Not covered here: "Kummer conditions at `2N` are preserved by this transport" (tex 2812–2813),
  and the derivative-prime checks (tex 2816–2820).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (GCx GHom)
open ZInQ.Contrib.CloudB3RC53.SelmerDuality (idGHom zeroGHom ghomComp)
open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs)

/-! ### Cochain isomorphisms of compatible pairs of isomorphisms -/

section Generic

variable {k : Type} [CommRing k] {G H : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
  [Group H] [TopologicalSpace H] [ContinuousMul H]
  {M N : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M]
  [AddCommGroup N] [Module k N] [DistribMulAction H N] [SMulCommClass H k N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul k N] [ContinuousSMul H N]

omit [ContinuousMul G] [ContinuousMul H] [SMulCommClass G k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul G M] [SMulCommClass H k N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul k N] [ContinuousSMul H N] in
/-- The inverse of a compatible pair of isomorphisms is a compatible pair. Kind: PROVED. -/
theorem locConjPair_symm (φ : H ≃ₜ* G) (f : M ≃ₗ[k] N)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) (g : G) (n : N) :
    f.symm (φ.symm g • n) = g • f.symm n := by
  have := hf (φ.symm g) (f.symm n)
  rw [ContinuousMulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
  rw [← this, LinearEquiv.symm_apply_apply]

/-- **The cochain isomorphism of a compatible pair of isomorphisms**: for a topological group
isomorphism `φ : H ≃ₜ* G` and a `k`-linear homeomorphism `f : M ≃ N` with
`f(φ(h) m) = h f(m)`, lane RC26's cochain maps `c ↦ f ∘ c ∘ φⁿ` and `c ↦ f⁻¹ ∘ c ∘ (φ⁻¹)ⁿ` are
inverse isomorphisms `C^•_cont(G, M) ≅ C^•_cont(H, N)`. Kind: DEF, inverse laws PROVED. -/
def locConjPairIso (φ : H ≃ₜ* G) (f : M ≃ₗ[k] N) (hfc : Continuous f) (hfc' : Continuous f.symm)
    (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    contCochains k G M ≅ contCochains k H N where
  hom := contCochainsMap ⟨φ.toMulEquiv.toMonoidHom, φ.continuous⟩ f.toLinearMap hfc hf
  inv := contCochainsMap ⟨φ.symm.toMulEquiv.toMonoidHom, φ.symm.continuous⟩ f.symm.toLinearMap
    hfc' (locConjPair_symm φ f hf)
  hom_inv_id := by
    ext n c
    apply Subtype.ext
    funext x
    change f.symm (f (asFun k G M ((contSubCx k G M).el c : contCochain k G M n)
      (fun i => φ (φ.symm (x i))))) = asFun k G M ((contSubCx k G M).el c : contCochain k G M n) x
    simp only [ContinuousMulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  inv_hom_id := by
    ext n c
    apply Subtype.ext
    funext x
    change f (f.symm (asFun k H N ((contSubCx k H N).el c : contCochain k H N n)
      (fun i => φ.symm (φ (x i))))) = asFun k H N ((contSubCx k H N).el c : contCochain k H N n) x
    simp only [ContinuousMulEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

end Generic

/-- The components of an isomorphism of cochain complexes of modules are bijective.
Kind: PROVED. -/
theorem locConjIso_f_bijective {k : Type} [CommRing k] {A B : CochainComplex (ModuleCat.{0} k) ℕ}
    (T : A ≅ B) (n : ℕ) : Function.Bijective (T.hom.f n).hom :=
  ((HomologicalComplex.eval (ModuleCat.{0} k) (ComplexShape.up ℕ) n).mapIso
    T).toLinearEquiv.bijective

/-- The extension by zero (lane RC26's `natHom`) of an isomorphism has bijective components in
every degree. Kind: PROVED. -/
theorem locConjNatHom_bijective {k : Type} [CommRing k] {A B : CochainComplex (ModuleCat.{0} k) ℕ}
    (T : A ≅ B) (n : ℤ) : Function.Bijective ((natHom T.hom).f n n rfl) := by
  rcases n with n | n
  · exact locConjIso_f_bijective T n
  · refine ⟨fun x y _ => Subsingleton.elim (α := PUnit) x y, fun y => ⟨0, ?_⟩⟩
    exact Subsingleton.elim (α := PUnit) _ _

/-! ### (d) The transport `C^•(G_{K_{κv}}, M) ≅ C^•(G_{K_v}, τ^*M)` and of local conditions -/

section Transport

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M]

/-- The coefficient map `M → τ^*M`, `m ↦ g⁻¹ m`, between `M` restricted along `p_{κv}` and
`τ^*M` restricted along `p_v`. -/
def conjTransportEquiv (g : GKS K S) (v w : HeightOneSpectrum (𝓞 K)) :
    ResMod (locMap K S w) M ≃ₗ[k] ResMod (locMap K S v) (PullMod C.conj M) where
  toFun m := show M from g⁻¹ • (show M from m)
  invFun n := show M from g • (show M from n)
  map_add' m m' := smul_add g⁻¹ (show M from m) (show M from m')
  map_smul' c m := smul_comm g⁻¹ c (show M from m)
  left_inv m := smul_inv_smul g (show M from m)
  right_inv n := inv_smul_smul g (show M from n)

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M] in
/-- **`(φ_v, m ↦ g⁻¹m)` is a compatible pair**: `g⁻¹(p_{κv}(φ_v σ) m) = c(p_v σ)(g⁻¹ m)`.
Hypothesis `hg`: PROVED satisfiable (`locConj_locMap`). Kind: PROVED. -/
theorem conjTransportEquiv_compat (g : GKS K S) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v,
      locMap K S w (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v σ) * g⁻¹)
    (σ : Gloc K v) (m : ResMod (locMap K S w) M) :
    conjTransportEquiv C k M g v w (locConjGal C.κ hvw σ • m) =
      σ • conjTransportEquiv C k M g v w m := by
  change g⁻¹ • (locMap K S w (locConjGal C.κ hvw σ) • (show M from m)) =
    C.conj (locMap K S v σ) • (g⁻¹ • (show M from m))
  rw [hg, mul_smul, mul_smul, inv_smul_smul]

/-- **(d) The cochain isomorphism `C^•_cont(G_{K_{κv}}, M) ≅ C^•_cont(G_{K_v}, τ^*M)`**,
`c ↦ g⁻¹ · c ∘ φ_vⁿ`, induced by the local conjugation `φ_v` and `m ↦ g⁻¹m` (tex 2810–2812).
Hypotheses: `hvw` (DEF), `hg` (PROVED satisfiable, `locConj_locMap`). DEPARTURE D1. -/
def conjTransportIso (g : GKS K S) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v,
      locMap K S w (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v σ) * g⁻¹) :
    contCochains k (Gloc K w) (ResMod (locMap K S w) M) ≅
      contCochains k (Gloc K v) (ResMod (locMap K S v) (PullMod C.conj M)) :=
  locConjPairIso (locConjGal C.κ hvw) (conjTransportEquiv C k M g v w)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (conjTransportEquiv_compat C k M g hvw hg)

variable {k M}

/-- The cochain isomorphism as a map of lane RC28's local complexes,
`locAt K S k M (κv) → locAt K S k (τ^*M) v`. -/
def conjTransportGHom (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹) :
    GHom (locAt K S k M w) (locAt K S k (PullMod C.conj M) v) :=
  natHom (conjTransportIso C k M g hvw hg).hom

/-- `conjTransportGHom` is bijective in every degree. Kind: PROVED. -/
theorem conjTransportGHom_bijective (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹) (n : ℤ) :
    Function.Bijective ((conjTransportGHom (k := k) (M := M) C g hvw hg).f n n rfl) :=
  locConjNatHom_bijective (conjTransportIso C k M g hvw hg) n

/-- **(d) The transport of local conditions** (tex 2810–2812): a local condition
`U → C^•_cont(G_{K_{κv}}, M)` at `κv` gives the local condition
`U → C^•_cont(G_{K_{κv}}, M) ≅ C^•_cont(G_{K_v}, τ^*M)` at `v` for `τ^*M = PullMod C.conj M`.
Hypotheses: `hvw` (DEF), `hg` (PROVED satisfiable). -/
def conjTransport (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹)
    (c : CondAt K S k M w) : CondAt K S k (PullMod C.conj M) v :=
  ⟨c.U, ghomComp c.i (conjTransportGHom C g hvw hg)⟩

/-- **The transport preserves injectivity** (subcomplexes go to subcomplexes). Kind: PROVED. -/
theorem conjTransport_isInjective (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹)
    (c : CondAt K S k M w) (hc : c.IsInjective) : (conjTransport C g hvw hg c).IsInjective :=
  fun n => (conjTransportGHom_bijective C g hvw hg n).1.comp (hc n)

/-- **The transport sends the zero condition to the zero condition** (an equality of local
conditions). Kind: PROVED. -/
theorem conjTransport_zeroAt (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹) :
    conjTransport C g hvw hg (zeroAt K S k M w) = zeroAt K S k (PullMod C.conj M) v := by
  have key : ∀ (a b : GHom (zeroCx k) (locAt K S k (PullMod C.conj M) v)), a.f = b.f → a = b := by
    rintro ⟨fa, ca⟩ ⟨fb, cb⟩ h
    subst h
    rfl
  change (⟨zeroCx k, ghomComp (zeroGHom _ _) (conjTransportGHom C g hvw hg)⟩ :
    CondAt K S k (PullMod C.conj M) v) = ⟨zeroCx k, zeroGHom _ _⟩
  congr 1
  apply key
  funext i j h
  subst h
  refine LinearMap.ext fun x => ?_
  change (conjTransportGHom C g hvw hg).f i i rfl 0 = 0
  exact map_zero _

/-- **The transport sends the full condition to the full condition**: the transported full
condition is the full local complex at `κv`, and its structure map is the full condition at `v`
composed with the cochain isomorphism (an isomorphism of local conditions onto `fullAt`).
Kind: PROVED. -/
theorem conjTransport_fullAt_apply (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹)
    (n : ℤ) (x : (locAt K S k M w).X n) :
    (conjTransport C g hvw hg (fullAt K S k M w)).i.f n n rfl x =
      (fullAt K S k (PullMod C.conj M) v).i.f n n rfl
        ((conjTransportGHom C g hvw hg).f n n rfl x) :=
  rfl

/-- The structure map of the transported full condition is bijective in every degree.
Kind: PROVED. -/
theorem conjTransport_fullAt_bijective (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹) (n : ℤ) :
    Function.Bijective ((conjTransport C g hvw hg (fullAt K S k M w)).i.f n n rfl) :=
  conjTransportGHom_bijective C g hvw hg n

end Transport

/-! ### The split and the fixed case with the canonical inner element -/

section Canonical

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M]

/-- **The conjugate place `τv ∈ S`** of `v ∈ S` (RC28's `conjPlace`, in `S` by stability). -/
def locConjPlaceS (v : Places K S) : Places K S :=
  ⟨conjPlace C.κ v.1, (mem_conjPlace_iff C.κ S C.hS v.1).mp v.2⟩

/-- The hypothesis `hvw` at the conjugate place holds by definition. Kind: PROVED. -/
theorem locConjPlaceS_asIdeal (v : Places K S) :
    (locConjPlaceS C v).1.asIdeal =
      v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K) :=
  rfl

/-- **The canonical inner element** `g = c(h|_{K_S})⁻¹` for the unique comparison element
`h = locConjElt` (`LocalConj.lean`). -/
def conjTransportElt {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K)) : GKS K S :=
  (C.conj (resAbs K S (locConjElt C.κ C.τ C.hτ hvw)))⁻¹

/-- The canonical inner element satisfies `hg`. Kind: PROVED. -/
theorem conjTransportElt_spec {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (σ : Gloc K v) :
    locMap K S w (locConjGal C.κ hvw σ) =
      conjTransportElt C hvw * C.conj (locMap K S v σ) * (conjTransportElt C hvw)⁻¹ :=
  locConj_locMap_of C hvw _ (locConjElt_spec C.κ C.τ C.hτ hvw) σ

/-- **Split places** (tex 2810–2811: "At a split place `v`, the dual local condition is
transported from the conjugate place `τv`"): the transport of a local condition at `τv` to `v`,
with the canonical inner element. -/
def conjTransportConjPlace (v : Places K S) (c : CondAt K S k M (locConjPlaceS C v)) :
    CondAt K S k (PullMod C.conj M) v :=
  conjTransport C (conjTransportElt C (locConjPlaceS_asIdeal C v)) (locConjPlaceS_asIdeal C v)
    (conjTransportElt_spec C (locConjPlaceS_asIdeal C v)) c

/-- **Fixed places** (tex 2811–2812: "At a fixed place it is transported by the actual local
representative of conjugation"): the transport at `w = v`, through the local conjugation of
`K_v` (`locConj_fixed`, `conjTransportFixed_rep`). Hypothesis `hfix`: ELLIOT, non-vacuous. -/
def conjTransportFixed (v : Places K S) (hfix : conjPlace C.κ v.1 = v.1) (c : CondAt K S k M v) :
    CondAt K S k (PullMod C.conj M) v :=
  conjTransport C (conjTransportElt C (locConjFixed_asIdeal C.κ hfix))
    (locConjFixed_asIdeal C.κ hfix) (conjTransportElt_spec C (locConjFixed_asIdeal C.κ hfix)) c

end Canonical

/-! ### Change of coefficients along an equivariant isomorphism -/

section Coef

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] {M M' : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module k M']
  [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) k M'] [TopologicalSpace M']
  [DiscreteTopology M'] [ContinuousAdd M'] [ContinuousSMul (GKS K S) M']

/-- An isomorphism of `G_{K,S}`-modules read on the restrictions along `p_v`. -/
def conjTransportCoefEquiv (ψ : M ≃ₗ[k] M') (v : HeightOneSpectrum (𝓞 K)) :
    ResMod (locMap K S v) M ≃ₗ[k] ResMod (locMap K S v) M' :=
  ψ

/-- The cochain isomorphism `C^•_cont(G_{K_v}, M) ≅ C^•_cont(G_{K_v}, M')` of an equivariant
`k`-linear isomorphism `ψ : M ≃ M'` of discrete `G_{K,S}`-modules. Hypothesis `hψ`: the
equivariance of `ψ`. -/
def conjTransportCoefIso (ψ : M ≃ₗ[k] M') (hψ : ∀ (σ : GKS K S) (m : M), ψ (σ • m) = σ • ψ m)
    (v : HeightOneSpectrum (𝓞 K)) :
    contCochains k (Gloc K v) (ResMod (locMap K S v) M) ≅
      contCochains k (Gloc K v) (ResMod (locMap K S v) M') :=
  locConjPairIso (ContinuousMulEquiv.refl (Gloc K v)) (conjTransportCoefEquiv ψ v)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (fun σ m => hψ (locMap K S v σ) m)

/-- **The local condition at `v` pushed along an equivariant isomorphism `ψ : M ≃ M'`.** -/
def conjTransportCoef (ψ : M ≃ₗ[k] M') (hψ : ∀ (σ : GKS K S) (m : M), ψ (σ • m) = σ • ψ m)
    {v : Places K S} (c : CondAt K S k M v) : CondAt K S k M' v :=
  ⟨c.U, ghomComp c.i (natHom (conjTransportCoefIso ψ hψ v.1).hom)⟩

/-- The coefficient change preserves injectivity. Kind: PROVED. -/
theorem conjTransportCoef_isInjective (ψ : M ≃ₗ[k] M')
    (hψ : ∀ (σ : GKS K S) (m : M), ψ (σ • m) = σ • ψ m) {v : Places K S} (c : CondAt K S k M v)
    (hc : c.IsInjective) : (conjTransportCoef ψ hψ c).IsInjective :=
  fun n => (locConjNatHom_bijective (conjTransportCoefIso ψ hψ v.1) n).1.comp (hc n)

/-- The coefficient change sends zero to zero. Kind: PROVED. -/
theorem conjTransportCoef_zeroAt (ψ : M ≃ₗ[k] M')
    (hψ : ∀ (σ : GKS K S) (m : M), ψ (σ • m) = σ • ψ m) (v : Places K S) :
    conjTransportCoef ψ hψ (zeroAt K S k M v) = zeroAt K S k M' v := by
  have key : ∀ (a b : GHom (zeroCx k) (locAt K S k M' v)), a.f = b.f → a = b := by
    rintro ⟨fa, ca⟩ ⟨fb, cb⟩ h
    subst h
    rfl
  change (⟨zeroCx k, ghomComp (zeroGHom _ _) (natHom (conjTransportCoefIso ψ hψ v.1).hom)⟩ :
    CondAt K S k M' v) = ⟨zeroCx k, zeroGHom _ _⟩
  congr 1
  apply key
  funext i j h
  subst h
  refine LinearMap.ext fun x => ?_
  change (natHom (conjTransportCoefIso ψ hψ v.1).hom).f i i rfl 0 = 0
  exact map_zero _

/-- The coefficient change sends full to full (bijective structure map). Kind: PROVED. -/
theorem conjTransportCoef_fullAt_bijective (ψ : M ≃ₗ[k] M')
    (hψ : ∀ (σ : GKS K S) (m : M), ψ (σ • m) = σ • ψ m) (v : Places K S) (n : ℤ) :
    Function.Bijective ((conjTransportCoef ψ hψ (fullAt K S k M v)).i.f n n rfl) :=
  locConjNatHom_bijective (conjTransportCoefIso ψ hψ v.1) n

end Coef

/-! ### The dual local conditions on `M_i^*(1) ≃ τ^*M_i` -/

section Dual

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.map (C.κ : K →+* K) = W)
  {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N) (A : Type) [CommRing A] [Algebra (ZMod N) A]
  (α : GKS K S →* Aˣ) [ContinuousSMul (GKS K S) (CoefMod A α (TorsS K S W N))]
  [ContinuousSMul (GKS K S) (DualM W hμ A α)]

/-- **The dual local condition at `v` on `M_i^*(1)`, transported from the conjugate place**
(tex 2810–2812, with `τ^*M_i ≃ M_i^*(1)` of tex 2765, 2805): the condition `c` at `w = κv` for
`M_i = (E(K_S)[N] ⊗ A)(α)` is transported to `v` for `τ^*M_i` (`conjTransport`) and pushed along
lane RC28's `conjDualEquiv : τ^*M_i ≃ M_i^*(1)` (`w ↦ (v ↦ e(v, ρ_T(τ)w))`).
Hypotheses: `hW` (RC28 DEPARTURE 3), `hFull` (GLUE, RC28), `hα` (ELLIOT tex 2786–2795),
`hvw` (DEF), `hg` (PROVED satisfiable). DEPARTURE D4: that the result is the orthogonal
complement `U_v^⊥` is not proved here. -/
def conjTransportDual (hFull : FullTorsion K S W N) (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹)
    (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹)
    (c : CondAt K S A (CoefMod A α (TorsS K S W N)) w) : CondAt K S A (DualM W hμ A α) v :=
  conjTransportCoef (conjDualEquiv C W hW hμ A α hFull) (conjDualEquiv_smul C W hW hμ A α hFull hα)
    (conjTransport C g hvw hg c)

/-- The dual condition preserves injectivity. Kind: PROVED. -/
theorem conjTransportDual_isInjective (hFull : FullTorsion K S W N)
    (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹)
    (c : CondAt K S A (CoefMod A α (TorsS K S W N)) w) (hc : c.IsInjective) :
    (conjTransportDual C W hW hμ A α hFull hα g hvw hg c).IsInjective :=
  conjTransportCoef_isInjective _ _ _ (conjTransport_isInjective C g hvw hg c hc)

/-- The conjugate transport of the zero condition at `τv` is the zero condition at `v`.
Kind: PROVED. -/
theorem conjTransportDual_zeroAt (hFull : FullTorsion K S W N)
    (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹) :
    conjTransportDual C W hW hμ A α hFull hα g hvw hg (zeroAt K S A _ w) =
      zeroAt K S A (DualM W hμ A α) v := by
  unfold conjTransportDual
  rw [conjTransport_zeroAt, conjTransportCoef_zeroAt]

/-- The conjugate transport of the full condition at `τv` is (isomorphic to) the full condition
at `v`. Kind: PROVED. -/
theorem conjTransportDual_fullAt_bijective (hFull : FullTorsion K S W N)
    (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) (g : GKS K S) {v w : Places K S}
    (hvw : w.1.asIdeal = v.1.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hg : ∀ σ : Gloc K v.1,
      locMap K S w.1 (locConjGal C.κ hvw σ) = g * C.conj (locMap K S v.1 σ) * g⁻¹) (n : ℤ) :
    Function.Bijective
      ((conjTransportDual C W hW hμ A α hFull hα g hvw hg (fullAt K S A _ w)).i.f n n rfl) :=
  (locConjNatHom_bijective (conjTransportCoefIso (conjDualEquiv C W hW hμ A α hFull)
    (conjDualEquiv_smul C W hW hμ A α hFull hα) v.1) n).comp
    (conjTransport_fullAt_bijective C g hvw hg n)

end Dual

/-! ### (e) The transport by a representative of conjugation -/

section Rep

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) (k : Type) [CommRing k] (M : Type) [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M]

/-- Conjugation `x ↦ τ' x τ'⁻¹` of `G_{K,S}` by a representative `τ'` of conjugation (a ring
automorphism of `K̄` over `κ`; RC28's `conjGKS`), as a continuous homomorphism. -/
def conjTransportRepHom (τ' : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ' : ∀ x : K, τ' (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (C.κ x)) :
    GKS K S →ₜ* GKS K S :=
  ⟨(conjGKS K C.κ τ' hτ' S C.hS).toMonoidHom, continuous_conjGKS K C.κ τ' hτ' S C.hS⟩

/-- The identity of `M`, from `M` restricted along `p_{κv}` to `τ'^*M` restricted along `p_v`. -/
def conjTransportRepId (τ' : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ' : ∀ x : K, τ' (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (C.κ x)) (v w : HeightOneSpectrum (𝓞 K)) :
    ResMod (locMap K S w) M →ₗ[k]
      ResMod (locMap K S v) (PullMod (conjTransportRepHom C τ' hτ') M) where
  toFun m := show M from m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The transport by the representative `τ'`**: `c ↦ c ∘ φ_vⁿ`,
`C^•(G_{K_{κv}}, M) → C^•(G_{K_v}, τ'^*M)`; no coefficient twist is needed because
`p_{κv}(φ_v σ) = τ' p_v(σ) τ'⁻¹` exactly (hypothesis `hrep`, PROVED satisfiable by
`locConj_locMap_rep`). -/
def conjTransportRepCochains (τ' : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ' : ∀ x : K, τ' (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (C.κ x)) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hrep : ∀ σ : Gloc K v,
      locMap K S w (locConjGal C.κ hvw σ) = conjTransportRepHom C τ' hτ' (locMap K S v σ)) :
    contCochains k (Gloc K w) (ResMod (locMap K S w) M) ⟶
      contCochains k (Gloc K v)
        (ResMod (locMap K S v) (PullMod (conjTransportRepHom C τ' hτ') M)) :=
  contCochainsMap ⟨(locConjGal C.κ hvw).toMulEquiv.toMonoidHom, (locConjGal C.κ hvw).continuous⟩
    (conjTransportRepId C k M τ' hτ' v w) continuous_of_discreteTopology (fun σ m => by
      change locMap K S w (locConjGal C.κ hvw σ) • (show M from m) =
        conjTransportRepHom C τ' hτ' (locMap K S v σ) • (show M from m)
      rw [hrep])

/-- The coefficient comparison `τ'^*M → τ^*M`, `m ↦ g⁻¹ m`. -/
def conjTransportRepCoef (τ' : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ' : ∀ x : K, τ' (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (C.κ x)) (g : GKS K S) (v : HeightOneSpectrum (𝓞 K)) :
    ResMod (locMap K S v) (PullMod (conjTransportRepHom C τ' hτ') M) →ₗ[k]
      ResMod (locMap K S v) (PullMod C.conj M) where
  toFun m := show M from g⁻¹ • (show M from m)
  map_add' m m' := smul_add g⁻¹ (show M from m) (show M from m')
  map_smul' c m := smul_comm g⁻¹ c (show M from m)

/-- The cochain map of the coefficient comparison, an equivariant map when conjugation by `τ'`
is `x ↦ g c(x) g⁻¹` (hypothesis `hτg`, PROVED satisfiable by `conjGKS_locConjRep`). -/
def conjTransportRepCoefCochains (τ' : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ' : ∀ x : K, τ' (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (C.κ x)) (g : GKS K S)
    (hτg : ∀ x : GKS K S, conjTransportRepHom C τ' hτ' x = g * C.conj x * g⁻¹)
    (v : HeightOneSpectrum (𝓞 K)) :
    contCochains k (Gloc K v) (ResMod (locMap K S v) (PullMod (conjTransportRepHom C τ' hτ') M)) ⟶
      contCochains k (Gloc K v) (ResMod (locMap K S v) (PullMod C.conj M)) :=
  contCochainsMap (ContinuousMonoidHom.id _) (conjTransportRepCoef C k M τ' hτ' g v)
    continuous_of_discreteTopology (fun σ m => by
      change g⁻¹ • (conjTransportRepHom C τ' hτ' (locMap K S v σ) • (show M from m)) =
        C.conj (locMap K S v σ) • (g⁻¹ • (show M from m))
      rw [hτg, mul_smul, mul_smul, inv_smul_smul])

/-- **(e) The transport is the transport by the representative of conjugation, followed by the
coefficient comparison**: `conjTransportIso` (with `g`) is the composite
`C^•(G_{K_{κv}}, M) → C^•(G_{K_v}, τ'^*M) → C^•(G_{K_v}, τ^*M)`. Kind: PROVED. -/
theorem conjTransport_eq_rep (τ' : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hτ' : ∀ x : K, τ' (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (C.κ x)) (g : GKS K S) {v w : HeightOneSpectrum (𝓞 K)}
    (hvw : w.asIdeal = v.asIdeal.map (RingOfIntegers.mapRingEquiv C.κ : 𝓞 K →+* 𝓞 K))
    (hrep : ∀ σ : Gloc K v,
      locMap K S w (locConjGal C.κ hvw σ) = conjTransportRepHom C τ' hτ' (locMap K S v σ))
    (hτg : ∀ x : GKS K S, conjTransportRepHom C τ' hτ' x = g * C.conj x * g⁻¹) :
    conjTransportRepCochains C k M τ' hτ' hvw hrep ≫
        conjTransportRepCoefCochains C k M τ' hτ' g hτg v =
      (conjTransportIso C k M g hvw (fun σ => (hrep σ).trans (hτg _))).hom := by
  ext n c
  apply Subtype.ext
  funext x
  rfl

/-- **(e) At a fixed place the transport is by the actual local representative of
conjugation** (tex 2811–2812): for `conjPlace κ v = v` there is the comparison element `h` such
that the local automorphism `Ē_v` of `K̄_v` restricts on `K̄` to `τ_v = τ ∘ h⁻¹`, and the
transport of cochains with `g = c(h|_{K_S})⁻¹` is the transport by `τ_v` followed by the
comparison `τ_v^*M ≅ τ^*M`. Hypothesis `hfix`: ELLIOT, non-vacuous. Kind: PROVED. DEPARTURE D2. -/
theorem conjTransportFixed_rep (v : HeightOneSpectrum (𝓞 K)) (hfix : conjPlace C.κ v = v) :
    ∃ (h : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (hrep : ∀ σ : Gloc K v, locMap K S v (locConjGal C.κ (locConjFixed_asIdeal C.κ hfix) σ) =
        conjTransportRepHom C (locConjRep C.τ h) (locConjRep_algebraMap C.κ C.τ C.hτ h)
          (locMap K S v σ))
      (hτg : ∀ x : GKS K S,
        conjTransportRepHom C (locConjRep C.τ h) (locConjRep_algebraMap C.κ C.τ C.hτ h) x =
          (C.conj (resAbs K S h))⁻¹ * C.conj x * (C.conj (resAbs K S h))⁻¹⁻¹),
      (∀ x, locConjBar C.κ (locConjFixed_asIdeal C.κ hfix) (decompLift K v x) =
        decompLift K v (locConjRep C.τ h x)) ∧
      conjTransportRepCochains C k M _ _ (locConjFixed_asIdeal C.κ hfix) hrep ≫
          conjTransportRepCoefCochains C k M _ _ _ hτg v =
        (conjTransportIso C k M _ (locConjFixed_asIdeal C.κ hfix)
          (fun σ => (hrep σ).trans (hτg _))).hom := by
  obtain ⟨-, -, -, -, h, h1, h2, h3⟩ := locConj_fixed C hfix
  exact ⟨h, h2, h3, h1, conjTransport_eq_rep C k M _ _ _ _ h2 h3⟩

end Rep

/-! ### The transported conditions at all places of `S` -/

section Assembly

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (C : ActualConj K S) {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousAdd M] [ContinuousSMul (GKS K S) M]

open Classical in
/-- **The transported condition at a place `v ∈ S`** (tex 2810–2812): at a fixed place the
transport of the condition at `v` itself (by the local representative of conjugation), otherwise
the transport of the condition at the conjugate place `τv`. -/
def conjTransportAt (Δ : ∀ w : Places K S, CondAt K S k M w) (v : Places K S) :
    CondAt K S k (PullMod C.conj M) v :=
  if hfix : conjPlace C.κ v.1 = v.1 then conjTransportFixed C v hfix (Δ v)
  else conjTransportConjPlace C v (Δ (locConjPlaceS C v))

/-- The transported conditions are injective when the given ones are. Kind: PROVED. -/
theorem conjTransportAt_isInjective (Δ : ∀ w : Places K S, CondAt K S k M w)
    (hΔ : ∀ w, (Δ w).IsInjective) (v : Places K S) : (conjTransportAt C Δ v).IsInjective := by
  unfold conjTransportAt
  split_ifs with hfix
  · exact conjTransport_isInjective C _ _ _ _ (hΔ v)
  · exact conjTransport_isInjective C _ _ _ _ (hΔ _)

/-- **The transported local conditions for `τ^*M`** in lane RC26's format. -/
def conjTransportConditions (Δ : ∀ w : Places K S, CondAt K S k M w) :
    GaloisLocalConditions K S k (PullMod C.conj M) :=
  ofCondAt K S k _ (conjTransportAt C Δ)

/-- The Selmer data of `τ^*M` with the transported conditions are genuine Galois Selmer data
(for finite `S` and injective given conditions). Kind: PROVED. -/
theorem conjTransport_isGaloisSelData (hSfin : S.Finite) (Δ : ∀ w : Places K S, CondAt K S k M w)
    (hΔ : ∀ w, (Δ w).IsInjective) :
    ZInQ.Manuscript.RC.Wiring.IsGaloisSelData
      (galoisSelData K S k (PullMod C.conj M) (conjTransportConditions C Δ)) :=
  ⟨K, inferInstance, inferInstance, S, PullMod C.conj M, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    conjTransportConditions C Δ, hSfin, fun v n => conjTransportAt_isInjective C Δ hΔ v n, rfl⟩

variable (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.map (C.κ : K →+* K) = W)
  {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N) (A : Type) [CommRing A] [Algebra (ZMod N) A]
  (α : GKS K S →* Aˣ) [ContinuousSMul (GKS K S) (CoefMod A α (TorsS K S W N))]
  [ContinuousSMul (GKS K S) (DualM W hμ A α)]

/-- **The dual local condition at `v ∈ S` on `M_i^*(1)`** (tex 2810–2812): the transported
condition (`conjTransportAt`) pushed along `conjDualEquiv : τ^*M_i ≃ M_i^*(1)`. Hypotheses as in
`conjTransportDual`. DEPARTURE D4. -/
def conjTransportDualAt (hFull : FullTorsion K S W N) (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹)
    (Δ : ∀ w : Places K S, CondAt K S A (CoefMod A α (TorsS K S W N)) w) (v : Places K S) :
    CondAt K S A (DualM W hμ A α) v :=
  conjTransportCoef (conjDualEquiv C W hW hμ A α hFull) (conjDualEquiv_smul C W hW hμ A α hFull hα)
    (conjTransportAt C Δ v)

/-- Local conditions on the coefficient dual M_i^*(1), obtained by conjugate transport of the
supplied system Δ. This constructor does not compute Δ's orthogonal complement. Full conditions
remain full and zero conditions remain zero. To represent U^⊥, first supply and identify the
actual orthogonal system, then transport that system (lane RC29's round-3
`conjActualLocalComplements`, `ConjComplements.lean`, proves that the transport of the actual
orthogonal system is the orthogonal complement of the actual conditions). -/
def conjTransportDualConditions (hFull : FullTorsion K S W N) (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹)
    (Δ : ∀ w : Places K S, CondAt K S A (CoefMod A α (TorsS K S W N)) w) :
    GaloisLocalConditions K S A (DualM W hμ A α) :=
  ofCondAt K S A _ (conjTransportDualAt C W hW hμ A α hFull hα Δ)

/-- The Selmer data on M_i^*(1) with conjugate-transported supplied conditions are genuine
Galois Selmer data, for finite S and injective supplied conditions. Kind: PROVED. -/
theorem conjTransportDual_isGaloisSelData (hFull : FullTorsion K S W N)
    (hα : ∀ σ, α (C.conj σ) = (α σ)⁻¹) (hSfin : S.Finite)
    (Δ : ∀ w : Places K S, CondAt K S A (CoefMod A α (TorsS K S W N)) w)
    (hΔ : ∀ w, (Δ w).IsInjective) :
    ZInQ.Manuscript.RC.Wiring.IsGaloisSelData
      (galoisSelData K S A (DualM W hμ A α)
        (conjTransportDualConditions C W hW hμ A α hFull hα Δ)) :=
  ⟨K, inferInstance, inferInstance, S, DualM W hμ A α, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    conjTransportDualConditions C W hW hμ A α hFull hα Δ, hSfin,
    fun v n => conjTransportCoef_isInjective _ _ _ (conjTransportAt_isInjective C Δ hΔ v) n, rfl⟩

end Assembly

/-! ### (f) Non-vacuity -/

section NonVacuity

/-- The places of `ℚ(i)` (the fourth cyclotomic field) above `2`: the set `S` of RC28's
`actualConj_nonempty_gaussian`. -/
abbrev conjTransportNVPlaces : Set (HeightOneSpectrum (𝓞 (CyclotomicField 4 ℚ))) :=
  {v | v.asIdeal.comap (algebraMap ℤ (𝓞 (CyclotomicField 4 ℚ))) ∈
    ({Ideal.span {(2 : ℤ)}} : Set (Ideal ℤ))}

/-- **`ℚ(i)` has exactly one place above `2`** (Mathlib's
`IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver`, the prime `(ζ₄ − 1)`).
Kind: PROVED. -/
theorem conjTransportNV_unique :
    ∃ v₀ : HeightOneSpectrum (𝓞 (CyclotomicField 4 ℚ)), v₀ ∈ conjTransportNVPlaces ∧
      ∀ v ∈ conjTransportNVPlaces, v = v₀ := by
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  have hK : IsCyclotomicExtension {2 ^ (1 + 1)} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 4 ℚ (CyclotomicField 4 ℚ)) (2 ^ (1 + 1)) :=
    IsCyclotomicExtension.zeta_spec 4 ℚ (CyclotomicField 4 ℚ)
  have hP : (Ideal.span {hζ.toInteger - 1}).IsPrime :=
    IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one 2 1 hζ
  have hP0 : Ideal.span {hζ.toInteger - 1} ≠ ⊥ :=
    IsCyclotomicExtension.Rat.span_zeta_sub_one_ne_bot 2 1 hζ
  have hPl : (Ideal.span {hζ.toInteger - 1}).LiesOver (Ideal.span {((2 : ℕ) : ℤ)}) :=
    IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one 2 1 hζ
  let v₀ : HeightOneSpectrum (𝓞 (CyclotomicField 4 ℚ)) := ⟨_, hP, hP0⟩
  have hv₀ : v₀.asIdeal.comap (algebraMap ℤ (𝓞 (CyclotomicField 4 ℚ))) = Ideal.span {(2 : ℤ)} := by
    have h := hPl.over
    rw [Nat.cast_ofNat] at h
    exact h.symm
  refine ⟨v₀, hv₀, fun v hv => ?_⟩
  have hv' : v.asIdeal.comap (algebraMap ℤ (𝓞 (CyclotomicField 4 ℚ))) = Ideal.span {(2 : ℤ)} := hv
  have : v.asIdeal.LiesOver (Ideal.span {((2 : ℕ) : ℤ)}) :=
    ⟨by rw [Nat.cast_ofNat]; exact hv'.symm⟩
  have : v.asIdeal.IsPrime := v.isPrime
  exact HeightOneSpectrum.ext
    (IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver 2 1 (CyclotomicField 4 ℚ)
      hζ v.asIdeal)

/-- The set of places of `ℚ(i)` above `2` is finite. Kind: PROVED. -/
theorem conjTransportNV_finite : conjTransportNVPlaces.Finite := by
  obtain ⟨v₀, -, hu⟩ := conjTransportNV_unique
  exact (Set.finite_singleton v₀).subset fun v hv => hu v hv

/-- **Non-vacuity of the fixed case** (`hfix`): the place of `ℚ(i)` above `2` is fixed by every
automorphism `κ` of `ℚ(i)`. Kind: PROVED. -/
theorem conjTransportNV_fixedPlace (κ : CyclotomicField 4 ℚ ≃+* CyclotomicField 4 ℚ) :
    ∃ v : HeightOneSpectrum (𝓞 (CyclotomicField 4 ℚ)), v ∈ conjTransportNVPlaces ∧
      conjPlace κ v = v := by
  obtain ⟨v₀, hv₀, hu⟩ := conjTransportNV_unique
  refine ⟨v₀, hv₀, hu _ ?_⟩
  have hv₀' : v₀.asIdeal.comap (algebraMap ℤ (𝓞 (CyclotomicField 4 ℚ))) = Ideal.span {(2 : ℤ)} :=
    hv₀
  change (conjPlace κ v₀).asIdeal.comap (algebraMap ℤ (𝓞 (CyclotomicField 4 ℚ))) ∈
    ({Ideal.span {(2 : ℤ)}} : Set (Ideal ℤ))
  rw [comap_int_eq_of_eq_map κ v₀ (conjPlace κ v₀) rfl, hv₀']
  rfl

/-- **An actual complex conjugation of `ℚ(i)`, nontrivial on `ℚ(i)`, with a fixed place in `S`.**
Kind: PROVED. -/
theorem conjTransportNV_actualConj :
    ∃ (C : ActualConj (CyclotomicField 4 ℚ) conjTransportNVPlaces)
      (v : Places (CyclotomicField 4 ℚ) conjTransportNVPlaces),
      C.κ ≠ RingEquiv.refl _ ∧ conjPlace C.κ v.1 = v.1 := by
  obtain ⟨C, hC⟩ := actualConj_nonempty_gaussian
  obtain ⟨v, hv, hfix⟩ := conjTransportNV_fixedPlace C.κ
  exact ⟨C, ⟨v, hv⟩, hC, hfix⟩

/-- Non-vacuity of the hypotheses `hvw` and `hg` at every pair of places. Kind: PROVED. -/
example {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (C : ActualConj K S) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ g : GKS K S, ∀ σ : Gloc K v,
      locMap K S (conjPlace C.κ v) (locConjGal C.κ (v := v) (w := conjPlace C.κ v) rfl σ) =
        g * C.conj (locMap K S v σ) * g⁻¹ :=
  locConj_locMap C rfl

/-- **Non-vacuity of `hW`**: `E_1 : y² = x(x − 1)(x + 3)` is defined over the fixed field of
every ring endomorphism. Kind: PROVED. -/
theorem conjTransportNV_curveEll_map {K : Type} [Field K] [NumberField K] (f : K →+* K) :
    (curveEll (1 : K)).map f = curveEll 1 := by
  rw [curveEll_coeffs]
  ext <;> simp [map_ofNat]

/-- `E_1` is an elliptic curve over `ℚ(i)`. Kind: PROVED. -/
theorem conjTransportNV_isElliptic : (curveEll (1 : CyclotomicField 4 ℚ)).IsElliptic :=
  isElliptic_curveEll one_ne_zero

attribute [local instance] conjTransportNV_isElliptic

/-- `E_1(K_S)[2]` is finite. Kind: PROVED. -/
theorem conjTransportNV_finiteTors :
    Finite (TorsS (CyclotomicField 4 ℚ) conjTransportNVPlaces (curveEll 1) ((2 : ℕ) : ℤ)) :=
  finite_torsS (by norm_num)

attribute [local instance] conjTransportNV_finiteTors

/-- **(f) Non-vacuity of the dual transport at a fixed place**: for `K = ℚ(i)`, `S` the places
above `2`, `E = E_1`, `N = 2`, `A = ℤ/2`, `α = 1`, an actual complex conjugation `C` (nontrivial
on `K`) and the fixed place `v` above `2`, every hypothesis of `conjTransportDual` is discharged
(`hW`, `FullTorsion`, `hα`, `hvw`, `hg`, the instances), and the conjugate transport of the full
condition is an injective local condition. Kind: PROVED. -/
theorem conjTransportDual_nonvacuous :
    ∃ (C : ActualConj (CyclotomicField 4 ℚ) conjTransportNVPlaces)
      (v : Places (CyclotomicField 4 ℚ) conjTransportNVPlaces) (hfix : conjPlace C.κ v.1 = v.1),
      C.κ ≠ RingEquiv.refl _ ∧
      (conjTransportDual C (curveEll 1) (conjTransportNV_curveEll_map _)
        (hasRootsOfUnity_two conjTransportNVPlaces) (ZMod 2) 1
        (fullTorsion_two_curveEll one_ne_zero) (fun σ => by simp)
        (conjTransportElt C (locConjFixed_asIdeal C.κ hfix)) (locConjFixed_asIdeal C.κ hfix)
        (conjTransportElt_spec C (locConjFixed_asIdeal C.κ hfix))
        (fullAt _ _ _ _ v)).IsInjective := by
  obtain ⟨C, v, hC, hfix⟩ := conjTransportNV_actualConj
  exact ⟨C, v, hfix, hC, conjTransportDual_isInjective _ _ _ _ _ _ _ _ _ _ _ _
    (fullAt_isInjective _ _ _ _ v)⟩

/-- Non-vacuity of generic conjugate transport on the coefficient dual, for the displayed
ℚ(i) example. Its supplied full conditions remain full; this is not the orthogonal-dual
system of full conditions. ℚ(i) is outside the manuscript's allowed fields (tex 2720).
Kind: PROVED. -/
theorem conjTransportNV_isGaloisSelData :
    ∃ C : ActualConj (CyclotomicField 4 ℚ) conjTransportNVPlaces, C.κ ≠ RingEquiv.refl _ ∧
      ZInQ.Manuscript.RC.Wiring.IsGaloisSelData
        (galoisSelData _ conjTransportNVPlaces (ZMod 2)
          (DualM (curveEll 1) (hasRootsOfUnity_two conjTransportNVPlaces) (ZMod 2) 1)
          (conjTransportDualConditions C (curveEll 1) (conjTransportNV_curveEll_map _)
            (hasRootsOfUnity_two conjTransportNVPlaces) (ZMod 2) 1
            (fullTorsion_two_curveEll one_ne_zero) (fun σ => by simp)
            (fun w => fullAt _ _ _ _ w))) := by
  obtain ⟨C, hC⟩ := actualConj_nonempty_gaussian
  exact ⟨C, hC, conjTransportDual_isGaloisSelData C _ _ _ _ _ _ _ conjTransportNV_finite _
    (fun w => fullAt_isInjective _ _ _ _ w)⟩

end NonVacuity

end ZInQ.Manuscript.RC.KummerMaps
