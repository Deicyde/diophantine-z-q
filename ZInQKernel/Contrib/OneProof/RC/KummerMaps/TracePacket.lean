import ZInQKernel.Contrib.OneProof.RC.KummerMaps.CycloInfl
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthActual

/-!
# Lane RC29 (round 2): the finite-level trace packet (Nekovář 5.4.1) and finite Selmer duality for the actual data

Manuscript `diophantine_zq.tex` (11/5):
* Lemma `ex:arith-local-kummer`, tex 3454–3456: "The global Selmer duality theorem
  [Nekovář, Sections 5.1, 5.2.4, 5.4.3 and 6.3.4] is applied to these actual local maps and
  homotopies";
* tex 3465–3467: "The compatible trace in (4.3) is coefficient-valued. A top-coefficient functional
  used to test a finite Frobenius ring's perfection is not used as a
  coefficient-reduction-compatible arithmetic trace";
* Lemma `ex:arith-conjugate-duality`, tex 2761–2830: the finite Selmer duality
  `C_U(M_i) ≃ RHom_{R_i}(C_{U^⊥}(M_i^*(1)), R_i)[−3]`.

The "compatible trace" consists of local traces `tr_v` (inducing `H²(G_{K_v}, R(1)) ≅ R`) and a
global trace `tr` on the compactly supported cochains (inducing `H³_c(G_{K,S}, R(1)) ≅ R`) whose
local part is `∑_v tr_v`. Lanes RC26 and RC29 (round 1) assume these as hypotheses (`trv`, `htrv`,
`htrv2`, `tr`, `htr`, `htr3`, `hsum`). This file states them as one PRINT, the finite-level mirror
of lane RC31's characteristic-zero packet (`FibreLocalTraces`, `Normalizes`,
`NekovarFibreTraces`).

## Source (read on the page images of the printed edition; quotations verbatim)

J. Nekovář, *Selmer complexes*, Astérisque 310 (2006), Chapter 5 ("Throughout Chapter 5 we assume
that `k = 𝔽_{p^r}` is a finite field of characteristic `p`", p. 113):
* 5.1 (p. 113): "Let `K` be a global field of characteristic `char(K) ≠ p` and `S` a finite set of
  primes of `K` containing all primes above `p` and all archimedean primes of `K` (if `K` is a
  number field). Denote by `S_f` the set of non-archimedean primes in `S`. In Sections 5.1–5.6,
  we assume that the following condition is satisfied (the general case is treated in 5.7):
  (P) If `p = 2`, then `K` has no real prime."
* 5.1.3 (p. 114): "For every `n ⩾ 0`, local class field theory defines an isomorphism
  `inv_v : H²(G_v, ℤ/p^nℤ(1)) = Br(K_v)[p^n] ⥲ ℤ/p^nℤ` (where `ℤ/p^nℤ(1) = μ_{p^n}`)."
* 5.1.5 (p. 114), "Reciprocity law. — The sum of the local invariants
  `inv_{S_f} = ∑_{v∈S_f} inv_v` defines a short exact sequence
  `0 → H²(G_{K,S}, ℤ/p^nℤ(1)) → ⊕_{v∈S_f} H²(G_v, ℤ/p^nℤ(1)) --inv_{S_f}--> ℤ/p^nℤ → 0`."
* 5.2.1 (pp. 114–115): "It follows from 5.1.2–5.1.3 that for every `R`-module `A` with trivial
  action of `G_v` we have `inv_v : H²_cont(G_v, A(1)) ⥲ A`, `H^i_cont(G_v, A(1)) = 0 (i > 2)`.
  … This implies that the canonical map of complexes (5.2.1.1)
  `A[−2] --i_v--> τ_{⩾2} C•_cont(G_v, A(1))` (in which `i_v` is induced by the inverse of `inv_v`)
  is a quasi-isomorphism. For `A = I` there is a morphism of complexes (5.2.1.2)
  `I[−2] <--r_v-- τ_{⩾2} C•_cont(G_v, I(1))` which is a homotopy inverse of (5.2.1.1). … If `A•`
  is a bounded below complex of injective `R`-modules, then `i_v` has a homotopy inverse (5.2.1.3)
  `r_v = r_{v,A•} : τ^{II}_{⩾2} C•_cont(G_v, A•(1)) → A•[−2]`, unique up to homotopy."
* 5.4.1 (pp. 125–126): "The sequence (5.3.1.2) together with 5.1.5 define an isomorphism
  `H³_{c,cont}(G_{K,S}, ℤ/p^nℤ(1)) ⥲ ℤ/p^nℤ`. As in 5.2.1 we get
  `H^i_{c,cont}(G_{K,S}, A(1)) ⥲ A (i = 3), 0 (i > 3)` for every `R`-module `A` with trivial action
  of `G_{K,S}` … As in 5.2.2, fix a bounded complex `J = J•` of injective `R`-modules. We claim
  that there is a homotopy equivalence `i_S` making the following diagram commutative up to
  homotopy: [`τ^{II}_{⩾2} C•_cont(G_{K,S}, J(1)) --res_{S_f}--> ⊕_{v∈S_f} τ^{II}_{⩾2}
  C•_cont(G_v, J(1)) --j--> Cone(res_{S_f})`, with `(i_v)` from `⊕_{v∈S_f} J[−2]`, `i_S` from
  `J[−2]` and `Σ : ⊕_{v∈S_f} J[−2] → J[−2]`] Indeed, fix `v₀ ∈ S_f` and put `i_S = j ∘ i_{v₀}`.
  Then `i_S` is a quasi-isomorphism, hence a homotopy equivalence (as `J[−2]` is a bounded below
  complex of injectives). Fix homotopy inverses `r_{v,J}` of `i_v` (`v ∈ S_f`) and also a homotopy
  inverse `r_S = r_{S,J}` of `i_S`. Then `r_S ∘ j` is homotopic to `Σ ∘ (r_{v,J})`. Composing
  `r_S[−1]` with the map (5.4.1.2) we obtain a quasi-isomorphism (5.4.1.3)
  `r_J : τ^{II}_{⩾3} C•_{c,cont}(G_{K,S}, J(1)) → J[−3]`, unique up to homotopy."

## Contents

* `FiniteLocalTraces S R T`: local traces at every `v ∈ S` (fields `trv`, `htrv`, `iso`), the
  `r_v` of 5.2.1, chosen once for all coefficients and local conditions. It mirrors lane RC31's
  `FibreLocalTraces` field by field.
* `FiniteLocalTraces.Normalizes L tr`: the global trace is normalized by `L` on the local part of
  the truncated compact cone, `tr(0, z) = ∑_v tr_v(z_v)`. This is lane RC26's `hsum` and mirrors
  lane RC31's `Normalizes`.
* `FiniteLocalTraces.NormalizesUpToHomotopy L tr`: Nekovář's literal relation `r_S ∘ j ∼ Σ ∘ (r_v)`,
  with an explicit homotopy `h : ⊕_v C³(G_v, T) → R`: `tr(0, z) = ∑_v tr_v(z_v) + h(dz)`.
* **`FiniteLocalTraces.exists_normalizes_of_upToHomotopy`** (PROVED, for every ring `R`): the
  homotopy can be absorbed. `tr' = tr − h̃ ∘ d` is again a trace killing coboundaries, agrees with
  `tr` on cocycles (so it induces the same map on `H³`), and is normalized exactly.
* PRINT **`NekovarFiniteTraces`** (exact normalization; Nekovář 5.1.3, 5.1.5, 5.2.1, 5.4.1) and
  PRINT `NekovarFiniteTracesH` (Nekovář's literal up-to-homotopy relation).
  **`nekovarFiniteTraces_of_homotopy : NekovarFiniteTracesH K → NekovarFiniteTraces K`** (PROVED);
  consistency with lane RC26: `nekovarProp541T_of_finiteTraces : NekovarFiniteTraces K →
  NekovarProp541T K` (PROVED).
* Non-vacuity: `finiteTraceEmpty` (the empty packet for `S = ∅`, normalizing every trace,
  `finiteTraceEmpty_normalizes`); `finiteTraceZero` (the packet over the zero ring at an arbitrary
  `S`, normalizing every trace, `finiteTraceZero_normalizes`); `Normalizes` implies
  `NormalizesUpToHomotopy` (`normalizesUpToHomotopy_of_normalizes`).
* The landed finite Selmer duality for the actual data, with the trace hypotheses taken from the
  packet and round 1's `hT` discharged by `cycloInfl_isCyclotomicTwist_tate1`:
  `orthogonalComplementsT_actualKummer_of_packet`, `orthSelmerDuality_actualKummer_of_packet` (a
  given packet `L` and a trace normalized by it). The Kummer per-place inputs `hisoK`, `hperfK`
  are kept as in the landed statements (lane RC29's `KummerSelmer.lean` and `KummerTraces.lean`
  discharge them at the Kummer places). Also `orthSelmerDuality_urOutside_of_cyclo`: the
  general-shape duality with `hT` discharged.

## DEPARTUREs (form)

1. **Exact normalization.** Nekovář 5.4.1 gives `r_S ∘ j ∼ Σ ∘ (r_v)` only up to homotopy;
   `Normalizes` (lane RC26's `hsum`) is an exact equality. The homotopy is absorbed into the
   choice of `r_S`, which Nekovář leaves free ("a homotopy inverse `r_S = r_{S,J}` of `i_S`").
   For any `R` (field or not), a homotopy is a map `h : ⊕_v C³_cont(G_v, T) → R`, and
   `r_S' = r_S − h̃ ∘ d` with `h̃(a, y) = −h(y)` on `Cone(…)[−1]⁴` is homotopic to `r_S`, hence
   again a homotopy inverse of `i_S`, and `r_S' ∘ j = Σ ∘ (r_v)` exactly. This is PROVED here
   (`exists_normalizes_of_upToHomotopy`, `nekovarFiniteTraces_of_homotopy`). For the finite
   self-injective `R` nothing beyond Nekovář's own homotopy is needed. The homotopy itself exists
   because `J[−2] = R[−2]` is a bounded complex of injectives (`R` self-injective), Nekovář's
   argument. An alternative route, as in lane RC31: extend `−∑_v tr_v ∘ res_v` (zero on
   `2`-cocycles by 5.1.5) from the coboundaries `B³(G_{K,S}, T)` to `C³` by self-injectivity
   of `R`.
2. **Traces quantified.** `FiniteLocalTraces` allows any traces inducing `H² ≅ R`, i.e. `u_v · r_v`
   with `u_v ∈ Rˣ`; the PRINT asserts the existence of ONE packet admitting normalized global
   traces. Nekovář's `r_v` are such a packet, and so are the `−r_v`. The latter absorb any
   difference between Nekovář's cone sign conventions and lane RC26's `coneCx`
   (`d(e, z) = (de, f e − dz)`).
3. **The cones** are lane RC26's: finite places only, as in 5.4.1 (`⊕_{v∈S_f}`). The global term
   is untruncated, which changes neither degree three, nor the coboundaries in degree three, nor
   `H³`. For coefficients in a single module, `τ^{II}_{⩾2}` is `τ_{⩾2}` (`truncSub`).
4. `J = R` (lane RC26's `J = I[0] = R`, `NekovarFiniteSetting.selfInjective`), and
   `T ≅ R(1) = J(1)` is lane RC26's `IsCyclotomicTwist`.

Kinds: definitions, PRINT (`NekovarFiniteTraces`, `NekovarFiniteTracesH`), PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-! ### The trace packet -/

section Packet

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (R : Type)
  [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) R T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]

/-- **Local traces at every place of `S`** (Nekovář, *Selmer complexes*, 5.2.1, pp. 114–115: the
homotopy inverse `r_v : τ_{⩾2} C•_cont(G_v, I(1)) → I[−2]` of `i_v`, `i_v` induced by the inverse of
`inv_v` of 5.1.3): cochain traces `tr_v : C²_cont(G_{K_v}, T) → R` killing coboundaries and inducing
`H²(G_{K_v}, T) ≅ R` (lane RC26's `InducesIsoH2`), for the finite discrete coefficient module `T`
(in the PRINT: `T ≅ R(1)`). In the trace packet they are chosen ONCE, for all coefficients and
local conditions. The finite-level mirror of lane RC31's `FibreLocalTraces`. Kind: definition. -/
structure FiniteLocalTraces where
  /-- The trace at `v`. -/
  trv : ∀ v : Places K S, (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) T v).X 2 →ₗ[R] R
  /-- It kills coboundaries. -/
  htrv : ∀ v z, trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) T v).d (2 - 1) 2 (by omega) z) = 0
  /-- It induces `H²(G_{K_v}, T) ≅ R`. -/
  iso : ∀ v, InducesIsoH2 (trv v)

variable {S R T}

/-- The field `htrv` with the differential written `d 1 2` (the form of lane RC29's round-1
statements). PROVED. -/
theorem FiniteLocalTraces.htrv₁ (L : FiniteLocalTraces S R T) (v : Places K S)
    (z : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T v).X 1) :
    L.trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0 :=
  L.htrv v z

section Normalization

variable [Fintype (Places K S)] (L : FiniteLocalTraces S R T) {M M' : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  {β : M →ₗ[R] M' →ₗ[R] T} {hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b}
  {ΔA : GaloisLocalConditions K S R M} {ΔB : GaloisLocalConditions K S R M'}
  {I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB}

/-- **A global trace normalized by the local traces** (lane RC26's `hsum`; Nekovář 5.4.1,
`r_S ∘ j ∼ Σ ∘ (r_v)`, here exactly, see the DEPARTURE in the file header): on the local part of
the truncated compact cone `Cone(C(G_{K,S}, T) → ⊕_v τ_{≥2} C(G_v, T))[−1]`,
`tr(0, z) = ∑_v tr_v(z_v)`. With one fixed `L` this forces the global trace to use the same
trivialization as all the local ones. The finite-level mirror of lane RC31's `Normalizes`.
Kind: definition. -/
def FiniteLocalTraces.Normalizes (tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R) : Prop :=
  ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) T).X (3 - 1),
    tr ((0 : (globalCx R (GKS K S) T).X 3), (truncSub (localSumCx R (GKS K S)
      (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
      ∑ v, L.trv v (z v)

/-- **Nekovář's literal normalization, up to homotopy** (5.4.1, p. 126: "`r_S ∘ j` is homotopic to
`Σ ∘ (r_{v,J})`"): a homotopy between the two maps `⊕_v τ_{≥2} C•(G_v, T)[−1] → R[−3]` is a linear
map `h` on the degree-four local term `⊕_v C³(G_v, T)` (the local component `EL^{4−1}` of the
degree-four term of the cone), and the relation reads `tr(0, z) = ∑_v tr_v(z_v) + h(dz)`.
Kind: definition. -/
def FiniteLocalTraces.NormalizesUpToHomotopy
    (tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R) : Prop :=
  ∃ h : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (4 - 1) →ₗ[R] R,
    ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) T).X 3), (truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
        ∑ v, L.trv v (z v) + h ((localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T).d (3 - 1) (4 - 1) (by omega) z)

/-- The exact normalization is the case `h = 0` of the homotopy form (non-vacuity of
`NormalizesUpToHomotopy`). PROVED. -/
theorem FiniteLocalTraces.normalizesUpToHomotopy_of_normalizes
    {tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R} (h : L.Normalizes tr) :
    L.NormalizesUpToHomotopy tr :=
  ⟨0, fun z => by rw [h z, LinearMap.zero_apply, add_zero]⟩

end Normalization

end Packet

/-! ### Absorbing the homotopy -/

section Absorb

variable {R : Type} [CommRing R]

/-- **The differential of a purely local degree-three element of `Cone(E → τ_{≥2} A)[−1]`**:
`d(0, [z]) = (0, −[dz])` (lane RC26's `coneCx`, `d(e, z) = (de, f e − dz)`). PROVED. -/
theorem finiteTrace_coneD_local {E A : GCx R} (f : GHom E (truncGe2 A)) (z : A.X (3 - 1)) :
    (coneCx f).d 3 4 rfl ((0 : E.X 3), (truncSub A (3 - 1)).mkQ z) =
      ((0 : E.X 4), -(truncSub A (4 - 1)).mkQ (A.d (3 - 1) (4 - 1) (by omega) z)) := by
  refine Prod.ext (map_zero (E.d 3 4 rfl)) ?_
  change f.f 3 (4 - 1) (by omega) 0 -
      (truncGe2 A).d (3 - 1) (4 - 1) (by omega) ((truncSub A (3 - 1)).mkQ z) = _
  rw [map_zero, zero_sub, truncGe2_d_mk]
  rfl

/-- **A trace agreeing with an `H³`-isomorphism on cocycles is one.** PROVED. -/
theorem finiteTrace_inducesIsoH3_of_agree {C : GCx R} {tr tr' : C.X 3 →ₗ[R] R}
    (hag : ∀ z, C.d 3 4 rfl z = 0 → tr' z = tr z) (h : InducesIsoH3 tr) : InducesIsoH3 tr' := by
  obtain ⟨h1, z, hz, hz1⟩ := h
  exact ⟨fun w hw hw0 => h1 w hw ((hag w hw).symm.trans hw0), z, hz, (hag z hz).trans hz1⟩

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {T : Type} [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) R T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T] {M M' : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  {β : M →ₗ[R] M' →ₗ[R] T} {hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b}
  {ΔA : GaloisLocalConditions K S R M} {ΔB : GaloisLocalConditions K S R M'}
  {I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB}

/-- `finiteTrace_coneD_local` for lane RC26's truncated compact cone `galoisCompactTT`. PROVED. -/
theorem finiteTrace_compact_d_local
    (z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1)) :
    (galoisCompactTT K S R β hβ ΔA ΔB I).d 3 4 rfl ((0 : (globalCx R (GKS K S) T).X 3),
      (truncSub (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
      ((0 : (globalCx R (GKS K S) T).X 4), -(truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (4 - 1)).mkQ
          ((localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) T).d (3 - 1) (4 - 1) (by omega) z)) :=
  finiteTrace_coneD_local (E := globalCx R (GKS K S) T)
    (A := localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T)
    (galoisPairDataT K S R β hβ ΔA ΔB I).resE z

/-- **The homotopy of Nekovář 5.4.1 can be absorbed into the global trace** (for every
coefficient ring `R`): if `tr` kills coboundaries and `tr(0, z) = ∑_v tr_v(z_v) + h(dz)`, then
`tr' = tr − h̃ ∘ d`, with `h̃(a, [y]) = −h(y)` on the degree-four term of the cone, kills
coboundaries, agrees with `tr` on cocycles (hence induces the same map on `H³`), and is normalized
exactly by `L`. PROVED. -/
theorem FiniteLocalTraces.exists_normalizes_of_upToHomotopy [Fintype (Places K S)]
    (L : FiniteLocalTraces S R T) (tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactTT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0)
    (hH : L.NormalizesUpToHomotopy tr) :
    ∃ (tr' : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
      (_ : ∀ z, tr' ((galoisCompactTT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0),
      (∀ z, (galoisCompactTT K S R β hβ ΔA ΔB I).d 3 4 rfl z = 0 → tr' z = tr z) ∧
        L.Normalizes tr' := by
  obtain ⟨h, hh⟩ := hH
  have hle : truncSub (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T) (4 - 1) ≤ LinearMap.ker h := by
    rw [truncSub_of_ge _ (by norm_num)]
    exact bot_le
  let hq := (truncSub (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T) (4 - 1)).liftQ h hle
  let hloc : (galoisCompactTT K S R β hβ ΔA ΔB I).X 4 →ₗ[R] R :=
    -(hq ∘ₗ LinearMap.snd R ((globalCx R (GKS K S) T).X 4)
      ((localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T).X (4 - 1) ⧸ truncSub (localSumCx R (GKS K S)
          (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (4 - 1)))
  refine ⟨tr - hloc ∘ₗ (galoisCompactTT K S R β hβ ΔA ΔB I).d 3 4 rfl, fun z => ?_,
    fun z hz => ?_, fun z => ?_⟩
  · rw [LinearMap.sub_apply, LinearMap.comp_apply, htr z,
      (galoisCompactTT K S R β hβ ΔA ΔB I).d_d 2 3 4 rfl rfl z, map_zero, sub_zero]
  · rw [LinearMap.sub_apply, LinearMap.comp_apply, hz, map_zero, sub_zero]
  · have e : hloc ((0 : (globalCx R (GKS K S) T).X 4), -(truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (4 - 1)).mkQ
          ((localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
            (fun v => locMap K S v.1) T).d (3 - 1) (4 - 1) (by omega) z)) =
        h ((localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) T).d (3 - 1) (4 - 1) (by omega) z) := by
      change -(hq (-(truncSub (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T) (4 - 1)).mkQ _)) = _
      rw [map_neg, neg_neg, Submodule.mkQ_apply, Submodule.liftQ_apply]
    show tr ((0 : (globalCx R (GKS K S) T).X 3), (truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) -
        hloc ((galoisCompactTT K S R β hβ ΔA ΔB I).d 3 4 rfl
          ((0 : (globalCx R (GKS K S) T).X 3), (truncSub (localSumCx R (GKS K S)
            (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z)) =
      ∑ v, L.trv v (z v)
    rw [finiteTrace_compact_d_local, hh z]
    erw [e]
    exact add_sub_cancel_right _ _

end Absorb

/-! ### The PRINTs -/

/-- **PRINT — the canonical traces for ONE trivialization, exactly normalized** (Nekovář,
*Selmer complexes*, Astérisque 310 (2006): 5.1.3, p. 114 (`inv_v`); 5.1.5, p. 114 (the reciprocity
law `inv_{S_f} = ∑_{v∈S_f} inv_v`); 5.2.1, pp. 114–115 (`H²_cont(G_v, A(1)) ≅ A`, the homotopy
inverse `r_v`); 5.4.1, pp. 125–126 (`H³_{c,cont}(G_{K,S}, A(1)) ≅ A`, `r_S`, "`r_S ∘ j` is homotopic
to `Σ ∘ (r_{v,J})`"); cited at tex 3454–3456 and 3465–3467). Under lane RC26's finite standing
hypotheses (`NekovarFiniteSetting K S p R`: 5.1 with `(P)`, `R` finite local with nilpotent `p`,
self-injective, so `J = R` is a bounded complex of injectives) and for `T ≅ R(1)`
(`IsCyclotomicTwist`), there are local traces `L` (`FiniteLocalTraces`: Nekovář's `r_v` for one
fixed `T ≅ R(1)`), chosen once for all coefficients and local conditions, such that for any genuine
data — finite discrete `M`, `M'`, an equivariant pairing `β : M × M' → T`, local conditions and
truncated isotropy data — there is a global trace on the truncated compact cone killing coboundaries
and inducing `H³_c(G_{K,S}, T) ≅ R` (Nekovář's `r_J` in degree three), normalized by `L`
(`Normalizes`, lane RC26's `hsum`).

DEPARTURE (exact normalization): Nekovář's relation is up to homotopy; the literal form is
`NekovarFiniteTracesH`, and `nekovarFiniteTraces_of_homotopy` (PROVED) derives this exact form from
it by absorbing the homotopy into the choice of `r_S` (file header, DEPARTURE 1). The other
DEPARTUREs (traces quantified up to units and cone sign conventions, lane RC26's cones,
`J = R`) are listed in the file header. The finite-level mirror of lane RC31's
`NekovarFibreTraces`. -/
def NekovarFiniteTraces (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (p : ℕ) (R : Type) [CommRing R] [IsLocalRing R],
    NekovarFiniteSetting K S p R → ∀ [Fintype (Places K S)] (T : Type)
      [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
      [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T],
      IsCyclotomicTwist K S R T →
      ∃ L : FiniteLocalTraces S R T,
        ∀ (M M' : Type)
          [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M]
          [SMulCommClass (GKS K S) R M] [TopologicalSpace M] [DiscreteTopology M]
          [ContinuousSMul (GKS K S) M]
          [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M']
          [SMulCommClass (GKS K S) R M'] [TopologicalSpace M'] [DiscreteTopology M']
          [ContinuousSMul (GKS K S) M']
          (β : M →ₗ[R] M' →ₗ[R] T)
          (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
          (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
          (I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB),
          ∃ (tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
            (_ : ∀ z, tr ((galoisCompactTT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0),
            InducesIsoH3 tr ∧ L.Normalizes tr

/-- **PRINT — Nekovář 5.4.1 in its literal form** (same locators as `NekovarFiniteTraces`): as
`NekovarFiniteTraces`, with the normalization only up to an explicit homotopy
(`NormalizesUpToHomotopy`: "`r_S ∘ j` is homotopic to `Σ ∘ (r_{v,J})`", p. 126). Implies
`NekovarFiniteTraces` (`nekovarFiniteTraces_of_homotopy`). -/
def NekovarFiniteTracesH (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ (S : Set (HeightOneSpectrum (𝓞 K))) (p : ℕ) (R : Type) [CommRing R] [IsLocalRing R],
    NekovarFiniteSetting K S p R → ∀ [Fintype (Places K S)] (T : Type)
      [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
      [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T],
      IsCyclotomicTwist K S R T →
      ∃ L : FiniteLocalTraces S R T,
        ∀ (M M' : Type)
          [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M]
          [SMulCommClass (GKS K S) R M] [TopologicalSpace M] [DiscreteTopology M]
          [ContinuousSMul (GKS K S) M]
          [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M']
          [SMulCommClass (GKS K S) R M'] [TopologicalSpace M'] [DiscreteTopology M']
          [ContinuousSMul (GKS K S) M']
          (β : M →ₗ[R] M' →ₗ[R] T)
          (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
          (ΔA : GaloisLocalConditions K S R M) (ΔB : GaloisLocalConditions K S R M')
          (I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB),
          ∃ (tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R)
            (_ : ∀ z, tr ((galoisCompactTT K S R β hβ ΔA ΔB I).d 2 3 rfl z) = 0),
            InducesIsoH3 tr ∧ L.NormalizesUpToHomotopy tr

/-- **The literal PRINT implies the exact one**: Nekovář's up-to-homotopy relation
`r_S ∘ j ∼ Σ ∘ (r_v)` can be made exact by changing `r_S` within its homotopy class
(`FiniteLocalTraces.exists_normalizes_of_upToHomotopy`). PROVED. -/
theorem nekovarFiniteTraces_of_homotopy {K : Type} [Field K] [NumberField K]
    (h : NekovarFiniteTracesH K) : NekovarFiniteTraces K := by
  intro S p R _ _ hset _ T _ _ _ _ _ _ _ hT
  obtain ⟨L, hL⟩ := h S p R hset T hT
  refine ⟨L, fun M M' _ _ _ _ _ _ _ _ _ _ _ _ _ _ β hβ ΔA ΔB I => ?_⟩
  obtain ⟨tr, htr, h3, hH⟩ := hL M M' β hβ ΔA ΔB I
  obtain ⟨tr', htr', hag, hN⟩ := L.exists_normalizes_of_upToHomotopy tr htr hH
  exact ⟨tr', htr', finiteTrace_inducesIsoH3_of_agree hag h3, hN⟩

/-- **Consistency with lane RC26: the packet PRINT implies `NekovarProp541T`** (a global trace on
the truncated compact cone killing coboundaries and inducing `H³_c(G_{K,S}, T) ≅ R` exists; there
`S` carries no `Fintype` instance, here it is the one given by `NekovarFiniteSetting.finite_S`).
`NekovarFiniteTraces` strengthens lane RC26's trace PRINT by the normalization. PROVED. -/
theorem nekovarProp541T_of_finiteTraces {K : Type} [Field K] [NumberField K]
    (h : NekovarFiniteTraces K) : NekovarProp541T K := by
  intro S p R _ _ hset M M' T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ β hβ hT ΔA ΔB I
  have : Fintype (Places K S) := hset.finite_S.fintype
  obtain ⟨L, hL⟩ := h S p R hset T hT
  obtain ⟨tr, htr, h3, -⟩ := hL M M' β hβ ΔA ΔB I
  exact ⟨tr, htr, h3⟩

/-! ### Non-vacuity of the packet and of the normalization -/

section NonVacuity

variable {K : Type} [Field K] [NumberField K] (R : Type) [CommRing R] (T : Type) [AddCommGroup T]
  [Module R T]

section Empty

variable [DistribMulAction (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) T]
  [SMulCommClass (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) R T] [TopologicalSpace T]
  [DiscreteTopology T] [ContinuousSMul (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) T]

/-- **The trace packet is a non-vacuous structure (empty `S`)**: for `S = ∅` the empty packet
(as lane RC31's `emptyLocalTraces`). Kind: definition (non-vacuity). -/
def finiteTraceEmpty : FiniteLocalTraces (∅ : Set (HeightOneSpectrum (𝓞 K))) R T where
  trv v := absurd v.2 (Set.notMem_empty _)
  htrv v := absurd v.2 (Set.notMem_empty _)
  iso v := absurd v.2 (Set.notMem_empty _)

/-- **Non-vacuity of `Normalizes` (empty `S`)**: for `S = ∅` every global trace is normalized by
the empty packet (both sides vanish). PROVED. -/
theorem finiteTraceEmpty_normalizes [Fintype (Places K (∅ : Set (HeightOneSpectrum (𝓞 K))))]
    {M M' : Type}
    [AddCommGroup M] [Module R M] [DistribMulAction (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) M]
    [SMulCommClass (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) R M] [TopologicalSpace M]
    [DiscreteTopology M] [ContinuousSMul (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) M]
    [AddCommGroup M'] [Module R M']
    [DistribMulAction (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) M']
    [SMulCommClass (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) R M'] [TopologicalSpace M']
    [DiscreteTopology M'] [ContinuousSMul (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) M']
    {β : M →ₗ[R] M' →ₗ[R] T}
    {hβ : ∀ (g : GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) (a : M) (b : M'),
      β (g • a) (g • b) = g • β a b}
    {ΔA : GaloisLocalConditions K (∅ : Set (HeightOneSpectrum (𝓞 K))) R M}
    {ΔB : GaloisLocalConditions K (∅ : Set (HeightOneSpectrum (𝓞 K))) R M'}
    {I : GaloisTruncIsotropyData K (∅ : Set (HeightOneSpectrum (𝓞 K))) R β hβ ΔA ΔB}
    (tr : (galoisCompactTT K (∅ : Set (HeightOneSpectrum (𝓞 K))) R β hβ ΔA ΔB I).X 3 →ₗ[R] R) :
    (finiteTraceEmpty R T).Normalizes tr := by
  intro z
  have hz : z = 0 := funext fun v => absurd v.2 (Set.notMem_empty _)
  have h0 : ((0 : (globalCx R (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K)))) T).X 3),
      (truncSub (localSumCx R (GKS K (∅ : Set (HeightOneSpectrum (𝓞 K))))
        (fun v : Places K (∅ : Set (HeightOneSpectrum (𝓞 K))) => Gloc K v.1)
        (fun v => locMap K (∅ : Set (HeightOneSpectrum (𝓞 K))) v.1) T) (3 - 1)).mkQ z) =
      (0 : (galoisCompactTT K (∅ : Set (HeightOneSpectrum (𝓞 K))) R β hβ ΔA ΔB I).X 3) := by
    rw [hz, map_zero]
    rfl
  have : IsEmpty (Places K (∅ : Set (HeightOneSpectrum (𝓞 K)))) :=
    ⟨fun v => absurd v.2 (Set.notMem_empty _)⟩
  rw [Finset.univ_eq_empty, Finset.sum_empty]
  exact (congrArg tr h0).trans (map_zero tr)

end Empty

section Zero

variable {S : Set (HeightOneSpectrum (𝓞 K))} [Subsingleton R] [DistribMulAction (GKS K S) T]
  [SMulCommClass (GKS K S) R T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (GKS K S) T]

/-- **The trace packet is a non-vacuous structure at every `S` (zero coefficients)**: over the
zero ring every module is zero, and the zero traces induce `H² ≅ R = 0` at every place.
Kind: definition (non-vacuity). -/
def finiteTraceZero : FiniteLocalTraces S R T where
  trv _ := 0
  htrv _ _ := LinearMap.zero_apply _
  iso v := by
    have hs : Subsingleton ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T v).X 2) := Module.subsingleton R _
    exact ⟨fun z _ _ => ⟨0, Subsingleton.elim _ _⟩, 0, map_zero _, Subsingleton.elim _ _⟩

/-- **Non-vacuity of `Normalizes` at every `S` (zero coefficients)**: over the zero ring every
global trace is normalized by `finiteTraceZero`. PROVED. -/
theorem finiteTraceZero_normalizes [Fintype (Places K S)] {M M' : Type}
    [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
    [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M']
    [SMulCommClass (GKS K S) R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [ContinuousSMul (GKS K S) M']
    {β : M →ₗ[R] M' →ₗ[R] T} {hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b}
    {ΔA : GaloisLocalConditions K S R M} {ΔB : GaloisLocalConditions K S R M'}
    {I : GaloisTruncIsotropyData K S R β hβ ΔA ΔB}
    (tr : (galoisCompactTT K S R β hβ ΔA ΔB I).X 3 →ₗ[R] R) :
    (finiteTraceZero R T (S := S)).Normalizes tr :=
  fun _ => Subsingleton.elim _ _

end Zero

end NonVacuity

/-- Non-vacuity, concretely: the empty packet over `ℚ` for the field `R = ℤ/2` and the trivial
module `T = ℤ/2` (lane RC26's `TrivMod`). PROVED. -/
example : FiniteLocalTraces (∅ : Set (HeightOneSpectrum (𝓞 ℚ))) (ZMod 2)
    (TrivMod (GKS ℚ ∅) (ZMod 2)) :=
  finiteTraceEmpty (ZMod 2) _

/-- Non-vacuity, concretely: the zero-coefficient packet over `ℚ` at every set of places `S`.
PROVED. -/
example (S : Set (HeightOneSpectrum (𝓞 ℚ))) :
    FiniteLocalTraces S PUnit (TrivMod (GKS ℚ S) PUnit) :=
  finiteTraceZero PUnit _

/-! ### The general-shape duality with `hT` discharged -/

section UrOutside

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (R : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {M₀ M₀' T₀ : Type}
  [AddCommGroup M₀] [Module R M₀] [DistribMulAction (GKS K S₀) M₀] [SMulCommClass (GKS K S₀) R M₀]
  [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  [AddCommGroup M₀'] [Module R M₀'] [DistribMulAction (GKS K S₀) M₀']
  [SMulCommClass (GKS K S₀) R M₀'] [TopologicalSpace M₀'] [DiscreteTopology M₀']
  [ContinuousSMul (GKS K S₀) M₀'] [Finite M₀']
  [AddCommGroup T₀] [Module R T₀] [DistribMulAction (GKS K S₀) T₀] [SMulCommClass (GKS K S₀) R T₀]
  [TopologicalSpace T₀] [DiscreteTopology T₀] [ContinuousSMul (GKS K S₀) T₀]
  (β₀ : M₀ →ₗ[R] M₀' →ₗ[R] T₀)
  (hβ₀ : ∀ (g : GKS K S₀) (a : M₀) (b : M₀'), β₀ (g • a) (g • b) = g • β₀ a b)
  (c : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S R (InflMod hS M₀) v)
  (c' : ∀ v : Places K S, v.1 ∈ S₀ → CondAt K S R (InflMod hS M₀') v)
  (hc : ∀ v h, OrthConcentratedAt (c v h)) (hc' : ∀ v h, OrthConcentratedAt (c' v h))
  (hiso : ∀ v h, OrthIsotropicAt (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
    (c v h) (c' v h))
  (trv : ∀ v : Places K S, (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS T₀) v).X 2 →ₗ[R] R)
  (htrv : ∀ v z, trv v ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS T₀) v).d 1 2 rfl z) = 0)

/-- **Round 1's `orthSelmerDuality_urOutside` without the hypothesis `hT`**: the inflation of the
cyclotomic twist `T₀` is a cyclotomic twist over `S` (`cycloInfl_isCyclotomicTwist`). The other
hypotheses are those of the landed statement. PROVED. -/
theorem orthSelmerDuality_urOutside_of_cyclo [Fintype (Places K S)] (h543 : NekovarProp543T K)
    (h756 : NekovarProp756 K) (p : ℕ) [IsLocalRing R] (hset₀ : NekovarFiniteSetting K S₀ p R)
    (hset : NekovarFiniteSetting K S p R) (hb : Function.Bijective β₀)
    (hb' : Function.Bijective β₀.flip) (hT₀ : IsCyclotomicTwist K S₀ R T₀)
    (htrv2 : ∀ v : Places K S, v.1 ∉ S₀ → InducesIsoH2 (trv v))
    (hperf : ∀ (v : Places K S) (h : v.1 ∈ S₀), QuasiIso (GHom.toCC (orthLocalMap (c v h).i
      (c' v h).i (orthUrPair hS R β₀ hβ₀ v) (orthZeroIsotropy (hc v h) (hc' v h) (hiso v h))
      (trv v) (htrv v))))
    (tr : (galoisCompactTT K S R (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
      (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
      (orthOutsideTrunc hS R β₀ hβ₀ c c' hc hc' hiso)).X 3 →ₗ[R] R)
    (htr : ∀ z, tr ((galoisCompactTT K S R (orthInflPair hS R β₀) (orthInflPair_smul hS R β₀ hβ₀)
      (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
      (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
      (orthOutsideTrunc hS R β₀ hβ₀ c c' hc hc' hiso)).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS T₀)).X (3 - 1),
      tr ((0 : (globalCx R (GKS K S) (InflMod hS T₀)).X 3), (truncSub (localSumCx R (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) (InflMod hS T₀)) (3 - 1)).mkQ
          z) = ∑ v, trv v (z v))
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S R (orthInflPair hS R β₀)
      (orthInflPair_smul hS R β₀ hβ₀) (ofCondAt K S R (InflMod hS M₀) (urOutside hS R M₀ c))
      (ofCondAt K S R (InflMod hS M₀') (urOutside hS R M₀' c'))
      (orthOutsideTrunc hS R β₀ hβ₀ c c' hc hc' hiso)) tr htr)) :=
  orthSelmerDuality_urOutside hS R β₀ hβ₀ c c' hc hc' hiso trv htrv h543 h756 p hset₀ hset hb hb'
    hT₀ (cycloInfl_isCyclotomicTwist hS hT₀) htrv2 hperf tr htr hsum htr3

end UrOutside

/-! ### The actual data: the landed duality with the trace packet and `hT` discharged -/

section Actual

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (α : GKS K S₀ →* (Acoef i)ˣ)
  [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
  (B B' : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
  [∀ v, (B' v).IsElliptic]
  (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) (2 ^ i) →+
    ResMod (locMap K S v.1) (MinS hS W i α))
  (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) (2 ^ i)),
    ι v (σ • t) = σ • ι v t)
  (ι' : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B' v) (2 ^ i) →+
    ResMod (locMap K S v.1) (MinS hS W i (charInv α)))
  (hι' : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B' v) (2 ^ i)),
    ι' v (σ • t) = σ • ι' v t)

/-- **Orthogonality for the actual data with a trace packet** (round 1's
`orthogonalComplementsT_actualKummer`): the local traces and `htrv`, `htrv2` are those of a packet
`L` (`FiniteLocalTraces`), and the trace normalization `hsum` is `L.Normalizes tr`. The Kummer
per-place inputs `hisoK` (ELLIOT, tex 3423, 3439–3448) and `hperfK` (ELLIOT, tex 3423, 3439–3450,
3456, stated for the traces of `L`) are kept as in the landed statement. PROVED. -/
theorem orthogonalComplementsT_actualKummer_of_packet [Fintype (Places K S)]
    (h756 : NekovarProp756 K) (hK : IsTotallyComplex K) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hW : FullTorsion K S₀ W (2 ^ i))
    (hisoK : ∀ v h, OrthIsotropicAt (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (orthKummerC hS W i α B ι hι v h) (orthKummerC' hS W i α B' ι' hι' v h))
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (hperfK : ∀ (v : Places K S) (h : v.1 ∈ S₀), QuasiIso (GHom.toCC (orthLocalMap
      (kummerAt v (B v) (2 ^ i) (ι v) (hι v)).i (kummerAt v (B' v) (2 ^ i) (ι' v) (hι' v)).i
      (orthUrPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
        (weilPairingM_smul W hμ₀ (Acoef i) α) v)
      (orthZeroIsotropy (orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) (hisoK v h))
      (L.trv v) (L.htrv₁ v))))
    (tr : (galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK)).X 3 →ₗ[Acoef i]
        Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK)).d 2 3 rfl
          z) = 0)
    (hsum : L.Normalizes tr) :
    OrthogonalComplementsT K (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK) tr htr :=
  orthogonalComplementsT_actualKummer hS W i α hμ₀ B B' ι hι ι' hι' h756 hK hS₀fin h2₀ hW hisoK
    L.trv L.htrv₁ (fun v _ => L.iso v) hperfK tr htr hsum

/-- **Finite Selmer duality for the actual data with a trace packet** (round 1's
`orthSelmerDuality_actualKummer`; Lemma `ex:arith-conjugate-duality`, tex 2761–2830, with tex
3454–3456): the local traces and `htrv`, `htrv2` are those of a packet `L`, the trace
normalization `hsum` is `L.Normalizes tr`, and round 1's GLUE `hT` is discharged
(`cycloInfl_isCyclotomicTwist_tate1`). The Kummer per-place inputs `hisoK`, `hperfK` (ELLIOT) are
kept as in the landed statement. PROVED. -/
theorem orthSelmerDuality_actualKummer_of_packet [Fintype (Places K S)]
    (h543 : NekovarProp543T K) (h756 : NekovarProp756 K) (hSfin : S.Finite)
    (hK : IsTotallyComplex K) (hS₀fin : S₀.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hW : FullTorsion K S₀ W (2 ^ i))
    (hisoK : ∀ v h, OrthIsotropicAt (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (orthKummerC hS W i α B ι hι v h) (orthKummerC' hS W i α B' ι' hι' v h))
    (L : FiniteLocalTraces S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (hperfK : ∀ (v : Places K S) (h : v.1 ∈ S₀), QuasiIso (GHom.toCC (orthLocalMap
      (kummerAt v (B v) (2 ^ i) (ι v) (hι v)).i (kummerAt v (B' v) (2 ^ i) (ι' v) (hι' v)).i
      (orthUrPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
        (weilPairingM_smul W hμ₀ (Acoef i) α) v)
      (orthZeroIsotropy (orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) (hisoK v h))
      (L.trv v) (L.htrv₁ v))))
    (tr : (galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK)).X 3 →ₗ[Acoef i]
        Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK)).d 2 3 rfl
          z) = 0)
    (hsum : L.Normalizes tr) (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) hisoK)) tr htr)) :=
  orthSelmerDuality_actualKummer hS W i α hμ₀ B B' ι hι ι' hι' h543 h756 hSfin
    (cycloInfl_isCyclotomicTwist_tate1 hS i hμ₀) hK hS₀fin h2₀ hW hisoK L.trv L.htrv₁
    (fun v _ => L.iso v) hperfK tr htr hsum htr3

end Actual

end ZInQ.Manuscript.RC.KummerMaps
