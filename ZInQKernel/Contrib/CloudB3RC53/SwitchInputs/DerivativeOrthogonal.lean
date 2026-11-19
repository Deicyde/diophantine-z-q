import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.FibreDualityWiring
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthPlaces

/-!
# RC53 SwitchInputs: the local complement criterion `horth` for the derivative pair

Proposition `ex:limits-uniform-lower-bound`, height-one regularity, the switch at a derivative
place (tex L5055–5086), "The retained localization-duality diagrams give `U = U^⊥`" (tex
L5062–5070, Nekovář 6.3.3–6.3.4); Nekovář, *Selmer complexes* (Astérisque 310, 2006), 6.2.7
(orthogonal complements are defined place by place: `Δ(X₁) ⊥⊥ Δ(X₂)` iff `Δ_v(X₁) ⊥⊥ Δ_v(X₂)` for
every `v`).

`FibreDualityWiring.lean` leaves the hypothesis `horth`
(`FibreOrthogonalComplementsT β … ΔS ΔR I tr htr`) open for the switch `galRelSwitch C c q T`:
strict conditions `ΔS = switchStrK q (old c)` against relaxed conditions
`ΔR = switchRelK q (old c)`, through a self-pairing `β : M × M → T`. This file reduces it to the
places.

**(1) The per-place reduction** (PROVED, from lane RC29's splitting lemma
`orth_localDualityMapT_quasiIso`): `fibreSwitch_horth_of_places` (any RC31 `FibreSwitch`) and
`galRelSwitch_horth_of_places` (the chain's switch). For finitely many places, local traces `tr_v`
killing coboundaries, a global trace whose local part is `∑_v tr_v` (`hsum`; RC31's
`FibreLocalTraces.Normalizes`), and any `τ≥2` isotropy data `I` (they are given place by place:
`I.h v`), `horth` holds as soon as the per-place local duality maps
`Cone(U_v → C(G_v, M))[−1] → Hom_k(U'_v, k)[−3]`, `(u, x) ↦ (y ↦ tr_v(x ∪ i'_v y + h_v(u, y)))`
(`switchPlaceMap`) are quasi-isomorphisms:
* at the switch place `q` (`hq`): strict `τ≤0 = [Z⁰ → 0]` against relaxed `τ≤1 = [C⁰ → Z¹]`;
* at every other place `v ≠ q` (`hold`): the old condition `old c v` against ITSELF (at `v ≠ q`
  both `switchStrK q (old c) v` and `switchRelK q (old c) v` are `old c v`). This is
  per-place self-orthogonality of the old conditions; it is an explicit hypothesis. The
  configuration conditions `SwitchCondsK.A₀`, `Ad` are arbitrary subcomplexes away from a switch
  place, so `hold` is not provable for the chain as stated; see (3) for the standard conditions.

**(2) The switch place: strict `τ≤0` is the orthogonal complement of relaxed `τ≤1`** (PROVED
from the PRINT `NekovarFibreLocalDuality`, Nekovář 5.6.3(i)):
* `TruncShape01` (the shape of the pair: `U` in degree `0` onto `Z⁰(L)`, `U'` in degrees `0, 1`
  onto `L'⁰` and `Z¹(L')`), and `trunc01_quasiIso` (generic, PROVED): if the full local duality map
  `L → Hom_k(L', k)[−2]` has acyclic cone, the per-place local duality map of a `TruncShape01` pair
  is a quasi-isomorphism, for any `τ≥2` isotropy homotopy (on homology: `H¹(L) ≅ H¹(L')^*`,
  `H²(L) ≅ H⁰(L')^*`; the proof adapts lane RC26's cone argument, `coneAdj_solve`, degree by
  degree, with `trunc01_finish`, `dual_factor_of_ker`, `dual_extend_of_injective`);
* `strRelK_truncShape01` (PROVED): the chain's strict `[Z⁰ → 0]` and relaxed `[C⁰ → Z¹]` at the
  switch place have that shape (any field, group, module and old conditions; non-vacuity of
  `TruncShape01`);
* `galRelSwitch_placeMap_q` (PROVED from the PRINT): `hq` at the fibre `k(𝔭)`, for any `τ≥2`
  isotropy data and the local traces of one packet; `galRelSwitch_horth_of_print` (PROVED from
  the PRINT and `hold`): `horth` with only the old places left as hypotheses.

**The step bundle** (alongside `FibreDualityWiring.lean`, whose structures are unchanged):
`FibreSwitchDualityHoldK` (`FibreSwitchDualityK` with a trace packet and `hold` in place of
`horth`), `FibreSwitchDualityHoldK.toK`, `.dual` (PROVED from the PRINTs),
`FibreNonquadStepsHoldK`, `FibreNonquadStepsHoldK.toFibre` and `regular_of_fibreStepsHold`
(PROVED wiring, from `NekovarFibreGlobalDuality` and `NekovarFibreLocalDuality`).

**(3) Finding: the singular side at a characteristic-zero fibre is not self-orthogonal.** For the
standard conditions (`PlaceTameK.std`: `finCond = sideOfSetK I_v`, `singCond = sideOfSetK {φ_v}`)
`hold` asks the finite side, resp. the singular side, to be its own orthogonal complement at each
place outside `c`, resp. in `c`. On homology a self-orthogonal condition `U ⊆ τ≤1` (with
`H⁰(U) = H⁰(G_v, M)`) has `H¹(U)` equal to its own annihilator in `H¹(G_v, M)` under local duality,
so `2 · dim H¹(U) = dim H¹(G_v, M)`.
* In the derivative model at an inert derivative place over a characteristic-zero fibre
  (`Φ = J² = 1`, `q = ℓ² ≠ 1` in `k(𝔭)`; tex L3298–3300) the singular part vanishes
  (`UnrCoords.singular_zero_of_q_ne_one`): `H¹` of the singular side is `0`, while
  `H¹(G_v, M) ≅ coker(Φ − 1) = M ≠ 0` (`UnrCoords.finrank_H1WrelK_of_q_ne_one`). So the singular
  side is NOT self-orthogonal there, and `hold` FAILS for the standard conditions whenever such a
  place carries the singular side.
* In the same model the fibre duality itself has no input: an equivariant self-pairing into a
  twist on which the Frobenius acts by `q` is zero unless `q = 1` when the Frobenius acts trivially
  on `M` (`selfPairing_zero_of_trivial_action`, PROVED below). So the derivative model and the
  perfect self-pairing `β` of RC31's duality are jointly satisfiable only when `q = 1`.
* For the genuine `V_𝔭` at a good inert `ℓ` the Frobenius is not trivial and (Weil bounds) has
  neither `1` nor `q` as an eigenvalue, so `H¹(G_v, V_𝔭) = 0`: every condition is self-orthogonal on
  homology, but there are no `2 + 2` coordinates and the switch step is empty.
This is the constraint of the `2 + 2` shape again (`UnrCoords.two_plus_two_iff_q_eq_one`): Elliot's
isotropic planes `F`, `S` exist only when `q ≡ 1`, i.e. in the inner limit `ℓᵢ → −1` (tex
L5030–5032), and the switch has to be formalised on inner-limit objects. The finite side (cocycles
vanishing on inertia; the unramified condition) is self-orthogonal at places not above `2` where
`M` is unramified (Nekovář 7.5.6; lane RC29's PRINT `NekovarProp756`, for discrete coefficients);
RC31 has no such print for the fibres. (Homological argument recorded, not formalised, except
`selfPairing_zero_of_trivial_action`.)

Kinds: definitions and PROVED (from the hypotheses named in each statement).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.SelmerComplex NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.FibreDuality (FibreSwitch GalTruncIsotropyData galCompactTT galPairDataT
  FibreOrthogonalComplementsT FibreLocalTraces)
open ZInQ.Manuscript.RC.KummerMaps (orthLocalMap orthNeg orthPlaceMap orth_localDualityMapT_quasiIso
  orthLocalMap_apply orthNeg_f_apply)
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)
open ZInQ.Manuscript.RC.FibreDuality (NekovarFibreLocalDuality NekovarFibreSetting IsLatticeTop
  IsTateTwistFibre NekovarFibreGlobalDuality)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.LambdaCoef (IsHeightOneOdd)

/-! ### (1) The per-place reduction -/

section Reduction

variable {k : Type} [Field k] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {M T : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) k T]
  [TopologicalSpace T] [ContinuousAdd T] [ContinuousConstSMul k T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[k] M →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : M × M => β x.1 x.2)

/-- **The per-place local duality map of a fibre switch** (Nekovář 6.2.2, `u⁻_{π,h_v}`): at the
place `v`, `Cone(U_str,v → C(G_v, M))[−1] → Hom_k(U_rel,v, k)[−3]`,
`(u, x) ↦ (y ↦ tr_v(x ∪ i_v y + h_v(u, y)))` (lane RC29's `orthPlaceMap` for `(ΔS, ΔR)`). -/
abbrev switchPlaceMap (X : FibreSwitch K S k M) (I : GalTruncIsotropyData S k β hβ hβc X.ΔS X.ΔR)
    (trv : ∀ v : Places K S, (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0) (v : Places K S) :=
  orthPlaceMap k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ hβc
    X.ΔS X.ΔR I trv htrv v

/-- **`horth` for a fibre switch, place by place** (Nekovář 6.2.7; tex L5062–5070): for finitely
many places, local traces `tr_v` killing coboundaries, a global trace on the truncated compact cone
whose local part is `∑_v tr_v` (`hsum`) and any `τ≥2` isotropy data `I`, the strict and relaxed
conditions of the switch are orthogonal complements once the per-place local duality map is a
quasi-isomorphism at the switch place `q` (`hq`) and at every other place (`hold`).
Classification: PROVED (lane RC29's `orth_localDualityMapT_quasiIso`). -/
theorem fibreSwitch_horth_of_places [Fintype (Places K S)] (X : FibreSwitch K S k M)
    (I : GalTruncIsotropyData S k β hβ hβc X.ΔS X.ΔR)
    (trv : ∀ v : Places K S, (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (tr : (galCompactTT S k β hβ hβc X.ΔS X.ΔR I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc X.ΔS X.ΔR I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx k (GKS K S) T).X 3), (truncSub (localSumCx k (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (q : Places K S)
    (hq : QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc X I trv htrv q)))
    (hold : ∀ v, v ≠ q → QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc X I trv htrv v))) :
    FibreOrthogonalComplementsT β hβ hβc X.ΔS X.ΔR I tr htr :=
  orth_localDualityMapT_quasiIso k (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) β hβ hβc X.ΔS X.ΔR I trv htrv tr htr hsum (fun v => by
      by_cases h : v = q
      · subst h
        exact hq
      · exact hold v h)

/-- **`horth` for a fibre switch from RC31's trace packet, place by place**: as
`fibreSwitch_horth_of_places`, with the local traces of one packet `L : FibreLocalTraces` and a
global trace normalized by it (`L.Normalizes tr`, RC31's form of `hsum`). Classification: PROVED. -/
theorem fibreSwitch_horth_of_packet [Fintype (Places K S)] (X : FibreSwitch K S k M)
    (I : GalTruncIsotropyData S k β hβ hβc X.ΔS X.ΔR) (L : FibreLocalTraces S k T)
    (tr : (galCompactTT S k β hβ hβc X.ΔS X.ΔR I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc X.ΔS X.ΔR I).d 2 3 rfl z) = 0)
    (hsum : L.Normalizes tr) (q : Places K S)
    (hq : QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc X I L.trv (fun v z => L.htrv v z) q)))
    (hold : ∀ v, v ≠ q →
      QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc X I L.trv (fun v z => L.htrv v z) v))) :
    FibreOrthogonalComplementsT β hβ hβc X.ΔS X.ΔR I tr htr :=
  fibreSwitch_horth_of_places β hβ hβc X I L.trv (fun v z => L.htrv v z) tr htr hsum q hq hold

variable (C : SwitchCondsK k K S M) (c : Finset (Places K S)) (q : Places K S)
  (Tq : TameCoordinatesTrivialK k (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q))

/-- **`horth` for the chain's switch, place by place** (tex L5055–5086 with Nekovář 6.2.7): for
`galRelSwitch C c q Tq`, the strict/relaxed derivative conditions at `q` and the old conditions
`old c` elsewhere are orthogonal complements once (at `q`) strict `τ≤0` is orthogonal to relaxed
`τ≤1` and (at `v ≠ q`) each old condition `old c v` is its own orthogonal complement.
Classification: PROVED (from `fibreSwitch_horth_of_places`). -/
theorem galRelSwitch_horth_of_places [Fintype (Places K S)]
    (I : GalTruncIsotropyData S k β hβ hβc (galRelSwitch C c q Tq).ΔS (galRelSwitch C c q Tq).ΔR)
    (trv : ∀ v : Places K S, (localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).X 2 →ₗ[k] k)
    (htrv : ∀ v z, trv v ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T v).d 1 2 rfl z) = 0)
    (tr : (galCompactTT S k β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I).X 3 →ₗ[k] k)
    (htr : ∀ z, tr ((galCompactTT S k β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) T).X (3 - 1),
      tr ((0 : (globalCx k (GKS K S) T).X 3), (truncSub (localSumCx k (GKS K S)
        (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) T) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (hq : QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc (galRelSwitch C c q Tq) I trv htrv q)))
    (hold : ∀ v, v ≠ q →
      QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc (galRelSwitch C c q Tq) I trv htrv v))) :
    FibreOrthogonalComplementsT β hβ hβc (galRelSwitch C c q Tq).ΔS (galRelSwitch C c q Tq).ΔR I
      tr htr :=
  fibreSwitch_horth_of_places β hβ hβc (galRelSwitch C c q Tq) I trv htrv tr htr hsum q hq hold

/-- At a place `v ≠ q` the strict condition complex of the chain's switch is the old condition
`old c v` (so the per-place hypothesis `hold` pairs `old c v` with itself). PROVED. -/
theorem galRelSwitch_US_ne {v : Places K S} (hv : v ≠ q) :
    (galRelSwitch C c q Tq).US v = (C.old c v).cx := by
  unfold galRelSwitch
  dsimp only
  rw [switchStrK, ite_eq_right hv]

/-- At a place `v ≠ q` the relaxed condition complex of the chain's switch is the old condition
`old c v`. PROVED. -/
theorem galRelSwitch_UR_ne {v : Places K S} (hv : v ≠ q) :
    (galRelSwitch C c q Tq).ΔR.U v = (C.old c v).cx := by
  unfold galRelSwitch
  dsimp only [galCond]
  rw [switchRelK, ite_eq_right hv]

end Reduction

/-! ### (2) At the switch place: strict `τ≤0` against relaxed `τ≤1` -/

section Trunc01

variable {k : Type} [Field k]

/-- **A linear form vanishing on `ker g` factors through `g`** (over a field: through
`V/ker g ≅ im g`, then extended from `im g`). PROVED. -/
theorem dual_factor_of_ker {V W : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (g : V →ₗ[k] W) (f : V →ₗ[k] k) (h : ∀ v, g v = 0 → f v = 0) :
    ∃ z : W →ₗ[k] k, ∀ v, z (g v) = f v := by
  let f₁ : (V ⧸ LinearMap.ker g) →ₗ[k] k := (LinearMap.ker g).liftQ f (fun v hv => h v hv)
  let f₂ : LinearMap.range g →ₗ[k] k := f₁ ∘ₗ g.quotKerEquivRange.symm.toLinearMap
  obtain ⟨z, hz⟩ := LinearMap.exists_extend f₂
  refine ⟨z, fun v => ?_⟩
  have h1 := LinearMap.congr_fun hz ⟨g v, LinearMap.mem_range_self g v⟩
  simp only [LinearMap.comp_apply, Submodule.coe_subtype] at h1
  rw [h1]
  simp only [f₂, f₁, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- **A linear form extends along an injective linear map** (over a field). PROVED. -/
theorem dual_extend_of_injective {V W : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (ι : V →ₗ[k] W) (hι : Function.Injective ι) (φ : V →ₗ[k] k) :
    ∃ z : W →ₗ[k] k, ∀ v, z (ι v) = φ v := by
  obtain ⟨r, hr⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hι)
  exact ⟨φ ∘ₗ r, fun v => by rw [LinearMap.comp_apply, ← LinearMap.comp_apply r ι, hr,
    LinearMap.id_apply]⟩

/-- **The shape of the pair (strict `τ≤0`, relaxed `τ≤1`)** of condition maps `iU : U → L`,
`iU' : U' → L'` into complexes concentrated in degrees `≥ 0`: `U` lives in degree `0` and maps
injectively onto the `0`-cocycles `Z⁰(L)`; `U'` lives in degrees `0, 1`, maps isomorphically onto
`L'⁰` in degree `0` and injectively onto the `1`-cocycles `Z¹(L')` in degree `1` (tex L5060–5061:
`D⁰ = τ≤0`, relaxed `τ≤1 = [C⁰ → Z¹]`). Kind: definition (non-vacuity: `strRelK_truncShape01`,
for every switch place of every genuine local complex). -/
structure TruncShape01 {U U' L L' : GCx k} (iU : GHom U L) (iU' : GHom U' L') : Prop where
  /-- `L` vanishes in negative degrees. -/
  hLneg : ∀ n, n < 0 → Subsingleton (L.X n)
  /-- `L'` vanishes in negative degrees. -/
  hL'neg : ∀ n, n < 0 → Subsingleton (L'.X n)
  /-- `U` lives in degree `0`. -/
  hUz : ∀ n, n ≠ 0 → Subsingleton (U.X n)
  /-- `U'` lives in degrees `0, 1`. -/
  hU'z : ∀ n, n ≠ 0 → n ≠ 1 → Subsingleton (U'.X n)
  /-- `iU` is injective. -/
  hUinj : ∀ n m (h : n = m), Function.Injective (iU.f n m h)
  /-- `iU` hits the `0`-cocycles. -/
  hU0 : ∀ n m (h : n = m) m' (h' : m + 1 = m'), n = 0 → ∀ x : L.X m, L.d m m' h' x = 0 →
    ∃ u, iU.f n m h u = x
  /-- `iU'` is injective. -/
  hU'inj : ∀ n, Function.Injective (iU'.f n n rfl)
  /-- `iU'` is onto in degree `0`. -/
  hU'0 : ∀ n, n = 0 → Function.Surjective (iU'.f n n rfl)
  /-- `iU'` hits the `1`-cocycles. -/
  hU'1 : ∀ n m (h : n + 1 = m), n = 1 → ∀ y : L'.X n, L'.d n m h y = 0 →
    ∃ y₁, iU'.f n n rfl y₁ = y

variable {U U' L L' E : GCx k} (iU : GHom U L) (iU' : GHom U' L')
  (P : GPair L L' E) (J : LocalTruncIsotropy iU iU' P) (trv : E.X 2 →ₗ[k] k)
  (htrv : ∀ z, trv (E.d 1 2 rfl z) = 0)

/-- **The primitive in degrees `j ≥ 2`**: a cycle `((u, x), φ)` of the cone of the per-place local
duality map, with `u = 0` (the condition `U` lives in degree `0`), has a primitive as soon as some
`z : Hom(L'^{4−j}, k)` restricts to `φ` on `U'` and satisfies `tr(x ∪ y) = (−1)^j z(dy)` on
`L'^{3−j}`: solve `de' = −x` with `tr(e' ∪ ·) + (−1)^{j−1} z'(d ·) = z` by the acyclicity of the
cone of the full local duality map (lane RC26's `coneAdj_solve`), and take `((0, e'), −z' ∘ i')`.
PROVED. -/
theorem trunc01_finish (htrv2 : ∀ z, trv (E.d (2 - 1) 2 (by omega) z) = 0)
    (hacyc : GAcyclic (coneCx (adjHom P 2 trv htrv2)))
    (hUz : ∀ n, n ≠ 0 → Subsingleton (U.X n))
    (i j l : ℤ) (hij : i + 1 = j) (hjl : j + 1 = l) (hj : 2 ≤ j)
    (u : U.X j) (x : L.X (j - 1)) (φ : (dualCx U' 3).X (j - 1))
    (hc : (coneCx (orthLocalMap iU iU' P J trv htrv)).d j l hjl
      ((((u, x) : coneT (orthNeg iU) j), φ) : coneT (orthLocalMap iU iU' P J trv htrv) j) = 0)
    (z : Module.Dual k (L'.X (3 - (j - 1))))
    (ha : ∀ y : U'.X (3 - (j - 1)), z (iU'.f _ _ rfl y) = asDual φ y)
    (hb : ∀ y : L'.X (3 - (l - 1)), trv (P.P (j - 1) (3 - (l - 1)) 2 (by omega) x y) =
      PairedFunctional.sgn (j - 2) • z (L'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y)) :
    ∃ c', (coneCx (orthLocalMap iU iU' P J trv htrv)).d i j hij c' =
      ((((u, x) : coneT (orthNeg iU) j), φ) : coneT (orthLocalMap iU iU' P J trv htrv) j) := by
  have := hUz j (by omega)
  have hu : u = 0 := Subsingleton.elim _ _
  have h1 : (orthNeg iU).f j (l - 1) (by omega) u - L.d (j - 1) (l - 1) (by omega) x = 0 :=
    congrArg (fun w => w.1.2) hc
  rw [hu, map_zero, zero_sub, neg_eq_zero] at h1
  have he : L.d (j - 1) (l - 1) (by omega) (-x) = 0 := by rw [map_neg, h1, neg_zero]
  have hz : ∀ y : L'.X (3 - (l - 1)), trv (P.P (j - 1) (3 - (l - 1)) 2 (by omega) (-x) y) =
      (-(PairedFunctional.sgn (j - 1 - 1))) • z (L'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y) := by
    intro y
    rw [show j - 1 - 1 = j - 2 by ring, LinearMap.map_neg₂, map_neg, hb y, neg_smul]
  obtain ⟨e', z', he', hz'⟩ := coneAdj_solve P trv htrv2 hacyc (i - 1) (j - 1) (l - 1) (by omega)
    (by omega) (3 - (l - 1)) (3 - (j - 1)) (3 - (i - 1)) (by omega) (by omega) (by omega) (-x) z he hz
  let φ' : Module.Dual k (U'.X (3 - (i - 1))) := -(z'.comp (iU'.f (3 - (i - 1)) (3 - (i - 1)) rfl))
  refine ⟨((((0 : U.X i), e') : coneT (orthNeg iU) i), φ'), ?_⟩
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · change U.d i j hij 0 = u
    rw [map_zero, hu]
  · change (orthNeg iU).f i (j - 1) (by omega) 0 - L.d (i - 1) (j - 1) (by omega) e' = x
    rw [map_zero, zero_sub, he', neg_neg]
  · refine dualCx_ext fun y => ?_
    change asDual ((orthLocalMap iU iU' P J trv htrv).f i (j - 1) (by omega)
        ((0, e') : coneT (orthNeg iU) i)) y -
      asDual ((dualCx U' 3).d (i - 1) (j - 1) (by omega) φ') y = asDual φ y
    rw [orthLocalMap_apply, LinearMap.map_zero₂, add_zero]
    erw [dualCx_d_apply]
    have hcomm := iU'.comm (3 - (j - 1)) (3 - (i - 1)) (3 - (j - 1)) (3 - (i - 1)) rfl (by omega)
      (by omega) rfl y
    have h3 : asDual φ' (U'.d (3 - (j - 1)) (3 - (i - 1)) (by omega) y) =
        -z' (L'.d (3 - (j - 1)) (3 - (i - 1)) (by omega) (iU'.f _ _ rfl y)) := by
      change -(z' (iU'.f (3 - (i - 1)) (3 - (i - 1)) rfl
        (U'.d (3 - (j - 1)) (3 - (i - 1)) _ y))) = _
      rw [hcomm]
    rw [h3, ← ha y, ← hz' (iU'.f _ _ rfl y), sgn_pred (i - 1)]
    simp only [zsmul_eq_mul, Int.cast_neg, smul_neg, neg_neg]
    ring

/-- **Strict `τ≤0` is the orthogonal complement of relaxed `τ≤1`, from local duality** (Nekovář
6.2.7 at one place; tex L5060–5071): for condition maps of the shape `TruncShape01`, a local cup
product `P : L × L' → E`, any `τ≥2` isotropy homotopy `J` and a local trace `tr` killing
coboundaries, if the full local duality map `L → Hom_k(L', k)[−2]`, `a ↦ (b ↦ tr(a ∪ b))` has
acyclic cone (it is a quasi-isomorphism: Nekovář 5.2.4/5.6.3(i)), then the per-place local duality
map `Cone(U → L)[−1] → Hom_k(U', k)[−3]` is a quasi-isomorphism. On homology this is
`H¹(L) ≅ H¹(L')^*` and `H²(L) ≅ H⁰(L')^*`; the proof is the cone chase, degree by degree (`≤ 0`:
the cycles vanish; `1`: `Z⁰(L)` comes from `U`; `2`: injectivity of `H¹(L) → H¹(L')^*`, by
factoring through `d`; `≥ 3`: extension along `U' → L'`, then `trunc01_finish`). PROVED. -/
theorem trunc01_quasiIso (htrv2 : ∀ z, trv (E.d (2 - 1) 2 (by omega) z) = 0)
    (hacyc : GAcyclic (coneCx (adjHom P 2 trv htrv2)))
    (hS : TruncShape01 iU iU') :
    QuasiIso (GHom.toCC (orthLocalMap iU iU' P J trv htrv)) := by
  obtain ⟨hLneg, hL'neg, hUz, hU'z, hUinj, hU0, hU'inj, hU'0, hU'1⟩ := hS
  refine quasiIso_of_coneCx_acyclic _ (fun i j l hij hjl c hc => ?_)
  obtain ⟨⟨u, x⟩, φ⟩ := c
  have h1 : (orthNeg iU).f j (l - 1) (by omega) u - L.d (j - 1) (l - 1) (by omega) x = 0 :=
    congrArg (fun w => w.1.2) hc
  have h2 : ∀ y : U'.X (3 - (l - 1)),
      trv (P.P (j - 1) (3 - (l - 1)) 2 (by omega) x (iU'.f _ _ rfl y) +
        J.h j (3 - (l - 1)) 2 (by omega) u y) =
      (-(PairedFunctional.sgn (j - 1))) • asDual φ (U'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y) := by
    intro y
    have h : asDual ((orthLocalMap iU iU' P J trv htrv).f j (l - 1) (by omega)
        ((u, x) : coneT (orthNeg iU) j)) y -
        asDual ((dualCx U' 3).d (j - 1) (l - 1) (by omega) φ) y = 0 :=
      LinearMap.congr_fun (congrArg Prod.snd hc) y
    erw [orthLocalMap_apply, dualCx_d_apply] at h
    exact sub_eq_zero.mp h
  rcases (show j ≤ 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with hj | hj | hj | hj
  · -- degrees `≤ 0`: the cycle is zero
    have hx : x = 0 := (hLneg (j - 1) (by omega)).elim _ _
    have hu : u = 0 := by
      by_cases hj0 : j = 0
      · rw [hx, map_zero, sub_zero, orthNeg_f_apply, neg_eq_zero] at h1
        exact hUinj j (l - 1) (by omega) (h1.trans (map_zero _).symm)
      · exact (hUz j hj0).elim _ _
    have hφ : φ = 0 := by
      have := hU'z (3 - (j - 1)) (by omega) (by omega)
      exact dualCx_ext fun y => by rw [Subsingleton.elim y 0, map_zero, map_zero]
    refine ⟨0, ?_⟩
    rw [map_zero, hu, hx, hφ]
    rfl
  · -- degree `1`: `x ∈ Z⁰` comes from the condition
    have hu : u = 0 := (hUz j (by omega)).elim _ _
    rw [hu, map_zero, zero_sub, neg_eq_zero] at h1
    obtain ⟨u', hu'⟩ := hU0 i (j - 1) (by omega) (l - 1) (by omega) (by omega) (-x)
      (by rw [map_neg, h1, neg_zero])
    refine ⟨((((u', 0) : coneT (orthNeg iU) i)), 0), ?_⟩
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · exact (hUz j (by omega)).elim _ _
    · change (orthNeg iU).f i (j - 1) (by omega) u' - L.d (i - 1) (j - 1) (by omega) 0 = x
      rw [map_zero, sub_zero, orthNeg_f_apply, hu', neg_neg]
    · have := hU'z (3 - (j - 1)) (by omega) (by omega)
      exact dualCx_ext fun y => by rw [Subsingleton.elim y 0, map_zero, map_zero]
  · -- degree `2`: injectivity of `H¹(L) → H¹(L')^*`
    have hu : u = 0 := (hUz j (by omega)).elim _ _
    have hf : ∀ y, L'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y = 0 →
        trv (P.P (j - 1) (3 - (l - 1)) 2 (by omega) x y) = 0 := by
      intro y hy
      obtain ⟨y₁, rfl⟩ := hU'1 (3 - (l - 1)) (3 - (j - 1)) (by omega) (by omega) y hy
      have h := h2 y₁
      rw [hu, LinearMap.map_zero₂, add_zero] at h
      have : Subsingleton (U'.X (3 - (j - 1))) := hU'z _ (by omega) (by omega)
      rw [h, Subsingleton.elim (U'.d (3 - (l - 1)) (3 - (j - 1)) (by omega) y₁) 0, map_zero,
        smul_zero]
    obtain ⟨z₀, hz₀⟩ := dual_factor_of_ker (L'.d (3 - (l - 1)) (3 - (j - 1)) (by omega))
      (trv ∘ₗ P.P (j - 1) (3 - (l - 1)) 2 (by omega) x) (fun y hy => hf y hy)
    refine trunc01_finish iU iU' P J trv htrv htrv2 hacyc hUz i j l hij hjl (by omega) u x φ hc
      (PairedFunctional.sgn (j - 2) • z₀) (fun y => ?_) (fun y => ?_)
    · have : Subsingleton (U'.X (3 - (j - 1))) := hU'z _ (by omega) (by omega)
      rw [Subsingleton.elim y 0]
      simp
    · rw [LinearMap.smul_apply, smul_smul, sgn_mul_self, one_smul, hz₀]
      rfl
  · -- degrees `≥ 3`: extend `φ` along the injective condition map
    have hu : u = 0 := (hUz j (by omega)).elim _ _
    obtain ⟨z, hz⟩ := dual_extend_of_injective (iU'.f (3 - (j - 1)) (3 - (j - 1)) rfl) (hU'inj _)
      (asDual φ)
    refine trunc01_finish iU iU' P J trv htrv htrv2 hacyc hUz i j l hij hjl (by omega) u x φ hc z hz
      (fun y => ?_)
    obtain ⟨y₀, rfl⟩ : ∃ y₀, iU'.f (3 - (l - 1)) (3 - (l - 1)) rfl y₀ = y := by
      by_cases h3 : j = 3
      · exact hU'0 _ (by omega) y
      · have := hL'neg (3 - (l - 1)) (by omega)
        exact ⟨0, Subsingleton.elim _ _⟩
    have h := h2 y₀
    rw [hu, LinearMap.map_zero₂, add_zero] at h
    rw [h, ← iU'.comm (3 - (l - 1)) (3 - (j - 1)) (3 - (l - 1)) (3 - (j - 1)) rfl (by omega)
      (by omega) rfl y₀, hz, show j - 2 = j - 1 - 1 by ring, sgn_pred, neg_smul, neg_smul]
    rw [neg_neg, sgn_pred (j - 1), sgn_pred j, neg_neg]

end Trunc01

/-! ### The strict and relaxed derivative conditions have the shape `TruncShape01` -/

section Shape

variable {k : Type} [Field k] {ι : Type} [DecidableEq ι]
  {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)]
  {Mv : ι → Type} [∀ v, AddCommGroup (Mv v)] [∀ v, Module k (Mv v)]
  [∀ v, DistribMulAction (Gv v) (Mv v)] [∀ v, SMulCommClass (Gv v) k (Mv v)]
  [∀ v, TopologicalSpace (Mv v)] [∀ v, ContinuousAdd (Mv v)]
  [∀ v, ContinuousConstSMul k (Mv v)] [∀ v, ContinuousSMul (Gv v) (Mv v)]

/-- The extension by zero of an `ℕ`-indexed complex vanishes in negative degrees. PROVED. -/
theorem natCx_subsingleton_neg (Kc : CochainComplex (ModuleCat.{0} k) ℕ) (n : ℤ) (hn : n < 0) :
    Subsingleton ((natCx Kc).X n) := by
  rcases n with n | n
  · exact absurd hn (not_lt.mpr (Int.natCast_nonneg n))
  · exact (inferInstance : Subsingleton PUnit)

/-- A submodule equal to `⊥` is a subsingleton. PROVED. -/
theorem subsingleton_of_eq_bot {V : Type} [AddCommGroup V] [Module k V] (p : Submodule k V)
    (h : p = ⊥) : Subsingleton p := by
  subst h
  infer_instance

/-- **The strict and relaxed derivative conditions at a switch place have the shape
`TruncShape01`** (tex L5060–5061): `[Z⁰ → 0] → C(G_q, M)` (through the relaxed condition) and
`[C⁰ → Z¹] → C(G_q, M)`, for every family of old conditions, every topological group and every
topological module (non-vacuity of `TruncShape01`). PROVED. -/
theorem strRelK_truncShape01 (q : ι) (old : ∀ v, SubFam (locCxK k Gv Mv v)) :
    TruncShape01 (ghomComp (SubFam.inclLe (switch_hsrK q old q)) (switchRelK k Gv Mv q old q).incl)
      (switchRelK k Gv Mv q old q).incl where
  hLneg n hn := natCx_subsingleton_neg _ n hn
  hL'neg n hn := natCx_subsingleton_neg _ n hn
  hUz n hn := by
    change Subsingleton ↥((switchStrK k Gv Mv q old q).S n)
    rw [switchStr_qK]
    rcases n with (_ | _ | n) | n
    · exact absurd rfl hn
    · exact subsingleton_of_eq_bot _ rfl
    · exact subsingleton_of_eq_bot _ rfl
    · exact subsingleton_of_eq_bot _ rfl
  hU'z n hn hn1 := by
    change Subsingleton ↥((switchRelK k Gv Mv q old q).S n)
    rw [switchRel_qK]
    rcases n with (_ | _ | n) | n
    · exact absurd rfl hn
    · exact absurd rfl hn1
    · exact subsingleton_of_eq_bot _ rfl
    · exact subsingleton_of_eq_bot _ rfl
  hUinj n m h := by
    subst h
    intro a b hab
    exact Subtype.ext hab
  hU0 n m h m' h' hn x hx := by
    subst h hn h'
    have hmem : x ∈ (switchStrK k Gv Mv q old q).S 0 := by
      rw [switchStr_qK]
      exact hx
    exact ⟨⟨x, hmem⟩, rfl⟩
  hU'inj n a b hab := Subtype.ext hab
  hU'0 n hn x := by
    subst hn
    have hmem : x ∈ (switchRelK k Gv Mv q old q).S 0 := by
      rw [switchRel_qK]
      exact (Submodule.mem_top : x ∈ (⊤ : Submodule k ((locCxK k Gv Mv q).X 0)))
    exact ⟨⟨x, hmem⟩, rfl⟩
  hU'1 n m h hn y hy := by
    subst hn h
    have hmem : y ∈ (switchRelK k Gv Mv q old q).S 1 := by
      rw [switchRel_qK]
      exact hy
    exact ⟨⟨y, hmem⟩, rfl⟩

end Shape

/-! ### At the fibres: `hq` from the local duality PRINT, and `horth` from `hold` -/

section Fibre

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {P : Ideal Lambda} [P.IsPrime] [IsHeightOneOdd P]
  {M T : Type}
  [AddCommGroup M] [Module (ResAt P) M] [Module Lambda M] [IsScalarTower Lambda (ResAt P) M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) (ResAt P) M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul (ResAt P) M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup T] [Module (ResAt P) T] [Module Lambda T] [IsScalarTower Lambda (ResAt P) T]
  [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) (ResAt P) T] [TopologicalSpace T]
  [IsTopologicalAddGroup T] [ContinuousConstSMul (ResAt P) T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[ResAt P] M →ₗ[ResAt P] T)
  (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : M × M => β x.1 x.2)
  (C : SwitchCondsK (ResAt P) K S M) (c : Finset (Places K S)) (q : Places K S)
  (Tq : TameCoordinatesTrivialK (ResAt P) (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q))

open Classical in
/-- **`hq`: at the switch place, strict `τ≤0` is the orthogonal complement of relaxed `τ≤1`**
(tex L5060–5071; Nekovář 6.2.7 at `q` from 5.6.3(i)): for the chain's switch at the fibre
`k(𝔭)`, any `τ≥2` isotropy data and the local traces of one packet `L`, the per-place local duality
map at `q` is a quasi-isomorphism. Classification: PROVED from the PRINT
`NekovarFibreLocalDuality` (with `trunc01_quasiIso` and `strRelK_truncShape01`). -/
theorem galRelSwitch_placeMap_q (hL : NekovarFibreLocalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T) (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR) (L : FibreLocalTraces S (ResAt P) T) :
    QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc (galRelSwitch C c q Tq) I L.trv
      (fun v z => L.htrv v z) q)) :=
  trunc01_quasiIso _ _ _ (I.toLocal q) (L.trv q) (fun z => L.htrv q z) (L.htrv q)
    (coneCx_acyclic_of_quasiIso _ (hL S P hset M M T hM hM hTl hT β hβ hβc hb hb' q (L.trv q)
      (L.htrv q) (L.iso q)))
    (strRelK_truncShape01 q (C.old c))

/-- **`horth` for the chain's switch at the fibre, modulo per-place self-orthogonality of the old
conditions** (tex L5055–5086; Nekovář 6.2.7): the hypothesis `horth` of `FibreDualityWiring.lean`
holds for the canonical trace packet once each old condition `old c v`, `v ≠ q`, is its own
orthogonal complement (`hold`); the switch place is discharged by `galRelSwitch_placeMap_q`.
Classification: PROVED from the PRINT `NekovarFibreLocalDuality` and the hypothesis `hold` (which
FAILS for the standard singular side at a characteristic-zero fibre; finding (3)). -/
theorem galRelSwitch_horth_of_print [Fintype (Places K S)] (hL : NekovarFibreLocalDuality K)
    (hset : NekovarFibreSetting K S) (hM : IsLatticeTop (GKS K S) M)
    (hTl : IsLatticeTop (GKS K S) T) (hT : IsTateTwistFibre K S P T) (hb : Function.Bijective β)
    (hb' : Function.Bijective β.flip)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR) (L : FibreLocalTraces S (ResAt P) T)
    (tr : (galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I).d 2 3 rfl z) = 0)
    (hsum : L.Normalizes tr)
    (hold : ∀ v, v ≠ q → QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc (galRelSwitch C c q Tq) I
      L.trv (fun v z => L.htrv v z) v))) :
    FibreOrthogonalComplementsT β hβ hβc (galRelSwitch C c q Tq).ΔS (galRelSwitch C c q Tq).ΔR I
      tr htr :=
  fibreSwitch_horth_of_packet β hβ hβc (galRelSwitch C c q Tq) I L tr htr hsum q
    (galRelSwitch_placeMap_q β hβ hβc C c q Tq hL hset hM hTl hT hb hb' I L) hold

end Fibre

/-! ### The fibre step bundle with `hold` in place of `horth` -/

section Bundle

open ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.UniformSwitch

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  [Fintype (Places K S)]
  {P : Ideal Lambda} [P.IsPrime] [IsHeightOneOdd P]
  {M T : Type}
  [AddCommGroup M] [Module (ResAt P) M] [Module Lambda M] [IsScalarTower Lambda (ResAt P) M]
  [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) (ResAt P) M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul (ResAt P) M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup T] [Module (ResAt P) T] [Module Lambda T] [IsScalarTower Lambda (ResAt P) T]
  [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) (ResAt P) T] [TopologicalSpace T]
  [IsTopologicalAddGroup T] [ContinuousConstSMul (ResAt P) T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[ResAt P] M →ₗ[ResAt P] T)
  (hβ : ∀ (g : GKS K S) (a b : M), β (g • a) (g • b) = g • β a b)
  (hβc : Continuous fun x : M × M => β x.1 x.2)
  (C : SwitchCondsK (ResAt P) K S M) (c : Finset (Places K S)) (q : Places K S)
  (Tq : TameCoordinatesTrivialK (ResAt P) (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q))

/-- **The fibre duality data at one switch step, with the local complement criterion reduced to
the old places** (tex L5055–5075): as `FibreSwitchDualityK`, but the trace comes with one packet
of local traces `L` normalizing it (`hsum`) and the field `horth` is replaced by `hold` — each old
condition `old c v`, `v ≠ q`, is its own orthogonal complement under the per-place local duality
map. The switch place is discharged by `galRelSwitch_placeMap_q` (PRINT
`NekovarFibreLocalDuality`), see `FibreSwitchDualityHoldK.toK`. Classification: hypothesis
(structure); `hold` FAILS for the standard singular side at a characteristic-zero fibre
(finding (3)). No non-vacuity instance: like `FibreSwitchDualityK`, it is a conditional interface
whose inputs (with `TameCoordinatesTrivialK`) are not jointly satisfiable at one genuine
characteristic-zero derivative place (`GenericNonVacuity.not_tameCoordinatesTrivialK_of_tame`,
finding (3)); its intended instances are the inner-limit objects. -/
structure FibreSwitchDualityHoldK where
  /-- Truncated isotropy data for (strict, relaxed). -/
  I : GalTruncIsotropyData S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
    (galRelSwitch C c q Tq).ΔR
  /-- One packet of local traces. -/
  L : FibreLocalTraces S (ResAt P) T
  /-- The trace on the truncated compact cone. -/
  tr : (galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
    (galRelSwitch C c q Tq).ΔR I).X 3 →ₗ[ResAt P] ResAt P
  /-- The trace kills coboundaries. -/
  htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
    (galRelSwitch C c q Tq).ΔR I).d 2 3 rfl z) = 0
  /-- The trace induces `H³_c ≅ k(𝔭)`. -/
  htr3 : InducesIsoH3 tr
  /-- The trace is normalized by the local traces. -/
  hsum : L.Normalizes tr
  /-- The old conditions are self-orthogonal at the places `v ≠ q`. -/
  hold : ∀ v, v ≠ q → QuasiIso (GHom.toCC (switchPlaceMap β hβ hβc (galRelSwitch C c q Tq) I
    L.trv (fun v z => L.htrv v z) v))
  /-- The switch-pairing constant `ε`. -/
  ε : ResAt P
  /-- The switch-pairing constant `σ`. -/
  σ : ResAt P
  /-- The switch-pairing matrix `J`. -/
  J : Matrix (Fin 2) (Fin 2) (ResAt P)
  hε : ε ≠ 0
  hσ : σ ≠ 0
  hJ2 : J * J = 1
  /-- The switch coordinates (ELLIOT). -/
  hsw : (galRelSwitch C c q Tq).SwitchCoordinates (galPairDataT S (ResAt P) β hβ hβc
    (galRelSwitch C c q Tq).ΔS (galRelSwitch C c q Tq).ΔR I) tr ε σ J

variable {β hβ hβc C c q Tq}

/-- **The bundle with `hold` gives `FibreSwitchDualityK`** (tex L5062–5070): its field `horth` is
`galRelSwitch_horth_of_print`. Classification: PROVED from the PRINT `NekovarFibreLocalDuality`. -/
def FibreSwitchDualityHoldK.toK (d : FibreSwitchDualityHoldK β hβ hβc C c q Tq)
    (hL : NekovarFibreLocalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) :
    FibreSwitchDualityK β hβ hβc C c q Tq where
  I := d.I
  tr := d.tr
  htr := d.htr
  htr3 := d.htr3
  horth := galRelSwitch_horth_of_print β hβ hβc C c q Tq hL hset hM hTl hT hb hb' d.I d.L d.tr
    d.htr d.hsum d.hold
  ε := d.ε
  σ := d.σ
  J := d.J
  hε := d.hε
  hσ := d.hσ
  hJ2 := d.hJ2
  hsw := d.hsw

/-- **The named duality input from the bundle with `hold`** (tex L5062–5070). Classification:
PROVED from the PRINTs `NekovarFibreGlobalDuality` and `NekovarFibreLocalDuality`. -/
theorem FibreSwitchDualityHoldK.dual (d : FibreSwitchDualityHoldK β hβ hβc C c q Tq)
    (hG : NekovarFibreGlobalDuality K) (hL : NekovarFibreLocalDuality K)
    (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) :
    LocalizationDualityInput d.ε d.σ d.J d.hε d.hσ d.hJ2 (galRelK C c q Tq).U :=
  (d.toK hL hset hM hTl hT hb hb').dual hG hset hM hTl hT hb hb'

variable {A F : Type} [CommRing A] [Field F] {ι : A →+* F} (ρ : A →+* ResAt P)

open Classical

variable (β hβ hβc C) (c₀ : Finset (Places K S)) (t : A)
  (zAct : (selCx (galoisSelData K S (ResAt P) M
    (condAt K S (ResAt P) M (galCond K S M C.A₀) (galCond K S M C.Ad) c₀))).toCC.X 1)
  (hzAct : ((selCx (galoisSelData K S (ResAt P) M
    (condAt K S (ResAt P) M (galCond K S M C.A₀) (galCond K S M C.Ad) c₀))).toCC.d 1 2).hom
      zAct = 0)
  (lamAct : (selCx (galoisSelData K S (ResAt P) M
    (condAt K S (ResAt P) M (galCond K S M C.A₀) (galCond K S M C.Ad) c₀))).toCC.X 2
      →ₗ[ResAt P] ResAt P)
  (hlamAct : ∀ y, lamAct (((selCx (galoisSelData K S (ResAt P) M
    (condAt K S (ResAt P) M (galCond K S M C.A₀) (galCond K S M C.Ad) c₀))).toCC.d 1 2).hom
      y) = 0)

/-- **The genuine nonquadratic steps at a fibre with the bundle with `hold`** (tex L4997–5003,
L5055–5086): `FibreNonquadStepsK` with `FibreSwitchDualityK` replaced by
`FibreSwitchDualityHoldK`. Classification: GLUE (input). -/
def FibreNonquadStepsHoldK (stage : Finset (Places K S) → TwoTermStage ι) : Prop :=
  ∀ c : Finset (Places K S),
    Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c →
    ¬ (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ →
    1 < (stage c).fiberDim ρ →
    ∃ (q : Places K S) (_ : q ∉ c)
      (Tq : TameCoordinatesTrivialK (ResAt P) (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q)),
      C.AdmissibleAt q ∧ Nonempty (CoordStep ι (stage c).u (stage (insert q c)).u) ∧
      Nonempty (FibreSwitchDualityHoldK β hβ hβc C c q Tq) ∧
        finPlane (ResAt P) (Fin 2 → ResAt P) (Fin 2 → ResAt P) ≤ (galRelK C c q Tq).U

variable {β hβ hβc C ρ c₀ t zAct hzAct lamAct hlamAct}

/-- **The steps with `hold` give the steps of `FibreDualityWiring.lean`** (the switch place
discharged by the local duality PRINT). Classification: PROVED from the PRINT
`NekovarFibreLocalDuality`. -/
theorem FibreNonquadStepsHoldK.toFibre {stage : Finset (Places K S) → TwoTermStage ι}
    (H : FibreNonquadStepsHoldK β hβ hβc C ρ c₀ t zAct hzAct lamAct hlamAct stage)
    (hL : NekovarFibreLocalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) :
    FibreNonquadStepsK β hβ hβc C ρ c₀ t zAct hzAct lamAct hlamAct stage := by
  intro c hc hnq h1
  obtain ⟨q, hq, Tq, hadm, hcs, ⟨d⟩, hdet⟩ := H c hc hnq h1
  exact ⟨q, hq, Tq, hadm, hcs, ⟨d.toK hL hset hM hTl hT hb hb'⟩, hdet⟩

/-- **Regularity at a fibre with the bundle with `hold`** (tex L4976–5195): as
`regular_of_fibreSteps`, with the step field `FibreNonquadStepsHoldK`. Classification: PROVED from
the PRINTs `NekovarFibreGlobalDuality`, `NekovarFibreLocalDuality` and the stated inputs. -/
theorem regular_of_fibreStepsHold [IsLocalRing A] (hι : Function.Injective ι)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {u : F}
    (hG : NekovarFibreGlobalDuality K) (hL : NekovarFibreLocalDuality K)
    (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (X : GaloisInputsK C ρ c₀ t zAct hzAct lamAct hlamAct ι u)
    (H : FibreNonquadStepsHoldK β hβ hβc C ρ c₀ t zAct hzAct lamAct hlamAct X.stage) :
    ∃ a : A, ι a = u :=
  regular_of_fibreSteps hι hρ hG hset hM hTl hT hb hb' X
    (H.toFibre hL hset hM hTl hT hb hb')

end Bundle

/-! ### (3) The self-pairing at a place with trivial Frobenius -/

section SelfPairing

variable {k : Type} [Field k] {G M T : Type} [Monoid G] [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [AddCommGroup T] [Module k T] [DistribMulAction G T]

/-- **An equivariant pairing is zero when an element acting trivially on `M` acts on the target by
a scalar `q ≠ 1`**: `β(a, b) = β(g a, g b) = g β(a, b) = q β(a, b)`. At a derivative place of the
model (`Φ = 1` on `M`, `Φ = q` on `k(𝔭)(1)`, `q = ℓ² ≠ 1` in characteristic zero) there is no
nonzero equivariant self-pairing into the Tate twist, so RC31's perfect `β` and the derivative
model are jointly satisfiable only when `q = 1`. Classification: PROVED. -/
theorem selfPairing_zero_of_trivial_action (β : M →ₗ[k] M →ₗ[k] T)
    (hβ : ∀ (g : G) (a b : M), β (g • a) (g • b) = g • β a b) (g : G) (q : k)
    (hM : ∀ m : M, g • m = m) (hT : ∀ t : T, g • t = q • t) (hq : q ≠ 1) (a b : M) :
    β a b = 0 := by
  have h := hβ g a b
  rw [hM a, hM b, hT] at h
  have h2 : (q - 1) • β a b = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hq)

end SelfPairing

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
