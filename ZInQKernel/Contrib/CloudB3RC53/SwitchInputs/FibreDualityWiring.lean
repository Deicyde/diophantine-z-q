import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.GenericAtFibre
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.FibreSwitch
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.NonVacuity

/-!
# RC53 SwitchInputs: the duality input of the field-generic chain at the fibres, from lane RC31

Proposition `ex:limits-uniform-lower-bound`, height-one regularity, tex L4976–5195; the switch at a
derivative place, tex L5055–5086, with "The retained localization-duality diagrams give
`U = U^⊥`" (tex L5062–5070, Nekovář 6.3.3–6.3.4).

The field-generic chain (`GenericWiring.lean`) takes the localization duality
`LocalizationDualityInput ε σ J … (galRelK C c q T).U` as a NAMED input (a field of
`GenuineNonquadStepsK`, hence of `GaloisInputsK`). This file discharges it at the fibres
`k = k(𝔭) = ResAt 𝔭`, `M = V_𝔭` through lane RC31's consumers (`FibreSwitch.adjunction_of_prints`,
`fibreSelmerDualityT`), modulo RC31's prints, which enter as hypotheses named after them (PRINT):
`NekovarFibreGlobalDuality` (Nekovář 5.6.3(ii); the Selmer duality is obtained from it as in
6.8.1/6.3.4) and `NekovarFibreTraces` (the canonical
traces, Nekovář 5.1.3–5.4.1 with 5.6.1).

Nodes:
* `galRelSwitch` (GLUE, PROVED): the genuine relaxed localization of the chain at a switch place is
  an RC31 `FibreSwitch` — relaxed conditions `switchRelK`, strict conditions `switchStrK`, the
  quotient `W_rel = relWK` and the coordinates `eRAtK`; `galRelSwitch_toQuasi` (PROVED, `rfl`):
  its `toQuasi` IS the chain's `galRelK C c q T`. So the shapes meet definitionally, over any
  field `k`.
* `fibreSwitchDualityFromSelmer` (GLUE, PROVED): an RC31 `FibreSwitch` with Selmer pairing data,
  the 6.3.4 quasi-isomorphism and the switch coordinates gives the chain's `DualityFromSelmer`
  (the duality input of the quadratic candidates, `GaloisWiringQuad.lean`).
* `galRelK_localizationDualityInput` (PROVED, any `k`, from the quasi-isomorphism `hγ`).
* At the fibres (`k = ResAt 𝔭`, a lattice-topologised `M` with a perfect continuous equivariant
  self-pairing `β : M × M → T`, `T ≅ k(𝔭)(1)`):
  `fibreSwitchDualityFromSelmer_of_prints`, `galRelK_switchDualityAdjunction_of_prints`,
  `galRelK_localizationDualityInput_of_prints` (PROVED from the PRINT `NekovarFibreGlobalDuality`);
  `galRelSwitch_exists_trace` (PROVED from the PRINT `NekovarFibreTraces`: a trace killing
  coboundaries and inducing `H³_c ≅ k(𝔭)` exists), `galRelK_localizationDualityInput_of_traces`
  (PROVED from both PRINTs, with orthogonality and coordinates required for the canonical traces,
  the constant `ε` depending on the trace).
* `FibreSwitchDualityK` (hypothesis bundle at one step: truncated isotropy data, a trace, the local
  complement criterion `horth`, the switch coordinates `hsw`), `FibreSwitchDualityK.dual`,
  `FibreSwitchDualityK.toDualityFromSelmer` (PROVED from the PRINT); `FibreNonquadStepsK` (the
  genuine steps with the duality replaced by `FibreSwitchDualityK`),
  `FibreNonquadStepsK.toGenuine` (PROVED from the PRINT: fills the duality field of
  `GenuineNonquadStepsK`), `GaloisInputsK.ofFibreSteps`, `regular_of_fibreSteps` (PROVED wiring:
  `GaloisInputsK` at `k = ResAt 𝔭` with the duality from the PRINT, and regularity `∃ a, ι a = u`).
* At `M = V_𝔭(α) = VP K S W 𝔭 α`: `betaSelf` (= `betaT`, read as a self-pairing; `VP` does not
  depend on `α` as a type), `vp_smul_inv`, `betaSelf_smul` (PROVED when `ᾱ⁻¹ = ᾱ` on `k(𝔭)`, i.e.
  the residual character is quadratic), `betaSelf_bijective`, `betaSelf_flip_bijective`,
  `continuous_betaSelf` (PROVED, from RC31's `betaT_*`); `galRelK_localizationDualityInput_VP`,
  `FibreNonquadStepsK.toGenuine_VP` (PROVED from the PRINT: every coefficient hypothesis
  discharged; the remaining step data cannot hold at a genuine place (open limit (3))).
* Non-vacuity at RC31's instance (`E_1 : y² = x(x − 1)(x + 3)` over `ℚ`, `S6`, `𝔭 = (t)`):
  `resChar_alphaLam_inv` (PROVED: the residual character is quadratic; RC28's `alphaLam` is the
  trivial character everywhere),
  `betaSelf_E1` (PROVED under RC28's GLUE `HasFullTwoTorsion ℚ S6 curveE1`, as in RC31's
  `betaConj_E1`): all coefficient hypotheses of `galRelK_localizationDualityInput_VP` hold; and
  RC31's `exFibreSwitch` over the fibre field `k((t)) = ResAt (t)` (`example`).

**Open limit (1): the local complement criterion per pair.** The hypothesis `horth`
(`FibreOrthogonalComplementsT β … ΔS ΔR I tr htr`, Nekovář 6.2.7) is the orthogonality of the
strict conditions `ΔS = switchStrK q (old c)` against the relaxed conditions
`ΔR = switchRelK q (old c)` of the switch. RC31 discharges it only for the full/zero pairs (tex
L2813–2814: "A full condition is paired with the zero condition"): `fibreOrthogonal_relaxed_strictT`
(full against zero, PROVED) and `fibreOrthogonal_strict_relaxedT_of_print` (zero against full, from
the PRINT `NekovarFibreLocalDuality`, Nekovář 5.6.3(i)) — conditions that are full or zero at EVERY
place. Our pair is not of that form: at the switch place `q` it is `[Z⁰ → 0]` against `[C⁰ → Z¹]`
(the strict/relaxed derivative conditions), and at the other places the old conditions of `c`
against themselves (the finite side `sideOfSetK I_v`, resp. the singular side `sideOfSetK {φ_v}`,
at the derivative places). Those derivative pairs are ours, and `horth` remains an explicit
hypothesis here (a field of `FibreSwitchDualityK`). `NekovarFibreLocalDuality` is therefore not
consumed by this file.
The text's orthogonality (tex 4866–4873) is for the transported duality (at a split place `v`
against the conjugate place `τv`, tex 2810–2813, with Kummer conditions at `2N`), not for an
equivariant self-pairing place by place; for the chain's conditions `fibreConds` (unramified at
every place of `S`, including those above 2) self-orthogonality fails at `v ∣ 2`
(`dim H¹_ur = h⁰ < ½ dim H¹(K_v, V)`).

**Open limit (2): per fixed `𝔭` only.** Everything here is at ONE height-one prime `𝔭` and one
switch place `q`. The chain's step data also carries the switch coordinates
`H¹(W_rel) ≅ k² × k²` (the GLUE `TameCoordinatesTrivialK`, through `eRAtK`) and the coordinate
identity `hsw` (`FibreSwitch.SwitchCoordinates`, ELLIOT, tex L2816–2818, L5035–5038). The `2 + 2`
shape exists only when `q ≡ 1` in the coefficient field (`UnrCoords.two_plus_two_iff_q_eq_one`,
`two_plus_two_iff_ell`; `GenericNonVacuity.not_tameCoordinatesTrivialK_of_tame`): at a single inert
derivative prime `ℓ`, `q = ℓ² ≠ 1` (tex L3298–3300) in `k(𝔭)` of characteristic zero kills the
singular part. The text's shape is reached only in the inner limit `ℓᵢ → −1` (tex L5030–5032). So at
a fixed `𝔭` the discharge below is conditional on step data that cannot all hold at one genuine
derivative prime; the switch needs the inner-limit / `Λ`-adic objects across the derivative primes.
The PRINT `NekovarFibreComparison` (Nekovář 3.7.4(ii), 4.2.2: fibre cohomology versus the `Λ`-adic
tower) is the bridge such a route would use; it is not consumed at a fixed `𝔭`.

**Open limit (3): the self-pairing is incompatible with the tame coordinates.** A
`TameCoordinatesTrivialK` at `q` makes `G_{K_q}` act trivially on `M`; with a perfect
`G_{K,S}`-equivariant `β : M × M → T` and `IsTateTwistFibre K S P T` this forces `G_{K_q}` to act
trivially on `T ≅ k(𝔭)(1)`, i.e. the cyclotomic character to be trivial on the decomposition group
at `q`, which is false at every place of a number field. So the hypotheses of
`galRelK_localizationDualityInput_of_prints`, `galRelK_switchDualityAdjunction_of_prints`,
`FibreSwitchDualityK.dual`, `.toDualityFromSelmer` and `galRelK_localizationDualityInput_VP` never
hold together for genuine objects, and `FibreNonquadStepsK` with the hypotheses of `toGenuine` holds
only when no switch is demanded. **The `V_𝔭(α)` case is vacuous:** `hα` (quadratic residual
character) is the quadratic case (tex 5005–5007), where `GenuineNonquadStepsK` holds trivially.
The route meant to be non-vacuous is `InnerLimitWiring.lean`: the switch steps on the inner-limit
objects (derivative labels with `q → 1`), with the duality from RC31's retained-data certificate,
where no fixed-fibre self-pairing is required and the local planes are Lagrangian.

**RC31's DEPARTURE.** RC31 proves the duality at `k(𝔭)` directly: Nekovář 6.8.1 with
`R = Λ/𝔭`, `𝒮 = R ∖ {0}`, `R_𝒮 = k(𝔭)` (Print.lean), instead of the text's route (duality over
`Λ_𝔭`, then specialisation to the residue field). The consumers used here inherit this: the
dualities are `k(𝔭)`-linear statements about `V_𝔭`-coefficients, with no specialisation step.

**Shape (self-pairing).** `FibreSwitch.adjunction_of_prints` pairs `C_str(M)` with `C_rel(M)` for
the SAME module, through a self-pairing `M × M → T`. On `V_𝔭(α)` RC31's Weil pairing `betaT` pairs
`V_𝔭(α)` with `V_𝔭(α⁻¹)`; it is a self-pairing exactly when the residual character is quadratic
(`resChar 𝔭 α⁻¹ = resChar 𝔭 α`), which holds at RC31's instance because RC28's `alphaLam ℚ S` is the
trivial character (`alphaLam_apply`), not the text's moving character; for the genuine character it
holds only at `𝔭 = (t), (t+2)`. For the text's transported form `(v, w) ↦ β(v, J w)` (tex
L2798–2805, RC31's `betaConj` against `τ^*V_𝔭(α)`, for `α ∘ c = α⁻¹`) the adjunction would pair
`C_str(V_𝔭(α))` with `C_rel(τ^*V_𝔭(α))`; the `FibreSwitch` shape does not cover that, and it is not
wired here.

Kinds: definitions, GLUE and PROVED (from the stated PRINT and hypotheses).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Manuscript.RC.SelmerComplex NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.FibreDuality (FibreSwitch NekovarFibreGlobalDuality NekovarFibreSetting
  NekovarFibreTraces IsLatticeTop IsTateTwistFibre GalTruncIsotropyData galCompactTT galPairDataT
  FibreOrthogonalComplementsT Tate1P betaT betaT_smul betaT_bijective betaT_flip_bijective
  continuous_betaT isLatticeTop_vp' isLatticeTop_tate1P isTateTwistFibre_tate1P
  hasTwoPowerRoots_of_fullTwoTorsion fibreSelmerDualityT S6 nekovarFibreSetting_S6 alphaLam_apply
  exFibreSwitch)
open ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.LambdaCoef (IsHeightOneOdd VP resChar HasFullTwoTorsion curveE1 Pt0
  alphaLam IsContChar)

/-! ### The genuine relaxed localization is an RC31 `FibreSwitch` (any field) -/

section Generic

variable {k : Type} [Field k] {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) k M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul (GKS K S) M]
  (C : SwitchCondsK k K S M) (c : Finset (Places K S)) (q : Places K S)
  (T : TameCoordinatesTrivialK k (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q))

open Classical in
/-- **The genuine relaxed localization at `q` as an RC31 `FibreSwitch`** (tex L5055–5086): relaxed
conditions `switchRelK q (old c)` (`[C⁰ → Z¹]` at `q`), strict conditions `switchStrK q (old c)`
(`[Z⁰ → 0]` at `q`), the inclusions `strict → relaxed`, the quotient `W_rel = relWK`, the quotient
map, and the coordinates `eRAtK` of the chain. Degreewise exactness of
`0 → ∏ U_str → ∏ U_rel → W_rel → 0` is that of a quotient by a submodule. Classification:
definition (degreewise exactness PROVED). -/
def galRelSwitch : FibreSwitch K S k M where
  ΔR := galCond K S M (switchRelK k (gGvK K S) (gMvK K S M) q (C.old c))
  US v := (switchStrK k (gGvK K S) (gMvK K S M) q (C.old c) v).cx
  φ v := SubFam.inclLe (switch_hsrK q (C.old c) v)
  W := relWK (switch_hsrK q (C.old c))
  g := quotMk (strRelK (switch_hsrK q (C.old c)))
  hfg _ u := (Submodule.Quotient.mk_eq_zero _).mpr ⟨u, rfl⟩
  φ_inj n _ _ h := funext fun v => SubFam.inclLe_injective (switch_hsrK q (C.old c) v) n
    (congrFun h v)
  g_surj n := quotMk_surjective _ n
  ex _ _ hu := (Submodule.Quotient.mk_eq_zero _).mp hu
  eR := eRAtK (switch_hsrK q (C.old c)) (switch_relAtK q (C.old c)) (C.D.φ q) (C.D.σ q) T.eM T

/-- **The shapes meet**: the relaxed localization of `galRelSwitch` is the chain's `galRelK`
(definitional). Classification: PROVED (`rfl`). -/
theorem galRelSwitch_toQuasi : (galRelSwitch C c q T).toQuasi = galRelK C c q T := rfl

/-- **An RC31 `FibreSwitch` with Selmer duality gives the chain's `DualityFromSelmer`** (tex
L5060–5071): the strict condition `∏ U_str → U_rel`, its degreewise exactness, the pairing data
`Q` between `C_str` and `C_rel`, the trace, the 6.3.4 quasi-isomorphism `hγ` and the switch
coordinates `hsw` are exactly the fields of `DualityFromSelmer X.toQuasi`. Classification:
definition (repackaging). -/
def fibreSwitchDualityFromSelmer (X : FibreSwitch K S k M) (Q : SelPairData X.Dstr X.toQuasi.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (hsw : X.SwitchCoordinates Q tr ε σ J) : DualityFromSelmer X.toQuasi where
  Ustr := piCx X.US
  f := piMap X.φ
  hfg := X.hfg
  hf := X.φ_inj
  hg := X.g_surj
  hex := X.ex
  Q := Q
  tr := tr
  htr := htr
  ε := ε
  σ := σ
  J := J
  hε := hε
  hσ := hσ
  hJ2 := hJ2
  hγ := hγ
  hsw := hsw

/-- **`U = U^⊥` for the chain's relaxed image, from Selmer duality** (tex L5062–5070), over any
field: RC31's `FibreSwitch.localizationDualityInput` at `galRelSwitch`. Classification: PROVED (from
the quasi-isomorphism `hγ` and the coordinates `hsw`). -/
theorem galRelK_localizationDualityInput
    (Q : SelPairData (galRelSwitch C c q T).Dstr (galRelSwitch C c q T).toQuasi.D)
    (tr : (coneCx Q.resE).X 3 →ₗ[k] k) (htr : ∀ z, tr ((coneCx Q.resE).d 2 3 rfl z) = 0)
    (ε σ : k) (J : Matrix (Fin 2) (Fin 2) k) (hε : ε ≠ 0) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hγ : QuasiIso (GHom.toCC (selmerDualityMap Q tr htr)))
    (hsw : (galRelSwitch C c q T).SwitchCoordinates Q tr ε σ J) :
    LocalizationDualityInput ε σ J hε hσ hJ2 (galRelK C c q T).U :=
  (galRelSwitch C c q T).localizationDualityInput Q tr htr ε σ J hε hσ hJ2 hγ hsw

end Generic

/-! ### At the fibres: the duality from RC31's PRINT -/

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

/-- **`DualityFromSelmer` at a fibre switch, from the PRINT** (tex L5062–5075; Nekovář 6.8.1 with
6.3.4): the quasi-isomorphism of `DualityFromSelmer` is RC31's `fibreSelmerDualityT`.
Classification: PROVED from the PRINT `NekovarFibreGlobalDuality`, the local complement criterion
`horth` (open limit (1)) and the switch coordinates `hsw` (ELLIOT). -/
def fibreSwitchDualityFromSelmer_of_prints (X : FibreSwitch K S (ResAt P) M)
    (hG : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc X.ΔS X.ΔR)
    (tr : (galCompactTT S (ResAt P) β hβ hβc X.ΔS X.ΔR I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc X.ΔS X.ΔR I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr) (horth : FibreOrthogonalComplementsT β hβ hβc X.ΔS X.ΔR I tr htr)
    (ε σ : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P)) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hJ2 : J * J = 1)
    (hsw : X.SwitchCoordinates (galPairDataT S (ResAt P) β hβ hβc X.ΔS X.ΔR I) tr ε σ J) :
    DualityFromSelmer X.toQuasi :=
  fibreSwitchDualityFromSelmer X (galPairDataT S (ResAt P) β hβ hβc X.ΔS X.ΔR I) tr htr ε σ J hε hσ
    hJ2 (fibreSelmerDualityT β hβ hβc hG hset hM hM hTl hT hb hb' X.ΔS X.ΔR I tr htr htr3 horth) hsw

variable (C : SwitchCondsK (ResAt P) K S M) (c : Finset (Places K S)) (q : Places K S)
  (Tq : TameCoordinatesTrivialK (ResAt P) (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q))

/-- **The switch duality adjunction for the chain's relaxed localization at a fibre** (tex
L5055–5075): RC31's `FibreSwitch.adjunction_of_prints` at `galRelSwitch`, whose relaxed
localization is `galRelK C c q Tq`. Classification: PROVED from the PRINT
`NekovarFibreGlobalDuality`, `horth` (open limit (1)) and `hsw` (ELLIOT). -/
theorem galRelK_switchDualityAdjunction_of_prints
    (hG : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR)
    (tr : (galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr)
    (horth : FibreOrthogonalComplementsT β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I tr htr)
    (ε σ : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P)) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hJ2 : J * J = 1)
    (hsw : (galRelSwitch C c q Tq).SwitchCoordinates (galPairDataT S (ResAt P) β hβ hβc
      (galRelSwitch C c q Tq).ΔS (galRelSwitch C c q Tq).ΔR I) tr ε σ J) :
    SwitchDualityAdjunction (galRelK C c q Tq) (galRelSwitch C c q Tq).Dstr ε σ J hε hσ hJ2
      (galRelSwitch C c q Tq).δ (galRelSwitch C c q Tq).hex :=
  (galRelSwitch C c q Tq).adjunction_of_prints hG hset hM hTl hT β hβ hβc hb hb' I tr htr htr3
    horth ε σ J hε hσ hJ2 hsw

/-- **The named duality input of the chain at a fibre** (tex L5062–5070):
`LocalizationDualityInput ε σ J … (galRelK C c q Tq).U`, i.e. `U^⊥ = U` for the switch pairing.
Classification: PROVED from the PRINT `NekovarFibreGlobalDuality`, `horth` (open limit (1)) and
`hsw` (ELLIOT). -/
theorem galRelK_localizationDualityInput_of_prints
    (hG : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR)
    (tr : (galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I).X 3 →ₗ[ResAt P] ResAt P)
    (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I).d 2 3 rfl z) = 0)
    (htr3 : InducesIsoH3 tr)
    (horth : FibreOrthogonalComplementsT β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR I tr htr)
    (ε σ : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P)) (hε : ε ≠ 0) (hσ : σ ≠ 0)
    (hJ2 : J * J = 1)
    (hsw : (galRelSwitch C c q Tq).SwitchCoordinates (galPairDataT S (ResAt P) β hβ hβc
      (galRelSwitch C c q Tq).ΔS (galRelSwitch C c q Tq).ΔR I) tr ε σ J) :
    LocalizationDualityInput ε σ J hε hσ hJ2 (galRelK C c q Tq).U :=
  localizationDualityInput_of_adjunction (galRelK C c q Tq) (galRelSwitch C c q Tq).Dstr ε σ J hε
    hσ hJ2 _ _ (galRelK_switchDualityAdjunction_of_prints β hβ hβc C c q Tq hG hset hM hTl hT hb
      hb' I tr htr htr3 horth ε σ J hε hσ hJ2 hsw)

omit [Module Lambda M] [IsScalarTower Lambda (ResAt P) M] in
/-- **The traces exist, from the PRINT `NekovarFibreTraces`** (Nekovář 5.1.3–5.4.1 with 5.6.1):
for the chain's (strict, relaxed) pair at `q` and any truncated isotropy data, there is a trace on
the truncated compact cone killing coboundaries and inducing `H³_c ≅ k(𝔭)`. Classification: PROVED
from the PRINT. -/
theorem galRelSwitch_exists_trace (hTr : NekovarFibreTraces K) (hset : NekovarFibreSetting K S)
    [Fintype (Places K S)] (hTl : IsLatticeTop (GKS K S) T) (hT : IsTateTwistFibre K S P T)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR) :
    ∃ (tr : (galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
        (galRelSwitch C c q Tq).ΔR I).X 3 →ₗ[ResAt P] ResAt P)
      (_ : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
        (galRelSwitch C c q Tq).ΔR I).d 2 3 rfl z) = 0), InducesIsoH3 tr := by
  obtain ⟨_, hL⟩ := hTr S P hset T hTl hT
  obtain ⟨tr, htr, h3, -⟩ := hL M M β hβ hβc _ _ I
  exact ⟨tr, htr, h3⟩

/-- **The named duality input from both PRINTs** (tex L5062–5070): the trace is supplied by
`NekovarFibreTraces`; the local complement criterion (open limit (1)) and the switch coordinates
(ELLIOT) are required for every trace killing coboundaries and inducing `H³_c ≅ k(𝔭)`; the
constant `ε` depends on the trace (tex 5035–5038: `ε ∈ k^×`). The conclusion is the duality input
for some `ε ≠ 0`. Classification: PROVED from the PRINTs `NekovarFibreGlobalDuality` and
`NekovarFibreTraces`. (Restated: an earlier form with one `ε` for every trace contradicted
`NekovarFibreTraces`.) -/
theorem galRelK_localizationDualityInput_of_traces
    (hG : NekovarFibreGlobalDuality K) (hTr : NekovarFibreTraces K)
    (hset : NekovarFibreSetting K S) [Fintype (Places K S)]
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (I : GalTruncIsotropyData S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
      (galRelSwitch C c q Tq).ΔR)
    (σ : ResAt P) (J : Matrix (Fin 2) (Fin 2) (ResAt P)) (hσ : σ ≠ 0) (hJ2 : J * J = 1)
    (hall : ∀ (tr : (galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
        (galRelSwitch C c q Tq).ΔR I).X 3 →ₗ[ResAt P] ResAt P)
      (htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
        (galRelSwitch C c q Tq).ΔR I).d 2 3 rfl z) = 0), InducesIsoH3 tr →
      ∃ ε : ResAt P, ε ≠ 0 ∧
        FibreOrthogonalComplementsT β hβ hβc (galRelSwitch C c q Tq).ΔS
          (galRelSwitch C c q Tq).ΔR I tr htr ∧
        (galRelSwitch C c q Tq).SwitchCoordinates (galPairDataT S (ResAt P) β hβ hβc
          (galRelSwitch C c q Tq).ΔS (galRelSwitch C c q Tq).ΔR I) tr ε σ J) :
    ∃ (ε : ResAt P) (hε : ε ≠ 0), LocalizationDualityInput ε σ J hε hσ hJ2 (galRelK C c q Tq).U := by
  obtain ⟨tr, htr, h3⟩ := galRelSwitch_exists_trace β hβ hβc C c q Tq hTr hset hTl hT I
  obtain ⟨ε, hε, horth, hsw⟩ := hall tr htr h3
  exact ⟨ε, hε, galRelK_localizationDualityInput_of_prints β hβ hβc C c q Tq hG hset hM hTl hT hb
    hb' I tr htr h3 horth ε σ J hε hσ hJ2 hsw⟩

/-- **The fibre duality data at one switch step** (tex L5055–5075): for the chain's relaxed
localization `galRelK C c q Tq` (as `galRelSwitch`), truncated isotropy data for the
(strict, relaxed) pair, a trace killing coboundaries and inducing `H³_c ≅ k(𝔭)`, the local
complement criterion `horth` for the derivative pair (open limit (1): not discharged by RC31), the
switch-pairing constants and the switch coordinates `hsw` (ELLIOT, tex L2816–2818, L5035–5038).
Classification: hypothesis (structure). -/
structure FibreSwitchDualityK where
  /-- Truncated isotropy data for (strict, relaxed). -/
  I : GalTruncIsotropyData S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
    (galRelSwitch C c q Tq).ΔR
  /-- The trace on the truncated compact cone. -/
  tr : (galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
    (galRelSwitch C c q Tq).ΔR I).X 3 →ₗ[ResAt P] ResAt P
  /-- The trace kills coboundaries. -/
  htr : ∀ z, tr ((galCompactTT S (ResAt P) β hβ hβc (galRelSwitch C c q Tq).ΔS
    (galRelSwitch C c q Tq).ΔR I).d 2 3 rfl z) = 0
  /-- The trace induces `H³_c ≅ k(𝔭)`. -/
  htr3 : InducesIsoH3 tr
  /-- The local complement criterion for the derivative pair (open limit (1)). -/
  horth : FibreOrthogonalComplementsT β hβ hβc (galRelSwitch C c q Tq).ΔS
    (galRelSwitch C c q Tq).ΔR I tr htr
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

/-- **The fibre duality data give the named duality input** (tex L5062–5070). Classification:
PROVED from the PRINT `NekovarFibreGlobalDuality`. -/
theorem FibreSwitchDualityK.dual (d : FibreSwitchDualityK β hβ hβc C c q Tq)
    (hG : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) :
    LocalizationDualityInput d.ε d.σ d.J d.hε d.hσ d.hJ2 (galRelK C c q Tq).U :=
  galRelK_localizationDualityInput_of_prints β hβ hβc C c q Tq hG hset hM hTl hT hb hb' d.I d.tr
    d.htr d.htr3 d.horth d.ε d.σ d.J d.hε d.hσ d.hJ2 d.hsw

/-- **The fibre duality data give the chain's `DualityFromSelmer`** for `galRelK C c q Tq` (the
duality input of the quadratic candidates). Classification: PROVED from the PRINT
`NekovarFibreGlobalDuality`. -/
def FibreSwitchDualityK.toDualityFromSelmer (d : FibreSwitchDualityK β hβ hβc C c q Tq)
    (hG : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) :
    DualityFromSelmer (galRelK C c q Tq) :=
  fibreSwitchDualityFromSelmer_of_prints β hβ hβc (galRelSwitch C c q Tq) hG hset hM hTl hT hb hb'
    d.I d.tr d.htr d.htr3 d.horth d.ε d.σ d.J d.hε d.hσ d.hJ2 d.hsw

/-! ### Filling the duality field of `GenuineNonquadStepsK` / `GaloisInputsK` at `k = ResAt 𝔭` -/

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

/-- **The genuine nonquadratic steps at a fibre with the fibre duality data** (tex L4997–5003,
L5055–5086): `GenuineNonquadStepsK` with the field `LocalizationDualityInput …` replaced by
`FibreSwitchDualityK` (the inputs of RC31's consumer). Classification: hypothesis (ELLIOT: new
derivative prime, `CoordStep`, rank-two detection; open inputs `TameCoordinatesTrivialK`, `horth`,
`hsw`; unsatisfiable when demanded, open limit (3)). -/
def FibreNonquadStepsK (stage : Finset (Places K S) → TwoTermStage ι) : Prop :=
  ∀ c : Finset (Places K S),
    Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c →
    ¬ (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ →
    1 < (stage c).fiberDim ρ →
    ∃ (q : Places K S) (_ : q ∉ c)
      (Tq : TameCoordinatesTrivialK (ResAt P) (gMvK K S M q) (C.D.I q) (C.D.φ q) (C.D.σ q)),
      C.AdmissibleAt q ∧ Nonempty (CoordStep ι (stage c).u (stage (insert q c)).u) ∧
      Nonempty (FibreSwitchDualityK β hβ hβc C c q Tq) ∧
        finPlane (ResAt P) (Fin 2 → ResAt P) (Fin 2 → ResAt P) ≤ (galRelK C c q Tq).U

variable {β hβ hβc C ρ c₀ t zAct hzAct lamAct hlamAct}

/-- **The duality field of `GenuineNonquadStepsK` is filled at the fibres** (tex L5062–5070): from
`FibreNonquadStepsK` and the PRINT, `GenuineNonquadStepsK` at `k = ResAt 𝔭`. Classification:
PROVED from the PRINT `NekovarFibreGlobalDuality`. -/
theorem FibreNonquadStepsK.toGenuine {stage : Finset (Places K S) → TwoTermStage ι}
    (H : FibreNonquadStepsK β hβ hβc C ρ c₀ t zAct hzAct lamAct hlamAct stage)
    (hG : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip) :
    GenuineNonquadStepsK C ρ c₀ t zAct hzAct lamAct hlamAct stage := by
  intro c hc hnq h1
  obtain ⟨q, hq, Tq, hadm, hcs, ⟨d⟩, hdet⟩ := H c hc hnq h1
  exact ⟨q, hq, Tq, hadm, hcs, d.ε, d.σ, d.J, d.hε, d.hσ, d.hJ2,
    d.dual hG hset hM hTl hT hb hb', hdet⟩

/-- **`GaloisInputsK` at `k = ResAt 𝔭` with the duality from the PRINT** (tex L4976–5195): the
fields of `GaloisInputsK` with the step field `GenuineNonquadStepsK` produced by
`FibreNonquadStepsK.toGenuine`. Classification: PROVED (wiring, from the PRINT
`NekovarFibreGlobalDuality`). -/
def GaloisInputsK.ofFibreSteps {u : F}
    (hG : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (stage : Finset (Places K S) → TwoTermStage ι)
    (model : ∀ c, HomotopyEquiv
      (selCx ((galΦK C A c₀ t zAct hzAct lamAct hlamAct).fibre c)).toCC
        (twoTermFiberComplex ρ (stage c)))
    (hz0 : ((model c₀).hom.f 1).hom zAct = fun i => ρ ((stage c₀).z i))
    (hw0 : ∀ y, lamAct y =
      (fun i => ρ ((stage c₀).w i)) ⬝ᵥ (((model c₀).hom.f 2).hom y : Fin _ → ResAt P))
    (hu0 : (stage c₀).u = u)
    (σ : ∀ c, fiberH1 ρ (stage c) →ₗ[ResAt P] fiberH1 ρ (stage c))
    (h2 : (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ → (2 : ResAt P) ≠ 0)
    (hσ : (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ →
      ∀ c, σ c ∘ₗ σ c = LinearMap.id)
    (primitive : ∀ c : Finset (Places K S),
      Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c → ∃ i, ρ ((stage c).z i) ≠ 0)
    (H : FibreNonquadStepsK β hβ hβc C ρ c₀ t zAct hzAct lamAct hlamAct stage)
    (mixed : ∀ c, Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c →
      (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ →
      (0 < Module.finrank (ResAt P) ↥(signPart (σ c) (1 : ResAt P)) ∧
        0 < Module.finrank (ResAt P) ↥(signPart (σ c) (-1 : ResAt P))) →
      1 < (stage c).fiberDim ρ →
      MixedCandidates (galΦK C A c₀ t zAct hzAct lamAct hlamAct) ρ stage σ c)
    (single : ∀ c, Reach (galΦK C A c₀ t zAct hzAct lamAct hlamAct).next c₀ c →
      (galΦK C A c₀ t zAct hzAct lamAct hlamAct).quadratic ρ →
      ¬ (0 < Module.finrank (ResAt P) ↥(signPart (σ c) (1 : ResAt P)) ∧
        0 < Module.finrank (ResAt P) ↥(signPart (σ c) (-1 : ResAt P))) →
      1 < (stage c).fiberDim ρ →
      SingleCandidates (galΦK C A c₀ t zAct hzAct lamAct hlamAct) ρ stage σ c) :
    GaloisInputsK C ρ c₀ t zAct hzAct lamAct hlamAct ι u where
  stage := stage
  model := model
  hz0 := hz0
  hw0 := hw0
  hu0 := hu0
  σ := σ
  h2 := h2
  hσ := hσ
  primitive := primitive
  step := H.toGenuine hG hset hM hTl hT hb hb'
  mixed := mixed
  single := single

/-- **Regularity at a fibre with the duality from the PRINT** (tex L4976–5195): for a local `A`
with residue map `ρ : A →+* k(𝔭)` killing the maximal ideal, the inputs of
`GaloisInputsK.ofFibreSteps` give `∃ a, ι a = u`. Classification: PROVED (from the PRINT
`NekovarFibreGlobalDuality` and the stated inputs, via `regular_of_galoisInputsK`); genuine content
only when no switch is demanded. -/
theorem regular_of_fibreSteps [IsLocalRing A] (hι : Function.Injective ι)
    (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) {u : F}
    (hG : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (hM : IsLatticeTop (GKS K S) M) (hTl : IsLatticeTop (GKS K S) T)
    (hT : IsTateTwistFibre K S P T)
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (X : GaloisInputsK C ρ c₀ t zAct hzAct lamAct hlamAct ι u)
    (H : FibreNonquadStepsK β hβ hβc C ρ c₀ t zAct hzAct lamAct hlamAct X.stage) :
    ∃ a : A, ι a = u :=
  regular_of_galoisInputsK hι hρ
    { X with step := H.toGenuine hG hset hM hTl hT hb hb' }

end Fibre

/-! ### At `M = V_𝔭(α)`: the coefficient hypotheses discharged -/

section VP

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) (P : Ideal Lambda) [P.IsPrime] (α : GKS K S →* Lambdaˣ)

/-- **RC31's Weil pairing `betaT` read as a self-pairing on `V_𝔭(α)`** (tex L2798–2805 at the
fibres): `VP K S W 𝔭 α` and `VP K S W 𝔭 α⁻¹` are the same `k(𝔭)`-module (only the Galois action
depends on `α`), so `betaT` is a bilinear form on `V_𝔭(α)`. Classification: definition. -/
def betaSelf [W.IsElliptic] [HasFullTwoTorsion K S W] :
    VP K S W P α →ₗ[ResAt P] VP K S W P α →ₗ[ResAt P] Tate1P K S P :=
  betaT W P α

/-- **The actions of `α` and `α⁻¹` on `V_𝔭` agree when the residual character is quadratic**
(`resChar 𝔭 α⁻¹ = resChar 𝔭 α`). Classification: PROVED. -/
theorem vp_smul_inv (hα : ∀ g, resChar P α⁻¹ g = resChar P α g) (g : GKS K S)
    (b : VP K S W P α) :
    (g • (show VP K S W P α⁻¹ from b) : VP K S W P α⁻¹) = (show VP K S W P α⁻¹ from g • b) := by
  change ZInQ.Manuscript.RC.LambdaCoef.VP.act (α := α⁻¹) P g b =
    ZInQ.Manuscript.RC.LambdaCoef.VP.act (α := α) P g b
  unfold ZInQ.Manuscript.RC.LambdaCoef.VP.act
  rw [hα g]
  rfl

variable [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **`betaSelf` is Galois-equivariant when the residual character is quadratic**:
`β(g a, g b) = χ_cyc(g) β(a, b)` (from RC31's `betaT_smul` and `vp_smul_inv`). Classification:
PROVED. -/
theorem betaSelf_smul (hα : ∀ g, resChar P α⁻¹ g = resChar P α g) (g : GKS K S)
    (a b : VP K S W P α) :
    betaSelf W P α (g • a) (g • b) = g • betaSelf W P α a b := by
  have h := betaT_smul W P α g a (show VP K S W P α⁻¹ from b)
  rw [vp_smul_inv W P α hα] at h
  exact h

/-- `betaSelf` is perfect on the left (RC31's `betaT_bijective`). Classification: PROVED. -/
theorem betaSelf_bijective : Function.Bijective (betaSelf W P α) :=
  betaT_bijective W P α

/-- `betaSelf` is perfect on the right (RC31's `betaT_flip_bijective`). Classification: PROVED. -/
theorem betaSelf_flip_bijective : Function.Bijective (betaSelf W P α).flip :=
  betaT_flip_bijective W P α

/-- `betaSelf` is jointly continuous for the lattice topology (RC31's `continuous_betaT`).
Classification: PROVED. -/
theorem continuous_betaSelf [IsHeightOneOdd P] :
    Continuous fun x : VP K S W P α × VP K S W P α => betaSelf W P α x.1 x.2 :=
  continuous_betaT W P α

variable [IsHeightOneOdd P] [IsContChar α] (hα : ∀ g, resChar P α⁻¹ g = resChar P α g)
  (C : SwitchCondsK (ResAt P) K S (VP K S W P α)) (c : Finset (Places K S)) (q : Places K S)
  (Tq : TameCoordinatesTrivialK (ResAt P) (gMvK K S (VP K S W P α) q) (C.D.I q) (C.D.φ q)
    (C.D.σ q))

/-- **The named duality input at `M = V_𝔭(α)`** (tex L5062–5070), with every coefficient
hypothesis discharged (`isLatticeTop_vp'`, `isLatticeTop_tate1P`, `isTateTwistFibre_tate1P`,
perfectness, continuity and equivariance of `betaSelf`): only the PRINT, the quadratic residual
character `hα` and the step data (isotropy data, trace, `horth` = open limit (1), `hsw` = ELLIOT)
remain. Classification: PROVED from the PRINT `NekovarFibreGlobalDuality`. VACUOUS for the genuine
objects (open limit (3)). -/
theorem galRelK_localizationDualityInput_VP
    (hG : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (d : FibreSwitchDualityK (betaSelf W P α) (betaSelf_smul W P α hα) (continuous_betaSelf W P α)
      C c q Tq) :
    LocalizationDualityInput d.ε d.σ d.J d.hε d.hσ d.hJ2 (galRelK C c q Tq).U :=
  d.dual hG hset (isLatticeTop_vp' P) (isLatticeTop_tate1P K S P)
    (haveI := hasTwoPowerRoots_of_fullTwoTorsion K S W; isTateTwistFibre_tate1P K S P)
    (betaSelf_bijective W P α) (betaSelf_flip_bijective W P α)

open Classical in
/-- **The duality field of `GenuineNonquadStepsK` at `M = V_𝔭(α)`** (tex L5062–5070): from the
PRINT and the quadratic residual character, all coefficient hypotheses discharged. Classification:
PROVED from the PRINT `NekovarFibreGlobalDuality`. VACUOUS for the genuine objects (open limit (3)).
-/
theorem FibreNonquadStepsK.toGenuine_VP {A F : Type} [CommRing A] [Field F] {ι : A →+* F}
    {ρ : A →+* ResAt P} {c₀ : Finset (Places K S)} {t : A}
    {zAct : (selCx (galoisSelData K S (ResAt P) (VP K S W P α)
      (condAt K S (ResAt P) (VP K S W P α) (galCond K S (VP K S W P α) C.A₀)
        (galCond K S (VP K S W P α) C.Ad) c₀))).toCC.X 1}
    {hzAct : ((selCx (galoisSelData K S (ResAt P) (VP K S W P α)
      (condAt K S (ResAt P) (VP K S W P α) (galCond K S (VP K S W P α) C.A₀)
        (galCond K S (VP K S W P α) C.Ad) c₀))).toCC.d 1 2).hom zAct = 0}
    {lamAct : (selCx (galoisSelData K S (ResAt P) (VP K S W P α)
      (condAt K S (ResAt P) (VP K S W P α) (galCond K S (VP K S W P α) C.A₀)
        (galCond K S (VP K S W P α) C.Ad) c₀))).toCC.X 2 →ₗ[ResAt P] ResAt P}
    {hlamAct : ∀ y, lamAct (((selCx (galoisSelData K S (ResAt P) (VP K S W P α)
      (condAt K S (ResAt P) (VP K S W P α) (galCond K S (VP K S W P α) C.A₀)
        (galCond K S (VP K S W P α) C.Ad) c₀))).toCC.d 1 2).hom y) = 0}
    {stage : Finset (Places K S) → TwoTermStage ι}
    (hG : NekovarFibreGlobalDuality K) (hset : NekovarFibreSetting K S)
    (H : FibreNonquadStepsK (betaSelf W P α) (betaSelf_smul W P α hα) (continuous_betaSelf W P α)
      C ρ c₀ t zAct hzAct lamAct hlamAct stage) :
    GenuineNonquadStepsK C ρ c₀ t zAct hzAct lamAct hlamAct stage :=
  H.toGenuine hG hset (isLatticeTop_vp' P) (isLatticeTop_tate1P K S P)
    (haveI := hasTwoPowerRoots_of_fullTwoTorsion K S W; isTateTwistFibre_tate1P K S P)
    (betaSelf_bijective W P α) (betaSelf_flip_bijective W P α)

end VP

/-! ### Non-vacuity at RC31's instance: `E_1` over `ℚ`, `S6`, `𝔭 = (t)` -/

section NonVacuity

/-- **The residual character of RC28's `α` at `(t)` is quadratic** (RC28's `alphaLam` is the trivial
character everywhere), so the self-pairing hypothesis `hα` holds. Classification:
PROVED. -/
theorem resChar_alphaLam_inv (S : Set (HeightOneSpectrum (𝓞 ℚ))) (g : GKS ℚ S) :
    resChar Pt0 (alphaLam ℚ S)⁻¹ g = resChar Pt0 (alphaLam ℚ S) g := by
  simp only [resChar, MonoidHom.comp_apply, MonoidHom.inv_apply, alphaLam_apply, inv_one]

/-- **Non-vacuity of the coefficient hypotheses at `E_1`, `S6`, `(t)`**: the fibre setting, the
lattice topologies of `V_(t)` and `k((t))(1)`, the Tate twist, and the equivariance, perfectness
and continuity of the self-pairing `betaSelf` — every hypothesis of
`galRelK_localizationDualityInput_VP` except the PRINT and the step data. Classification: PROVED
under RC28's GLUE `HasFullTwoTorsion ℚ S6 curveE1` (as RC31's `betaConj_E1`). -/
theorem betaSelf_E1 [HasFullTwoTorsion ℚ S6 curveE1] :
    NekovarFibreSetting ℚ S6 ∧
    IsLatticeTop (GKS ℚ S6) (VP ℚ S6 curveE1 Pt0 (alphaLam ℚ S6)) ∧
    IsLatticeTop (GKS ℚ S6) (Tate1P ℚ S6 Pt0) ∧
    IsTateTwistFibre ℚ S6 Pt0 (Tate1P ℚ S6 Pt0) ∧
    (∀ (g : GKS ℚ S6) (a b : VP ℚ S6 curveE1 Pt0 (alphaLam ℚ S6)),
      betaSelf curveE1 Pt0 (alphaLam ℚ S6) (g • a) (g • b) =
        g • betaSelf curveE1 Pt0 (alphaLam ℚ S6) a b) ∧
    Function.Bijective (betaSelf curveE1 Pt0 (alphaLam ℚ S6)) ∧
    Function.Bijective (betaSelf curveE1 Pt0 (alphaLam ℚ S6)).flip ∧
    Continuous fun x : VP ℚ S6 curveE1 Pt0 (alphaLam ℚ S6) × VP ℚ S6 curveE1 Pt0 (alphaLam ℚ S6) =>
      betaSelf curveE1 Pt0 (alphaLam ℚ S6) x.1 x.2 :=
  ⟨nekovarFibreSetting_S6, isLatticeTop_vp' Pt0, isLatticeTop_tate1P ℚ S6 Pt0,
    (haveI := hasTwoPowerRoots_of_fullTwoTorsion ℚ S6 curveE1; isTateTwistFibre_tate1P ℚ S6 Pt0),
    betaSelf_smul curveE1 Pt0 _ (resChar_alphaLam_inv S6), betaSelf_bijective curveE1 Pt0 _,
    betaSelf_flip_bijective curveE1 Pt0 _, continuous_betaSelf curveE1 Pt0 _⟩

/-- Non-vacuity: RC31's `FibreSwitch` example over the fibre field `k((t)) = ResAt (t)`, and its
relaxed localization (the shape `galRelSwitch` produces). -/
example (q : HeightOneSpectrum (𝓞 ℚ)) :
    FibreSwitch ℚ {q} (ResAt Pt0) (TrivMod (GKS ℚ {q}) PUnit) :=
  exFibreSwitch ℚ q

example (q : HeightOneSpectrum (𝓞 ℚ)) : QuasiRelaxedLocalization (ResAt Pt0) :=
  (exFibreSwitch (k := ResAt Pt0) ℚ q).toQuasi

end NonVacuity

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
