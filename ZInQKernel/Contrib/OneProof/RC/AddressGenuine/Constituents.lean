import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.GaloisModel
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Chebotarev
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.TraceModelInstance
import ZInQKernel.Contrib.OneProof.RC.TateWiring.Image

/-!
# Theorem 5.3, Lane RC24: the constituent model over `G_ℚ`

Its readings are on reduced expansions; its module is the auxiliary quotient `Mst`.

Manuscript `diophantine_zq.tex`, App F, proof of Proposition `ex:app-coefficient-rules`
(tex 9447–9976): the integral trace module (tex 9638–9668) and the constituent operators
(tex 9705–9797).

**Reduced expansions (round 3).** The text reads every identity of the trace argument as an
identity of coefficientwise reduced expansions: "In the following trace argument a reduced
expansion means coefficientwise reduction modulo `𝔪_coef` … No saturation of the integral Fourier
module is assumed, and no identification of its abstract quotient with all reduced expansions is
needed" (tex 9639–9646); "the conclusion is an identity of coefficientwise reduced expansions"
(9716–9717); the trace identities hold "on the reduced trace orbit of `F_U`" (9728–9729). The
model therefore carries the integral Fourier expansion `expand : Λ → (C → 𝒪)` of the integral
module, and every field is the coefficientwise reduction (`redE`) of an identity between vectors
of `Λ`: `det_orbit`, `two_fresh`, the defining condition of `N_U` (`consN`) and the readings
`read`.

Round 4: the model makes NO assumption that the operators preserve coefficientwise congruences
on `Λ`. The text proves the integrality of the diamond translates with correction coefficients
(tex 9655–9660), evaluates its identities in `Λ` and then reduces (tex 9898–9900); it does not
say that the diamond operators preserve coefficientwise congruences. Round 3's fields `cong_t`,
`cong_d` and its module of reduced expansions are therefore removed. The abstract module of the
Galois trace model is now `Mst`, which is `Λ` modulo the largest submodule `Kst` of the reduction
kernel that is stable under all `t(g)`, `d(g)`. The operators descend because `Kst` is stable,
the readings descend because `Kst` lies in the kernel, and the two identities and `N_U` land in
`Kst` by the exact characteristic-zero identities (`detSpan_le_Kst`, `galN_eq_N`). Round 2 stated
them as membership in the abstract submodule `𝔪Λ`; without saturation, coefficientwise
vanishing modulo `𝔪` does not give that, so the old form was stronger than the text. Membership
in `𝔪Λ` is now the separate hypothesis `GaloisConstituentModel.Saturated`, which the text does
not assume. Only
the bridge to lane RC0's `ConstituentModelRel`, whose reduced module is `Λ/𝔪Λ`, uses it
(`RelBridge.lean`).

* `GaloisConstituentModel T R ap B chiType`: constituents `ρ` over `G_ℚ`, the integral module `Λ`,
  its Fourier expansion, genuine Frobenius elements, `chiBit := bitChar`, and `N_U := consN …`
  defined from the characters and the reduced trace orbit. The fields `level_red`, `N_anti`,
  `N_chi`, `typ_frob`, `bit_frob` and `chi_surj` (good `U`) of lane RC0 are PROVED here.
* `GaloisConstituentModel.toGaloisTraceModel`: `Mst` with the induced operators is a
  `GaloisTraceModel`, whose type is unchanged. Within the budget, `consN` is `galN` of the induced
  operators (`galN_eq_N`). `toGaloisDensityModel` gives the density form of the wired leaf (type
  unchanged), given openness and unramifiedness. The readings and RC2's rules follow.
* Non-vacuity with a genuine Galois representation: for an elliptic curve `E/ℚ`,
  `tateConstituentModel'` has one constituent, the `2`-adic Tate representation of `E`. Its data
  are the `ℤ₂`-lattice of integral vectors, its coordinate as the Fourier expansion, and the zero
  forms. Its module `Mst` is nonzero (`tateConstituentModelOf_nontrivial`).
  **The constituents of the actual forms `F_U = θ H_U` are weight-two cuspidal newforms and
  Eisenstein character pairs (tex 9647–9654, 9762–9771), not `E` or its twists; the Tate
  representation of `E` only shows that the structure is inhabited by a genuine Galois
  representation.**

DEPARTURE (the constituent representations as data). Mathlib has no Galois representations
attached to modular forms. The field `ρ` therefore carries the representations as data. Their
existence is Carayol's theorem (PRINT, tex 9773–9797). The properties of them that the proof uses
enter through these fields, all stated for the operators built from `ρ`:
`stable_t` and `stable_d` (GLUE); `det_orbit`, `two_fresh` and the inputs `reading`, `o12`
(ELLIOT).

Hypotheses stronger than the text (flagged where defined): `GaloisConstituentModel.Unbudgeted`
(the fields off the operator budget) and `GaloisConstituentModel.Saturated` (membership in
`𝔪Λ`); only the bridges to lane RC0's interfaces use them (`RelBridge.lean`).

Kinds: `PROVED` (a Lean proof), `PRINT` (a printed theorem taken as a field), `GLUE` (a
textbook fact taken as a field), `ELLIOT` (a step of the manuscript's argument taken as a field
or input), `definition`.

References: [Carayol] H. Carayol, *Sur les représentations `ℓ`-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. École Norm. Sup. (4) 19 (1986), 409–468, §§0.3–0.7,
Théorème A, pp. 409–411 (the locator of tex 9778; statement page `UNVERIFIED` here).
[Neukirch] J. Neukirch, *Algebraic number theory*, Grundlehren 322 (Springer 1999), Ch. VII,
Theorem (13.4) (Čebotarev's density theorem; statement page `UNVERIFIED`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-! ## The lattice operators and coefficientwise reduction -/

section Lattice

variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]

/-- `t(g)` on an integral module `Λ` preserved by the scalar traces of `ρ` (tex 9762–9771).
Kind: definition. -/
def latT (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (g : GalQ) : Λ →ₗ[O] Λ :=
  ((tV ρ g).restrictScalars O).restrict (hst g)

/-- `d(g)` on an integral module `Λ` preserved by the determinants of `ρ` (tex 9762–9771).
Kind: definition. -/
def latD (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hsd : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ) (g : GalQ) : Λ →ₗ[O] Λ :=
  ((dV ρ g).restrictScalars O).restrict (hsd g)

/-- Kind: PROVED (definition). -/
theorem latT_coe (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (g : GalQ) (v : Λ) :
    (latT ρ Λ hst g v : I → K) = tV ρ g v := rfl

/-- Kind: PROVED (definition). -/
theorem latD_coe (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hsd : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ) (g : GalQ) (v : Λ) :
    (latD ρ Λ hsd g v : I → K) = dV ρ g v := rfl

/-- **Coefficientwise reduction modulo `𝔪`** of the integral expansion (tex 9639–9641: "a reduced
expansion means coefficientwise reduction modulo `𝔪_coef`"). Kind: definition. -/
def redExpOf (m : Ideal O) {Λ : Submodule O (I → K)} {C : Type} (expand : Λ →ₗ[O] (C → O)) :
    Λ →ₗ[O] (C → O ⧸ m) :=
  (LinearMap.compLeft (Submodule.mkQ m) C) ∘ₗ expand

/-- Kind: PROVED (definition). -/
theorem redExpOf_apply (m : Ideal O) {Λ : Submodule O (I → K)} {C : Type}
    (expand : Λ →ₗ[O] (C → O)) (v : Λ) (n : C) :
    redExpOf m expand v n = Ideal.Quotient.mk m (expand v n) := rfl

/-- **`𝔪Λ` reduces to zero coefficientwise** (the reduced expansions are annihilated by `𝔪`; the
converse, saturation, is not assumed by the text, tex 9644–9646). Kind: PROVED. -/
theorem le_ker_redExpOf (m : Ideal O) {Λ : Submodule O (I → K)} {C : Type}
    (expand : Λ →ₗ[O] (C → O)) :
    (m • ⊤ : Submodule O Λ) ≤ LinearMap.ker (redExpOf m expand) := by
  intro v hv
  refine Submodule.smul_induction_on hv (fun r hr w _ => ?_) (fun x y hx hy => ?_)
  · rw [LinearMap.mem_ker, map_smul]
    funext n
    show r • redExpOf m expand w n = 0
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hr,
      zero_mul]
  · exact Submodule.add_mem _ hx hy

/-- **The reduced trace orbit**: `(g, U) ↦` the reduced expansion of `t(g) F_U` (tex 9716–9729).
Kind: definition. -/
def redTrace (m : Ideal O) {Λ : Submodule O (I → K)} {C : Type} (expand : Λ →ₗ[O] (C → O))
    (ρ : I → GalQ →* GL (Fin 2) K) (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (F : Finset ℕ → Λ) :
    GalQ → Finset ℕ → (C → O ⧸ m) :=
  fun g U => redExpOf m expand (latT ρ Λ hst g (F U))

end Lattice

/-! ## The subgroup `N_U` of a reduced trace orbit -/

section ConsN

variable {Y : Type*}

/-- **The subgroup `N_U` cut out by the characters and the reduced trace orbit** (tex 9663–9668,
9745–9750, 9919–9921). It consists of the `n ∈ G_ℚ` such that
* `χ_type(n) = 1` and `χ_s(n) = 1` for `s ∈ U`;
* `rt(gn, U') = rt(g, U')` for every `g ∈ G_ℚ` and every `U' ⊆ U`.

For the constituent model, `rt(g, U')` is the reduced expansion of `t(g)F_{U'}` (`redTrace`),
and within the budget `N_U` is `galN` of the operators induced on `Mst`
(`GaloisConstituentModel.galN_eq_N`). Kind:
definition. -/
def consN (chiType : GalQ →* Multiplicative L) (rt : GalQ → Finset ℕ → Y) (U : Finset ℕ) :
    Subgroup GalQ where
  carrier := {n | chiType n = 1 ∧ (∀ s ∈ U, bitChar s n = 1) ∧
    ∀ g : GalQ, ∀ U' ⊆ U, rt (g * n) U' = rt g U'}
  one_mem' := ⟨map_one _, fun _ _ => map_one _, fun g _ _ => by rw [mul_one]⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨by rw [map_mul, ha.1, hb.1, mul_one], fun s hs => by
      rw [map_mul, ha.2.1 s hs, hb.2.1 s hs, mul_one], fun g U' hU' => ?_⟩
    rw [← mul_assoc, hb.2.2 (g * a) U' hU', ha.2.2 g U' hU']
  inv_mem' := by
    intro a ha
    refine ⟨by rw [map_inv, ha.1, inv_one], fun s hs => by rw [map_inv, ha.2.1 s hs, inv_one],
      fun g U' hU' => ?_⟩
    have h := ha.2.2 (g * a⁻¹) U' hU'
    rw [inv_mul_cancel_right] at h
    exact h.symm

variable {chiType : GalQ →* Multiplicative L} {rt : GalQ → Finset ℕ → Y}

/-- Membership in `consN`. Kind: PROVED (definition). -/
theorem mem_consN {U : Finset ℕ} {n : GalQ} :
    n ∈ consN chiType rt U ↔ chiType n = 1 ∧ (∀ s ∈ U, bitChar s n = 1) ∧
      ∀ g : GalQ, ∀ U' ⊆ U, rt (g * n) U' = rt g U' :=
  Iff.rfl

/-- **For an orbit constant in `g` (e.g. the zero forms), `N_U` is the common kernel of the type
character and the `χ_s`, `s ∈ U`.** Kind: PROVED. -/
theorem mem_consN_of_const (hrt : ∀ g U, rt g U = rt 1 U) {U : Finset ℕ} {n : GalQ} :
    n ∈ consN chiType rt U ↔ chiType n = 1 ∧ ∀ s ∈ U, bitChar s n = 1 :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun g U' _ => by rw [hrt, hrt g]⟩⟩

/-- **For an orbit constant in `g`, `N_U` has finite index** when the type alphabet is finite.
Kind: PROVED (it contains the kernel of the joint character, valued in a finite group). -/
theorem consN_const_finiteIndex [Finite L] (hrt : ∀ g U, rt g U = rt 1 U) (U : Finset ℕ) :
    (consN chiType rt U).FiniteIndex := by
  let φ : GalQ →* Multiplicative L × (U → Multiplicative (ZMod 2)) :=
    chiType.prod (MonoidHom.pi fun s : U => bitChar s)
  have hle : φ.ker ≤ consN chiType rt U := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    refine (mem_consN_of_const hrt).mpr ⟨congrArg Prod.fst hn, fun s hs => ?_⟩
    exact congrFun (congrArg Prod.snd hn) ⟨s, hs⟩
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  exact Subgroup.finiteIndex_of_le hle

/-- **Chebotarev relative to `N_U` for an orbit constant in `g`, by Dirichlet** (tex 2151–2174,
9938–9942). Kind: PROVED (`exists_good_frob`). -/
theorem consN_const_chebotarev (T : TypeData L ε) (htyp : IsTypeChar T chiType)
    (hrt : ∀ g U, rt g U = rt 1 U) {frob : ℕ → GalQ}
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s)
    (g : GalQ) (avoid : Finset ℕ) :
    ∃ q h, ∃ n ∈ consN chiType rt U, T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹ * n := by
  obtain ⟨q, hq, -, hqa, h1, h2⟩ := exists_good_frob T htyp hfrob U avoid hU
    (Multiplicative.toAdd (chiType g)) (fun s => Multiplicative.toAdd (bitChar s g))
  refine ⟨q, 1, g⁻¹ * frob q, (mem_consN_of_const hrt).mpr ⟨?_, fun s hs => ?_⟩, hq, hqa,
    by group⟩
  · rw [map_mul, map_inv, h1, ofAdd_toAdd, inv_mul_cancel]
  · rw [map_mul, map_inv, h2 s hs, ofAdd_toAdd, inv_mul_cancel]

end ConsN

/-! ## The constituent model over `G_ℚ` -/

/-- **The constituent model of the integral trace module over `G_ℚ`, on the auxiliary quotient
`Mst`**,
within the budget `B`, for the type character `chiType` (tex 9638–9668, 9705–9797).
The module is the auxiliary quotient `Mst = Λ/Kst`, not an identification
with the image of coefficientwise reduction. Its readings factor through
that reduction; the budgeted orbit identities and subgroup comparison are
proved. The density conversion needs no saturation. The legacy bridge to
`ConstituentModelRel` separately requires `Saturated` and `Unbudgeted`.
Every identity of the trace argument is an identity of coefficientwise reduced expansions
(tex 9639–9646, 9716–9717, 9728–9729; see the module docstring). This constituent interface is
not the wired density leaf: the leaf asks for density models (`Chebotarev.lean`), which
`toGaloisDensityModel` builds from it given its inputs, openness and unramifiedness.

Kinds:
* `ρ`: PRINT ([Carayol, §§0.3–0.7, Théorème A, pp. 409–411], tex 9773–9797, stated as data);
* `stable_t`, `stable_d`, `kummer`, `finiteIndex`: GLUE;
* `det_orbit`, `two_fresh`: ELLIOT;
* `chebotarev`: PRINT ([Neukirch, Ch. VII, Theorem (13.4)]; tex 9666–9668, 9919–9921);
* `I`, `K`, `O`, `m`, `Λ`, `C`, `coefK`, `expand`, `expand_spec`, `F`, `read`, `frob_spec`:
  definition (data of the construction, tex 9638–9668).

The ELLIOT inputs `reading`, `o12` are `GaloisConstituentModel.Inputs`. Budget (tex 9447–9468,
9649–9654, 9741–9745, 10533–10548): the fields about one `U` are stated for `U` a set of good
primes with `|U| + 1 ≤ B`. Owner: RC12 (App F), Lane RC24. -/
structure GaloisConstituentModel (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ)
    (chiType : GalQ →* Multiplicative L) where
  /-- the constituents, with their multiplicities and degeneracies (tex 9649–9654, 9762–9771) -/
  I : Type
  /-- the characteristic-zero coefficient field, containing all constituents (tex 9649–9652) -/
  K : Type
  [instK : Field K]
  /-- the coefficient valuation ring `𝒪_coef` (tex 9638–9641) -/
  O : Type
  [instO : CommRing O]
  [instAlg : Algebra O K]
  /-- the maximal ideal `𝔪_coef` (tex 9638–9641) -/
  m : Ideal O
  /-- `2 ∈ 𝔪_coef`: the coefficient place lies above two (tex 9780–9781) -/
  two_mem : (2 : O) ∈ m
  /-- PRINT ([Carayol, Théorème A], tex 9773–9797; stated as data): the two-dimensional Galois
  representations of the constituents (the sum of the two characters on an Eisenstein
  constituent, tex 9652–9654, 9762–9771) -/
  ρ : I → GalQ →* GL (Fin 2) K
  /-- the integral module generated by the translates of the forms (tex 9655–9665) -/
  Λ : Submodule O (I → K)
  /-- GLUE (tex 9663–9668): `Λ` is preserved by the scalar trace operators -/
  stable_t : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ
  /-- GLUE (tex 9663–9668): `Λ` is preserved by the determinant operators -/
  stable_d : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ
  /-- the Fourier indices of the coordinates (tex 9661–9662) -/
  C : Type
  /-- the Fourier expansion of the characteristic-zero space (tex 9655–9662) -/
  coefK : (I → K) →ₗ[K] (C → K)
  /-- the integral Fourier coefficients of the integral module (tex 9655–9662) -/
  expand : Λ →ₗ[O] (C → O)
  /-- definition: `expand` records the Fourier coefficients of the integral forms in `𝒪`
  (the translates remain integral, tex 9655–9660) -/
  expand_spec : ∀ (v : Λ) (n : C), algebraMap O K (expand v n) = coefK v n
  /-- the integral forms `F_U = θ H_U` (tex 9647–9648, 9672) for `U` a set of good primes within
  the budget; the values elsewhere are constrained by no field -/
  F : Finset ℕ → Λ
  /-- the coefficient-one functionals on reduced expansions (tex 9686–9690) -/
  read : Finset ℕ → (C → O ⧸ m) →+ ZMod 2
  /-- the Frobenius elements in `G_ℚ` -/
  frob : ℕ → GalQ
  /-- definition: `frob q` is a genuine arithmetic Frobenius element at every good prime `q` -/
  frob_spec : ∀ q, T.Good q → IsFrobAt (frob q) q
  /-- ELLIOT (tex 9712–9733: the diamond/trace-orbit calculation; "the conclusion is an identity
  of coefficientwise reduced expansions", 9716–9717), within the budget: `d(u) t(v) F_U` and
  `t(v) F_U` have the same reduced expansion -/
  det_orbit : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ u v,
    redExpOf m expand (latD ρ Λ stable_d u (latT ρ Λ stable_t v (F U))) =
      redExpOf m expand (latT ρ Λ stable_t v (F U))
  /-- ELLIOT (tex 9741–9745: "It follows that `t(g)t(h)F_U = 0` after reduction"), within the
  budget: the reduced expansion of `t(g) t(h) F_U` vanishes -/
  two_fresh : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h,
    redExpOf m expand (latT ρ Λ stable_t g (latT ρ Λ stable_t h (F U))) = 0
  /-- GLUE (Kummer theory for the several radicals, tex 9745–9750), within the budget -/
  kummer : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g, chiType g = 1 →
    (∀ s ∈ U, bitChar s g = 1) →
      g ∈ Subgroup.closure (sqSet GalQ) ⊔ consN chiType (redTrace m expand ρ stable_t F) U
  /-- GLUE (continuity on the finite module, tex 9663–9668), within the budget: `G_ℚ/N_U` is
  finite -/
  finiteIndex : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    (consN chiType (redTrace m expand ρ stable_t F) U).FiniteIndex
  /-- PRINT ([Neukirch, Ch. VII, Theorem (13.4)], in the finite quotient `G_ℚ/N_U`, tex 9666–9668,
  9919–9921), within the budget -/
  chebotarev : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    ∀ (g : GalQ) (avoid : Finset ℕ), ∃ q h, ∃ n ∈ consN chiType (redTrace m expand ρ stable_t F) U,
      T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹ * n

namespace GaloisConstituentModel

variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
  {chiType : GalQ →* Multiplicative L} (X : GaloisConstituentModel T R ap B chiType)

attribute [instance] GaloisConstituentModel.instK GaloisConstituentModel.instO
  GaloisConstituentModel.instAlg

/-- `t(g)` on `Λ`. Kind: definition. -/
abbrev tΛ (g : GalQ) : X.Λ →ₗ[X.O] X.Λ := latT X.ρ X.Λ X.stable_t g

/-- `d(g)` on `Λ`. Kind: definition. -/
abbrev dΛ (g : GalQ) : X.Λ →ₗ[X.O] X.Λ := latD X.ρ X.Λ X.stable_d g

/-- Coefficientwise reduction of the integral expansion (tex 9639–9641). Kind: definition. -/
abbrev redE : X.Λ →ₗ[X.O] (X.C → X.O ⧸ X.m) := redExpOf X.m X.expand

/-- The subgroup `N_U` of the model. Kind: definition. -/
abbrev N (U : Finset ℕ) : Subgroup GalQ :=
  consN chiType (redTrace X.m X.expand X.ρ X.stable_t X.F) U

/-! ### RC0's fields, PROVED -/

/-- **`level_red`** (RC0's field, on reduced expansions; tex 9524–9548, 9663–9668): for
`n ∈ N_U` the reduced expansions of `t(gn) F_U` and `t(g) F_U` agree. Kind: PROVED (definition of
`consN`). -/
theorem level_red (U : Finset ℕ) (g n : GalQ) (hn : n ∈ X.N U) :
    X.redE (X.tΛ (g * n) (X.F U)) = X.redE (X.tΛ g (X.F U)) :=
  hn.2.2 g U (subset_refl U)

/-- **`N_anti`** (RC0's field). Kind: PROVED (definition of `consN`). -/
theorem N_anti (U U' : Finset ℕ) (h : U' ⊆ U) : X.N U ≤ X.N U' :=
  fun _ hn => ⟨hn.1, fun s hs => hn.2.1 s (h hs), fun g U'' hU'' => hn.2.2 g U'' (hU''.trans h)⟩

/-- **`N_chi`** (RC0's field). Kind: PROVED (definition of `consN`). -/
theorem N_chi (U : Finset ℕ) : ∀ n ∈ X.N U, chiType n = 1 ∧ ∀ s ∈ U, bitChar s n = 1 :=
  fun _ hn => ⟨hn.1, hn.2.1⟩

/-- **`typ_frob`** (RC0's field; tex 2017–2020, 9936–9940). Kind: PROVED. -/
theorem typ_frob (htyp : IsTypeChar T chiType) (q : ℕ) (hq : T.Good q) :
    chiType (X.frob q) = Multiplicative.ofAdd (T.typ q) :=
  htyp q _ hq (X.frob_spec q hq)

/-- **`bit_frob`** (RC0's field; tex 9938–9942). Kind: PROVED (`bitChar_of_good`). -/
theorem bit_frob (q s : ℕ) (hq : T.Good q) (hs : T.Good s) (hqs : q ≠ s) :
    bitChar s (X.frob q) = Multiplicative.ofAdd (legBit q s) :=
  bitChar_of_good T hq hs hqs (X.frob_spec q hq)

include X in
/-- **`chi_surj` at sets of good primes** (RC0's field restricted to good `U`; at other `U` it
is false, `not_chi_surj_all`). Kind: PROVED (`exists_good_frob`). -/
theorem chi_surj (htyp : IsTypeChar T chiType) (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (ℓ : L)
    (b : ℕ → ZMod 2) :
    ∃ g : GalQ, chiType g = Multiplicative.ofAdd ℓ ∧
      ∀ s ∈ U, bitChar s g = Multiplicative.ofAdd (b s) := by
  obtain ⟨q, -, -, -, h1, h2⟩ := exists_good_frob T htyp X.frob_spec U ∅ hU ℓ b
  exact ⟨_, h1, h2⟩

/-! ### Identities on the integral module (exact, characteristic zero) -/

/-- `t` and `d` commute on `Λ` (both are scalar operators on each constituent). Kind: PROVED. -/
theorem tΛ_dΛ (g h : GalQ) (v : X.Λ) : X.tΛ g (X.dΛ h v) = X.dΛ h (X.tΛ g v) := by
  apply Subtype.ext
  funext i
  simp only [latT_coe, latD_coe, tV, dV, scalarOp_apply]
  ring

/-- `t(g)t(h) = t(gh) + d(h)t(gh⁻¹)` on `Λ` (batch 3's `tV_mul`, tex 9734–9737). Kind:
PROVED. -/
theorem tΛ_mul (g h : GalQ) (v : X.Λ) :
    X.tΛ g (X.tΛ h v) = X.tΛ (g * h) v + X.dΛ h (X.tΛ (g * h⁻¹) v) :=
  Subtype.ext (tV_mul X.ρ g h (v : X.I → X.K))

/-- `d` is multiplicative on `Λ` (`det` is multiplicative). Kind: PROVED. -/
theorem dΛ_mul (g h : GalQ) (v : X.Λ) : X.dΛ (g * h) v = X.dΛ g (X.dΛ h v) := by
  apply Subtype.ext
  funext i
  simp only [latD_coe, dV, scalarOp_apply, map_mul, Units.val_mul, Matrix.det_mul]
  ring

/-- `t(1) = 2` on `Λ`. Kind: PROVED (`tV_one`). -/
theorem tΛ_one (v : X.Λ) : X.tΛ 1 v = (2 : ℕ) • v := by
  apply Subtype.ext
  show tV X.ρ 1 (v : X.I → X.K) = (((2 : ℕ) • v : X.Λ) : X.I → X.K)
  rw [tV_one, two_smul]
  simp [two_nsmul]

/-- `t` is a class function on `Λ` (`tV_conj`). Kind: PROVED. -/
theorem tΛ_conj (g h : GalQ) : X.tΛ (h * g * h⁻¹) = X.tΛ g := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show tV X.ρ (h * g * h⁻¹) (v : X.I → X.K) = tV X.ρ g v
  rw [tV_conj]

/-- **`N_U` is normal** (tex 9919–9921). Kind: PROVED (`tΛ_conj`). -/
theorem N_normal (U : Finset ℕ) : (X.N U).Normal := by
  refine ⟨fun n hn k => ⟨?_, fun s hs => ?_, fun g U' hU' => ?_⟩⟩
  · rw [map_mul, map_mul, map_inv, hn.1, mul_one, mul_inv_cancel]
  · rw [map_mul, map_mul, map_inv, hn.2.1 s hs, mul_one, mul_inv_cancel]
  · show X.redE (X.tΛ (g * (k * n * k⁻¹)) (X.F U')) = X.redE (X.tΛ g (X.F U'))
    have e1 : X.tΛ (g * (k * n * k⁻¹)) = X.tΛ ((k⁻¹ * g * k) * n) := by
      rw [← X.tΛ_conj ((k⁻¹ * g * k) * n) k]
      congr 1
      group
    have e2 : X.tΛ g = X.tΛ (k⁻¹ * g * k) := by
      rw [← X.tΛ_conj (k⁻¹ * g * k) k]
      congr 1
      group
    rw [e1, e2]
    exact hn.2.2 _ U' hU'

/-! ### The largest operator-stable submodule of the reduction kernel

The text evaluates every identity of the trace argument in `Λ` and then reduces coefficientwise
(tex 9639–9646, 9716–9717, 9728–9729, 9898–9900). It does not assert that the operators
preserve coefficientwise congruences on `Λ`. The abstract module of the Galois trace model is
therefore `Λ` modulo the largest submodule `Kst` of the kernel of coefficientwise reduction that
is stable under all `t(g)` and `d(g)`. The operators descend because `Kst` is stable, and the
readings descend because `Kst` lies in the kernel. The two identities of the trace argument land
in `Kst` (`detSpan_le_Kst`): the submodule they generate is operator-stable by the exact
characteristic-zero identities (`tΛ_mul`, `dΛ_mul`, `tΛ_dΛ`), and it lies in the kernel by the
coefficientwise identities. The subgroup `galN` of the quotient is `N_U` (`galN_eq_N`). -/

/-- The submodules of the reduction kernel stable under every `t(g)` and `d(g)`. Kind:
definition. -/
def StableKer : Set (Submodule X.O X.Λ) :=
  {P | P ≤ LinearMap.ker X.redE ∧ (∀ g, P ≤ P.comap (X.tΛ g)) ∧ ∀ g, P ≤ P.comap (X.dΛ g)}

/-- **The largest operator-stable submodule of the kernel of coefficientwise reduction.** Kind:
definition. -/
def Kst : Submodule X.O X.Λ := sSup X.StableKer

/-- Kind: PROVED. -/
theorem Kst_le_ker : X.Kst ≤ LinearMap.ker X.redE := sSup_le fun _ hP => hP.1

/-- Kind: PROVED. -/
theorem Kst_stable_t (g : GalQ) : X.Kst ≤ X.Kst.comap (X.tΛ g) :=
  sSup_le fun _ hP => (hP.2.1 g).trans (Submodule.comap_mono (le_sSup hP))

/-- Kind: PROVED. -/
theorem Kst_stable_d (g : GalQ) : X.Kst ≤ X.Kst.comap (X.dΛ g) :=
  sSup_le fun _ hP => (hP.2.2 g).trans (Submodule.comap_mono (le_sSup hP))

/-- A stable submodule of the kernel lies in `Kst`. Kind: PROVED. -/
theorem le_Kst {P : Submodule X.O X.Λ} (h1 : P ≤ LinearMap.ker X.redE)
    (h2 : ∀ g, P ≤ P.comap (X.tΛ g)) (h3 : ∀ g, P ≤ P.comap (X.dΛ g)) : P ≤ X.Kst :=
  le_sSup ⟨h1, h2, h3⟩

/-- `𝔪Λ ≤ Kst`. Kind: PROVED. -/
theorem mLam_le_Kst : (X.m • ⊤ : Submodule X.O X.Λ) ≤ X.Kst := by
  refine X.le_Kst (le_ker_redExpOf X.m X.expand) (fun g => ?_) (fun g => ?_) <;>
  · rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact smul_mono_right _ le_top

/-- The generators of the determinant and two-trace identities for `F_U`. Kind: definition. -/
def orbitGens (U : Finset ℕ) : Set X.Λ :=
  {x | (∃ a b, x = X.dΛ a (X.tΛ b (X.F U)) - X.tΛ b (X.F U)) ∨
    ∃ g h, x = X.tΛ g (X.tΛ h (X.F U))}

/-- **The submodule generated by the two identities of the trace argument at `U`** (tex
9712–9745): the vectors `(d(a) − 1) t(b) F_U` and `t(g) t(h) F_U`. Kind: definition. -/
def detSpan (U : Finset ℕ) : Submodule X.O X.Λ := Submodule.span X.O (X.orbitGens U)

theorem gen1_mem (U : Finset ℕ) (a b : GalQ) :
    X.dΛ a (X.tΛ b (X.F U)) - X.tΛ b (X.F U) ∈ X.detSpan U :=
  Submodule.subset_span (Or.inl ⟨a, b, rfl⟩)

theorem gen2_mem (U : Finset ℕ) (g h : GalQ) : X.tΛ g (X.tΛ h (X.F U)) ∈ X.detSpan U :=
  Submodule.subset_span (Or.inr ⟨g, h, rfl⟩)

/-- `(d(a) − 1) t(x) t(y) F_U` lies in the span (exact identities). Kind: PROVED. -/
theorem dsub_tt_mem (U : Finset ℕ) (a x y : GalQ) :
    X.dΛ a (X.tΛ x (X.tΛ y (X.F U))) - X.tΛ x (X.tΛ y (X.F U)) ∈ X.detSpan U := by
  have e : X.dΛ a (X.tΛ x (X.tΛ y (X.F U))) - X.tΛ x (X.tΛ y (X.F U)) =
      (X.dΛ a (X.tΛ (x * y) (X.F U)) - X.tΛ (x * y) (X.F U)) +
        ((X.dΛ (a * y) (X.tΛ (x * y⁻¹) (X.F U)) - X.tΛ (x * y⁻¹) (X.F U)) -
          (X.dΛ y (X.tΛ (x * y⁻¹) (X.F U)) - X.tΛ (x * y⁻¹) (X.F U))) := by
    rw [X.tΛ_mul, map_add, X.dΛ_mul]
    abel
  rw [e]
  exact Submodule.add_mem _ (X.gen1_mem U _ _)
    (Submodule.sub_mem _ (X.gen1_mem U _ _) (X.gen1_mem U _ _))

/-- The span is stable under `t(k)`. Kind: PROVED (`tΛ_mul`, `dΛ_mul`, `tΛ_dΛ`). -/
theorem detSpan_stable_t (U : Finset ℕ) (k : GalQ) :
    X.detSpan U ≤ (X.detSpan U).comap (X.tΛ k) := by
  rw [detSpan, Submodule.span_le]
  rintro x (⟨a, b, rfl⟩ | ⟨g, h, rfl⟩)
  · show X.tΛ k (X.dΛ a (X.tΛ b (X.F U)) - X.tΛ b (X.F U)) ∈ X.detSpan U
    rw [map_sub, X.tΛ_dΛ]
    exact X.dsub_tt_mem U a k b
  · show X.tΛ k (X.tΛ g (X.tΛ h (X.F U))) ∈ X.detSpan U
    have e : X.tΛ k (X.tΛ g (X.tΛ h (X.F U))) = X.tΛ k (X.tΛ (g * h) (X.F U)) +
        X.tΛ k (X.tΛ (g * h⁻¹) (X.F U)) +
        (X.dΛ h (X.tΛ k (X.tΛ (g * h⁻¹) (X.F U))) - X.tΛ k (X.tΛ (g * h⁻¹) (X.F U))) := by
      rw [X.tΛ_mul g h, map_add, X.tΛ_dΛ]
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _ (X.gen2_mem U _ _) (X.gen2_mem U _ _))
      (X.dsub_tt_mem U h k _)

/-- The span is stable under `d(k)`. Kind: PROVED. -/
theorem detSpan_stable_d (U : Finset ℕ) (k : GalQ) :
    X.detSpan U ≤ (X.detSpan U).comap (X.dΛ k) := by
  rw [detSpan, Submodule.span_le]
  rintro x (⟨a, b, rfl⟩ | ⟨g, h, rfl⟩)
  · show X.dΛ k (X.dΛ a (X.tΛ b (X.F U)) - X.tΛ b (X.F U)) ∈ X.detSpan U
    have e : X.dΛ k (X.dΛ a (X.tΛ b (X.F U)) - X.tΛ b (X.F U)) =
        (X.dΛ (k * a) (X.tΛ b (X.F U)) - X.tΛ b (X.F U)) -
          (X.dΛ k (X.tΛ b (X.F U)) - X.tΛ b (X.F U)) := by
      rw [map_sub, X.dΛ_mul]
      abel
    rw [e]
    exact Submodule.sub_mem _ (X.gen1_mem U _ _) (X.gen1_mem U _ _)
  · show X.dΛ k (X.tΛ g (X.tΛ h (X.F U))) ∈ X.detSpan U
    have e : X.dΛ k (X.tΛ g (X.tΛ h (X.F U))) = X.tΛ g (X.tΛ h (X.F U)) +
        (X.dΛ k (X.tΛ g (X.tΛ h (X.F U))) - X.tΛ g (X.tΛ h (X.F U))) := by abel
    rw [e]
    exact Submodule.add_mem _ (X.gen2_mem U _ _) (X.dsub_tt_mem U k g h)

/-- **The span lies in the reduction kernel** for `U` a set of good primes within the budget:
the coefficientwise identities `det_orbit` and `two_fresh`. Kind: PROVED. -/
theorem detSpan_le_ker (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) :
    X.detSpan U ≤ LinearMap.ker X.redE := by
  rw [detSpan, Submodule.span_le]
  rintro x (⟨a, b, rfl⟩ | ⟨g, h, rfl⟩)
  · show X.redE _ = 0
    rw [map_sub, sub_eq_zero]
    exact X.det_orbit U hU hUB a b
  · exact X.two_fresh U hU hUB g h

/-- **The two identities land in `Kst`** within the budget. Kind: PROVED. -/
theorem detSpan_le_Kst (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) :
    X.detSpan U ≤ X.Kst :=
  X.le_Kst (X.detSpan_le_ker U hU hUB) (X.detSpan_stable_t U) (X.detSpan_stable_d U)

/-- The vectors `t(gn) F_{U'} − t(g) F_{U'}`, `n ∈ N_U`, with the identities at `U'`. Kind:
definition. -/
def levelSpan (U U' : Finset ℕ) : Submodule X.O X.Λ :=
  Submodule.span X.O {x | ∃ g, ∃ n ∈ X.N U, x = X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')} ⊔
    X.detSpan U'

/-- **`t(gn) F_{U'} − t(g) F_{U'}` lies in `Kst`** for `n ∈ N_U`, `U' ⊆ U`, `U` within the
budget (the span is operator-stable by the exact identities and the normality of `N_U`, and it
lies in the kernel by the definition of `N_U` and the coefficientwise identities). Kind:
PROVED. -/
theorem level_mem_Kst (U U' : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B)
    (hU' : U' ⊆ U) (g n : GalQ) (hn : n ∈ X.N U) :
    X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U') ∈ X.Kst := by
  have hU'g : ∀ s ∈ U', T.Good s := fun s hs => hU s (hU' hs)
  have hU'B : U'.card + 1 ≤ B := (Nat.add_le_add_right (Finset.card_le_card hU') 1).trans hUB
  have hnorm := X.N_normal U
  have hgen : ∀ g, ∀ n ∈ X.N U, X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U') ∈ X.levelSpan U U' :=
    fun g n hn => Submodule.mem_sup_left (Submodule.subset_span ⟨g, n, hn, rfl⟩)
  have hdet : ∀ x ∈ X.detSpan U', x ∈ X.levelSpan U U' := fun x hx => Submodule.mem_sup_right hx
  refine X.le_Kst (P := X.levelSpan U U') ?_ (fun k => ?_) (fun k => ?_) (hgen g n hn)
  · refine sup_le ?_ (X.detSpan_le_ker U' hU'g hU'B)
    rw [Submodule.span_le]
    rintro x ⟨g, n, hn, rfl⟩
    show X.redE _ = 0
    rw [map_sub, sub_eq_zero]
    exact hn.2.2 g U' hU'
  · refine sup_le ?_ ((X.detSpan_stable_t U' k).trans (Submodule.comap_mono le_sup_right))
    rw [Submodule.span_le]
    rintro x ⟨g, n, hn, rfl⟩
    show X.tΛ k (X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')) ∈ X.levelSpan U U'
    have hn' : g * n⁻¹ * g⁻¹ ∈ X.N U := hnorm.conj_mem _ (inv_mem hn) g
    have e : X.tΛ k (X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')) =
        (X.tΛ ((k * g) * n) (X.F U') - X.tΛ (k * g) (X.F U')) +
          (X.tΛ ((k * g⁻¹) * (g * n⁻¹ * g⁻¹)) (X.F U') - X.tΛ (k * g⁻¹) (X.F U')) +
          ((X.dΛ (g * n) (X.tΛ (k * (g * n)⁻¹) (X.F U')) - X.tΛ (k * (g * n)⁻¹) (X.F U')) -
            (X.dΛ g (X.tΛ (k * g⁻¹) (X.F U')) - X.tΛ (k * g⁻¹) (X.F U'))) := by
      rw [map_sub, X.tΛ_mul, X.tΛ_mul]
      have h1 : k * (g * n) = (k * g) * n := by group
      have h2 : k * (g * n)⁻¹ = (k * g⁻¹) * (g * n⁻¹ * g⁻¹) := by group
      rw [h1, ← h2]
      abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.add_mem _ (hgen _ _ hn) (hgen _ _ hn')) ?_
    exact Submodule.sub_mem _ (hdet _ (X.gen1_mem U' _ _)) (hdet _ (X.gen1_mem U' _ _))
  · refine sup_le ?_ ((X.detSpan_stable_d U' k).trans (Submodule.comap_mono le_sup_right))
    rw [Submodule.span_le]
    rintro x ⟨g, n, hn, rfl⟩
    show X.dΛ k (X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')) ∈ X.levelSpan U U'
    have e : X.dΛ k (X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')) =
        (X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')) +
          ((X.dΛ k (X.tΛ (g * n) (X.F U')) - X.tΛ (g * n) (X.F U')) -
            (X.dΛ k (X.tΛ g (X.F U')) - X.tΛ g (X.F U'))) := by
      rw [map_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (hgen _ _ hn)
      (Submodule.sub_mem _ (hdet _ (X.gen1_mem U' _ _)) (hdet _ (X.gen1_mem U' _ _)))

/-! ### The abstract module of the Galois trace model -/

/-- **The module of the Galois trace model**: `Λ` modulo the largest operator-stable submodule of
the kernel of coefficientwise reduction. It needs no congruence property of the operators
(tex 9639–9646, 9898–9900). Kind: definition. -/
abbrev Mst : Type := X.Λ ⧸ X.Kst

/-- `2 = 0` on `Mst` (`2 ∈ 𝔪`, `𝔪Λ ≤ Kst`). Kind: PROVED. -/
theorem two_nsmul_Mst (x : X.Mst) : 2 • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    show 2 • X.Kst.mkQ v = 0
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← Nat.cast_smul_eq_nsmul X.O]
    exact X.mLam_le_Kst (Submodule.smul_mem_smul (by exact_mod_cast X.two_mem) trivial)

/-- The `𝔽₂`-structure of `Mst`. Kind: definition. -/
abbrev modMst : Module (ZMod 2) X.Mst := AddCommGroup.zmodModule X.two_nsmul_Mst

attribute [local instance] GaloisConstituentModel.modMst

/-- `t(g)` on `Mst`. Kind: definition. -/
def tK (g : GalQ) : X.Mst →ₗ[ZMod 2] X.Mst :=
  (X.Kst.mapQ X.Kst (X.tΛ g) (X.Kst_stable_t g)).toAddMonoidHom.toZModLinearMap 2

/-- `d(g)` on `Mst`. Kind: definition. -/
def dK (g : GalQ) : X.Mst →ₗ[ZMod 2] X.Mst :=
  (X.Kst.mapQ X.Kst (X.dΛ g) (X.Kst_stable_d g)).toAddMonoidHom.toZModLinearMap 2

/-- The forms `F_U` in `Mst`. Kind: definition. -/
def FK (U : Finset ℕ) : X.Mst := Submodule.Quotient.mk (X.F U)

/-- The coefficient-one functionals, through coefficientwise reduction (`Kst` lies in its
kernel). Kind: definition. -/
def readK (U : Finset ℕ) : X.Mst →ₗ[ZMod 2] ZMod 2 :=
  ((X.read U).comp (X.Kst.liftQ X.redE X.Kst_le_ker).toAddMonoidHom).toZModLinearMap 2

theorem tK_mk (g : GalQ) (v : X.Λ) :
    X.tK g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (X.tΛ g v) := rfl

theorem dK_mk (g : GalQ) (v : X.Λ) :
    X.dK g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (X.dΛ g v) := rfl

/-- The readings of `Mst` are those of the reduced expansions. Kind: PROVED (definition). -/
theorem readK_mk (U : Finset ℕ) (v : X.Λ) :
    X.readK U (Submodule.Quotient.mk v) = X.read U (X.redE v) := rfl

theorem mk_eq_mk_iff (v w : X.Λ) :
    (Submodule.Quotient.mk v : X.Mst) = Submodule.Quotient.mk w ↔ v - w ∈ X.Kst :=
  Submodule.Quotient.eq _

/-- **`trace_mul` on `Mst`** (tex 9734–9737). Kind: PROVED (`tΛ_mul`). -/
theorem trace_mul (g h : GalQ) (x : X.Mst) :
    X.tK g (X.tK h x) = X.tK (g * h) x + X.dK h (X.tK (g * h⁻¹) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [tK_mk, tK_mk, tK_mk, tK_mk, dK_mk, ← Submodule.Quotient.mk_add, X.tΛ_mul]

/-- **`det_orbit` on `Mst`** (tex 9712–9733), within the budget. Kind: PROVED (from the
coefficientwise field, `detSpan_le_Kst`). -/
theorem det_orbit' (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) (u v : GalQ) :
    X.dK u (X.tK v (X.FK U)) = X.tK v (X.FK U) := by
  rw [FK, tK_mk, dK_mk, mk_eq_mk_iff]
  exact X.detSpan_le_Kst U hU hUB (X.gen1_mem U u v)

/-- **`two_fresh` on `Mst`** (tex 9741–9745), within the budget. Kind: PROVED. -/
theorem two_fresh' (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) (g h : GalQ) :
    X.tK g (X.tK h (X.FK U)) = 0 := by
  rw [FK, tK_mk, tK_mk, Submodule.Quotient.mk_eq_zero]
  exact X.detSpan_le_Kst U hU hUB (X.gen2_mem U g h)

/-- **`trace_one`** (tex 9739). Kind: PROVED. -/
theorem trace_one (x : X.Mst) : X.tK 1 x = (2 : ZMod 2) • x := by
  rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [tK_mk, X.tΛ_one]
    show X.Kst.mkQ ((2 : ℕ) • v) = 0
    rw [map_nsmul]
    exact X.two_nsmul_Mst _

/-- **`t` is a class function** (tex 9762–9771). Kind: PROVED. -/
theorem t_class (g h : GalQ) : X.tK (h * g * h⁻¹) = X.tK g := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H v => rw [tK_mk, tK_mk, X.tΛ_conj]

/-- **Within the budget, `N_U` is the subgroup `galN` of `Mst`.** Kind: PROVED
(`level_mem_Kst`, `Kst_le_ker`). -/
theorem galN_eq_N (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) :
    galN chiType X.tK X.FK U = X.N U := by
  ext n
  rw [mem_galN]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun g U' hU' => ?_⟩
    have h := h3 g U' hU'
    rw [FK, tK_mk, tK_mk, mk_eq_mk_iff] at h
    have := X.Kst_le_ker h
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  · intro hn
    refine ⟨hn.1, hn.2.1, fun g U' hU' => ?_⟩
    rw [FK, tK_mk, tK_mk, mk_eq_mk_iff]
    exact X.level_mem_Kst U U' hU hUB hU' g n hn

/-! ### The genuine Galois trace model of the constituent model -/

/-- **The two ELLIOT inputs**, on reduced expansions of vectors of `Λ` (tex 9671–9704,
9905–9918): the coefficient-one reading of a fresh vertex and (O.12) at coefficient one. Kind:
definition. -/
def Inputs : Prop :=
  (∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
      (insert q U).card ≤ B → R (insert q U) = X.read U (X.redE (X.tΛ (X.frob q) (X.F U)))) ∧
  (∀ (U : Finset ℕ) (p : ℕ), p ∈ U → (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g : GalQ,
      ∃ (τ φ : GalQ) (κ0 : ℤ), (κ0 = 1 ∨ κ0 = -1) ∧
        chiType τ = 1 ∧ (∀ s ∈ U, s ≠ p → bitChar s τ = 1) ∧
        bitChar p τ = Multiplicative.ofAdd 1 ∧
        chiType φ = Multiplicative.ofAdd (T.typ p) ∧
        (∀ s ∈ U, s ≠ p → bitChar s φ = Multiplicative.ofAdd (legBit p s)) ∧
        ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) *
            X.read (U.erase p) (X.redE (X.tΛ (g * τ * φ) (X.F (U.erase p)))) -
          ((Cp (ap p) κ0 : ℤ) : ZMod 2) *
            X.read (U.erase p) (X.redE (X.tΛ (g * φ) (X.F (U.erase p)))) =
        X.read U (X.redE (X.tΛ (g * τ) (X.F U))) - X.read U (X.redE (X.tΛ g (X.F U))))

/-- **The genuine Galois trace model of the constituent model** (tex 9638–9771): `Mst` with the
induced operators, forms and functionals. Kind: PROVED. -/
def toGaloisTraceModel (hI : X.Inputs) : GaloisTraceModel T R ap B chiType where
  M := X.Mst
  instMod := X.modMst
  t := X.tK
  d := X.dK
  F := X.FK
  read := X.readK
  frob := X.frob
  frob_spec := X.frob_spec
  trace_mul := X.trace_mul
  det_orbit := X.det_orbit'
  two_fresh := X.two_fresh'
  trace_one := X.trace_one
  t_class := X.t_class
  kummer U hU hUB g h1 h2 := by
    rw [X.galN_eq_N U hU hUB]
    exact X.kummer U hU hUB g h1 h2
  finiteIndex U hU hUB := by
    rw [X.galN_eq_N U hU hUB]
    exact X.finiteIndex U hU hUB
  chebotarev U hU hUB g avoid := by
    rw [X.galN_eq_N U hU hUB]
    exact X.chebotarev U hU hUB g avoid
  reading := hI.1
  o12 := hI.2

/-- **The density form** (the model of the wired leaf; its type is unchanged) from a constituent
model: `Mst` with the induced operators, given the GLUE openness (a) and unramifiedness (b) of
`galN` of `Mst`. Kind: PROVED. -/
def toGaloisDensityModel (hI : X.Inputs) (hopen : GalNOpen T chiType X.tK X.FK B)
    (hunr : GalNUnramified T chiType X.tK X.FK B) : GaloisDensityModel T R ap B chiType where
  M := X.Mst
  instMod := X.modMst
  t := X.tK
  d := X.dK
  F := X.FK
  read := X.readK
  frob := X.frob
  frob_spec := X.frob_spec
  trace_mul := X.trace_mul
  det_orbit := X.det_orbit'
  two_fresh := X.two_fresh'
  trace_one := X.trace_one
  t_class := X.t_class
  kummer U hU hUB g h1 h2 := by
    rw [X.galN_eq_N U hU hUB]
    exact X.kummer U hU hUB g h1 h2
  isOpen := hopen
  unramified := hunr
  reading := hI.1
  o12 := hI.2

/-- **Openness of `N_U` within the budget gives the hypothesis (a) of the density form.** Kind:
PROVED (`galN_eq_N`). -/
theorem galNOpen_of_N (h : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧ E.fixingSubgroup ≤ X.N U) :
    GalNOpen T chiType X.tK X.FK B := by
  intro U hU hUB
  rw [X.galN_eq_N U hU hUB]
  exact h U hU hUB

/-- **The fixed-`U` factorization from the constituent model** (tex 9745–9750). Kind: PROVED. -/
theorem fixedU_of_constituents (hI : X.Inputs) (htyp : IsTypeChar T chiType) :
    FixedUFactorization T R B :=
  (X.toGaloisTraceModel hI).fixedU_of_model htyp

/-- **Primary isolation from the constituent model** (tex 9739, 9947–9948). Kind: PROVED. -/
theorem primary_of_constituents (hI : X.Inputs) (htyp : IsTypeChar T chiType) :
    PrimaryReading T R B :=
  (X.toGaloisTraceModel hI).primary_of_model htyp

/-- **The (O.12) reading from the constituent model** (tex 9905–9945). Kind: PROVED. -/
theorem o12_of_constituents (hI : X.Inputs) (htyp : IsTypeChar T chiType) :
    O12Reading T R ap B :=
  (X.toGaloisTraceModel hI).o12_of_model htyp

/-! ### The unbudgeted forms and saturation (bridges to lane RC0's interfaces) -/

/-- **The unbudgeted forms of the budgeted fields**, on reduced expansions: `det_orbit`,
`two_fresh` and `kummer` at every finite set `U`, `chebotarev` at every set `U` of good primes.
This is NOT given by the text off the budget (tex 9447–9468, 9649–9654, 9741–9745, 10533–10548);
it holds for the zero-form models. Kind: definition (bridge hypothesis, no tex line). -/
def Unbudgeted : Prop :=
  (∀ (U : Finset ℕ) (u v : GalQ), X.redE (X.dΛ u (X.tΛ v (X.F U))) = X.redE (X.tΛ v (X.F U))) ∧
    (∀ (U : Finset ℕ) (g h : GalQ), X.redE (X.tΛ g (X.tΛ h (X.F U))) = 0) ∧
    (∀ (U : Finset ℕ) (g : GalQ), chiType g = 1 → (∀ s ∈ U, bitChar s g = 1) →
      g ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N U) ∧
    (∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (g : GalQ) (avoid : Finset ℕ),
      ∃ q h, ∃ n ∈ X.N U, T.Good q ∧ q ∉ avoid ∧ X.frob q = h * g * h⁻¹ * n)

variable {X} in
/-- `det_orbit` at every `U`, from `Unbudgeted`. Kind: PROVED (projection). -/
theorem Unbudgeted.det_orbit (hX : X.Unbudgeted) (U : Finset ℕ) (u v : GalQ) :
    X.redE (X.dΛ u (X.tΛ v (X.F U))) = X.redE (X.tΛ v (X.F U)) :=
  hX.1 U u v

variable {X} in
/-- `two_fresh` at every `U`, from `Unbudgeted`. Kind: PROVED (projection). -/
theorem Unbudgeted.two_fresh (hX : X.Unbudgeted) (U : Finset ℕ) (g h : GalQ) :
    X.redE (X.tΛ g (X.tΛ h (X.F U))) = 0 :=
  hX.2.1 U g h

variable {X} in
/-- `kummer` at every `U`, from `Unbudgeted`. Kind: PROVED (projection). -/
theorem Unbudgeted.kummer (hX : X.Unbudgeted) :
    ∀ (U : Finset ℕ) (g : GalQ), chiType g = 1 → (∀ s ∈ U, bitChar s g = 1) →
      g ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N U :=
  hX.2.2.1

variable {X} in
/-- `chebotarev` at every set `U` of good primes, from `Unbudgeted`. Kind: PROVED
(projection). -/
theorem Unbudgeted.chebotarev (hX : X.Unbudgeted) :
    ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (g : GalQ) (avoid : Finset ℕ),
      ∃ q h, ∃ n ∈ X.N U, T.Good q ∧ q ∉ avoid ∧ X.frob q = h * g * h⁻¹ * n :=
  hX.2.2.2

/-- With the unbudgeted forms, the two identities land in `Kst` at every `U`. Kind: PROVED. -/
theorem detSpan_le_Kst_of_unbudgeted (hX : X.Unbudgeted) (U : Finset ℕ) :
    X.detSpan U ≤ X.Kst := by
  refine X.le_Kst ?_ (X.detSpan_stable_t U) (X.detSpan_stable_d U)
  rw [detSpan, Submodule.span_le]
  rintro x (⟨a, b, rfl⟩ | ⟨g, h, rfl⟩)
  · show X.redE _ = 0
    rw [map_sub, sub_eq_zero]
    exact hX.1 U a b
  · exact hX.2.1 U g h

/-- With the unbudgeted forms, `galN` of `Mst` is `N_U` at every `U` (no budget). Kind:
PROVED. -/
theorem galN_eq_N_of_unbudgeted (hX : X.Unbudgeted) (U : Finset ℕ) :
    galN chiType X.tK X.FK U = X.N U := by
  ext n
  rw [mem_galN]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun g U' hU' => ?_⟩
    have h := h3 g U' hU'
    rw [FK, tK_mk, tK_mk, mk_eq_mk_iff] at h
    have := X.Kst_le_ker h
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  · intro hn
    refine ⟨hn.1, hn.2.1, fun g U' hU' => ?_⟩
    rw [FK, tK_mk, tK_mk, mk_eq_mk_iff]
    have hnorm := X.N_normal U
    let P : Submodule X.O X.Λ :=
      Submodule.span X.O {x | ∃ g, ∃ n ∈ X.N U, x = X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')} ⊔
        X.detSpan U'
    have hgen : ∀ g, ∀ n ∈ X.N U, X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U') ∈ P :=
      fun g n hn => Submodule.mem_sup_left (Submodule.subset_span ⟨g, n, hn, rfl⟩)
    have hdet : ∀ x ∈ X.detSpan U', x ∈ P := fun x hx => Submodule.mem_sup_right hx
    refine X.le_Kst (P := P) ?_ (fun k => ?_) (fun k => ?_) (hgen g n hn)
    · refine sup_le ?_ (X.Kst_le_ker.trans' (X.detSpan_le_Kst_of_unbudgeted hX U'))
      rw [Submodule.span_le]
      rintro x ⟨g, n, hn, rfl⟩
      show X.redE _ = 0
      rw [map_sub, sub_eq_zero]
      exact hn.2.2 g U' hU'
    · refine sup_le ?_ ((X.detSpan_stable_t U' k).trans (Submodule.comap_mono le_sup_right))
      rw [Submodule.span_le]
      rintro x ⟨g, n, hn, rfl⟩
      show X.tΛ k (X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')) ∈ P
      have hn' : g * n⁻¹ * g⁻¹ ∈ X.N U := hnorm.conj_mem _ (inv_mem hn) g
      have e : X.tΛ k (X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')) =
          (X.tΛ ((k * g) * n) (X.F U') - X.tΛ (k * g) (X.F U')) +
            (X.tΛ ((k * g⁻¹) * (g * n⁻¹ * g⁻¹)) (X.F U') - X.tΛ (k * g⁻¹) (X.F U')) +
            ((X.dΛ (g * n) (X.tΛ (k * (g * n)⁻¹) (X.F U')) - X.tΛ (k * (g * n)⁻¹) (X.F U')) -
              (X.dΛ g (X.tΛ (k * g⁻¹) (X.F U')) - X.tΛ (k * g⁻¹) (X.F U'))) := by
        rw [map_sub, X.tΛ_mul, X.tΛ_mul]
        have h1 : k * (g * n) = (k * g) * n := by group
        have h2 : k * (g * n)⁻¹ = (k * g⁻¹) * (g * n⁻¹ * g⁻¹) := by group
        rw [h1, ← h2]
        abel
      rw [e]
      refine Submodule.add_mem _ (Submodule.add_mem _ (hgen _ _ hn) (hgen _ _ hn')) ?_
      exact Submodule.sub_mem _ (hdet _ (X.gen1_mem U' _ _)) (hdet _ (X.gen1_mem U' _ _))
    · refine sup_le ?_ ((X.detSpan_stable_d U' k).trans (Submodule.comap_mono le_sup_right))
      rw [Submodule.span_le]
      rintro x ⟨g, n, hn, rfl⟩
      show X.dΛ k (X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')) ∈ P
      have e : X.dΛ k (X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')) =
          (X.tΛ (g * n) (X.F U') - X.tΛ g (X.F U')) +
            ((X.dΛ k (X.tΛ (g * n) (X.F U')) - X.tΛ (g * n) (X.F U')) -
              (X.dΛ k (X.tΛ g (X.F U')) - X.tΛ g (X.F U'))) := by
        rw [map_sub]
        abel
      rw [e]
      exact Submodule.add_mem _ (hgen _ _ hn)
        (Submodule.sub_mem _ (hdet _ (X.gen1_mem U' _ _)) (hdet _ (X.gen1_mem U' _ _)))

/-- **The unbudgeted forms pass to the Galois trace model** (no tex line). Kind: PROVED. -/
theorem unbudgeted_toGaloisTraceModel (hX : X.Unbudgeted) (hI : X.Inputs) :
    (X.toGaloisTraceModel hI).Unbudgeted := by
  refine ⟨fun U u v => ?_, fun U g h => ?_, fun U g h1 h2 => ?_, fun U hU g avoid => ?_⟩
  · show X.dK u (X.tK v (X.FK U)) = X.tK v (X.FK U)
    rw [FK, tK_mk, dK_mk, mk_eq_mk_iff]
    exact X.detSpan_le_Kst_of_unbudgeted hX U (X.gen1_mem U u v)
  · show X.tK g (X.tK h (X.FK U)) = 0
    rw [FK, tK_mk, tK_mk, Submodule.Quotient.mk_eq_zero]
    exact X.detSpan_le_Kst_of_unbudgeted hX U (X.gen2_mem U g h)
  · show g ∈ Subgroup.closure (sqSet GalQ) ⊔ galN chiType X.tK X.FK U
    rw [X.galN_eq_N_of_unbudgeted hX U]
    exact hX.2.2.1 U g h1 h2
  · show ∃ q h, ∃ n ∈ galN chiType X.tK X.FK U, T.Good q ∧ q ∉ avoid ∧
      X.frob q = h * g * h⁻¹ * n
    rw [X.galN_eq_N_of_unbudgeted hX U]
    exact hX.2.2.2 U hU g avoid

/-- **The reduced trace orbit of zero forms is constant** (zero). Kind: PROVED. -/
theorem redTrace_const_of_forms_eq_zero (hF : ∀ U, X.F U = 0) :
    ∀ g U, redTrace X.m X.expand X.ρ X.stable_t X.F g U =
      redTrace X.m X.expand X.ρ X.stable_t X.F 1 U := by
  intro g U
  simp only [redTrace, hF U, map_zero]

/-- **A constituent model with zero forms satisfies the unbudgeted forms** (no tex line). Kind:
PROVED. -/
theorem unbudgeted_of_forms_eq_zero (hF : ∀ U, X.F U = 0) (htyp : IsTypeChar T chiType) :
    X.Unbudgeted := by
  have hrt := X.redTrace_const_of_forms_eq_zero hF
  refine ⟨fun U u v => ?_, fun U g h => ?_, fun U g h1 h2 => ?_, fun U hU g avoid => ?_⟩
  · simp only [hF U, map_zero]
  · simp only [hF U, map_zero]
  · exact Subgroup.mem_sup_right ((mem_consN_of_const hrt).mpr ⟨h1, h2⟩)
  · exact consN_const_chebotarev T htyp hrt X.frob_spec U hU g avoid

/-- **`Mst` is nonzero as soon as some vector of `Λ` has a nonzero reduced expansion** (`Kst` lies
in the reduction kernel). Kind: PROVED. -/
theorem nontrivial_Mst (v : X.Λ) (hv : X.redE v ≠ 0) : Nontrivial X.Mst :=
  ⟨⟨Submodule.Quotient.mk v, 0, fun h => hv (by
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact X.Kst_le_ker h)⟩⟩

/-- **Saturation of the integral module** (NOT assumed by the text: "No saturation of the
integral Fourier module is assumed, and no identification of its abstract quotient with all
reduced expansions is needed", tex 9644–9646): a vector of `Λ` whose reduced expansion vanishes
lies in `𝔪Λ`. Only the bridge to lane RC0's `ConstituentModelRel` uses it, because that
interface reads the forms in `Λ/𝔪Λ`. Kind: definition (bridge hypothesis). -/
def Saturated : Prop :=
  ∀ v : X.Λ, X.redE v = 0 → (v : X.I → X.K) ∈ (X.m • ⊤ : Submodule X.O X.Λ).map X.Λ.subtype

/-- **`𝔪Λ` reduces to zero** (the converse of saturation, always true). Kind: PROVED (the
reduced expansions are annihilated by `𝔪`). -/
theorem le_ker_redE : (X.m • ⊤ : Submodule X.O X.Λ) ≤ LinearMap.ker X.redE :=
  le_ker_redExpOf X.m X.expand

end GaloisConstituentModel

/-- **RC2's rules within a budget from a constituent model over `G_ℚ`** (the odd source at one
stage). Kind: PROVED (`GaloisTraceModel.rulesUpTo_of_model`). -/
theorem rulesUpTo_of_galoisConstituents {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} {chiType : GalQ →* Multiplicative L} {W : ℕ}
    (X : GaloisConstituentModel T R ap (W + 1) chiType) (hI : X.Inputs)
    (htyp : IsTypeChar T chiType) (hap : ApEven T ap) : RulesUpTo ε (symb T R) W :=
  GaloisTraceModel.rulesUpTo_of_model (X.toGaloisTraceModel hI) htyp hap

/-- **RC2's coefficient rules from constituent models at every budget** (the even source). Kind:
PROVED (`coefficientRules_of_galois`). -/
theorem coefficientRules_of_galoisConstituents {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} {chiType : GalQ →* Multiplicative L}
    (X : ∀ B, GaloisConstituentModel T R ap B chiType) (hI : ∀ B, (X B).Inputs)
    (htyp : IsTypeChar T chiType) (hap : ApEven T ap) : CoefficientRules ε (symb T R) :=
  coefficientRules_of_galois (fun B => (X B).toGaloisTraceModel (hI B)) htyp hap

/-! ## Constituent models with zero forms -/

section ZeroForms

variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]

/-- **A constituent model of the zero reading on given constituent representations** (the zero
forms `F_U = 0`, the zero functionals). It is built from
* `FrobeniusExists` and a type character reading the types;
* a coefficient ring with `2 ∈ 𝔪`;
* representations `ρ` of `G_ℚ` and a lattice `Λ` preserved by their scalar traces and
  determinants;
* an integral expansion of `Λ`.

The fields about `U` hold at every `U`: the reduced trace orbit of the zero forms is constant, so
`N_U` is the common kernel of the characters (`mem_consN_of_const`). Kind: PROVED. -/
def GaloisConstituentModel.zeroForms (hFrob : FrobeniusExists) (T : TypeData L ε) (ap : ℕ → ℤ)
    (B : ℕ) (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType) (m : Ideal O)
    (two_mem : (2 : O) ∈ m) (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (stable_t : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (stable_d : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ)
    {C : Type} (coefK : (I → K) →ₗ[K] (C → K)) (expand : Λ →ₗ[O] (C → O))
    (expand_spec : ∀ (v : Λ) (n : C), algebraMap O K (expand v n) = coefK v n) :
    GaloisConstituentModel T (fun _ => 0) ap B chiType where
  I := I
  K := K
  O := O
  m := m
  two_mem := two_mem
  ρ := ρ
  Λ := Λ
  stable_t := stable_t
  stable_d := stable_d
  C := C
  coefK := coefK
  expand := expand
  expand_spec := expand_spec
  F _ := 0
  read _ := 0
  frob := chooseFrob hFrob
  frob_spec _ hq := chooseFrob_spec hFrob hq.1
  det_orbit _ _ _ _ _ := by simp only [map_zero]
  two_fresh _ _ _ _ _ := by simp only [map_zero]
  kummer _ _ _ _ h1 h2 := Subgroup.mem_sup_right
    ((mem_consN_of_const (fun g U => by simp only [redTrace, map_zero])).mpr ⟨h1, h2⟩)
  finiteIndex U _ _ := by
    have := finite_of_typeData T
    exact consN_const_finiteIndex (fun g U => by simp only [redTrace, map_zero]) U
  chebotarev U hU _ g avoid :=
    consN_const_chebotarev T htyp (fun g U => by simp only [redTrace, map_zero])
      (fun _ hq => chooseFrob_spec hFrob hq.1) U hU g avoid

variable (hFrob : FrobeniusExists) (T : TypeData L ε) (ap : ℕ → ℤ) (B : ℕ)
  (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType) (m : Ideal O)
  (two_mem : (2 : O) ∈ m) (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
  (stable_t : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (stable_d : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ)
  {C : Type} (coefK : (I → K) →ₗ[K] (C → K)) (expand : Λ →ₗ[O] (C → O))
  (expand_spec : ∀ (v : Λ) (n : C), algebraMap O K (expand v n) = coefK v n)

attribute [local instance] GaloisConstituentModel.modMst

/-- The functionals of a zero-forms model vanish. Kind: PROVED (definition). -/
theorem GaloisConstituentModel.zeroForms_readK (U : Finset ℕ)
    (x : (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d coefK expand expand_spec).Mst) :
    (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d coefK expand expand_spec).readK U x = 0 :=
  rfl

/-- **The inputs of a zero-forms model hold**: every reading is zero; in (O.12) the elements
`τ, φ` have the prescribed characters by `chi_surj` at the good set `U`. Kind: PROVED. -/
theorem GaloisConstituentModel.zeroForms_inputs :
    (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d coefK expand expand_spec).Inputs := by
  set X := GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
    stable_d coefK expand expand_spec
  refine ⟨fun U q _ _ _ _ => rfl, fun U p hpU hU _ g => ?_⟩
  obtain ⟨τ, hτT, hτB⟩ := X.chi_surj htyp U hU 0 (fun s => if s = p then 1 else 0)
  obtain ⟨φ, hφT, hφB⟩ := X.chi_surj htyp U hU (T.typ p) (fun s => legBit p s)
  refine ⟨τ, φ, 1, Or.inl rfl, by rw [hτT, ofAdd_zero], fun s hs hsp => ?_, ?_, hφT,
    fun s hs _ => hφB s hs, ?_⟩
  · rw [hτB s hs, if_neg' hsp, ofAdd_zero]
  · rw [hτB p hpU, if_pos' rfl]
  · change _ * (0 : ZMod 2) - _ * (0 : ZMod 2) = (0 : ZMod 2) - 0
    simp

/-- **A zero-forms model satisfies the unbudgeted forms** (no tex line). Kind: PROVED. -/
theorem GaloisConstituentModel.zeroForms_unbudgeted :
    (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d coefK expand expand_spec).Unbudgeted :=
  GaloisConstituentModel.unbudgeted_of_forms_eq_zero _ (fun _ => rfl) htyp

end ZeroForms

/-! ## Non-vacuity: one constituent with the genuine `2`-adic Tate representation -/

section Tate

open ZInQ.Manuscript.RC.TateWiring

/-- `2 ∈ 𝔪_{ℤ₂}`. Kind: PROVED (`𝔪_{ℤ₂} = (2)`). -/
theorem two_mem_maximalIdeal_padicInt : (2 : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact_mod_cast Ideal.mem_span_singleton_self ((2 : ℕ) : ℤ_[2])

/-- **The lattice of integral vectors** `{v : Unit → ℚ₂ | v () ∈ ℤ₂}`. Kind: definition. -/
def intLattice : Submodule ℤ_[2] (Unit → ℚ_[2]) := Submodule.pi Set.univ fun _ => 1

/-- Membership in the lattice of integral vectors. Kind: PROVED. -/
theorem mem_intLattice {v : Unit → ℚ_[2]} :
    v ∈ intLattice ↔ ∀ i, ∃ a : ℤ_[2], (a : ℚ_[2]) = v i := by
  simp only [intLattice, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    PadicInt.algebraMap_apply]

/-- The coordinate of an integral vector has norm at most one. Kind: PROVED. -/
theorem norm_le_one_of_mem_intLattice (v : intLattice) (i : Unit) :
    ‖(v : Unit → ℚ_[2]) i‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := mem_intLattice.mp v.2 i
  rw [← ha, ← PadicInt.norm_def]
  exact PadicInt.norm_le_one a

/-- **The integral coordinate** of a vector of the integral lattice, the Fourier expansion of
the one-constituent model (`C = Unit`). Kind: definition. -/
def intCoord : intLattice →ₗ[ℤ_[2]] (Unit → ℤ_[2]) where
  toFun v i := Padic.lift ((v : Unit → ℚ_[2]) i) (norm_le_one_of_mem_intLattice v i)
  map_add' v w := by
    funext i
    apply PadicInt.ext
    rfl
  map_smul' r v := by
    funext i
    apply PadicInt.ext
    rfl

/-- Kind: PROVED (definition). -/
theorem intCoord_coe (v : intLattice) (i : Unit) :
    ((intCoord v i : ℤ_[2]) : ℚ_[2]) = (v : Unit → ℚ_[2]) i := rfl

/-- The integral coordinate is the coordinate (`expand_spec` of the one-constituent model).
Kind: PROVED. -/
theorem intCoord_spec (v : intLattice) (n : Unit) :
    algebraMap ℤ_[2] ℚ_[2] (intCoord v n) = (LinearMap.id : (Unit → ℚ_[2]) →ₗ[ℚ_[2]] _) v n := by
  rw [PadicInt.algebraMap_apply, intCoord_coe]
  rfl

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The `2`-adic Tate representation of `E` with values in `GL₂(ℚ₂)`**: lane RC17's
`rhoGL E` composed with `ℤ₂ ⊂ ℚ₂`. Kind: definition. -/
def tateRhoQ : GalQ →* GL (Fin 2) ℚ_[2] :=
  (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := 2))).comp (rhoGL E)

/-- Kind: PROVED (definition). -/
theorem coe_tateRhoQ (σ : GalQ) :
    ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]) =
      (tateMatrix E σ).map (PadicInt.Coe.ringHom (p := 2)) :=
  rfl

/-- **The trace of `tateRhoQ E σ` is the trace of `ρ_T(σ)` on `T₂E`.** Kind: PROVED. -/
theorem trace_tateRhoQ (σ : GalQ) :
    ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).trace =
      ((LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) := by
  rw [coe_tateRhoQ, ← trace_tateMatrix]
  exact (AddMonoidHom.map_trace (PadicInt.Coe.ringHom (p := 2)) (tateMatrix E σ)).symm

/-- **The determinant of `tateRhoQ E σ` is the determinant of `ρ_T(σ)` on `T₂E`.** Kind:
PROVED. -/
theorem det_tateRhoQ (σ : GalQ) :
    ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).det =
      ((LinearMap.det (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) := by
  rw [coe_tateRhoQ, ← det_tateMatrix]
  exact (RingHom.map_det (PadicInt.Coe.ringHom (p := 2)) (tateMatrix E σ)).symm

/-- **The integral lattice is preserved by the scalar trace of the Tate representation.** Kind:
PROVED. -/
theorem tate_stable_t (g : GalQ) (v : Unit → ℚ_[2]) (hv : v ∈ intLattice) :
    tV (fun _ : Unit => tateRhoQ E) g v ∈ intLattice := by
  rw [mem_intLattice] at hv ⊢
  intro i
  obtain ⟨a, ha⟩ := hv i
  refine ⟨LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 g) * a, ?_⟩
  simp only [tV, scalarOp_apply, trace_tateRhoQ, PadicInt.coe_mul, ha]

/-- **The integral lattice is preserved by the determinant of the Tate representation.** Kind:
PROVED. -/
theorem tate_stable_d (g : GalQ) (v : Unit → ℚ_[2]) (hv : v ∈ intLattice) :
    dV (fun _ : Unit => tateRhoQ E) g v ∈ intLattice := by
  rw [mem_intLattice] at hv ⊢
  intro i
  obtain ⟨a, ha⟩ := hv i
  refine ⟨LinearMap.det (tateRep E 2 g) * a, ?_⟩
  simp only [dV, scalarOp_apply, det_tateRhoQ, PadicInt.coe_mul, ha]

/-- The coordinate of `t(g) v` is the trace of `ρ_T(g)` times the coordinate of `v`. Kind:
PROVED. -/
theorem intCoord_latT (g : GalQ) (v : intLattice) (i : Unit) :
    intCoord (latT (fun _ : Unit => tateRhoQ E) intLattice (tate_stable_t E) g v) i =
      LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 g) * intCoord v i := by
  apply PadicInt.ext
  rw [PadicInt.coe_mul, intCoord_coe, intCoord_coe, latT_coe]
  simp only [tV, scalarOp_apply, trace_tateRhoQ]

/-- The coordinate of `d(g) v` is the determinant of `ρ_T(g)` times the coordinate of `v`. Kind:
PROVED. -/
theorem intCoord_latD (g : GalQ) (v : intLattice) (i : Unit) :
    intCoord (latD (fun _ : Unit => tateRhoQ E) intLattice (tate_stable_d E) g v) i =
      LinearMap.det (tateRep E 2 g) * intCoord v i := by
  apply PadicInt.ext
  rw [PadicInt.coe_mul, intCoord_coe, intCoord_coe, latD_coe]
  simp only [dV, scalarOp_apply, det_tateRhoQ]

/-- The integral vector `1`. Kind: definition. -/
def intOne : intLattice := ⟨fun _ => 1, mem_intLattice.mpr fun _ => ⟨1, PadicInt.coe_one⟩⟩

/-- **The reduced coordinate of the integral vector `1` is nonzero** (`1 ∉ 𝔪_{ℤ₂}`). Kind:
PROVED. -/
theorem intOne_red_ne_zero : redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord intOne ≠ 0 := by
  intro h
  have h1 := congrFun h ()
  rw [redExpOf_apply] at h1
  have hone : intCoord intOne () = 1 := PadicInt.ext rfl
  rw [hone] at h1
  exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one (Ideal.Quotient.eq_zero_iff_mem.mp h1)

/-- **The integral lattice is saturated** (`ℤ₂` is a DVR and the lattice has rank one): a vector
with vanishing reduced coordinate lies in `𝔪Λ`. Kind: PROVED. -/
theorem intLattice_saturated (v : intLattice)
    (hv : redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord v = 0) :
    (v : Unit → ℚ_[2]) ∈
      (IsLocalRing.maximalIdeal ℤ_[2] • ⊤ : Submodule ℤ_[2] intLattice).map intLattice.subtype := by
  have h := congrFun hv ()
  rw [redExpOf_apply] at h
  have ha := Ideal.Quotient.eq_zero_iff_mem.mp h
  have hv' : v = intCoord v () • intOne := by
    apply Subtype.ext
    funext i
    show (v : Unit → ℚ_[2]) i = (intCoord v () • (intOne : Unit → ℚ_[2])) i
    rw [Pi.smul_apply, Algebra.smul_def, PadicInt.algebraMap_apply, intCoord_coe]
    simp [intOne]
  refine ⟨v, ?_, rfl⟩
  rw [hv']
  exact Submodule.smul_mem_smul ha Submodule.mem_top

variable (hFrob : FrobeniusExists)

/-- **Non-vacuity of `GaloisConstituentModel` with a genuine Galois representation**, for every
type data and every type character reading the types. For an elliptic curve `E/ℚ`, given
`FrobeniusExists`, it is the constituent model with the following data:
* ONE constituent (`I = Unit`), whose representation is the `2`-adic Tate representation of `E`;
* `K = ℚ₂`, `O = ℤ₂`, `𝔪` the maximal ideal of `ℤ₂`;
* `Λ` the lattice of integral vectors, with Fourier expansion its coordinate (`C = Unit`);
* the zero forms and the zero functionals.

The operators preserve `Λ` (`tate_stable_t`, `tate_stable_d`), and the module of the Galois
trace model is nonzero (`tateConstituentModelOf_nontrivial`). The
constituents of the actual forms `F_U = θ H_U` are weight-two cuspidal newforms and Eisenstein
character pairs (tex 9647–9654, 9762–9771), not `E` or its twists. Kind: PROVED. -/
def tateConstituentModelOf (T : TypeData L ε) (chiType : GalQ →* Multiplicative L)
    (htyp : IsTypeChar T chiType) (ap : ℕ → ℤ) (B : ℕ) :
    GaloisConstituentModel T (fun _ => 0) ap B chiType :=
  GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp (IsLocalRing.maximalIdeal ℤ_[2])
    two_mem_maximalIdeal_padicInt (fun _ : Unit => tateRhoQ E) intLattice (tate_stable_t E)
    (tate_stable_d E) LinearMap.id intCoord intCoord_spec

section Of

variable (T : TypeData L ε) (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType)
  (ap : ℕ → ℤ) (B : ℕ)

/-- The constituent representation of `tateConstituentModelOf` is the Tate representation of
`E`. Kind: PROVED (definition). -/
theorem tateConstituentModelOf_ρ :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).ρ () = tateRhoQ E :=
  rfl

/-- **The data of `tateConstituentModelOf`**: one constituent, `K = ℚ₂`, `O = ℤ₂`, `𝔪` the
maximal ideal of `ℤ₂`, `Λ` the lattice of integral vectors with its coordinate as expansion,
zero forms and zero functionals. Kind: PROVED (definition). -/
theorem tateConstituentModelOf_data :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).I = Unit ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).K = ℚ_[2] ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).O = ℤ_[2] ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).m = IsLocalRing.maximalIdeal ℤ_[2] ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).Λ = intLattice ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).C = Unit ∧
      (∀ U, (tateConstituentModelOf E hFrob T chiType htyp ap B).F U = 0) ∧
      (∀ U, (tateConstituentModelOf E hFrob T chiType htyp ap B).read U = 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- The scalar trace operator of `tateConstituentModelOf` is multiplication by the trace of
`ρ_T(σ)` on `T₂E`. Kind: PROVED (`trace_tateRhoQ`). -/
theorem tateConstituentModelOf_tV (σ : GalQ) (v : Unit → ℚ_[2]) :
    tV (tateConstituentModelOf E hFrob T chiType htyp ap B).ρ σ v () =
      ((LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) * v () := by
  show ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).trace * v () = _
  rw [trace_tateRhoQ]

/-- The determinant operator of `tateConstituentModelOf` is multiplication by the determinant of
`ρ_T(σ)` on `T₂E`. Kind: PROVED (`det_tateRhoQ`). -/
theorem tateConstituentModelOf_dV (σ : GalQ) (v : Unit → ℚ_[2]) :
    dV (tateConstituentModelOf E hFrob T chiType htyp ap B).ρ σ v () =
      ((LinearMap.det (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) * v () := by
  show ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).det * v () = _
  rw [det_tateRhoQ]

/-- The inputs of `tateConstituentModelOf` hold. Kind: PROVED (`zeroForms_inputs`). -/
theorem tateConstituentModelOf_inputs :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).Inputs :=
  GaloisConstituentModel.zeroForms_inputs hFrob _ ap B _ _ _ _ _ _ _ _ _ _ _

/-- `tateConstituentModelOf` satisfies the unbudgeted forms (its forms are zero; no tex line).
Kind: PROVED (`zeroForms_unbudgeted`). -/
theorem tateConstituentModelOf_unbudgeted :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).Unbudgeted :=
  GaloisConstituentModel.zeroForms_unbudgeted hFrob _ ap B _ _ _ _ _ _ _ _ _ _ _

/-- **The module of reduced expansions of the Tate constituent model is nonzero** (it is
`ℤ₂/𝔪`, on which `t(σ)` is the reduction of the trace of `ρ_T(σ)`). Kind: PROVED
(`intOne_red_ne_zero`). -/
theorem tateConstituentModelOf_nontrivial :
    Nontrivial (tateConstituentModelOf E hFrob T chiType htyp ap B).Mst :=
  GaloisConstituentModel.nontrivial_Mst _ intOne intOne_red_ne_zero

/-- **The Tate constituent model is saturated** (the bridge hypothesis of lane RC0's interface
holds here; no tex line). Kind: PROVED (`intLattice_saturated`). -/
theorem tateConstituentModelOf_saturated :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).Saturated :=
  intLattice_saturated

end Of

variable (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model over the genuine type data** `typeData m`, with the genuine type
character `typChar m`. The Tate representation of `E` only shows that the structure is inhabited
by a genuine Galois representation. Kind: PROVED. -/
def tateConstituentModel :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  tateConstituentModelOf E hFrob (typeData m hm h4) (typChar m) (isTypeChar_typeData m hm h4) ap B

/-- Kind: PROVED (definition). -/
theorem tateConstituentModel_ρ :
    (tateConstituentModel E hFrob m hm h4 ap B).ρ () = tateRhoQ E :=
  rfl

/-- The inputs of `tateConstituentModel` hold. Kind: PROVED. -/
theorem tateConstituentModel_inputs : (tateConstituentModel E hFrob m hm h4 ap B).Inputs :=
  tateConstituentModelOf_inputs E hFrob _ _ _ ap B

/-- `tateConstituentModel` satisfies the unbudgeted forms (no tex line). Kind: PROVED. -/
theorem tateConstituentModel_unbudgeted :
    (tateConstituentModel E hFrob m hm h4 ap B).Unbudgeted :=
  tateConstituentModelOf_unbudgeted E hFrob _ _ _ ap B

/-- `tateConstituentModel` is saturated (no tex line). Kind: PROVED. -/
theorem tateConstituentModel_saturated :
    (tateConstituentModel E hFrob m hm h4 ap B).Saturated :=
  tateConstituentModelOf_saturated E hFrob _ _ _ ap B

/-- **The genuine Galois trace model of the Tate constituent model** over `typeData m`: the
nonzero module of reduced expansions with the induced scalar traces and determinants of `ρ_T`.
Kind: PROVED (`toGaloisTraceModel`). -/
def tateGaloisTraceModel : GaloisTraceModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  (tateConstituentModel E hFrob m hm h4 ap B).toGaloisTraceModel
    (tateConstituentModel_inputs E hFrob m hm h4 ap B)

/-- **The module of `tateGaloisTraceModel` is nonzero.** Kind: PROVED. -/
theorem tateGaloisTraceModel_nontrivial :
    Nontrivial (tateGaloisTraceModel E hFrob m hm h4 ap B).M :=
  GaloisConstituentModel.nontrivial_Mst _ intOne intOne_red_ne_zero

/-- **The Tate constituent model over stage type data**, with the stage type character
`stageChar m₁ ℓ₀`. Kind: PROVED. -/
def tateConstituentModelStage {m₁ ℓ₀ : ℕ} [NeZero m₁] {ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2}
    (T : TypeData (SqClass m₁ × ZMod 2) ε₁) (hTm : T.m = m₁ * ℓ₀)
    (hTtyp : ∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀)) (hℓ₀ : ℓ₀.Prime) (hℓ₀2 : ℓ₀ ≠ 2) :
    GaloisConstituentModel T (fun _ => 0) ap B (stageChar m₁ ℓ₀) :=
  tateConstituentModelOf E hFrob T (stageChar m₁ ℓ₀) (isTypeChar_stage T hTm hTtyp hℓ₀ hℓ₀2) ap B

end Tate

/-- **The readings of the Tate constituent models compose**: the coefficient rules for the zero
symbol over `typeData m`. Kind: PROVED. -/
theorem coefficientRules_tate (E : WeierstrassCurve ℚ) [E.IsElliptic] (hFrob : FrobeniusExists)
    (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m) :
    CoefficientRules (signChar m h4) (symb (typeData m hm h4) (fun _ => 0)) :=
  coefficientRules_of_galoisConstituents
    (fun B => tateConstituentModel E hFrob m hm h4 (fun _ => 0) B)
    (fun B => tateConstituentModel_inputs E hFrob m hm h4 (fun _ => 0) B)
    (isTypeChar_typeData m hm h4) (fun _ _ => ⟨0, (add_zero 0).symm⟩)

/-! ### The case `E = E_ℓ` -/

section Ecurve

variable (hFrob : FrobeniusExists) {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) [NeZero m] (hm : 0 < m)
  (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model of `E_ℓ`** over the genuine type data `typeData m`. Kind:
PROVED. -/
def tateConstituentModelEcurve :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  @tateConstituentModel (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hFrob m _ hm
    h4 ap B

/-- Kind: PROVED (definition). -/
theorem tateConstituentModelEcurve_ρ :
    (tateConstituentModelEcurve hFrob hℓ m hm h4 ap B).ρ () =
      @tateRhoQ (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) :=
  rfl

/-- The inputs of `tateConstituentModelEcurve` hold. Kind: PROVED. -/
theorem tateConstituentModelEcurve_inputs :
    (tateConstituentModelEcurve hFrob hℓ m hm h4 ap B).Inputs :=
  @tateConstituentModel_inputs (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hFrob
    m _ hm h4 ap B

/-- `tateConstituentModelEcurve` satisfies the unbudgeted forms (no tex line). Kind: PROVED. -/
theorem tateConstituentModelEcurve_unbudgeted :
    (tateConstituentModelEcurve hFrob hℓ m hm h4 ap B).Unbudgeted :=
  @tateConstituentModel_unbudgeted (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ)
    hFrob m _ hm h4 ap B

/-- The genuine Galois trace model of `tateConstituentModelEcurve`. Kind: PROVED. -/
def tateGaloisTraceModelEcurve :
    GaloisTraceModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  @tateGaloisTraceModel (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hFrob m _ hm
    h4 ap B

end Ecurve

/-! ### Unconditional forms (`FrobeniusExists` is proved, `frobeniusExists`) -/

section Unconditional

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m)
  (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model over `typeData m`, with no hypothesis** (`frobeniusExists`).
The Tate representation of `E` only shows that the structure is inhabited by a genuine Galois
representation. Kind: PROVED. -/
def tateConstituentModel' :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  tateConstituentModel E frobeniusExists m hm h4 ap B

/-- Kind: PROVED (definition). -/
theorem tateConstituentModel'_ρ : (tateConstituentModel' E m hm h4 ap B).ρ () = tateRhoQ E :=
  rfl

/-- The inputs of `tateConstituentModel'` hold. Kind: PROVED. -/
theorem tateConstituentModel'_inputs : (tateConstituentModel' E m hm h4 ap B).Inputs :=
  tateConstituentModel_inputs E frobeniusExists m hm h4 ap B

/-- `tateConstituentModel'` satisfies the unbudgeted forms (`F = 0`; no tex line). Kind:
PROVED. -/
theorem tateConstituentModel'_unbudgeted : (tateConstituentModel' E m hm h4 ap B).Unbudgeted :=
  tateConstituentModel_unbudgeted E frobeniusExists m hm h4 ap B

/-- `tateConstituentModel'` is saturated (no tex line). Kind: PROVED. -/
theorem tateConstituentModel'_saturated : (tateConstituentModel' E m hm h4 ap B).Saturated :=
  tateConstituentModel_saturated E frobeniusExists m hm h4 ap B

/-- The module of reduced expansions of `tateConstituentModel'` is nonzero. Kind: PROVED. -/
theorem tateConstituentModel'_nontrivial :
    Nontrivial (tateConstituentModel' E m hm h4 ap B).Mst :=
  GaloisConstituentModel.nontrivial_Mst _ intOne intOne_red_ne_zero

end Unconditional

/-- **The coefficient rules for the zero symbol from the Tate constituent models, with no
hypothesis.** Kind: PROVED. -/
theorem coefficientRules_tate' (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) [NeZero m]
    (hm : 0 < m) (h4 : 4 ∣ m) :
    CoefficientRules (signChar m h4) (symb (typeData m hm h4) (fun _ => 0)) :=
  coefficientRules_tate E frobeniusExists m hm h4

section UnconditionalEcurve

variable {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model of `E_ℓ` over `typeData m`, with no hypothesis.** Kind:
PROVED. -/
def tateConstituentModelEcurve' :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  tateConstituentModelEcurve frobeniusExists hℓ m hm h4 ap B

/-- The inputs of `tateConstituentModelEcurve'` hold. Kind: PROVED. -/
theorem tateConstituentModelEcurve'_inputs :
    (tateConstituentModelEcurve' hℓ m hm h4 ap B).Inputs :=
  tateConstituentModelEcurve_inputs frobeniusExists hℓ m hm h4 ap B

/-- `tateConstituentModelEcurve'` satisfies the unbudgeted forms (no tex line). Kind: PROVED. -/
theorem tateConstituentModelEcurve'_unbudgeted :
    (tateConstituentModelEcurve' hℓ m hm h4 ap B).Unbudgeted :=
  tateConstituentModelEcurve_unbudgeted frobeniusExists hℓ m hm h4 ap B

end UnconditionalEcurve

end ZInQ.Manuscript.RC.AddressGenuine
