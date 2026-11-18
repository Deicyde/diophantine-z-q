import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.GaloisModel
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.TraceModelInstance
import ZInQKernel.Contrib.OneProof.RC.TateWiring.Image

/-!
# Theorem 5.3, Lane RC24: the constituent model over the genuine Galois group `G_ℚ`

Manuscript `diophantine_zq.tex`, App F, proof of Proposition `ex:app-coefficient-rules`
(tex 9447–9976): the integral trace module (tex 9638–9668) and the constituent operators
(tex 9712–9797). "For a fixed stage and `U`, choose a finite complete coefficient-field extension
containing all constituents and retain their old multiplicities and diamond translates in the
finite-dimensional characteristic-zero space. Use modular Galois representations on cuspidal
constituents and the two character summands on Eisenstein constituents" (tex 9649–9654). "On a
constituent and all its degeneracies, define `t(g)` and `d(g)` to be the scalar trace and
determinant of its two-dimensional Galois representation, acting as the identity on its
multiplicity space" (tex 9762–9771). The representation of a cuspidal constituent is Carayol's
(tex 9773–9797).

Lane RC0 (round 3) stated the constituent model over an abstract group (`ConstituentModelRel`).
This file is its instance over the genuine group `G_ℚ = GalQ`, feeding the genuine Galois trace
model `GaloisTraceModel` of `GaloisModel.lean`:

* `GaloisConstituentModel T R ap B chiType` is RC0's `ConstituentModelRel` with `G := G_ℚ`,
  genuine Frobenius elements (`frob_spec`), `chiBit := bitChar`, and `N_U := consN …`
  **defined** from the characters and the constituent operators: the `n ∈ G_ℚ` with trivial
  type, trivial `χ_s` for `s ∈ U`, and `t(gn)F_{U'} − t(g)F_{U'} ∈ 𝔪Λ` for every `g ∈ G_ℚ` and every
  `U' ⊆ U`. RC0's fields `level_red`, `N_anti`, `N_chi`, `typ_frob`, `bit_frob` and `chi_surj` are
  PROVED here, not fields; `chi_surj` only at sets of good primes, since at other sets it is false
  for the genuine characters (`not_chi_surj_all` in `GaloisModel.lean`).
* `GaloisConstituentModel.toGaloisTraceModel`: the reduced module `Λ/𝔪Λ` with the induced
  operators is a `GaloisTraceModel` (the proofs of batch 3's `ConstituentModel.toTraceModel` and
  RC0's `ConstituentModelRel.toTraceModelRel`; `consN` is `galN` of the reduced operators,
  `consN_eq_galN`). Hence the readings and RC2's rules: `fixedU_of_constituents`,
  `primary_of_constituents`, `o12_of_constituents`, `rulesUpTo_of_galoisConstituents`,
  `coefficientRules_of_galoisConstituents`.
* Non-vacuity with a genuine Galois representation: for an elliptic curve `E/ℚ`,
  `tateConstituentModel E hFrob m …` has ONE constituent, whose representation is the genuine
  `2`-adic Tate representation of `E` (lane RC17's `rhoGL E`, mapped to `GL₂(ℚ₂)`), on the
  `ℤ₂`-lattice of integral vectors, with `K = ℚ₂`, `O = ℤ₂`, `𝔪` the maximal ideal of `ℤ₂`, the zero
  forms, the zero functionals and the zero reading, over the genuine type data `typeData m` with
  the genuine type character `typChar m`; `tateConstituentModelOf` is the same construction over
  every type data with a type character reading the types (e.g. the stage type data,
  `tateConstituentModelStage`), and `tateConstituentModelEcurve` is the case `E = E_ℓ`. Its
  scalar trace and determinant operators are multiplication by the trace and determinant of
  `ρ_T(σ)` on `T₂E` (`tateConstituentModelOf_tV`, `tateConstituentModelOf_dV`). The
  reduced module `Λ/𝔪Λ = ℤ₂/2ℤ₂` of these models is nonzero (`tateConstituentModelOf_nontrivial`),
  so `tateGaloisTraceModel` is a genuine Galois trace model on a nonzero module. Since
  `FrobeniusExists` is proved (`frobeniusExists`), the primed forms (`tateConstituentModel'`,
  `tateConstituentModelEcurve'`, `coefficientRules_tate'`) carry no hypothesis.
  **The constituents of the actual forms `F_U = θ H_U` are weight-two cuspidal newforms and
  Eisenstein character pairs (tex 9647–9654, 9762–9771), not `E` or its twists; the Tate
  representation of `E` is used only to show that the structure is inhabited by a genuine Galois
  representation.**

DEPARTURE (the constituent representations as data). Mathlib has no Galois representations
attached to modular forms. The field `ρ` therefore carries the representations as data; their
existence is Carayol's theorem (PRINT, tex 9773–9797), and the properties of them that the proof
uses enter through the fields `stable_t`, `stable_d` (GLUE: scalar traces and determinants are
Chebotarev limits of good Hecke and diamond operations, tex 9663–9668), `det_orbit` (GLUE),
`two_fresh` and the inputs `reading`, `o12` (ELLIOT), all stated for the operators built from `ρ`.
As in `GaloisModel.lean`, `finiteIndex` is stated for sets of good primes and records only the
finiteness of `G_ℚ/N_U` (openness is not stated).

Kinds: `PROVED` (a Lean proof), `PRINT` (a printed theorem taken as a field), `GLUE` (a
textbook fact taken as a field), `ELLIOT` (a step of the manuscript's argument taken as a field
or input), `definition`.

References: [Carayol] H. Carayol, *Sur les représentations `ℓ`-adiques associées aux formes
modulaires de Hilbert*, Ann. Sci. École Norm. Sup. (4) 19 (1986), 409–468, §§0.3–0.7,
Théorème A, pp. 409–411 (the locator of tex 9778; not re-read for this file, statement page
`UNVERIFIED` here; a packaged printed form for weight-two newforms is the repository's leaf
`CarayolPrinted.CarayolThmA`, which this file does not use).
[Neukirch] J. Neukirch, *Algebraic number theory*, Grundlehren 322 (Springer 1999), Ch. VII,
Theorem (13.4) (Čebotarev's density theorem; statement page `UNVERIFIED`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-! ## The subgroup `N_U` of the constituent operators -/

section ConsN

variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]

/-- **The subgroup `N_U` cut out by the characters and the constituent operators** (tex
9663–9668, 9745–9750, 9919–9921): the `n ∈ G_ℚ` with `χ_type(n) = 1`, `χ_s(n) = 1` for `s ∈ U`,
and `t(gn)F_{U'} − t(g)F_{U'} ∈ 𝔪Λ` for every `g ∈ G_ℚ` and every `U' ⊆ U`, where `t(g)` is the
scalar trace of the constituent representations `ρ` on `I → K` (batch 3's `tV`) and `𝔪Λ` is the
image of `𝔪 • Λ` in `I → K`. It is the subgroup `galN` of the reduced operators on `Λ/𝔪Λ`
(`GaloisConstituentModel.consN_eq_galN`). Kind: definition. -/
def consN (chiType : GalQ →* Multiplicative L) (m : Ideal O) (ρ : I → GalQ →* GL (Fin 2) K)
    (Λ : Submodule O (I → K)) (F : Finset ℕ → Λ) (U : Finset ℕ) : Subgroup GalQ where
  carrier := {n | chiType n = 1 ∧ (∀ s ∈ U, bitChar s n = 1) ∧ ∀ g : GalQ, ∀ U' ⊆ U,
    tV ρ (g * n) (F U' : I → K) - tV ρ g (F U' : I → K) ∈ (m • ⊤ : Submodule O Λ).map Λ.subtype}
  one_mem' := ⟨map_one _, fun _ _ => map_one _, fun g _ _ => by
    rw [mul_one, sub_self]
    exact Submodule.zero_mem _⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2, ha3⟩ := ha
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine ⟨by rw [map_mul, ha1, hb1, mul_one], fun s hs => by
      rw [map_mul, ha2 s hs, hb2 s hs, mul_one], fun g U' hU' => ?_⟩
    have h := Submodule.add_mem _ (hb3 (g * a) U' hU') (ha3 g U' hU')
    rwa [sub_add_sub_cancel, mul_assoc] at h
  inv_mem' := by
    intro a ha
    obtain ⟨ha1, ha2, ha3⟩ := ha
    refine ⟨by rw [map_inv, ha1, inv_one], fun s hs => by rw [map_inv, ha2 s hs, inv_one],
      fun g U' hU' => ?_⟩
    have h := Submodule.neg_mem _ (ha3 (g * a⁻¹) U' hU')
    rwa [inv_mul_cancel_right, neg_sub] at h

variable {chiType : GalQ →* Multiplicative L} {m : Ideal O} {ρ : I → GalQ →* GL (Fin 2) K}
  {Λ : Submodule O (I → K)}

/-- Membership in `consN`. Kind: PROVED (definition). -/
theorem mem_consN {F : Finset ℕ → Λ} {U : Finset ℕ} {n : GalQ} :
    n ∈ consN chiType m ρ Λ F U ↔ chiType n = 1 ∧ (∀ s ∈ U, bitChar s n = 1) ∧
      ∀ g : GalQ, ∀ U' ⊆ U, tV ρ (g * n) (F U' : I → K) - tV ρ g (F U' : I → K) ∈
        (m • ⊤ : Submodule O Λ).map Λ.subtype :=
  Iff.rfl

/-- **For the zero forms, `N_U` is the common kernel of the type character and the `χ_s`,
`s ∈ U`.** Kind: PROVED. -/
theorem mem_consN_zero {U : Finset ℕ} {n : GalQ} :
    n ∈ consN chiType m ρ Λ (fun _ => 0) U ↔ chiType n = 1 ∧ ∀ s ∈ U, bitChar s n = 1 := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun g U' _ => ?_⟩⟩
  simp only [ZeroMemClass.coe_zero, map_zero, sub_self]
  exact Submodule.zero_mem _

/-- **For the zero forms, `N_U` has finite index** when the type alphabet is finite: it contains
the kernel of the joint character `(χ_type, (χ_s)_{s ∈ U})`, with values in a finite group. Kind:
PROVED (as `galN_finiteIndex_of_subsingleton` in `GaloisModel.lean`). -/
theorem consN_zero_finiteIndex [Finite L] (U : Finset ℕ) :
    (consN chiType m ρ Λ (fun _ => 0) U).FiniteIndex := by
  let φ : GalQ →* Multiplicative L × (U → Multiplicative (ZMod 2)) :=
    chiType.prod (MonoidHom.pi fun s : U => bitChar s)
  have hle : φ.ker ≤ consN chiType m ρ Λ (fun _ => 0) U := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    refine mem_consN_zero.mpr ⟨congrArg Prod.fst hn, fun s hs => ?_⟩
    exact congrFun (congrArg Prod.snd hn) ⟨s, hs⟩
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  exact Subgroup.finiteIndex_of_le hle

/-- **Chebotarev relative to `N_U` for the zero forms, by Dirichlet** (tex 2151–2174, 9938–9942):
for `U` a set of good primes, every `g ∈ G_ℚ` is `h g h⁻¹ n` with `h = 1`, `n ∈ N_U`, at the
Frobenius element of a good prime `q ∉ avoid`. Kind: PROVED (`exists_good_frob`: a good prime with
the type of `g` and the bits of `g` at `U`, batch 3's `realizeNat`; then `n = g⁻¹ Fr_q`). -/
theorem consN_zero_chebotarev (T : TypeData L ε) (htyp : IsTypeChar T chiType)
    {frob : ℕ → GalQ} (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) (U : Finset ℕ)
    (hU : ∀ s ∈ U, T.Good s) (g : GalQ) (avoid : Finset ℕ) :
    ∃ q h, ∃ n ∈ consN chiType m ρ Λ (fun _ => 0) U, T.Good q ∧ q ∉ avoid ∧
      frob q = h * g * h⁻¹ * n := by
  obtain ⟨q, hq, -, hqa, h1, h2⟩ := exists_good_frob T htyp hfrob U avoid hU
    (Multiplicative.toAdd (chiType g)) (fun s => Multiplicative.toAdd (bitChar s g))
  refine ⟨q, 1, g⁻¹ * frob q, mem_consN_zero.mpr ⟨?_, fun s hs => ?_⟩, hq, hqa, by group⟩
  · rw [map_mul, map_inv, h1, ofAdd_toAdd, inv_mul_cancel]
  · rw [map_mul, map_inv, h2 s hs, ofAdd_toAdd, inv_mul_cancel]

end ConsN

/-! ## The constituent model over `G_ℚ` -/

/-- **The constituent model of the integral trace module over `G_ℚ`**, within the budget `B`,
for the type character `chiType` (tex 9638–9668, 9705–9797): RC0's `ConstituentModelRel` with
`G := G_ℚ`, genuine Frobenius elements (`frob_spec`), `chiBit := bitChar`, and
`N_U := consN chiType m ρ Λ F U` defined (see `consN`).
Kinds: `ρ` PRINT ([Carayol, §§0.3–0.7, Théorème A, pp. 409–411], tex 9773–9797, stated as data:
the two-dimensional Galois representations of the cuspidal constituents, and the sums of the two
characters on the Eisenstein constituents, tex 9652–9654, 9762–9771); `stable_t`, `stable_d` GLUE
(tex 9663–9668); `det_orbit` GLUE (tex 9712–9729); `two_fresh` ELLIOT (the squarefree weight
count of (O.9), tex 9741–9745); `kummer` GLUE (tex 9745–9750); `finiteIndex` GLUE (continuity,
tex 9663–9668); `chebotarev` PRINT ([Neukirch, Ch. VII, Theorem (13.4)], in the finite quotient
`G_ℚ/N_U`, `U` good, tex 9666–9668, 9919–9921); `frob_spec` definition; `I`, `K`, `O`, `m`,
`Λ`, `F`, `read` definition (data of the construction, tex 9638–9668). The ELLIOT inputs
`reading`, `o12` are `GaloisConstituentModel.Inputs`, as in RC0. The fields `level_red`, `N_anti`,
`N_chi`, `typ_frob`, `bit_frob`, `chi_surj` of RC0 are theorems here. The constituents of the
actual forms `F_U = θ H_U` are weight-two cuspidal newforms and Eisenstein character pairs.
Owner: RC12 (App F), Lane RC24. -/
structure GaloisConstituentModel (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ)
    (chiType : GalQ →* Multiplicative L) where
  /-- the constituents, with their multiplicities and degeneracies (tex 9649–9654, 9762–9771) -/
  I : Type
  /-- the characteristic-zero coefficient field, containing all constituents (tex 9649–9652,
  9762–9763) -/
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
  /-- PRINT ([Carayol, §§0.3–0.7, Théorème A, pp. 409–411], tex 9773–9797; stated as data): the
  two-dimensional Galois representations of `G_ℚ` of the constituents (Carayol's `ρ_f` on a
  cuspidal newform constituent, the sum of the two characters on an Eisenstein constituent,
  tex 9652–9654, 9762–9771), on the coordinate of each constituent -/
  ρ : I → GalQ →* GL (Fin 2) K
  /-- the integral module generated by the translates of the forms, finite over the coefficient
  ring (tex 9655–9665) -/
  Λ : Submodule O (I → K)
  /-- GLUE (tex 9663–9668): `Λ` is preserved by the scalar trace operators -/
  stable_t : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ
  /-- GLUE (tex 9663–9668): `Λ` is preserved by the determinant operators -/
  stable_d : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ
  /-- the integral forms `F_U = θ H_U` (tex 9647–9648, 9672) -/
  F : Finset ℕ → Λ
  /-- the coefficient-one functionals on the reduced module (tex 9686–9690) -/
  read : Finset ℕ → (Λ ⧸ (m • ⊤ : Submodule O Λ)) →+ ZMod 2
  /-- the Frobenius elements in `G_ℚ` -/
  frob : ℕ → GalQ
  /-- definition: `frob q` is a genuine arithmetic Frobenius element at every good prime `q` -/
  frob_spec : ∀ q, T.Good q → IsFrobAt (frob q) q
  /-- GLUE (tex 9712–9729, the diamond formula and the fresh-trace vanishing of the
  corrections): `(d(u) − 1) t(v) F_U ∈ 𝔪Λ` -/
  det_orbit : ∀ U u v, dV ρ u (tV ρ v (F U : I → K)) - tV ρ v (F U : I → K) ∈
    (m • ⊤ : Submodule O Λ).map Λ.subtype
  /-- ELLIOT (the squarefree weight count of (O.9), tex 9741–9745): `t(g) t(h) F_U ∈ 𝔪Λ` -/
  two_fresh : ∀ U g h, tV ρ g (tV ρ h (F U : I → K)) ∈ (m • ⊤ : Submodule O Λ).map Λ.subtype
  /-- GLUE (Kummer theory for the several radicals, tex 9745–9750): an element with trivial type
  and trivial `χ_s`, `s ∈ U`, lies in the subgroup generated by the squares and `N_U` -/
  kummer : ∀ U g, chiType g = 1 → (∀ s ∈ U, bitChar s g = 1) →
    g ∈ Subgroup.closure (sqSet GalQ) ⊔ consN chiType m ρ Λ F U
  /-- GLUE (continuity of the characters and of the trace action on the finite module,
  tex 9663–9668): for `U` a set of good primes, `G_ℚ/N_U` is finite -/
  finiteIndex : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → (consN chiType m ρ Λ F U).FiniteIndex
  /-- PRINT ([Neukirch, Ch. VII, Theorem (13.4)], Čebotarev's density theorem for the finite
  quotient `G_ℚ/N_U`, `U` good, tex 9666–9668, 9919–9921): every class of `G_ℚ/N_U` is the
  Frobenius class of a good prime outside any finite set -/
  chebotarev : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (g : GalQ) (avoid : Finset ℕ),
    ∃ q h, ∃ n ∈ consN chiType m ρ Λ F U, T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹ * n

namespace GaloisConstituentModel

variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
  {chiType : GalQ →* Multiplicative L} (X : GaloisConstituentModel T R ap B chiType)

attribute [instance] GaloisConstituentModel.instK GaloisConstituentModel.instO
  GaloisConstituentModel.instAlg

/-- The subgroup `N_U` of the model, `consN chiType m ρ Λ F U`. Kind: definition. -/
abbrev N (U : Finset ℕ) : Subgroup GalQ := consN chiType X.m X.ρ X.Λ X.F U

/-! ### RC0's fields, PROVED -/

/-- **`level_red`** (RC0's field; tex 9524–9548, 9663–9668): for `n ∈ N_U` the scalar traces at
`gn` and `g` agree on `F_U` modulo `𝔪Λ`. Kind: PROVED (definition of `consN`, with `U' = U`). -/
theorem level_red (U : Finset ℕ) (g : GalQ) (n : GalQ) (hn : n ∈ X.N U) :
    tV X.ρ (g * n) (X.F U : X.I → X.K) - tV X.ρ g (X.F U : X.I → X.K) ∈
      (X.m • ⊤ : Submodule X.O X.Λ).map X.Λ.subtype :=
  hn.2.2 g U (subset_refl U)

/-- **`N_anti`** (RC0's field): `N_U ≤ N_{U'}` for `U' ⊆ U` (the `U'`-extension lies in the
`U`-extension). Kind: PROVED (definition of `consN`). -/
theorem N_anti (U U' : Finset ℕ) (h : U' ⊆ U) : X.N U ≤ X.N U' :=
  fun _ hn => ⟨hn.1, fun s hs => hn.2.1 s (h hs), fun g U'' hU'' => hn.2.2 g U'' (hU''.trans h)⟩

/-- **`N_chi`** (RC0's field): `N_U` fixes the type fields and `ℚ(√s*)`, `s ∈ U`. Kind: PROVED
(definition of `consN`). -/
theorem N_chi (U : Finset ℕ) : ∀ n ∈ X.N U, chiType n = 1 ∧ ∀ s ∈ U, bitChar s n = 1 :=
  fun _ hn => ⟨hn.1, hn.2.1⟩

/-- **`typ_frob`** (RC0's field): the type of `q` is `χ_type(Fr_q)` (tex 2017–2020, 9936–9940).
Kind: PROVED (from `IsTypeChar` and `frob_spec`). -/
theorem typ_frob (htyp : IsTypeChar T chiType) (q : ℕ) (hq : T.Good q) :
    chiType (X.frob q) = Multiplicative.ofAdd (T.typ q) :=
  htyp q _ hq (X.frob_spec q hq)

/-- **`bit_frob`** (RC0's field): `χ_s(Fr_q) = (s*/q) = (q/s)` (tex 9938–9942). Kind: PROVED
(`bitChar_of_good`). -/
theorem bit_frob (q s : ℕ) (hq : T.Good q) (hs : T.Good s) (hqs : q ≠ s) :
    bitChar s (X.frob q) = Multiplicative.ofAdd (legBit q s) :=
  bitChar_of_good T hq hs hqs (X.frob_spec q hq)

include X in
/-- **`chi_surj` at sets of good primes** (RC0's field, restricted to good `U`; at other `U` it is
false for the genuine characters, `not_chi_surj_all`). Kind: PROVED (`exists_good_frob`: batch 3's
`realizeNat`, CRT and Dirichlet, then the model's Frobenius elements). -/
theorem chi_surj (htyp : IsTypeChar T chiType) (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (ℓ : L)
    (b : ℕ → ZMod 2) :
    ∃ g : GalQ, chiType g = Multiplicative.ofAdd ℓ ∧
      ∀ s ∈ U, bitChar s g = Multiplicative.ofAdd (b s) := by
  obtain ⟨q, -, -, -, h1, h2⟩ := exists_good_frob T htyp X.frob_spec U ∅ hU ℓ b
  exact ⟨_, h1, h2⟩

/-! ### The reduced trace module `Λ/𝔪Λ` -/

/-- **The reduced trace module** `M = Λ/𝔪Λ` (tex 9638–9646, 9729). Kind: definition. -/
abbrev Mred : Type := X.Λ ⧸ (X.m • ⊤ : Submodule X.O X.Λ)

/-- `2 • x = 0` on the reduced module (`2 ∈ 𝔪`). Kind: PROVED. -/
theorem two_nsmul_Mred (x : X.Mred) : 2 • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    show 2 • (X.m • ⊤ : Submodule X.O X.Λ).mkQ v = 0
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← Nat.cast_smul_eq_nsmul X.O]
    exact Submodule.smul_mem_smul (by exact_mod_cast X.two_mem) trivial

/-- The `𝔽₂`-structure of the reduced module (`2 ∈ 𝔪`). Kind: definition. -/
abbrev modMred : Module (ZMod 2) X.Mred := AddCommGroup.zmodModule X.two_nsmul_Mred

/-- `t(g)` on `Λ` (tex 9762–9771). Kind: definition. -/
def tΛ (g : GalQ) : X.Λ →ₗ[X.O] X.Λ :=
  ((tV X.ρ g).restrictScalars X.O).restrict (X.stable_t g)

/-- `d(g)` on `Λ` (tex 9762–9771). Kind: definition. -/
def dΛ (g : GalQ) : X.Λ →ₗ[X.O] X.Λ :=
  ((dV X.ρ g).restrictScalars X.O).restrict (X.stable_d g)

/-- An `O`-linear endomorphism of `Λ` preserves `𝔪Λ`. Kind: PROVED. -/
theorem le_comap (f : X.Λ →ₗ[X.O] X.Λ) :
    (X.m • ⊤ : Submodule X.O X.Λ) ≤ (X.m • ⊤ : Submodule X.O X.Λ).comap f := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact smul_mono_right _ le_top

/-- The reduction of an `O`-linear endomorphism of `Λ`, as an additive map of `M`. Kind:
definition. -/
def redOp (f : X.Λ →ₗ[X.O] X.Λ) : X.Mred →+ X.Mred :=
  ((X.m • ⊤ : Submodule X.O X.Λ).mapQ _ f (X.le_comap f)).toAddMonoidHom

attribute [local instance] GaloisConstituentModel.modMred

/-- `t(g)` on the reduced trace module. Kind: definition. -/
def tM (g : GalQ) : X.Mred →ₗ[ZMod 2] X.Mred := (X.redOp (X.tΛ g)).toZModLinearMap 2

/-- `d(g)` on the reduced trace module. Kind: definition. -/
def dM (g : GalQ) : X.Mred →ₗ[ZMod 2] X.Mred := (X.redOp (X.dΛ g)).toZModLinearMap 2

/-- The reduced forms `F_U`. Kind: definition. -/
def FM (U : Finset ℕ) : X.Mred := Submodule.Quotient.mk (X.F U)

/-- The coefficient-one functionals. Kind: definition. -/
def readM (U : Finset ℕ) : X.Mred →ₗ[ZMod 2] ZMod 2 := (X.read U).toZModLinearMap 2

/-- Kind: PROVED (definition). -/
theorem tM_mk (g : GalQ) (v : X.Λ) :
    X.tM g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (X.tΛ g v) := rfl

/-- Kind: PROVED (definition). -/
theorem dM_mk (g : GalQ) (v : X.Λ) :
    X.dM g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (X.dΛ g v) := rfl

/-- Two vectors of `Λ` have the same reduction iff their difference lies in `𝔪Λ`. Kind:
PROVED. -/
theorem mk_eq_mk_iff (v w : X.Λ) :
    (Submodule.Quotient.mk v : X.Mred) = Submodule.Quotient.mk w ↔
      (v : X.I → X.K) - w ∈ (X.m • ⊤ : Submodule X.O X.Λ).map X.Λ.subtype := by
  rw [Submodule.Quotient.eq]
  constructor
  · intro h
    exact ⟨v - w, h, rfl⟩
  · rintro ⟨y, hy, hyw⟩
    have e : y = v - w := Subtype.ext hyw
    rwa [e] at hy

/-- A vector of `Λ` lying in `𝔪Λ` reduces to zero. Kind: PROVED. -/
theorem mk_eq_zero_of_mem {w : X.Λ}
    (hw : (w : X.I → X.K) ∈ (X.m • ⊤ : Submodule X.O X.Λ).map X.Λ.subtype) :
    (Submodule.Quotient.mk w : X.Mred) = 0 := by
  obtain ⟨y, hy, hyw⟩ := hw
  rw [Submodule.Quotient.mk_eq_zero]
  have e : w = y := Subtype.ext hyw.symm
  rw [e]
  exact hy

/-- **`trace_mul` on the reduced module** (tex 9734–9737). Kind: PROVED (lane RC12's matrix
identity on each constituent, batch 3's `tV_mul`, then reduction). -/
theorem trace_mul (g h : GalQ) (x : X.Mred) :
    X.tM g (X.tM h x) = X.tM (g * h) x + X.dM h (X.tM (g * h⁻¹) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [tM_mk, tM_mk, tM_mk, tM_mk, dM_mk, ← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact tV_mul X.ρ g h (v : X.I → X.K)

/-- **`det_orbit` on the reduced module** (tex 9719–9733). Kind: PROVED (from the GLUE field
`det_orbit`). -/
theorem det_orbit' (U : Finset ℕ) (u v : GalQ) : X.dM u (X.tM v (X.FM U)) = X.tM v (X.FM U) := by
  rw [FM, tM_mk, dM_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  exact X.mk_eq_zero_of_mem (X.det_orbit U u v)

/-- **`two_fresh` on the reduced module** (tex 9741–9745). Kind: PROVED (from the ELLIOT field
`two_fresh`). -/
theorem two_fresh' (U : Finset ℕ) (g h : GalQ) : X.tM g (X.tM h (X.FM U)) = 0 := by
  rw [FM, tM_mk, tM_mk]
  exact X.mk_eq_zero_of_mem (X.two_fresh U g h)

/-- **`trace_one`** (tex 9739). Kind: PROVED (`tr 1 = 2`, `2 ∈ 𝔪`). -/
theorem trace_one (x : X.Mred) : X.tM 1 x = (2 : ZMod 2) • x := by
  rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [tM_mk]
    have e : X.tΛ 1 v = (2 : ℕ) • v := by
      apply Subtype.ext
      show tV X.ρ 1 (v : X.I → X.K) = (((2 : ℕ) • v : X.Λ) : X.I → X.K)
      rw [tV_one, two_smul]
      simp [two_nsmul]
    rw [e, ← Submodule.mkQ_apply, map_nsmul, Submodule.mkQ_apply]
    exact X.two_nsmul_Mred _

/-- **`t` is a class function** (tex 9762–9771). Kind: PROVED (the trace of a matrix is
conjugation invariant, batch 3's `tV_conj`). -/
theorem t_class (g h : GalQ) : X.tM (h * g * h⁻¹) = X.tM g := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [tM_mk, tM_mk]
    congr 1
    apply Subtype.ext
    show tV X.ρ (h * g * h⁻¹) (v : X.I → X.K) = tV X.ρ g v
    rw [tV_conj]

/-- **The reduced traces agree on `F_U` iff the constituent traces agree modulo `𝔪Λ`.** Kind:
PROVED. -/
theorem tM_FM_eq_iff (g n : GalQ) (U : Finset ℕ) :
    X.tM (g * n) (X.FM U) = X.tM g (X.FM U) ↔
      tV X.ρ (g * n) (X.F U : X.I → X.K) - tV X.ρ g (X.F U : X.I → X.K) ∈
        (X.m • ⊤ : Submodule X.O X.Λ).map X.Λ.subtype := by
  rw [FM, tM_mk, tM_mk]
  exact X.mk_eq_mk_iff _ _

/-- **`level`** (RC0's `TraceModelRel.level`): `t(·)F_U` factors through `G_ℚ/N_U` on the
reduced module. Kind: PROVED (`level_red`). -/
theorem level (U : Finset ℕ) (g n : GalQ) (hn : n ∈ X.N U) :
    X.tM (g * n) (X.FM U) = X.tM g (X.FM U) :=
  (X.tM_FM_eq_iff g n U).mpr (X.level_red U g n hn)

/-- **`N_U` is the subgroup `galN` of the reduced operators** (`GaloisModel.lean`): the defining
condition `t(gn)F_{U'} − t(g)F_{U'} ∈ 𝔪Λ` is `t(gn)F_{U'} = t(g)F_{U'}` on `Λ/𝔪Λ`. Kind:
PROVED. -/
theorem consN_eq_galN (U : Finset ℕ) : X.N U = galN chiType X.tM X.FM U := by
  ext n
  rw [mem_galN, N, mem_consN]
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun g =>
    forall₂_congr fun U' _ => (X.tM_FM_eq_iff g n U').symm))

/-- **`N_U` is normal** (it fixes a Galois extension; tex 9919–9921). Kind: PROVED
(`consN_eq_galN`, `galN_normal`, `t_class`). -/
theorem N_normal (U : Finset ℕ) : (X.N U).Normal := by
  rw [X.consN_eq_galN U]
  exact galN_normal X.t_class

/-! ### The genuine Galois trace model of the constituent model -/

/-- **The two ELLIOT inputs of the constituent model**, for the reduced operators (as RC0's
`ConstituentModelRel.Inputs`): the coefficient-one reading of a fresh vertex (tex 9671–9704) and
(O.12) at coefficient one (tex 9905–9918), with `χ_s = bitChar s`. Kind: definition. -/
def Inputs : Prop :=
  (∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
      (insert q U).card ≤ B → R (insert q U) = X.readM U (X.tM (X.frob q) (X.FM U))) ∧
  (∀ (U : Finset ℕ) (p : ℕ), p ∈ U → (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g : GalQ,
      ∃ (τ φ : GalQ) (κ0 : ℤ), (κ0 = 1 ∨ κ0 = -1) ∧
        chiType τ = 1 ∧ (∀ s ∈ U, s ≠ p → bitChar s τ = 1) ∧
        bitChar p τ = Multiplicative.ofAdd 1 ∧
        chiType φ = Multiplicative.ofAdd (T.typ p) ∧
        (∀ s ∈ U, s ≠ p → bitChar s φ = Multiplicative.ofAdd (legBit p s)) ∧
        ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) *
            X.readM (U.erase p) (X.tM (g * τ * φ) (X.FM (U.erase p))) -
          ((Cp (ap p) κ0 : ℤ) : ZMod 2) * X.readM (U.erase p) (X.tM (g * φ) (X.FM (U.erase p))) =
        X.readM U (X.tM (g * τ) (X.FM U)) - X.readM U (X.tM g (X.FM U)))

/-- **The genuine Galois trace model of the constituent model** (tex 9638–9771): the reduced
module `Λ/𝔪Λ` with the reduced constituent operators, forms and functionals. Kind: PROVED (the
trace identities, `t(1) = 2` and class invariance from the construction; `kummer`,
`finiteIndex`, `chebotarev` transported along `consN_eq_galN`; `reading`, `o12` the inputs). -/
def toGaloisTraceModel (hI : X.Inputs) : GaloisTraceModel T R ap B chiType where
  M := X.Mred
  instMod := X.modMred
  t := X.tM
  d := X.dM
  F := X.FM
  read := X.readM
  frob := X.frob
  frob_spec := X.frob_spec
  trace_mul := X.trace_mul
  det_orbit := X.det_orbit'
  two_fresh := X.two_fresh'
  trace_one := X.trace_one
  t_class := X.t_class
  kummer U g h1 h2 := by
    rw [← X.consN_eq_galN U]
    exact X.kummer U g h1 h2
  finiteIndex U hU := by
    rw [← X.consN_eq_galN U]
    exact X.finiteIndex U hU
  chebotarev U hU g avoid := by
    rw [← X.consN_eq_galN U]
    exact X.chebotarev U hU g avoid
  reading := hI.1
  o12 := hI.2

/-- **The fixed-`U` factorization from the constituent model** (tex 9745–9750). Kind: PROVED
(`GaloisTraceModel.fixedU_of_model`). -/
theorem fixedU_of_constituents (hI : X.Inputs) (htyp : IsTypeChar T chiType) :
    FixedUFactorization T R B :=
  (X.toGaloisTraceModel hI).fixedU_of_model htyp

/-- **Primary isolation from the constituent model** (tex 9739, 9947–9948). Kind: PROVED
(`GaloisTraceModel.primary_of_model`). -/
theorem primary_of_constituents (hI : X.Inputs) (htyp : IsTypeChar T chiType) :
    PrimaryReading T R B :=
  (X.toGaloisTraceModel hI).primary_of_model htyp

/-- **The (O.12) reading on prime sets from the constituent model** (tex 9905–9945). Kind: PROVED
(`GaloisTraceModel.o12_of_model`). -/
theorem o12_of_constituents (hI : X.Inputs) (htyp : IsTypeChar T chiType) :
    O12Reading T R ap B :=
  (X.toGaloisTraceModel hI).o12_of_model htyp

end GaloisConstituentModel

/-- **RC2's rules within a budget from a constituent model over `G_ℚ`** (the odd source at one
stage). Kind: PROVED (`GaloisTraceModel.rulesUpTo_of_model`). -/
theorem rulesUpTo_of_galoisConstituents {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} {chiType : GalQ →* Multiplicative L} {W : ℕ}
    (X : GaloisConstituentModel T R ap (W + 1) chiType) (hI : X.Inputs)
    (htyp : IsTypeChar T chiType) (hap : ApEven T ap) : RulesUpTo ε (symb T R) W :=
  GaloisTraceModel.rulesUpTo_of_model (X.toGaloisTraceModel hI) htyp hap

/-- **RC2's coefficient rules from constituent models over `G_ℚ` at every budget** (the even
source). Kind: PROVED (`coefficientRules_of_galois`). -/
theorem coefficientRules_of_galoisConstituents {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} {chiType : GalQ →* Multiplicative L}
    (X : ∀ B, GaloisConstituentModel T R ap B chiType) (hI : ∀ B, (X B).Inputs)
    (htyp : IsTypeChar T chiType) (hap : ApEven T ap) : CoefficientRules ε (symb T R) :=
  coefficientRules_of_galois (fun B => (X B).toGaloisTraceModel (hI B)) htyp hap

/-! ## Constituent models with zero forms -/

section ZeroForms

variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]

/-- **A constituent model of the zero reading on given constituent representations**: given
`FrobeniusExists`, a type character reading the types, a coefficient ring with `2 ∈ 𝔪`,
representations `ρ` of `G_ℚ` and a lattice `Λ` preserved by their scalar traces and
determinants, the model with the zero forms `F_U = 0`, the zero functionals and the zero reading.
`frob` is chosen by `FrobeniusExists`; `N_U` is the common kernel of the characters
(`mem_consN_zero`), so `kummer` holds, `finiteIndex` holds (`consN_zero_finiteIndex`, the type
alphabet being finite, `finite_of_typeData`), and `chebotarev` holds by Dirichlet
(`consN_zero_chebotarev`). Kind: PROVED. -/
def GaloisConstituentModel.zeroForms (hFrob : FrobeniusExists) (T : TypeData L ε) (ap : ℕ → ℤ)
    (B : ℕ) (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType) (m : Ideal O)
    (two_mem : (2 : O) ∈ m) (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (stable_t : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (stable_d : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ) :
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
  F _ := 0
  read _ := 0
  frob := chooseFrob hFrob
  frob_spec _ hq := chooseFrob_spec hFrob hq.1
  det_orbit _ _ _ := by
    simp only [ZeroMemClass.coe_zero, map_zero, sub_self]
    exact Submodule.zero_mem _
  two_fresh _ _ _ := by
    simp only [ZeroMemClass.coe_zero, map_zero]
    exact Submodule.zero_mem _
  kummer _ _ h1 h2 := Subgroup.mem_sup_right (mem_consN_zero.mpr ⟨h1, h2⟩)
  finiteIndex U _ := by
    have := finite_of_typeData T
    exact consN_zero_finiteIndex U
  chebotarev U hU g avoid :=
    consN_zero_chebotarev T htyp (fun _ hq => chooseFrob_spec hFrob hq.1) U hU g avoid

variable (hFrob : FrobeniusExists) (T : TypeData L ε) (ap : ℕ → ℤ) (B : ℕ)
  (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType) (m : Ideal O)
  (two_mem : (2 : O) ∈ m) (ρ : I → GalQ →* GL (Fin 2) K) (Λ : Submodule O (I → K))
  (stable_t : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (stable_d : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ)

/-- The functionals of a zero-forms model vanish. Kind: PROVED (definition). -/
theorem GaloisConstituentModel.zeroForms_readM (U : Finset ℕ)
    (x : (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d).Mred) :
    (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d).readM U x = 0 :=
  rfl

/-- **The inputs of a zero-forms model hold**: every reading is zero; in (O.12) the elements
`τ, φ` have the prescribed characters by `chi_surj` at the good set `U`. Kind: PROVED. -/
theorem GaloisConstituentModel.zeroForms_inputs :
    (GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
      stable_d).Inputs := by
  set X := GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp m two_mem ρ Λ stable_t
    stable_d
  refine ⟨fun U q _ _ _ _ => (GaloisConstituentModel.zeroForms_readM hFrob T ap B chiType htyp m
    two_mem ρ Λ stable_t stable_d U _).symm, fun U p hpU hU _ g => ?_⟩
  obtain ⟨τ, hτT, hτB⟩ := X.chi_surj htyp U hU 0 (fun s => if s = p then 1 else 0)
  obtain ⟨φ, hφT, hφB⟩ := X.chi_surj htyp U hU (T.typ p) (fun s => legBit p s)
  refine ⟨τ, φ, 1, Or.inl rfl, by rw [hτT, ofAdd_zero], fun s hs hsp => ?_, ?_, hφT,
    fun s hs _ => hφB s hs, ?_⟩
  · rw [hτB s hs, if_neg' hsp, ofAdd_zero]
  · rw [hτB p hpU, if_pos' rfl]
  · change _ * (0 : ZMod 2) - _ * (0 : ZMod 2) = (0 : ZMod 2) - 0
    simp

end ZeroForms

/-! ## Non-vacuity: one constituent with the genuine `2`-adic Tate representation -/

section Tate

open ZInQ.Manuscript.RC.TateWiring

/-- `2 ∈ 𝔪_{ℤ₂}`. Kind: PROVED (`𝔪_{ℤ₂} = (2)`). -/
theorem two_mem_maximalIdeal_padicInt : (2 : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact_mod_cast Ideal.mem_span_singleton_self ((2 : ℕ) : ℤ_[2])

/-- **The lattice of integral vectors** `{v : Unit → ℚ₂ | v () ∈ ℤ₂}`, a `ℤ₂`-submodule. Kind:
definition. -/
def intLattice : Submodule ℤ_[2] (Unit → ℚ_[2]) := Submodule.pi Set.univ fun _ => 1

/-- Membership in the lattice of integral vectors. Kind: PROVED. -/
theorem mem_intLattice {v : Unit → ℚ_[2]} :
    v ∈ intLattice ↔ ∀ i, ∃ a : ℤ_[2], (a : ℚ_[2]) = v i := by
  simp only [intLattice, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one,
    PadicInt.algebraMap_apply]

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The `2`-adic Tate representation of `E` with values in `GL₂(ℚ₂)`**: lane RC17's
`rhoGL E : G_ℚ →* GL₂(ℤ₂)` (the matrices of `ρ_T(σ)` on `T₂E` in a `ℤ₂`-basis) composed with the
inclusion `ℤ₂ ⊂ ℚ₂`. Kind: definition. -/
def tateRhoQ : GalQ →* GL (Fin 2) ℚ_[2] :=
  (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := 2))).comp (rhoGL E)

/-- The matrix of `tateRhoQ E σ` is the Tate matrix of `σ`, entries in `ℤ₂`. Kind: PROVED
(definition). -/
theorem coe_tateRhoQ (σ : GalQ) :
    ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]) =
      (tateMatrix E σ).map (PadicInt.Coe.ringHom (p := 2)) :=
  rfl

/-- **The trace of `tateRhoQ E σ` is the trace of `ρ_T(σ)` on `T₂E`**, an element of `ℤ₂`.
Kind: PROVED. -/
theorem trace_tateRhoQ (σ : GalQ) :
    ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).trace =
      ((LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) := by
  rw [coe_tateRhoQ, ← trace_tateMatrix]
  exact (AddMonoidHom.map_trace (PadicInt.Coe.ringHom (p := 2)) (tateMatrix E σ)).symm

/-- **The determinant of `tateRhoQ E σ` is the determinant of `ρ_T(σ)` on `T₂E`**, an element
of `ℤ₂`. Kind: PROVED. -/
theorem det_tateRhoQ (σ : GalQ) :
    ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).det =
      ((LinearMap.det (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) := by
  rw [coe_tateRhoQ, ← det_tateMatrix]
  exact (RingHom.map_det (PadicInt.Coe.ringHom (p := 2)) (tateMatrix E σ)).symm

/-- **The integral lattice is preserved by the scalar trace of the Tate representation.** Kind:
PROVED (the trace of `ρ_T(σ)` lies in `ℤ₂`, `trace_tateRhoQ`). -/
theorem tate_stable_t (g : GalQ) (v : Unit → ℚ_[2]) (hv : v ∈ intLattice) :
    tV (fun _ : Unit => tateRhoQ E) g v ∈ intLattice := by
  rw [mem_intLattice] at hv ⊢
  intro i
  obtain ⟨a, ha⟩ := hv i
  refine ⟨LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 g) * a, ?_⟩
  simp only [tV, scalarOp_apply, trace_tateRhoQ, PadicInt.coe_mul, ha]

/-- **The integral lattice is preserved by the determinant of the Tate representation.** Kind:
PROVED (the determinant of `ρ_T(σ)` lies in `ℤ₂`, `det_tateRhoQ`). -/
theorem tate_stable_d (g : GalQ) (v : Unit → ℚ_[2]) (hv : v ∈ intLattice) :
    dV (fun _ : Unit => tateRhoQ E) g v ∈ intLattice := by
  rw [mem_intLattice] at hv ⊢
  intro i
  obtain ⟨a, ha⟩ := hv i
  refine ⟨LinearMap.det (tateRep E 2 g) * a, ?_⟩
  simp only [dV, scalarOp_apply, det_tateRhoQ, PadicInt.coe_mul, ha]

/-- **Every vector of `𝔪Λ` has its coordinate in `𝔪_{ℤ₂}`**: norm `< 1`. Kind: PROVED (induction
on `𝔪 • Λ`, the ultrametric inequality). -/
theorem norm_lt_one_of_mem_maximalIdeal_smul {y : intLattice}
    (hy : y ∈ (IsLocalRing.maximalIdeal ℤ_[2] • ⊤ : Submodule ℤ_[2] intLattice)) :
    ‖(y : Unit → ℚ_[2]) ()‖ < 1 := by
  refine Submodule.smul_induction_on (p := fun y : intLattice => ‖(y : Unit → ℚ_[2]) ()‖ < 1) hy
    (fun r hr n _ => ?_) (fun x y hx hy => ?_)
  · have hr' : ‖r‖ < 1 := PadicInt.mem_nonunits.mp ((IsLocalRing.mem_maximalIdeal r).mp hr)
    obtain ⟨a, ha⟩ := mem_intLattice.mp n.2 ()
    show ‖(r • (n : Unit → ℚ_[2])) ()‖ < 1
    rw [Pi.smul_apply, ← ha, Algebra.smul_def, PadicInt.algebraMap_apply, norm_mul,
      ← PadicInt.norm_def, ← PadicInt.norm_def]
    calc ‖r‖ * ‖a‖ ≤ ‖r‖ * 1 := by gcongr; exact PadicInt.norm_le_one a
      _ < 1 := by rw [mul_one]; exact hr'
  · show ‖(x : Unit → ℚ_[2]) () + (y : Unit → ℚ_[2]) ()‖ < 1
    exact lt_of_le_of_lt (Padic.nonarchimedean _ _) (max_lt hx hy)

/-- **The reduced lattice `Λ/𝔪Λ` is nonzero**: the integral vector `1` is not in `𝔪Λ`. Kind:
PROVED (`norm_lt_one_of_mem_maximalIdeal_smul`). -/
theorem intLattice_quot_nontrivial :
    Nontrivial
      (intLattice ⧸ (IsLocalRing.maximalIdeal ℤ_[2] • ⊤ : Submodule ℤ_[2] intLattice)) := by
  refine ⟨⟨Submodule.Quotient.mk ⟨fun _ => 1, mem_intLattice.mpr fun _ => ⟨1, PadicInt.coe_one⟩⟩,
    0, fun h => ?_⟩⟩
  rw [Submodule.Quotient.mk_eq_zero] at h
  have := norm_lt_one_of_mem_maximalIdeal_smul h
  simp at this

variable (hFrob : FrobeniusExists)

/-- **Non-vacuity of `GaloisConstituentModel` with a genuine Galois representation**, for every
type data and every type character reading the types: for an elliptic curve `E/ℚ`, given
`FrobeniusExists`, the constituent model with ONE constituent (`I = Unit`) whose representation is
the `2`-adic Tate representation of `E` (`tateRhoQ E`), `K = ℚ₂`, `O = ℤ₂`, `𝔪` the maximal ideal of
`ℤ₂`, `Λ` the lattice of integral vectors (preserved since `ρ_T(σ)` has entries in `ℤ₂`:
`tate_stable_t`, `tate_stable_d`), the zero forms, the zero functionals and the zero reading;
`chebotarev`, `kummer`, `finiteIndex` are proved (`zeroForms`). The constituents of the actual
forms `F_U = θ H_U` are weight-two cuspidal newforms and Eisenstein character pairs
(tex 9647–9654, 9762–9771), not `E` or its twists: the Tate representation of `E` is used only to
show that the structure is inhabited by a genuine Galois representation. Kind: PROVED. -/
def tateConstituentModelOf (T : TypeData L ε) (chiType : GalQ →* Multiplicative L)
    (htyp : IsTypeChar T chiType) (ap : ℕ → ℤ) (B : ℕ) :
    GaloisConstituentModel T (fun _ => 0) ap B chiType :=
  GaloisConstituentModel.zeroForms hFrob T ap B chiType htyp (IsLocalRing.maximalIdeal ℤ_[2])
    two_mem_maximalIdeal_padicInt (fun _ : Unit => tateRhoQ E) intLattice (tate_stable_t E)
    (tate_stable_d E)

section Of

variable (T : TypeData L ε) (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType)
  (ap : ℕ → ℤ) (B : ℕ)

/-- **The constituent representation of `tateConstituentModelOf` is the Tate representation of
`E`.** Kind: PROVED (definition). -/
theorem tateConstituentModelOf_ρ :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).ρ () = tateRhoQ E :=
  rfl

/-- **The data of `tateConstituentModelOf`**: one constituent, `K = ℚ₂`, `O = ℤ₂`, `𝔪` the maximal
ideal of `ℤ₂`, `Λ` the lattice of integral vectors, zero forms and zero functionals. Kind: PROVED
(definition). -/
theorem tateConstituentModelOf_data :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).I = Unit ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).K = ℚ_[2] ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).O = ℤ_[2] ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).m = IsLocalRing.maximalIdeal ℤ_[2] ∧
      (tateConstituentModelOf E hFrob T chiType htyp ap B).Λ = intLattice ∧
      (∀ U, (tateConstituentModelOf E hFrob T chiType htyp ap B).F U = 0) ∧
      (∀ U, (tateConstituentModelOf E hFrob T chiType htyp ap B).read U = 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- **The scalar trace operator of `tateConstituentModelOf` is multiplication by the trace of
`ρ_T(σ)` on `T₂E`.** Kind: PROVED (`trace_tateRhoQ`). -/
theorem tateConstituentModelOf_tV (σ : GalQ) (v : Unit → ℚ_[2]) :
    tV (tateConstituentModelOf E hFrob T chiType htyp ap B).ρ σ v () =
      ((LinearMap.trace ℤ_[2] (TateMod E 2) (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) * v () := by
  show ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).trace * v () = _
  rw [trace_tateRhoQ]

/-- **The determinant operator of `tateConstituentModelOf` is multiplication by the determinant
of `ρ_T(σ)` on `T₂E`.** Kind: PROVED (`det_tateRhoQ`). -/
theorem tateConstituentModelOf_dV (σ : GalQ) (v : Unit → ℚ_[2]) :
    dV (tateConstituentModelOf E hFrob T chiType htyp ap B).ρ σ v () =
      ((LinearMap.det (tateRep E 2 σ) : ℤ_[2]) : ℚ_[2]) * v () := by
  show ((tateRhoQ E σ : GL (Fin 2) ℚ_[2]) : Matrix (Fin 2) (Fin 2) ℚ_[2]).det * v () = _
  rw [det_tateRhoQ]

/-- **The inputs of `tateConstituentModelOf` hold.** Kind: PROVED (`zeroForms_inputs`). -/
theorem tateConstituentModelOf_inputs :
    (tateConstituentModelOf E hFrob T chiType htyp ap B).Inputs :=
  GaloisConstituentModel.zeroForms_inputs hFrob _ ap B _ _ _ _ _ _ _ _

/-- **The reduced module of the Tate constituent model is nonzero** (it is `ℤ₂/2ℤ₂`, on which
`t(σ)` is the reduction of the trace of `ρ_T(σ)`). Kind: PROVED
(`intLattice_quot_nontrivial`). -/
theorem tateConstituentModelOf_nontrivial :
    Nontrivial (tateConstituentModelOf E hFrob T chiType htyp ap B).Mred :=
  intLattice_quot_nontrivial

end Of

variable (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model over the genuine type data** `typeData m` (`4 ∣ m`), with the
genuine type character `typChar m` (`isTypeChar_typeData`): one constituent whose representation
is the `2`-adic Tate representation of `E`. The constituents of the actual forms `F_U = θ H_U`
are weight-two cuspidal newforms and Eisenstein character pairs (tex 9647–9654, 9762–9771), not
`E` or its twists: the Tate representation of `E` is used only to show that the structure is
inhabited by a genuine Galois representation. Kind: PROVED. -/
def tateConstituentModel :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  tateConstituentModelOf E hFrob (typeData m hm h4) (typChar m) (isTypeChar_typeData m hm h4) ap B

/-- **The constituent representation of `tateConstituentModel` is the Tate representation of
`E`.** Kind: PROVED (definition). -/
theorem tateConstituentModel_ρ :
    (tateConstituentModel E hFrob m hm h4 ap B).ρ () = tateRhoQ E :=
  rfl

/-- **The inputs of `tateConstituentModel` hold.** Kind: PROVED (`zeroForms_inputs`). -/
theorem tateConstituentModel_inputs : (tateConstituentModel E hFrob m hm h4 ap B).Inputs :=
  tateConstituentModelOf_inputs E hFrob _ _ _ ap B

/-- **The genuine Galois trace model of the Tate constituent model** over `typeData m`: the
reduced module `ℤ₂/2ℤ₂` (nonzero, `tateGaloisTraceModel_nontrivial`) with the reduced scalar
traces and determinants of `ρ_T`. Kind: PROVED (`toGaloisTraceModel`). -/
def tateGaloisTraceModel : GaloisTraceModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  (tateConstituentModel E hFrob m hm h4 ap B).toGaloisTraceModel
    (tateConstituentModel_inputs E hFrob m hm h4 ap B)

/-- **The module of `tateGaloisTraceModel` is nonzero.** Kind: PROVED
(`intLattice_quot_nontrivial`). -/
theorem tateGaloisTraceModel_nontrivial :
    Nontrivial (tateGaloisTraceModel E hFrob m hm h4 ap B).M :=
  intLattice_quot_nontrivial

/-- **The Tate constituent model over stage type data** (types `(sqClassOf m₁ p, legBit p ℓ₀)` at
the modulus `m₁ ℓ₀`, `ℓ₀` an odd prime), with the stage type character `stageChar m₁ ℓ₀`
(`isTypeChar_stage`). As for `tateConstituentModel`, the Tate representation of `E` only shows
that the structure is inhabited by a genuine Galois representation. Kind: PROVED. -/
def tateConstituentModelStage {m₁ ℓ₀ : ℕ} [NeZero m₁] {ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2}
    (T : TypeData (SqClass m₁ × ZMod 2) ε₁) (hTm : T.m = m₁ * ℓ₀)
    (hTtyp : ∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀)) (hℓ₀ : ℓ₀.Prime) (hℓ₀2 : ℓ₀ ≠ 2) :
    GaloisConstituentModel T (fun _ => 0) ap B (stageChar m₁ ℓ₀) :=
  tateConstituentModelOf E hFrob T (stageChar m₁ ℓ₀) (isTypeChar_stage T hTm hTtyp hℓ₀ hℓ₀2) ap B

end Tate

/-- **The readings of the Tate constituent models compose**: the coefficient rules for the zero
symbol over `typeData m`, from `coefficientRules_of_galoisConstituents` applied to the models
`tateConstituentModel E` at every budget (with `a_p = 0`). Kind: PROVED. -/
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

/-- **The Tate constituent model of `E_ℓ`** (`ℓ > 0`; `E_ℓ` is elliptic, `ecurve_isElliptic`) over
the genuine type data `typeData m`: one constituent whose representation is the `2`-adic Tate
representation of `E_ℓ`. As for `tateConstituentModel`, the constituents of the actual forms
`F_U` are weight-two cuspidal newforms and Eisenstein character pairs, not `E_ℓ` or its twists;
this only shows that the structure is inhabited by a genuine Galois representation. Kind:
PROVED. -/
def tateConstituentModelEcurve :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  @tateConstituentModel (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hFrob m _ hm
    h4 ap B

/-- The constituent representation of `tateConstituentModelEcurve` is the Tate representation of
`E_ℓ`. Kind: PROVED (definition). -/
theorem tateConstituentModelEcurve_ρ :
    (tateConstituentModelEcurve hFrob hℓ m hm h4 ap B).ρ () =
      @tateRhoQ (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) :=
  rfl

/-- The inputs of `tateConstituentModelEcurve` hold. Kind: PROVED. -/
theorem tateConstituentModelEcurve_inputs :
    (tateConstituentModelEcurve hFrob hℓ m hm h4 ap B).Inputs :=
  @tateConstituentModel_inputs (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hFrob
    m _ hm h4 ap B

/-- The genuine Galois trace model of `tateConstituentModelEcurve` (its module is nonzero,
`tateGaloisTraceModel_nontrivial`). Kind: PROVED (`toGaloisTraceModel`). -/
def tateGaloisTraceModelEcurve :
    GaloisTraceModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  @tateGaloisTraceModel (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (ecurve_isElliptic hℓ) hFrob m _ hm
    h4 ap B

end Ecurve

/-! ### Unconditional forms (`FrobeniusExists` is proved, `frobeniusExists`) -/

section Unconditional

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m)
  (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model over `typeData m`, with no hypothesis**: `tateConstituentModel`
with `FrobeniusExists` discharged by `frobeniusExists`. The constituents of the actual forms
`F_U = θ H_U` are weight-two cuspidal newforms and Eisenstein character pairs, not `E` or its
twists; the Tate representation of `E` only shows that the structure is inhabited by a genuine
Galois representation. Kind: PROVED. -/
def tateConstituentModel' :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  tateConstituentModel E frobeniusExists m hm h4 ap B

/-- The constituent representation of `tateConstituentModel'` is the Tate representation of `E`.
Kind: PROVED (definition). -/
theorem tateConstituentModel'_ρ : (tateConstituentModel' E m hm h4 ap B).ρ () = tateRhoQ E :=
  rfl

/-- The inputs of `tateConstituentModel'` hold. Kind: PROVED. -/
theorem tateConstituentModel'_inputs : (tateConstituentModel' E m hm h4 ap B).Inputs :=
  tateConstituentModel_inputs E frobeniusExists m hm h4 ap B

end Unconditional

/-- **The coefficient rules for the zero symbol over `typeData m` from the Tate constituent models,
with no hypothesis** (`coefficientRules_tate` with `frobeniusExists`). Kind: PROVED. -/
theorem coefficientRules_tate' (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) [NeZero m]
    (hm : 0 < m) (h4 : 4 ∣ m) :
    CoefficientRules (signChar m h4) (symb (typeData m hm h4) (fun _ => 0)) :=
  coefficientRules_tate E frobeniusExists m hm h4

section UnconditionalEcurve

variable {ℓ : ℕ} (hℓ : 0 < ℓ) (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ)

/-- **The Tate constituent model of `E_ℓ` over `typeData m`, with no hypothesis**
(`tateConstituentModelEcurve` with `frobeniusExists`); the Tate representation of `E_ℓ` only shows
that the structure is inhabited by a genuine Galois representation. Kind: PROVED. -/
def tateConstituentModelEcurve' :
    GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  tateConstituentModelEcurve frobeniusExists hℓ m hm h4 ap B

/-- The inputs of `tateConstituentModelEcurve'` hold. Kind: PROVED. -/
theorem tateConstituentModelEcurve'_inputs :
    (tateConstituentModelEcurve' hℓ m hm h4 ap B).Inputs :=
  tateConstituentModelEcurve_inputs frobeniusExists hℓ m hm h4 ap B

end UnconditionalEcurve

end ZInQ.Manuscript.RC.AddressGenuine
