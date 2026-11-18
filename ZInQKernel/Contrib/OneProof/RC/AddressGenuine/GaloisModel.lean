import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Frobenius
import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.RC12Bridge

/-!
# Theorem 5.3, Lane RC24: the genuine Galois instance of the trace model

Manuscript `diophantine_zq.tex`, App F, proof of Proposition `ex:app-coefficient-rules`
(tex 9447–9976): the integral trace module and its operators (tex 9641–9669, 9705–9771), the
reading of an added vertex (tex 9671–9704), the elementary quadratic quotient (tex 9745–9750),
(O.12) at coefficient one and the joint quotient of the representatives (tex 9905–9945).

Lane RC0 (round 3) stated the trace model abstractly (`TraceModelRel`: an abstract group `G`,
abstract Frobenius elements, characters and subgroups `N_U`). This file is its **genuine Galois
instance**:

* the group is `G_ℚ = GalQ` itself;
* the Frobenius elements are genuine: `frob q` is an arithmetic Frobenius element at every good
  prime `q` (`IsFrobAt`, field `frob_spec`);
* the characters are genuine: `χ_s = bitChar s` is the character of `ℚ(√s*)`,
  `s* = (−1)^{(s−1)/2} s`, and the type character `chiType` is a parameter, required to read the
  type of a good prime at its Frobenius elements (`IsTypeChar`); for the residue-class type data
  of lane RC24 it is the genuine squareclass character `typChar m` (`isTypeChar_typeData`), and
  for the stage type data the pair `(typChar m₁, χ_{ℓ₀})` (`stageChar`, `isTypeChar_stage`);
* `N_U` is **defined** (`galN`): the subgroup of `n ∈ G_ℚ` with trivial type, trivial characters
  `χ_s`, `s ∈ U`, and `t(gn)F_{U'} = t(g)F_{U'}` for every `g` and every `U' ⊆ U` — the subgroup
  fixing the compositum of the type fields, the fields `ℚ(√s*)`, `s ∈ U`, and the fields cut out
  by the reduced trace action on the forms `F_{U'}` (tex 9663–9669, 9745–9750, 9919–9921).

The remaining fields of `GaloisTraceModel` are those of `TraceModelRel`, verbatim with
`G := G_ℚ`, `chiBit := bitChar`, `N := galN chiType t F`: the trace identities of lane RC12 on
the reduced module (ELLIOT, tex 9705–9745), Kummer detection of the elementary quotient (GLUE,
tex 9745–9750), Chebotarev in the finite quotient `G_ℚ/N_U` (PRINT), the coefficient-one reading
and (O.12) (ELLIOT, tex 9671–9704, 9905–9918); and one added GLUE field, `finiteIndex`: `N_U`
has finite index for good `U` (continuity of the trace action on the finite module, tex
9663–9669), so that the hypothesis of Chebotarev's theorem is part of the type.

The fields `level`, `N_anti`, `N_chi`, `typ_frob`, `bit_frob` and `chi_surj` of `TraceModelRel`
are **not** fields here: they are PROVED. `level`, `N_anti`, `N_chi` (and the normality of `N_U`)
follow from the definition of `galN`; `bit_frob` from `bitChar_of_isFrobAt` (good primes are odd
primes, `2 ∣ T.m`); `typ_frob` from the hypothesis `IsTypeChar T chiType`; and `chi_surj`, for a
set `U` of good primes, from the genuine Frobenius elements and batch 3's `realizeNat` (CRT and
Dirichlet: a good prime with prescribed type and bits, then its Frobenius).

**Finding on `TraceModelRel.chi_surj`.** RC0's field `chi_surj` is stated for *every* finite set
`U`. With the genuine characters it is false as soon as `U` contains an `s` that is not a good
prime: for `s = 1`, `1* = 1` and `√1 = ±1` is fixed by `G_ℚ`, so `χ₁ = bitChar 1` is trivial
(`bitChar_one`), and no `g` has `χ₁(g) = −1`. Hence `chi_surj` fails at `U = {1}`, `b ≡ 1`, for
every type character (`not_chi_surj_all`), and no `TraceModelRel` built on `G_ℚ` with
`chiBit := bitChar` exists. RC0's proofs use `chi_surj` only at sets of good primes (the
set `U` of `O12Reading`), where it is PROVED here (`GaloisTraceModel.chi_surj`); RC0's readings
are therefore re-proved for `GaloisTraceModel` (`fixedU_of_model`, `primary_of_model`,
`o12_of_model`, `rulesUpTo_of_model`, `coefficientRules_of_galois`, by RC0's proofs).

**Non-vacuity** (PROVED): `GaloisTraceModel.zero` is a model of the zero reading over every type
data and every type character reading the types, given `FrobeniusExists`; `M` is the zero module,
`N_U` is the common kernel of the characters (of finite index: the type alphabet is finite,
`finite_of_typeData`), and `chebotarev` is proved by Dirichlet's theorem (batch 3's
`realizeNat`). In particular the model is inhabited over the genuine type data `typeData m` and
over the stage type data (`galoisTraceModel_typeData_nonempty`,
`galoisTraceModel_stage_nonempty`). `FrobeniusExists` is proved in the Frobenius module
(`frobeniusExists`), which gives the unconditional forms `chi_surj_good`,
`galoisTraceModel_nonempty`, `galoisTraceModel_typeData_nonempty'`,
`galoisTraceModel_stage_nonempty'` and `coefficientRules_zero'`.

DEPARTURE (Chebotarev and openness). Čebotarev's density theorem concerns open normal subgroups
of `G_ℚ` (finite Galois extensions of `ℚ`). The genuine `N_U` is open: the characters are
continuous and `g ↦ t(g)F_{U'}` is continuous on the finite module (tex 9663–9669). The field
`finiteIndex` records only the finiteness of `G_ℚ/N_U`; openness is not stated, since the
continuity of the type character is not part of the Frobenius interface. The finite form of
Čebotarev's theorem is proved in this repository (`ZInQ.Contrib.chebotarevExists`, through the
density form `ZInQ.Contrib.ChebFD.C10.frobDense`); lane RC24's `Chebotarev.lean` derives the field
`chebotarev` from it (`chebotarev_of_density`), given the openness of `N_U` and the
unramifiedness of `N_U` at the good primes outside `U` (both GLUE), and `GaloisDensityModel` there
is the model with these two hypotheses in place of `chebotarev` and `finiteIndex`.

References: [Neukirch] J. Neukirch, *Algebraic number theory*, Grundlehren 322 (Springer 1999),
Ch. VII, Theorem (13.4) (Čebotarev's density theorem; statement page `UNVERIFIED`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-! ## The characters `χ_s` of `ℚ(√s*)` -/

/-- **The bit character** `χ_s`: the character of `ℚ(√s*)`, `s* = (−1)^{(s−1)/2} s`, written
multiplicatively (tex 9745–9750, 9932–9942). Kind: definition. -/
def bitChar (s : ℕ) : GalQ →* Multiplicative (ZMod 2) := sqrtChar (sstar s)

/-- The value of `χ_s` (tex 9745–9750). Kind: PROVED (definition). -/
theorem bitChar_apply (s : ℕ) (σ : GalQ) : bitChar s σ = sqrtChar (sstar s) σ := rfl

/-- **`χ_s` reads `(q/s)` at a Frobenius element at `q`**, for distinct good primes `q, s`
(tex 9938–9942). Kind: PROVED (from `bitChar_of_isFrobAt`; good primes are odd, `2 ∣ T.m`). -/
theorem bitChar_of_good (T : TypeData L ε) {q s : ℕ} {σ : GalQ} (hq : T.Good q) (hs : T.Good s)
    (hqs : q ≠ s) (hσ : IsFrobAt σ q) : bitChar s σ = Multiplicative.ofAdd (legBit q s) :=
  bitChar_of_isFrobAt hq.1 hs.1 hq.ne_two hs.ne_two hqs hσ

/-- `1* = 1` (no tex line: part of the finding on RC0's `chi_surj`). Kind: PROVED. -/
theorem sstar_one : sstar 1 = 1 := by
  simp [sstar]

/-- **`χ₁` is trivial**: `√1 = ±1` is fixed by every `σ ∈ G_ℚ` (no tex line: part of the finding
on RC0's `chi_surj`). Kind: PROVED (`sqrtChar_eq_one_iff`, `sqrtQbar_sq`). -/
theorem bitChar_one_apply (σ : GalQ) : bitChar 1 σ = 1 := by
  rw [bitChar_apply, sstar_one, sqrtChar_eq_one_iff 1 one_ne_zero]
  have h : sqrtQbar 1 ^ 2 = (1 : Qbar) ^ 2 := by rw [sqrtQbar_sq, Int.cast_one, one_pow]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
  · rw [h1, map_one]
  · rw [h1, map_neg, map_one]

/-- **`χ₁ = 1`** (no tex line: part of the finding on RC0's `chi_surj`). Kind: PROVED. -/
theorem bitChar_one : bitChar 1 = 1 := MonoidHom.ext bitChar_one_apply

/-- **RC0's `chi_surj` fails for the genuine characters** (the finding recorded in the module
docstring): for every type character, the independence statement "every type and every bits at
every finite `U` are taken by some `g`" is false (`U = {1}`, `b ≡ 1`, since `χ₁` is trivial).
Kind: PROVED. -/
theorem not_chi_surj_all (chiType : GalQ →* Multiplicative L) :
    ¬ ∀ (U : Finset ℕ) (ℓ : L) (b : ℕ → ZMod 2), ∃ g : GalQ,
      chiType g = Multiplicative.ofAdd ℓ ∧ ∀ s ∈ U, bitChar s g = Multiplicative.ofAdd (b s) := by
  intro h
  obtain ⟨g, -, hg⟩ := h {1} 0 (fun _ => 1)
  have h1 := hg 1 (mem_singleton_self 1)
  rw [bitChar_one_apply, ← ofAdd_zero] at h1
  exact absurd (Multiplicative.ofAdd.injective h1) (by decide)

/-- A homomorphism to a commutative group is a class function (the characters are read on
Frobenius classes, tex 9932–9938). Kind: PROVED. -/
theorem map_conj_of_comm {G H : Type*} [Group G] [CommGroup H] (f : G →* H) (g h : G) :
    f (h * g * h⁻¹) = f g := by
  rw [map_mul, map_mul, map_inv, mul_comm (f h), mul_inv_cancel_right]

/-! ## The subgroup `N_U` -/

section GalN

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- **The subgroup `N_U` of `G_ℚ`** fixing the compositum of the type fields, the fields `ℚ(√s*)`,
`s ∈ U`, and the fields cut out by the reduced trace action on the forms `F_{U'}`, `U' ⊆ U`
(tex 9663–9669, 9745–9750, 9919–9921): the `n` with `χ_type(n) = 1`, `χ_s(n) = 1` for `s ∈ U`,
and `t(gn)F_{U'} = t(g)F_{U'}` for every `g ∈ G_ℚ` and every `U' ⊆ U`. Kind: definition. -/
def galN (chiType : GalQ →* Multiplicative L) (t : GalQ → M →ₗ[ZMod 2] M) (F : Finset ℕ → M)
    (U : Finset ℕ) : Subgroup GalQ where
  carrier := {n | chiType n = 1 ∧ (∀ s ∈ U, bitChar s n = 1) ∧
    ∀ g : GalQ, ∀ U' ⊆ U, t (g * n) (F U') = t g (F U')}
  one_mem' := ⟨map_one _, fun _ _ => map_one _, fun g _ _ => by rw [mul_one]⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2, ha3⟩ := ha
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine ⟨by rw [map_mul, ha1, hb1, mul_one], fun s hs => by
      rw [map_mul, ha2 s hs, hb2 s hs, mul_one], fun g U' hU' => ?_⟩
    rw [← mul_assoc, hb3 (g * a) U' hU', ha3 g U' hU']
  inv_mem' := by
    intro a ha
    obtain ⟨ha1, ha2, ha3⟩ := ha
    refine ⟨by rw [map_inv, ha1, inv_one], fun s hs => by rw [map_inv, ha2 s hs, inv_one],
      fun g U' hU' => ?_⟩
    rw [← ha3 (g * a⁻¹) U' hU', inv_mul_cancel_right]

variable {chiType : GalQ →* Multiplicative L} {t : GalQ → M →ₗ[ZMod 2] M} {F : Finset ℕ → M}

/-- Membership in `N_U` (tex 9663–9669, 9745–9750, 9919–9921). Kind: PROVED (definition). -/
theorem mem_galN {U : Finset ℕ} {n : GalQ} :
    n ∈ galN chiType t F U ↔ chiType n = 1 ∧ (∀ s ∈ U, bitChar s n = 1) ∧
      ∀ g : GalQ, ∀ U' ⊆ U, t (g * n) (F U') = t g (F U') := Iff.rfl

/-- **`N_U ≤ N_{U'}` for `U' ⊆ U`**: the `U'`-extension lies in the `U`-extension (tex
9919–9921: one joint quotient for the `U` and `V` forms). Kind: PROVED (definition of `galN`). -/
theorem galN_anti {U U' : Finset ℕ} (hU' : U' ⊆ U) : galN chiType t F U ≤ galN chiType t F U' := by
  intro n hn
  obtain ⟨h1, h2, h3⟩ := mem_galN.mp hn
  exact mem_galN.mpr ⟨h1, fun s hs => h2 s (hU' hs), fun g U'' hU'' => h3 g U'' (hU''.trans hU')⟩

/-- **`N_U` is normal** when `t` is a class function (`N_U` fixes a Galois extension, tex
9745–9750, 9762–9771). Kind: PROVED. -/
theorem galN_normal {U : Finset ℕ} (ht : ∀ g h : GalQ, t (h * g * h⁻¹) = t g) :
    (galN chiType t F U).Normal := by
  refine ⟨fun n hn h => ?_⟩
  obtain ⟨h1, h2, h3⟩ := mem_galN.mp hn
  refine mem_galN.mpr ⟨by rw [map_conj_of_comm, h1], fun s hs => by rw [map_conj_of_comm, h2 s hs],
    fun g U' hU' => ?_⟩
  have e1 : g * (h * n * h⁻¹) = h * (h⁻¹ * g * h * n) * h⁻¹ := by group
  have e2 : g = h * (h⁻¹ * g * h) * h⁻¹ := by group
  calc t (g * (h * n * h⁻¹)) (F U') = t (h⁻¹ * g * h * n) (F U') := by rw [e1, ht]
    _ = t (h⁻¹ * g * h) (F U') := h3 _ U' hU'
    _ = t g (F U') := by rw [← ht (h⁻¹ * g * h) h, ← e2]

/-- On a zero module, `N_U` is the common kernel of the type character and the `χ_s`, `s ∈ U`
(tex 9745–9750). Kind: PROVED. -/
theorem mem_galN_of_subsingleton [Subsingleton M] {U : Finset ℕ} {n : GalQ} :
    n ∈ galN chiType t F U ↔ chiType n = 1 ∧ ∀ s ∈ U, bitChar s n = 1 :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun _ _ _ => Subsingleton.elim _ _⟩⟩

end GalN

/-! ## Type characters and Frobenius elements -/

/-- **`chiType` reads the type at Frobenius elements**: for a good prime `q` and every Frobenius
element `σ` at `q`, `χ_type(σ)` is the type of `q` (tex 2017–2020, 9936–9940). This is the
hypothesis `htyp` of the readings below. Kind: definition. -/
def IsTypeChar (T : TypeData L ε) (chiType : GalQ →* Multiplicative L) : Prop :=
  ∀ q σ, T.Good q → IsFrobAt σ q → chiType σ = Multiplicative.ofAdd (T.typ q)

/-- **Chosen Frobenius elements** `Fr_q` (tex 9688–9695; `1` at non-primes), given their
existence. Kind: definition. -/
def chooseFrob (hFrob : FrobeniusExists) (q : ℕ) : GalQ :=
  if h : q.Prime then (hFrob q h).choose else 1

/-- The chosen `Fr_q` is a Frobenius element at every prime `q` (tex 9688–9695). Kind: PROVED. -/
theorem chooseFrob_spec (hFrob : FrobeniusExists) {q : ℕ} (hq : q.Prime) :
    IsFrobAt (chooseFrob hFrob q) q := by
  rw [chooseFrob, dif_pos' hq]
  exact (hFrob q hq).choose_spec

/-- **Frobenius elements of good primes take every type and every bits at a set of good primes**
(tex 2151–2174, 9938–9942): for `U` a finite set of good primes, every type `ℓ` and bits `b`,
there is a good prime `q ∉ U ∪ avoid` whose Frobenius element has type `ℓ` and `χ_s`-values
`b s`, `s ∈ U`. Kind: PROVED (batch 3's `realizeNat`: CRT and Dirichlet; then `IsTypeChar` and
`bitChar_of_good`). -/
theorem exists_good_frob (T : TypeData L ε) {chiType : GalQ →* Multiplicative L}
    (htyp : IsTypeChar T chiType) {frob : ℕ → GalQ} (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (U avoid : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (ℓ : L) (b : ℕ → ZMod 2) :
    ∃ q, T.Good q ∧ q ∉ U ∧ q ∉ avoid ∧ chiType (frob q) = Multiplicative.ofAdd ℓ ∧
      ∀ s ∈ U, bitChar s (frob q) = Multiplicative.ofAdd (b s) := by
  obtain ⟨x, -, hx, hold, -⟩ := realizeNat T U avoid hU (fun _ => ℓ) (fun _ s => b s)
    (fun _ _ => 0) 1
  obtain ⟨hq, hqU, hqa, htq⟩ := hx 0 (by norm_num)
  refine ⟨x 0, hq, hqU, hqa, by rw [htyp _ _ hq (hfrob _ hq), htq], fun s hs => ?_⟩
  rw [bitChar_of_good T hq (hU s hs) (fun h => hqU (h ▸ hs)) (hfrob _ hq),
    hold 0 (by norm_num) s hs]

/-- **Independence of the genuine characters at a set of good primes** (the statement of RC0's
`chi_surj`, for `U` a set of good primes): given `FrobeniusExists` and a type character reading the
types, every type and every bits at `U` are taken by some `g ∈ G_ℚ`. Kind: PROVED (a good prime
with prescribed type and bits, batch 3's `realizeNat`, then its Frobenius). -/
theorem chi_surj_of_frobeniusExists (hFrob : FrobeniusExists) (T : TypeData L ε)
    {chiType : GalQ →* Multiplicative L} (htyp : IsTypeChar T chiType) (U : Finset ℕ)
    (hU : ∀ s ∈ U, T.Good s) (ℓ : L) (b : ℕ → ZMod 2) :
    ∃ g : GalQ, chiType g = Multiplicative.ofAdd ℓ ∧
      ∀ s ∈ U, bitChar s g = Multiplicative.ofAdd (b s) := by
  obtain ⟨q, -, -, -, h1, h2⟩ :=
    exists_good_frob T htyp (fun q hq => chooseFrob_spec hFrob hq.1) U ∅ hU ℓ b
  exact ⟨_, h1, h2⟩

/-! ## The genuine Galois trace model -/

/-- **The trace-module model of lane RC12's readings over `G_ℚ`**, within the budget `B`, for the
type character `chiType` (tex 9641–9771, 9905–9953): RC0's `TraceModelRel` with `G := G_ℚ`, genuine
Frobenius elements (`frob_spec`), `chiBit := bitChar`, and `N := galN chiType t F` defined.
Kinds: `frob_spec` definition (genuine Frobenius elements); `trace_mul`, `det_orbit`, `two_fresh`,
`trace_one`, `t_class` ELLIOT (lane RC12's trace identities on the reduced module, tex 9705–9745,
9762–9771); `kummer` GLUE (Kummer theory for the several radicals, tex 9745–9750); `finiteIndex`
GLUE (continuity on the finite module, tex 9663–9669); `chebotarev` PRINT (J. Neukirch,
*Algebraic number theory*, Grundlehren 322, Springer 1999, Ch. VII, Theorem (13.4), Čebotarev's
density theorem, statement page `UNVERIFIED`; applied to the finite quotient `G_ℚ/N_U`, tex
9666–9668, 9919–9921); `reading` ELLIOT (tex 9671–9704); `o12` ELLIOT (tex 9905–9918). The
fields `level`, `N_anti`, `N_chi`, `chi_surj`, `typ_frob`, `bit_frob` of `TraceModelRel` are
theorems here (see the module docstring). Owner: RC12 (App F), Lane RC24. -/
structure GaloisTraceModel (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ)
    (chiType : GalQ →* Multiplicative L) where
  /-- the reduced integral trace module (characteristic two, tex 9663–9669, 9893–9899) -/
  M : Type
  [instM : AddCommGroup M]
  [instMod : Module (ZMod 2) M]
  /-- the scalar trace operators `t(g)` (tex 9762–9771) -/
  t : GalQ → M →ₗ[ZMod 2] M
  /-- the determinant (diamond) operators `d(g)` (tex 9762–9771) -/
  d : GalQ → M →ₗ[ZMod 2] M
  /-- the reduced forms `F_U = θ H_U` (tex 9672) -/
  F : Finset ℕ → M
  /-- the coefficient-one functional on the `U`-forms (tex 9688–9695) -/
  read : Finset ℕ → M →ₗ[ZMod 2] ZMod 2
  /-- the Frobenius elements in `G_ℚ` -/
  frob : ℕ → GalQ
  /-- definition: `frob q` is a genuine arithmetic Frobenius element at every good prime `q` -/
  frob_spec : ∀ q, T.Good q → IsFrobAt (frob q) q
  /-- ELLIOT (RC12, tex 9729–9737): `t(g)t(h) = t(gh) + d(h)t(gh⁻¹)` -/
  trace_mul : ∀ g h (x : M), t g (t h x) = t (g * h) x + d h (t (g * h⁻¹) x)
  /-- ELLIOT (RC12, tex 9719–9733): `d` acts trivially on the trace orbit of `F_U` -/
  det_orbit : ∀ U u v, d u (t v (F U)) = t v (F U)
  /-- ELLIOT (RC12, tex 9741–9745): two fresh traces vanish -/
  two_fresh : ∀ U g h, t g (t h (F U)) = 0
  /-- ELLIOT (RC12, tex 9739): `t(1) = 2` -/
  trace_one : ∀ x, t 1 x = (2 : ZMod 2) • x
  /-- ELLIOT (tex 9762–9771; `t(g)` is a limit of Hecke operators `T_q`, `Fr_q` in the class of
  `g`, tex 9666–9668): `t` is a class function -/
  t_class : ∀ g h, t (h * g * h⁻¹) = t g
  /-- GLUE (Kummer theory for the several radicals, tex 9745–9750): an element with trivial type
  and trivial `χ_s`, `s ∈ U`, lies in the subgroup generated by the squares and `N_U` -/
  kummer : ∀ U g, chiType g = 1 → (∀ s ∈ U, bitChar s g = 1) →
    g ∈ Subgroup.closure (sqSet GalQ) ⊔ galN chiType t F U
  /-- GLUE (continuity of the characters and of the trace action on the finite module,
  tex 9663–9669): for `U` a set of good primes, `G_ℚ/N_U` is finite -/
  finiteIndex : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → (galN chiType t F U).FiniteIndex
  /-- PRINT (J. Neukirch, *Algebraic number theory*, Grundlehren 322, Springer 1999, Ch. VII,
  Theorem (13.4), Čebotarev's density theorem, statement page `UNVERIFIED`), applied to the
  finite quotient `G_ℚ/N_U`, `U` good (tex 9666–9668, 9919–9921): every class of `G_ℚ/N_U` is
  the Frobenius class of a good prime outside any finite set -/
  chebotarev : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (g : GalQ) (avoid : Finset ℕ),
    ∃ q h, ∃ n ∈ galN chiType t F U, T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹ * n
  /-- ELLIOT (tex 9671–9704): the reading of a fresh vertex `q` adjoining `U` is the
  coefficient-one coefficient of `t(Fr_q) F_U` -/
  reading : ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
    (insert q U).card ≤ B → R (insert q U) = read U (t (frob q) (F U))
  /-- ELLIOT ((O.12) at coefficient one, tex 9905–9918), as in RC0's `TraceModelRel.o12`: for
  `p ∈ U` and every `g`, with `τ` the inertia (flipping only the character of `p`), `φ` a
  Frobenius at `p` (carrying the labels of `p`) and `κ₀ = ±1` the Legendre sign of `vr₀` at `p` -/
  o12 : ∀ (U : Finset ℕ) (p : ℕ), p ∈ U → (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g : GalQ,
    ∃ (τ φ : GalQ) (κ0 : ℤ), (κ0 = 1 ∨ κ0 = -1) ∧
      chiType τ = 1 ∧ (∀ s ∈ U, s ≠ p → bitChar s τ = 1) ∧
      bitChar p τ = Multiplicative.ofAdd 1 ∧
      chiType φ = Multiplicative.ofAdd (T.typ p) ∧
      (∀ s ∈ U, s ≠ p → bitChar s φ = Multiplicative.ofAdd (legBit p s)) ∧
      ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) * read (U.erase p) (t (g * τ * φ) (F (U.erase p))) -
          ((Cp (ap p) κ0 : ℤ) : ZMod 2) * read (U.erase p) (t (g * φ) (F (U.erase p))) =
        read U (t (g * τ) (F U)) - read U (t g (F U))

namespace GaloisTraceModel

variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
  {chiType : GalQ →* Multiplicative L} (X : GaloisTraceModel T R ap B chiType)

attribute [instance] GaloisTraceModel.instM GaloisTraceModel.instMod

/-- The subgroup `N_U` of the model, `galN chiType t F U`. Kind: definition. -/
abbrev N (U : Finset ℕ) : Subgroup GalQ := galN chiType X.t X.F U

include X

/-- **`level`** (RC0's field): `t(·)F_U` factors through `G_ℚ/N_U`. Kind: PROVED (definition of
`galN`, with `U' = U`). -/
theorem level (U : Finset ℕ) (g n : GalQ) (hn : n ∈ X.N U) : X.t (g * n) (X.F U) = X.t g (X.F U) :=
  (mem_galN.mp hn).2.2 g U (subset_refl U)

/-- **`N_anti`** (RC0's field). Kind: PROVED (`galN_anti`). -/
theorem N_anti (U U' : Finset ℕ) (h : U' ⊆ U) : X.N U ≤ X.N U' := galN_anti h

/-- **`N_chi`** (RC0's field): `N_U` fixes the type fields and `ℚ(√s*)`, `s ∈ U`. Kind: PROVED
(definition of `galN`). -/
theorem N_chi (U : Finset ℕ) : ∀ n ∈ X.N U, chiType n = 1 ∧ ∀ s ∈ U, bitChar s n = 1 :=
  fun _ hn => ⟨(mem_galN.mp hn).1, (mem_galN.mp hn).2.1⟩

/-- `N_U` is normal. Kind: PROVED (`galN_normal`, `t_class`). -/
theorem N_normal (U : Finset ℕ) : (X.N U).Normal := galN_normal X.t_class

/-- **`typ_frob`** (RC0's field): the type of `q` is `χ_type(Fr_q)`. Kind: PROVED (from
`IsTypeChar` and `frob_spec`). -/
theorem typ_frob (htyp : IsTypeChar T chiType) (q : ℕ) (hq : T.Good q) :
    chiType (X.frob q) = Multiplicative.ofAdd (T.typ q) :=
  htyp q _ hq (X.frob_spec q hq)

/-- **`bit_frob`** (RC0's field): `χ_s(Fr_q) = (s*/q) = (q/s)` (tex 9938–9942). Kind: PROVED
(`bitChar_of_isFrobAt`). -/
theorem bit_frob (q s : ℕ) (hq : T.Good q) (hs : T.Good s) (hqs : q ≠ s) :
    bitChar s (X.frob q) = Multiplicative.ofAdd (legBit q s) :=
  bitChar_of_good T hq hs hqs (X.frob_spec q hq)

/-- **`chi_surj` at sets of good primes** (RC0's field, restricted to good `U`; for other `U` it
is false, `not_chi_surj_all`). Kind: PROVED (`exists_good_frob`: batch 3's `realizeNat`, then the
model's Frobenius elements). -/
theorem chi_surj (htyp : IsTypeChar T chiType) (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (ℓ : L)
    (b : ℕ → ZMod 2) :
    ∃ g : GalQ, chiType g = Multiplicative.ofAdd ℓ ∧
      ∀ s ∈ U, bitChar s g = Multiplicative.ofAdd (b s) := by
  obtain ⟨q, -, -, -, h1, h2⟩ := exists_good_frob T htyp X.frob_spec U ∅ hU ℓ b
  exact ⟨_, h1, h2⟩

/-- Invariance of `g ↦ t(g)F_U` under the subgroup generated by the squares and `N_U`. Kind:
PROVED (RC0's `TraceModelRel.trace_join`: RC12's `trace_square_invariance` and `level`). -/
theorem trace_join (U : Finset ℕ) (g x : GalQ)
    (hx : x ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N U) : X.t (g * x) (X.F U) = X.t g (X.F U) := by
  rw [← Subgroup.closure_eq (X.N U), ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction generalizing g with
  | mem x hx =>
    rcases hx with ⟨h, rfl⟩ | hn
    · exact trace_square_invariance X.t X.d (X.F U) X.trace_mul (X.det_orbit U) (X.two_fresh U)
        g h
    · exact X.level U g x hn
  | one => simp
  | mul x y _ _ ihx ihy => rw [← mul_assoc, ihy, ihx]
  | inv x _ ihx => rw [← ihx (g * x⁻¹), inv_mul_cancel_right]

/-- **The fixed-`U` factorization from RC12's square invariance** (tex 9745–9750). Kind: PROVED
(RC0's `TraceModelRel.fixedU_of_model`). -/
theorem fixedU_of_model (htyp : IsTypeChar T chiType) : FixedUFactorization T R B := by
  intro W p p' hcard hW hp hp' hpW hp'W ht hb
  have hcard' : (insert p' W).card ≤ B := by
    rwa [card_insert_of_notMem hp'W, ← card_insert_of_notMem hpW]
  rw [X.reading W p hW hp hpW hcard, X.reading W p' hW hp' hp'W hcard']
  congr 1
  have hx : (X.frob p)⁻¹ * X.frob p' ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N W := by
    refine X.kummer W _ ?_ fun s hs => ?_
    · rw [map_mul, map_inv, X.typ_frob htyp p hp, X.typ_frob htyp p' hp', ht, inv_mul_cancel]
    · have hps : p ≠ s := fun h => hpW (h ▸ hs)
      have hp's : p' ≠ s := fun h => hp'W (h ▸ hs)
      rw [map_mul, map_inv, X.bit_frob p s hp (hW s hs) hps, X.bit_frob p' s hp' (hW s hs) hp's,
        hb s hs, inv_mul_cancel]
  have := X.trace_join W (X.frob p) _ hx
  rw [mul_inv_cancel_left] at this
  rw [this]

/-- **Primary isolation from RC12's square invariance and `t(1) = 2`** (tex 9739, 9947–9948).
Kind: PROVED (RC0's `TraceModelRel.primary_of_model`). -/
theorem primary_of_model (htyp : IsTypeChar T chiType) : PrimaryReading T R B := by
  intro W q hW hq hqW hcard ht hb
  rw [X.reading W q hW hq hqW hcard]
  have hx : X.frob q ∈ Subgroup.closure (sqSet GalQ) ⊔ X.N W := by
    refine X.kummer W _ ?_ fun s hs => ?_
    · rw [X.typ_frob htyp q hq, ht, ofAdd_zero]
    · rw [X.bit_frob q s hq (hW s hs) (fun h => hqW (h ▸ hs)), hb s hs, ofAdd_zero]
  have := X.trace_join W 1 _ hx
  rw [one_mul] at this
  rw [this, X.trace_one, show (2 : ZMod 2) = 0 from rfl, zero_smul, map_zero]

/-- **The (O.12) reading from the module-level identity and Chebotarev representatives in
`G_ℚ/N_U`** (tex 9905–9945): fresh good primes whose Frobenius elements lie in the classes of
`g, gτ, gφ, gτφ` modulo `N_U` (`g` with the prescribed type and bits, `chi_surj` at the good set
`U`) carry the labels of `O12Reading` (product-label rule); `N_U` moves neither the labels at `U`
(`N_chi`) nor the traces on `F_U`, `F_{U∖p}` (`level`, `N_anti`). Kind: PROVED (RC0's
`TraceModelRel.o12_of_model`). -/
theorem o12_of_model (htyp : IsTypeChar T chiType) : O12Reading T R ap B := by
  intro U p hpU hU hUB ℓ bq
  obtain ⟨g, hgT, hgB⟩ := X.chi_surj htyp U hU ℓ bq
  obtain ⟨τ, φ, κ0, hκ, hτT, hτB, hτp, hφT, hφB, hO⟩ := X.o12 U p hpU hU hUB g
  obtain ⟨q, h1, n1, hn1, hq, hqU, hfq⟩ := X.chebotarev U hU g U
  obtain ⟨qτ, h2, n2, hn2, hqτ, hqτU, hfqτ⟩ := X.chebotarev U hU (g * τ) U
  obtain ⟨r0, h3, n3, hn3, hr0, hr0U, hfr0⟩ := X.chebotarev U hU (g * φ) U
  obtain ⟨r1, h4, n4, hn4, hr1, hr1U, hfr1⟩ := X.chebotarev U hU (g * τ * φ) U
  have ne_of : ∀ {x s : ℕ}, x ∉ U → s ∈ U → x ≠ s := fun hx hs h => hx (h ▸ hs)
  -- types
  have typ_of : ∀ {x : ℕ} {y h n : GalQ}, n ∈ X.N U → T.Good x →
      X.frob x = h * y * h⁻¹ * n → Multiplicative.ofAdd (T.typ x) = chiType y := by
    intro x y h n hn hx hf
    rw [← X.typ_frob htyp x hx, hf, map_mul, (X.N_chi U n hn).1, mul_one, map_conj_of_comm]
  have htq : T.typ q = ℓ := Multiplicative.ofAdd.injective ((typ_of hn1 hq hfq).trans hgT)
  have htqτ : T.typ qτ = ℓ := by
    have := typ_of hn2 hqτ hfqτ
    rw [map_mul, hgT, hτT, mul_one] at this
    exact Multiplicative.ofAdd.injective this
  have htr0 : T.typ r0 = T.typ p + ℓ := by
    have := typ_of hn3 hr0 hfr0
    rw [map_mul, hgT, hφT, ← ofAdd_add, add_comm] at this
    exact Multiplicative.ofAdd.injective this
  have htr1 : T.typ r1 = T.typ p + ℓ := by
    have := typ_of hn4 hr1 hfr1
    rw [map_mul, map_mul, hgT, hτT, mul_one, hφT, ← ofAdd_add, add_comm] at this
    exact Multiplicative.ofAdd.injective this
  -- bits
  have bit_of : ∀ {x : ℕ} {y h n : GalQ}, n ∈ X.N U → T.Good x → x ∉ U →
      X.frob x = h * y * h⁻¹ * n → ∀ s ∈ U, Multiplicative.ofAdd (legBit x s) = bitChar s y := by
    intro x y h n hn hx hxU hf s hs
    rw [← X.bit_frob x s hx (hU s hs) (ne_of hxU hs), hf, map_mul, (X.N_chi U n hn).2 s hs,
      mul_one, map_conj_of_comm]
  -- traces
  have t_of : ∀ {U' : Finset ℕ} {x : ℕ} {y h n : GalQ}, U' ⊆ U → n ∈ X.N U →
      X.frob x = h * y * h⁻¹ * n → X.t (X.frob x) (X.F U') = X.t y (X.F U') := by
    intro U' x y h n hU' hn hf
    rw [hf, X.level U' _ n (X.N_anti U U' hU' hn), X.t_class]
  refine ⟨q, qτ, r0, r1, κ0, hq, hqτ, hr0, hr1, hqU, hqτU, hr0U, hr1U, htq, htqτ,
    fun s hs => ?_, fun s hs hsp => ?_, ?_, htr0, htr1, fun s hs hsp => ⟨?_, ?_⟩, ?_, hκ, ?_⟩
  · have := bit_of hn1 hq hqU hfq s hs
    rw [hgB s hs] at this
    exact Multiplicative.ofAdd.injective this
  · have := bit_of hn2 hqτ hqτU hfqτ s hs
    rw [map_mul, hgB s hs, hτB s hs hsp, mul_one] at this
    exact Multiplicative.ofAdd.injective this
  · have := bit_of hn2 hqτ hqτU hfqτ p hpU
    rw [map_mul, hgB p hpU, hτp, ← ofAdd_add] at this
    exact Multiplicative.ofAdd.injective this
  · have := bit_of hn3 hr0 hr0U hfr0 s hs
    rw [map_mul, hgB s hs, hφB s hs hsp, ← ofAdd_add, add_comm] at this
    exact Multiplicative.ofAdd.injective this
  · have := bit_of hn4 hr1 hr1U hfr1 s hs
    rw [map_mul, map_mul, hgB s hs, hτB s hs hsp, mul_one, hφB s hs hsp, ← ofAdd_add,
      add_comm] at this
    exact Multiplicative.ofAdd.injective this
  · have e1 := bit_of hn4 hr1 hr1U hfr1 p hpU
    have e0 := bit_of hn3 hr0 hr0U hfr0 p hpU
    rw [map_mul, map_mul, hτp] at e1
    rw [map_mul] at e0
    apply Multiplicative.ofAdd.injective
    rw [ofAdd_add, e1, e0]
    rw [mul_assoc, mul_comm (Multiplicative.ofAdd (1 : ZMod 2)), ← mul_assoc]
  · -- the identity, transported to the representatives
    have hUe : ∀ s ∈ U.erase p, T.Good s := fun s hs => hU s (mem_of_mem_erase hs)
    have hcardV : ∀ {x : ℕ}, x ∉ U → (insert x (U.erase p)).card ≤ B := by
      intro x _
      calc (insert x (U.erase p)).card ≤ (U.erase p).card + 1 := card_insert_le _ _
        _ = U.card := card_erase_add_one hpU
        _ ≤ B := by omega
    have hcardU : ∀ {x : ℕ}, x ∉ U → (insert x U).card ≤ B := by
      intro x hx
      rw [card_insert_of_notMem hx]; omega
    have hnV : ∀ {x : ℕ}, x ∉ U → x ∉ U.erase p := fun hx h => hx (mem_of_mem_erase h)
    rw [X.reading _ r1 hUe hr1 (hnV hr1U) (hcardV hr1U), X.reading _ r0 hUe hr0 (hnV hr0U)
      (hcardV hr0U), X.reading U qτ hU hqτ hqτU (hcardU hqτU), X.reading U q hU hq hqU
      (hcardU hqU), t_of (erase_subset p U) hn4 hfr1, t_of (erase_subset p U) hn3 hfr0,
      t_of (subset_refl U) hn2 hfqτ, t_of (subset_refl U) hn1 hfq]
    exact hO

omit X in
/-- **RC2's rules within a budget from the genuine Galois model** (the odd source at one stage).
Kind: PROVED (batch 3's `rulesUpTo_symb`). -/
theorem rulesUpTo_of_model {W : ℕ} (X : GaloisTraceModel T R ap (W + 1) chiType)
    (htyp : IsTypeChar T chiType) (hap : ApEven T ap) : RulesUpTo ε (symb T R) W :=
  rulesUpTo_symb T R ap W (X.fixedU_of_model htyp) (X.o12_of_model htyp) hap
    (X.primary_of_model htyp)

end GaloisTraceModel

/-- **RC2's coefficient rules from the genuine Galois model at every budget** (the even source).
Kind: PROVED (batch 3's `coefficientRules_symb`). -/
theorem coefficientRules_of_galois {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    {chiType : GalQ →* Multiplicative L} (X : ∀ B, GaloisTraceModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) (hap : ApEven T ap) : CoefficientRules ε (symb T R) :=
  coefficientRules_symb T R ap (fun B => (X B).fixedU_of_model htyp)
    (fun B => (X B).o12_of_model htyp) hap (fun B => (X B).primary_of_model htyp)

/-! ## The genuine type characters -/

/-- **The type character of the residue-class type data `typeData m` is `typChar m`** (tex
2017–2020, 9936–9940). Kind: PROVED (`typeData_typ`, `typeData_m`, `typChar_of_isFrobAt`). -/
theorem isTypeChar_typeData (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m) :
    IsTypeChar (typeData m hm h4) (typChar m) := by
  intro q σ hq hσ
  have hqm : Nat.Coprime q m := by
    have := hq.2
    rwa [typeData_m] at this
  rw [typChar_of_isFrobAt m hq.1 hqm hσ, typeData_typ]

/-- **The stage type character** `(typChar m₁, χ_{ℓ₀})`, with values in
`Multiplicative (SqClass m₁ × 𝔽₂)` (the type at an odd stage records the squareclass modulo `m₁`
and the residue bit at the stage prime `ℓ₀`, tex 2017–2025). Kind: definition. -/
def stageChar (m₁ ℓ₀ : ℕ) [NeZero m₁] : GalQ →* Multiplicative (SqClass m₁ × ZMod 2) where
  toFun σ := Multiplicative.ofAdd
    (Multiplicative.toAdd (typChar m₁ σ), Multiplicative.toAdd (bitChar ℓ₀ σ))
  map_one' := by
    simp only [map_one, toAdd_one]
    rfl
  map_mul' σ τ := by
    simp only [map_mul, toAdd_mul]
    rfl

/-- The value of the stage type character (tex 2017–2025). Kind: PROVED (definition). -/
theorem stageChar_apply (m₁ ℓ₀ : ℕ) [NeZero m₁] (σ : GalQ) :
    stageChar m₁ ℓ₀ σ = Multiplicative.ofAdd
      (Multiplicative.toAdd (typChar m₁ σ), Multiplicative.toAdd (bitChar ℓ₀ σ)) := rfl

/-- **The stage type character reads the stage types**: for type data at the modulus
`T.m = m₁ ℓ₀` whose type is `(sqClassOf m₁ p, legBit p ℓ₀)`, with `ℓ₀` an odd prime, `stageChar`
satisfies `IsTypeChar`. Kind: PROVED (`typChar_of_isFrobAt`, `bitChar_of_isFrobAt`). -/
theorem isTypeChar_stage {m₁ ℓ₀ : ℕ} [NeZero m₁] {ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2}
    (T : TypeData (SqClass m₁ × ZMod 2) ε₁) (hTm : T.m = m₁ * ℓ₀)
    (hTtyp : ∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀)) (hℓ₀ : ℓ₀.Prime) (hℓ₀2 : ℓ₀ ≠ 2) :
    IsTypeChar T (stageChar m₁ ℓ₀) := by
  intro q σ hq hσ
  have hqm : Nat.Coprime q (m₁ * ℓ₀) := by
    have := hq.2
    rwa [hTm] at this
  have hq1 : Nat.Coprime q m₁ := Nat.Coprime.coprime_dvd_right (dvd_mul_right m₁ ℓ₀) hqm
  have hqℓ : q ≠ ℓ₀ := by
    intro h
    rw [h] at hqm
    exact hℓ₀.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hqm (dvd_mul_left ℓ₀ m₁))
  rw [stageChar_apply, typChar_of_isFrobAt m₁ hq.1 hq1 hσ, bitChar_apply,
    bitChar_of_isFrobAt hq.1 hℓ₀ hq.ne_two hℓ₀2 hqℓ hσ, toAdd_ofAdd, toAdd_ofAdd, hTtyp]

/-! ## Non-vacuity -/

/-- **The type alphabet of a type data is finite** (two types read from the same reduced class
agree at a prime of that class, Dirichlet). Kind: PROVED (RC2's `finite_realization_nat`). -/
theorem finite_of_typeData (T : TypeData L ε) : Finite L := by
  have : NeZero T.m := ⟨T.m_pos.ne'⟩
  choose c hcu hc using T.classes
  refine Finite.of_injective c fun ℓ ℓ' h => ?_
  obtain ⟨q, -, hq, -, -⟩ := finite_realization_nat T.m T.m_pos T.two_dvd ∅ (by simp) ∅
    (fun _ => c ℓ) (fun _ => hcu ℓ) (fun _ _ => 0) (fun _ _ => 0) 1
  obtain ⟨hp, -, -, hcl⟩ := hq 0 (by norm_num)
  exact (hc ℓ (q 0) hp hcl).symm.trans (hc ℓ' (q 0) hp (hcl.trans h))

/-- **On a zero module `N_U` has finite index**: it contains the kernel of the joint character
`(χ_type, (χ_s)_{s ∈ U})` with values in a finite group. Kind: PROVED. -/
theorem galN_finiteIndex_of_subsingleton (T : TypeData L ε) (chiType : GalQ →* Multiplicative L)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Subsingleton M]
    (t : GalQ → M →ₗ[ZMod 2] M) (F : Finset ℕ → M) (U : Finset ℕ) :
    (galN chiType t F U).FiniteIndex := by
  have := finite_of_typeData T
  let φ : GalQ →* Multiplicative L × (U → Multiplicative (ZMod 2)) :=
    chiType.prod (MonoidHom.pi fun s : U => bitChar s)
  have hle : φ.ker ≤ galN chiType t F U := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    refine mem_galN_of_subsingleton.mpr ⟨congrArg Prod.fst hn, fun s hs => ?_⟩
    exact congrFun (congrArg Prod.snd hn) ⟨s, hs⟩
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_ker φ
  exact Subgroup.finiteIndex_of_le hle

/-- **Non-vacuity of `GaloisTraceModel`** (no tex line): given `FrobeniusExists`, for every type
data, every type character reading the types, every `a_p` and budget, a model of the zero reading.
The module is zero, `frob` is chosen by `FrobeniusExists`, `N_U` is the common kernel of the
characters (finite index: `galN_finiteIndex_of_subsingleton`), `chebotarev` holds by Dirichlet (a
good prime `q ∉ avoid` with the type of `g` and the bits of `g` at `U`, batch 3's `realizeNat`;
then `Fr_q = g n` with `n = g⁻¹ Fr_q ∈ N_U`), and in `o12` the elements `τ, φ` are Frobenius
elements (of a good prime of trivial type with bits `[s = p]` at `U`, and of `p`). Kind:
PROVED. -/
def GaloisTraceModel.zero (hFrob : FrobeniusExists) (T : TypeData L ε) (ap : ℕ → ℤ) (B : ℕ)
    (chiType : GalQ →* Multiplicative L) (htyp : IsTypeChar T chiType) :
    GaloisTraceModel T (fun _ => 0) ap B chiType where
  M := PUnit
  t _ := 0
  d _ := 0
  F _ := PUnit.unit
  read _ := 0
  frob := chooseFrob hFrob
  frob_spec _ hq := chooseFrob_spec hFrob hq.1
  trace_mul _ _ _ := Subsingleton.elim _ _
  det_orbit _ _ _ := Subsingleton.elim _ _
  two_fresh _ _ _ := Subsingleton.elim _ _
  trace_one _ := Subsingleton.elim _ _
  t_class _ _ := rfl
  kummer _ _ h1 h2 := Subgroup.mem_sup_right (mem_galN_of_subsingleton.mpr ⟨h1, h2⟩)
  finiteIndex U _ := galN_finiteIndex_of_subsingleton T chiType _ _ U
  chebotarev U hU g avoid := by
    obtain ⟨q, hq, -, hqa, h1, h2⟩ := exists_good_frob T htyp
      (fun q hq => chooseFrob_spec hFrob hq.1) U avoid hU (Multiplicative.toAdd (chiType g))
      (fun s => Multiplicative.toAdd (bitChar s g))
    refine ⟨q, 1, g⁻¹ * chooseFrob hFrob q, mem_galN_of_subsingleton.mpr ⟨?_, fun s hs => ?_⟩,
      hq, hqa, by group⟩
    · rw [map_mul, map_inv, h1, ofAdd_toAdd, inv_mul_cancel]
    · rw [map_mul, map_inv, h2 s hs, ofAdd_toAdd, inv_mul_cancel]
  reading _ _ _ _ _ _ := rfl
  o12 U p hpU hU _ g := by
    have hp := hU p hpU
    obtain ⟨q, -, -, -, h1, h2⟩ := exists_good_frob T htyp
      (fun q hq => chooseFrob_spec hFrob hq.1) U ∅ hU 0 (fun s => if s = p then 1 else 0)
    refine ⟨chooseFrob hFrob q, chooseFrob hFrob p, 1, Or.inl rfl, by rw [h1, ofAdd_zero],
      fun s hs hsp => ?_, ?_, htyp p _ hp (chooseFrob_spec hFrob hp.1),
      fun s hs hsp => bitChar_of_good T hp (hU s hs) (Ne.symm hsp) (chooseFrob_spec hFrob hp.1),
      ?_⟩
    · rw [h2 s hs, if_neg' hsp, ofAdd_zero]
    · rw [h2 p hpU, if_pos' rfl]
    · simp

/-- **The genuine Galois model is inhabited** for every type data and type character reading the
types, given `FrobeniusExists`. Kind: PROVED (`GaloisTraceModel.zero`). -/
theorem galoisTraceModel_zero_nonempty (hFrob : FrobeniusExists) (T : TypeData L ε)
    (ap : ℕ → ℤ) (B : ℕ) {chiType : GalQ →* Multiplicative L} (htyp : IsTypeChar T chiType) :
    Nonempty (GaloisTraceModel T (fun _ => 0) ap B chiType) :=
  ⟨GaloisTraceModel.zero hFrob T ap B chiType htyp⟩

/-- **The model of the zero reading over the genuine residue-class type data** `typeData m`, with
the genuine type character `typChar m`. Kind: PROVED. -/
def GaloisTraceModel.zeroTypeData (hFrob : FrobeniusExists) (m : ℕ) [NeZero m] (hm : 0 < m)
    (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ) :
    GaloisTraceModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  GaloisTraceModel.zero hFrob _ ap B _ (isTypeChar_typeData m hm h4)

/-- **The genuine Galois model over `typeData m` is inhabited**, given `FrobeniusExists`. Kind:
PROVED. -/
theorem galoisTraceModel_typeData_nonempty (hFrob : FrobeniusExists) (m : ℕ) [NeZero m]
    (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ) :
    Nonempty (GaloisTraceModel (typeData m hm h4) (fun _ => 0) ap B (typChar m)) :=
  ⟨GaloisTraceModel.zeroTypeData hFrob m hm h4 ap B⟩

/-- **The model of the zero reading over stage type data** (types `(sqClassOf m₁ p, legBit p ℓ₀)`
at the modulus `m₁ ℓ₀`, `ℓ₀` an odd prime), with the stage type character. Kind: PROVED. -/
def GaloisTraceModel.zeroStage (hFrob : FrobeniusExists) {m₁ ℓ₀ : ℕ} [NeZero m₁]
    {ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2} (T : TypeData (SqClass m₁ × ZMod 2) ε₁)
    (hTm : T.m = m₁ * ℓ₀) (hTtyp : ∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀))
    (hℓ₀ : ℓ₀.Prime) (hℓ₀2 : ℓ₀ ≠ 2) (ap : ℕ → ℤ) (B : ℕ) :
    GaloisTraceModel T (fun _ => 0) ap B (stageChar m₁ ℓ₀) :=
  GaloisTraceModel.zero hFrob T ap B _ (isTypeChar_stage T hTm hTtyp hℓ₀ hℓ₀2)

/-- **The genuine Galois model over stage type data is inhabited**, given `FrobeniusExists`.
Kind: PROVED. -/
theorem galoisTraceModel_stage_nonempty (hFrob : FrobeniusExists) {m₁ ℓ₀ : ℕ} [NeZero m₁]
    {ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2} (T : TypeData (SqClass m₁ × ZMod 2) ε₁)
    (hTm : T.m = m₁ * ℓ₀) (hTtyp : ∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀))
    (hℓ₀ : ℓ₀.Prime) (hℓ₀2 : ℓ₀ ≠ 2) (ap : ℕ → ℤ) (B : ℕ) :
    Nonempty (GaloisTraceModel T (fun _ => 0) ap B (stageChar m₁ ℓ₀)) :=
  ⟨GaloisTraceModel.zeroStage hFrob T hTm hTtyp hℓ₀ hℓ₀2 ap B⟩

/-- **The readings of the zero model compose**: the coefficient rules for the zero symbol over
every type data, from `coefficientRules_of_galois` applied to `GaloisTraceModel.zero` (with
`a_p = 0`). Kind: PROVED. -/
theorem coefficientRules_zero (hFrob : FrobeniusExists) (T : TypeData L ε)
    {chiType : GalQ →* Multiplicative L} (htyp : IsTypeChar T chiType) :
    CoefficientRules ε (symb T (fun _ => 0)) :=
  coefficientRules_of_galois (fun B => GaloisTraceModel.zero hFrob T (fun _ => 0) B chiType htyp)
    htyp (fun _ _ => ⟨0, (add_zero 0).symm⟩)

/-! ### Unconditional forms (`frobeniusExists`) -/

/-- **Independence of the genuine characters at a set of good primes** (RC0's `chi_surj` for good
`U`, tex 2151–2174, 9938–9942), unconditionally. Kind: PROVED (`chi_surj_of_frobeniusExists`,
`frobeniusExists`). -/
theorem chi_surj_good (T : TypeData L ε) {chiType : GalQ →* Multiplicative L}
    (htyp : IsTypeChar T chiType) (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (ℓ : L)
    (b : ℕ → ZMod 2) :
    ∃ g : GalQ, chiType g = Multiplicative.ofAdd ℓ ∧
      ∀ s ∈ U, bitChar s g = Multiplicative.ofAdd (b s) :=
  chi_surj_of_frobeniusExists frobeniusExists T htyp U hU ℓ b

/-- **The genuine Galois model is inhabited** for every type data and type character reading the
types (no tex line). Kind: PROVED (`galoisTraceModel_zero_nonempty`, `frobeniusExists`). -/
theorem galoisTraceModel_nonempty (T : TypeData L ε) (ap : ℕ → ℤ) (B : ℕ)
    {chiType : GalQ →* Multiplicative L} (htyp : IsTypeChar T chiType) :
    Nonempty (GaloisTraceModel T (fun _ => 0) ap B chiType) :=
  galoisTraceModel_zero_nonempty frobeniusExists T ap B htyp

/-- **The genuine Galois model over `typeData m` is inhabited** (no tex line). Kind: PROVED
(`galoisTraceModel_typeData_nonempty`, `frobeniusExists`). -/
theorem galoisTraceModel_typeData_nonempty' (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m)
    (ap : ℕ → ℤ) (B : ℕ) :
    Nonempty (GaloisTraceModel (typeData m hm h4) (fun _ => 0) ap B (typChar m)) :=
  galoisTraceModel_typeData_nonempty frobeniusExists m hm h4 ap B

/-- **The genuine Galois model over stage type data is inhabited** (no tex line). Kind: PROVED
(`galoisTraceModel_stage_nonempty`, `frobeniusExists`). -/
theorem galoisTraceModel_stage_nonempty' {m₁ ℓ₀ : ℕ} [NeZero m₁]
    {ε₁ : SqClass m₁ × ZMod 2 →+ ZMod 2} (T : TypeData (SqClass m₁ × ZMod 2) ε₁)
    (hTm : T.m = m₁ * ℓ₀) (hTtyp : ∀ p : ℕ, T.typ p = (sqClassOf m₁ p, legBit p ℓ₀))
    (hℓ₀ : ℓ₀.Prime) (hℓ₀2 : ℓ₀ ≠ 2) (ap : ℕ → ℤ) (B : ℕ) :
    Nonempty (GaloisTraceModel T (fun _ => 0) ap B (stageChar m₁ ℓ₀)) :=
  galoisTraceModel_stage_nonempty frobeniusExists T hTm hTtyp hℓ₀ hℓ₀2 ap B

/-- **The readings of the zero model compose**, unconditionally (no tex line). Kind: PROVED
(`coefficientRules_zero`, `frobeniusExists`). -/
theorem coefficientRules_zero' (T : TypeData L ε) {chiType : GalQ →* Multiplicative L}
    (htyp : IsTypeChar T chiType) : CoefficientRules ε (symb T (fun _ => 0)) :=
  coefficientRules_zero frobeniusExists T htyp

end ZInQ.Manuscript.RC.AddressGenuine
