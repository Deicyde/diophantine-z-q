import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Constituents
import ZInQKernel.Contrib.OneProof.RC.Wiring.ConstituentModelRel

/-!
# Theorem 5.3: lane RC0's constituent model on coefficientwise reduced expansions

Manuscript `diophantine_zq.tex`, App F, proof of Proposition `ex:app-coefficient-rules`: the
operator budget (tex 9447–9468), the integral trace module and its coefficientwise reduction
(tex 9638–9668), the reading of an added vertex (tex 9671–9704), the trace identities on the
reduced trace orbit (tex 9705–9750) and (O.12) (tex 9905–9945).

**Why lane RC24's bridges to lane RC0 carry two extra hypotheses.** Lane RC0's
`ConstituentModelRel` reads the forms `F_U` in the abstract quotient `Λ/𝔪Λ`: its fields
`det_orbit`, `two_fresh`, `level_red` assert that `(d(u) − 1)t(v)F_U`, `t(g)t(h)F_U` and
`t(gn)F_U − t(g)F_U` lie in `𝔪Λ`, for every finite set `U`, and its fields `kummer`,
`chebotarev` hold at every (good) `U`. Lane RC24's genuine model `GaloisConstituentModel`
states what the text proves:
* coefficientwise identities: "a reduced expansion means coefficientwise reduction modulo
  `𝔪_coef` … No saturation of the integral Fourier module is assumed" (tex 9639–9646), "the
  conclusion is an identity of coefficientwise reduced expansions" (tex 9716–9717). A vector of
  `Λ` whose reduced expansion vanishes need not lie in `𝔪Λ` (`tateDoubled_not_saturated`).
  Passing to RC0's fields needs `GaloisConstituentModel.Saturated`;
* identities within the operator budget: the text fixes "a finite operator budget `|U| ≤ W`"
  before the stage (tex 9447–9468), builds the module "for a fixed stage and `U`"
  (tex 9649–9654), and in the two-trace test "`R ≥ 2` and the actual-stage budget were fixed
  before the test" (tex 9741–9745). Passing to RC0's fields at every `U` needs
  `GaloisConstituentModel.Unbudgeted`.

**The restatement.** `ConstituentModelRed` is RC0's `ConstituentModelRel` with
* the integral Fourier expansion `expand : Λ → (C → 𝒪)` of the construction (tex 9655–9662),
  and the readings `read` as functionals of the reduced expansion (tex 9686–9695);
* `det_orbit`, `two_fresh`, `level_red` as identities of coefficientwise reduced expansions;
* the fields about one set `U` involving the forms or `N_U` (`det_orbit`, `two_fresh`,
  `level_red`, `kummer`, `chebotarev`) stated for `U` a set of good primes with `|U| + 1 ≤ B`.
The other fields are RC0's, verbatim. It is consumed through `TraceModelBudget`, RC0's
`TraceModelRel` within the same budget, whose readings are proved by RC0's arguments; this gives
RC2's rules (`rulesUpTo_of_constituentsRed`, `coefficientRules_of_constituentsRed`). The module
of the trace model is `Λ` modulo the largest operator-stable submodule of the reduction kernel
(lane RC24's construction, here over an abstract group, with the class-function property of `t`
in place of the normality of `N_U`).

**Bridges without `Unbudgeted` or `Saturated`** (PROVED): `ConstituentModelRed.ofGalois` (with
`ofGalois_inputs`), `TraceModelBudget.ofGaloisTrace`, `TraceModelBudget.ofGaloisConstituent`, the
conjunct forms `oddModelsRed_of_galois`, `evenModelsRed_of_galois`, and the genuine instances
`tateConstituentModelRed`, `tateTraceModelBudget` (nonzero module:
`tateConstituentModelRed_nontrivial`). The zero model is `ConstituentModelRed.zero`.
`exists_galois_not_saturated`: a genuine constituent model that is not saturated, to which the
reduced bridge applies.

**Relation to lane RC0's interfaces** (PROVED):
* `TraceModelBudget.ofTraceModelRel`: every `TraceModelRel` is a `TraceModelBudget`;
* `ConstituentModelRed.ofConstituentModelRel`: a `ConstituentModelRel` with an integral expansion
  through whose reduction its readings factor (the data of tex 9655–9662, 9686–9695) is a
  `ConstituentModelRed`, with its inputs; only `𝔪Λ ≤ ker` of the reduction is used;
* `ConstituentModelRed.toConstituentModelRel`: conversely, given `Saturated` and `Unbudgeted`
  (neither is supplied by the text), a `ConstituentModelRed` is a `ConstituentModelRel`, with its
  inputs.

Kinds: `PROVED` (a Lean proof), `GLUE`, `ELLIOT`, `PRINT`, `definition`, as in lane RC0.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.RelBridge

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd
open ZInQ.Manuscript.RC.AddressGenuine ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-! ## The trace model within the operator budget -/

/-- **Lane RC0's `TraceModelRel` within the operator budget** (tex 9447–9468, 9649–9654,
9741–9745, 10533–10548): the fields `det_orbit`, `two_fresh`, `level`, `kummer`, `chebotarev`
are stated for `U` a set of good primes with `|U| + 1 ≤ B`, the quantifier of the text; all other
fields are those of `TraceModelRel`, verbatim (kinds as there). -/
structure TraceModelBudget (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ) where
  /-- the joint Galois group -/
  G : Type
  [instG : Group G]
  /-- the reduced integral trace module (characteristic two) -/
  M : Type
  [instM : AddCommGroup M]
  [instMod : Module (ZMod 2) M]
  /-- trace operators `t(g)` -/
  t : G → M →ₗ[ZMod 2] M
  /-- determinant (diamond) operators `d(g)` -/
  d : G → M →ₗ[ZMod 2] M
  /-- the reduced forms `F_U` -/
  F : Finset ℕ → M
  /-- the coefficient-one functional on the `U`-forms -/
  read : Finset ℕ → M →ₗ[ZMod 2] ZMod 2
  /-- Frobenius elements -/
  frob : ℕ → G
  /-- the subgroup fixing the `U`-extension -/
  N : Finset ℕ → Subgroup G
  /-- the type characters -/
  chiType : G →* Multiplicative L
  /-- the character of `ℚ(√s*)` -/
  chiBit : ℕ → G →* Multiplicative (ZMod 2)
  /-- RC12 (tex 9734–9737): `t(g)t(h) = t(gh) + d(h)t(gh⁻¹)` -/
  trace_mul : ∀ g h (x : M), t g (t h x) = t (g * h) x + d h (t (g * h⁻¹) x)
  /-- RC12 (tex 9719–9733), within the budget: `d` acts trivially on the trace orbit of `F_U` -/
  det_orbit : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    ∀ u v, d u (t v (F U)) = t v (F U)
  /-- RC12 (tex 9741–9745), within the budget: two fresh traces vanish on `F_U` -/
  two_fresh : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    ∀ g h, t g (t h (F U)) = 0
  /-- RC12 (tex 9739): `t(1) = 2` -/
  trace_one : ∀ x, t 1 x = (2 : ZMod 2) • x
  /-- GLUE (tex 9524–9548, 9663–9669), within the budget: `t(·)F_U` factors through `G/N_U` -/
  level : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
    ∀ g n, n ∈ N U → t (g * n) (F U) = t g (F U)
  /-- definition: the `U'`-extension lies in the `U`-extension for `U' ⊆ U` -/
  N_anti : ∀ U U', U' ⊆ U → N U ≤ N U'
  /-- definition: the `U`-extension contains the type fields and `ℚ(√s*)`, `s ∈ U` -/
  N_chi : ∀ U, ∀ n ∈ N U, chiType n = 1 ∧ ∀ s ∈ U, chiBit s n = 1
  /-- GLUE (Kummer, tex 9745–9750), within the budget -/
  kummer : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g, chiType g = 1 →
    (∀ s ∈ U, chiBit s g = 1) → g ∈ Subgroup.closure (sqSet G) ⊔ N U
  /-- GLUE (independence of the quadratic characters at a set of good primes) -/
  chi_surj : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (ℓ : L) (b : ℕ → ZMod 2), ∃ g,
    chiType g = Multiplicative.ofAdd ℓ ∧ ∀ s ∈ U, chiBit s g = Multiplicative.ofAdd (b s)
  /-- GLUE (Chebotarev in the finite group `G/N_U`), within the budget -/
  chebotarev : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ (g : G)
    (avoid : Finset ℕ), ∃ q h, ∃ n ∈ N U, T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹ * n
  /-- GLUE (`t(g)` is a limit of Hecke operators `T_q`) -/
  t_class : ∀ g h, t (h * g * h⁻¹) = t g
  /-- GLUE (Frobenius dictionary): the type of `q` is `χ_type(Fr_q)` -/
  typ_frob : ∀ q, T.Good q → chiType (frob q) = Multiplicative.ofAdd (T.typ q)
  /-- GLUE (Frobenius dictionary): `(q/s) = χ_s(Fr_q)` -/
  bit_frob : ∀ q s, T.Good q → T.Good s → q ≠ s →
    chiBit s (frob q) = Multiplicative.ofAdd (legBit q s)
  /-- ELLIOT (tex 9671–9704): the reading of a fresh vertex -/
  reading : ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
    (insert q U).card ≤ B → R (insert q U) = read U (t (frob q) (F U))
  /-- ELLIOT ((O.12) at coefficient one, tex 9905–9918) -/
  o12 : ∀ (U : Finset ℕ) (p : ℕ), p ∈ U → (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g : G,
    ∃ (τ φ : G) (κ0 : ℤ), (κ0 = 1 ∨ κ0 = -1) ∧
      chiType τ = 1 ∧ (∀ s ∈ U, s ≠ p → chiBit s τ = 1) ∧
      chiBit p τ = Multiplicative.ofAdd 1 ∧
      chiType φ = Multiplicative.ofAdd (T.typ p) ∧
      (∀ s ∈ U, s ≠ p → chiBit s φ = Multiplicative.ofAdd (legBit p s)) ∧
      ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) * read (U.erase p) (t (g * τ * φ) (F (U.erase p))) -
          ((Cp (ap p) κ0 : ℤ) : ZMod 2) * read (U.erase p) (t (g * φ) (F (U.erase p))) =
        read U (t (g * τ) (F U)) - read U (t g (F U))

namespace TraceModelBudget

variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
  (X : TraceModelBudget T R ap B)

attribute [instance] TraceModelBudget.instG TraceModelBudget.instM TraceModelBudget.instMod

include X

/-- Invariance of `g ↦ t(g)F_U` under the squares and `N_U`, within the budget (PROVED: RC12's
`trace_square_invariance` and `level`, as RC0's `TraceModelRel.trace_join`). -/
theorem trace_join (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) (g x : X.G)
    (hx : x ∈ Subgroup.closure (sqSet X.G) ⊔ X.N U) : X.t (g * x) (X.F U) = X.t g (X.F U) := by
  rw [← Subgroup.closure_eq (X.N U), ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction generalizing g with
  | mem x hx =>
    rcases hx with ⟨h, rfl⟩ | hn
    · exact trace_square_invariance X.t X.d (X.F U) X.trace_mul (X.det_orbit U hU hUB)
        (X.two_fresh U hU hUB) g h
    · exact X.level U hU hUB g x hn
  | one => simp
  | mul x y _ _ ihx ihy => rw [← mul_assoc, ihy, ihx]
  | inv x _ ihx => rw [← ihx (g * x⁻¹), inv_mul_cancel_right]

theorem chiType_conj (g h : X.G) : X.chiType (h * g * h⁻¹) = X.chiType g := by
  rw [map_mul, map_mul, map_inv, mul_comm (X.chiType h), mul_inv_cancel_right]

theorem chiBit_conj (s : ℕ) (g h : X.G) : X.chiBit s (h * g * h⁻¹) = X.chiBit s g := by
  rw [map_mul, map_mul, map_inv, mul_comm (X.chiBit s h), mul_inv_cancel_right]

/-- **The fixed-`U` factorization** (tex 9745–9750; PROVED as RC0's
`TraceModelRel.fixedU_of_model`, the fields used at the good set `W` with `|W| + 1 ≤ B`). -/
theorem fixedU_of_model : FixedUFactorization T R B := by
  intro W p p' hcard hW hp hp' hpW hp'W ht hb
  have hWB : W.card + 1 ≤ B := by
    rw [← card_insert_of_notMem hpW]
    exact hcard
  have hcard' : (insert p' W).card ≤ B := by
    rwa [card_insert_of_notMem hp'W, ← card_insert_of_notMem hpW]
  rw [X.reading W p hW hp hpW hcard, X.reading W p' hW hp' hp'W hcard']
  congr 1
  have hx : (X.frob p)⁻¹ * X.frob p' ∈ Subgroup.closure (sqSet X.G) ⊔ X.N W := by
    refine X.kummer W hW hWB _ ?_ fun s hs => ?_
    · rw [map_mul, map_inv, X.typ_frob p hp, X.typ_frob p' hp', ht, inv_mul_cancel]
    · have hps : p ≠ s := fun h => hpW (h ▸ hs)
      have hp's : p' ≠ s := fun h => hp'W (h ▸ hs)
      rw [map_mul, map_inv, X.bit_frob p s hp (hW s hs) hps, X.bit_frob p' s hp' (hW s hs) hp's,
        hb s hs, inv_mul_cancel]
  have := X.trace_join W hW hWB (X.frob p) _ hx
  rw [mul_inv_cancel_left] at this
  rw [this]

/-- **Primary isolation** (tex 9739, 9947–9948; PROVED as RC0's
`TraceModelRel.primary_of_model`). -/
theorem primary_of_model : PrimaryReading T R B := by
  intro W q hW hq hqW hcard ht hb
  have hWB : W.card + 1 ≤ B := by
    rw [← card_insert_of_notMem hqW]
    exact hcard
  rw [X.reading W q hW hq hqW hcard]
  have hx : X.frob q ∈ Subgroup.closure (sqSet X.G) ⊔ X.N W := by
    refine X.kummer W hW hWB _ ?_ fun s hs => ?_
    · rw [X.typ_frob q hq, ht, ofAdd_zero]
    · rw [X.bit_frob q s hq (hW s hs) (fun h => hqW (h ▸ hs)), hb s hs, ofAdd_zero]
  have := X.trace_join W hW hWB 1 _ hx
  rw [one_mul] at this
  rw [this, X.trace_one, show (2 : ZMod 2) = 0 from rfl, zero_smul, map_zero]

/-- **The (O.12) reading** (tex 9905–9945; PROVED as RC0's `TraceModelRel.o12_of_model`, with
`chebotarev` and `level` used at the good sets `U`, `U ∖ {p}` within the budget). -/
theorem o12_of_model : O12Reading T R ap B := by
  intro U p hpU hU hUB ℓ bq
  obtain ⟨g, hgT, hgB⟩ := X.chi_surj U hU ℓ bq
  obtain ⟨τ, φ, κ0, hκ, hτT, hτB, hτp, hφT, hφB, hO⟩ := X.o12 U p hpU hU hUB g
  obtain ⟨q, h1, n1, hn1, hq, hqU, hfq⟩ := X.chebotarev U hU hUB g U
  obtain ⟨qτ, h2, n2, hn2, hqτ, hqτU, hfqτ⟩ := X.chebotarev U hU hUB (g * τ) U
  obtain ⟨r0, h3, n3, hn3, hr0, hr0U, hfr0⟩ := X.chebotarev U hU hUB (g * φ) U
  obtain ⟨r1, h4, n4, hn4, hr1, hr1U, hfr1⟩ := X.chebotarev U hU hUB (g * τ * φ) U
  have ne_of : ∀ {x s : ℕ}, x ∉ U → s ∈ U → x ≠ s := fun hx hs h => hx (h ▸ hs)
  have typ_of : ∀ {x : ℕ} {y h n : X.G}, n ∈ X.N U → T.Good x →
      X.frob x = h * y * h⁻¹ * n → Multiplicative.ofAdd (T.typ x) = X.chiType y := by
    intro x y h n hn hx hf
    rw [← X.typ_frob x hx, hf, map_mul, (X.N_chi U n hn).1, mul_one, X.chiType_conj]
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
  have bit_of : ∀ {x : ℕ} {y h n : X.G}, n ∈ X.N U → T.Good x → x ∉ U →
      X.frob x = h * y * h⁻¹ * n → ∀ s ∈ U, Multiplicative.ofAdd (legBit x s) = X.chiBit s y := by
    intro x y h n hn hx hxU hf s hs
    rw [← X.bit_frob x s hx (hU s hs) (ne_of hxU hs), hf, map_mul, (X.N_chi U n hn).2 s hs,
      mul_one, X.chiBit_conj]
  have t_of : ∀ {U' : Finset ℕ} {x : ℕ} {y h n : X.G}, U' ⊆ U → n ∈ X.N U →
      X.frob x = h * y * h⁻¹ * n → X.t (X.frob x) (X.F U') = X.t y (X.F U') := by
    intro U' x y h n hU' hn hf
    have hU'g : ∀ s ∈ U', T.Good s := fun s hs => hU s (hU' hs)
    have hU'B : U'.card + 1 ≤ B := (Nat.add_le_add_right (card_le_card hU') 1).trans hUB
    rw [hf, X.level U' hU'g hU'B _ n (X.N_anti U U' hU' hn), X.t_class]
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
  · have hUe : ∀ s ∈ U.erase p, T.Good s := fun s hs => hU s (mem_of_mem_erase hs)
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
/-- **RC2's rules within a budget from the budgeted trace model** (PROVED: batch 3's
`rulesUpTo_symb`). -/
theorem rulesUpTo_of_model {W : ℕ} (X : TraceModelBudget T R ap (W + 1)) (hap : ApEven T ap) :
    RulesUpTo ε (symb T R) W :=
  rulesUpTo_symb T R ap W X.fixedU_of_model X.o12_of_model hap X.primary_of_model

end TraceModelBudget

/-- **RC2's coefficient rules from budgeted trace models at every budget** (PROVED: batch 3's
`coefficientRules_symb`). -/
theorem coefficientRules_of_modelBudget {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} (X : ∀ B, TraceModelBudget T R ap B) (hap : ApEven T ap) :
    CoefficientRules ε (symb T R) :=
  coefficientRules_symb T R ap (fun B => (X B).fixedU_of_model) (fun B => (X B).o12_of_model)
    hap (fun B => (X B).primary_of_model)

/-- **Every `TraceModelRel` is a budgeted trace model** (PROVED: the budget guards are dropped
hypotheses). -/
def TraceModelBudget.ofTraceModelRel {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    {B : ℕ} (X : TraceModelRel T R ap B) : TraceModelBudget T R ap B where
  G := X.G
  M := X.M
  t := X.t
  d := X.d
  F := X.F
  read := X.read
  frob := X.frob
  N := X.N
  chiType := X.chiType
  chiBit := X.chiBit
  trace_mul := X.trace_mul
  det_orbit U _ _ := X.det_orbit U
  two_fresh U _ _ := X.two_fresh U
  trace_one := X.trace_one
  level U _ _ := X.level U
  N_anti := X.N_anti
  N_chi := X.N_chi
  kummer U _ _ := X.kummer U
  chi_surj := X.chi_surj
  chebotarev U hU _ := X.chebotarev U hU
  t_class := X.t_class
  typ_frob := X.typ_frob
  bit_frob := X.bit_frob
  reading := X.reading
  o12 := X.o12

/-- **Lane RC24's genuine Galois trace model is a budgeted trace model, with no `Unbudgeted`**
(PROVED: `G = G_ℚ`, `chiBit = bitChar`, `N = galN`; `level`, `N_anti`, `N_chi`, `chi_surj`,
`typ_frob`, `bit_frob` are the theorems of lane RC24). -/
def TraceModelBudget.ofGaloisTrace {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    {B : ℕ} {chiType : GalQ →* Multiplicative L} (X : GaloisTraceModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) : TraceModelBudget T R ap B where
  G := GalQ
  M := X.M
  t := X.t
  d := X.d
  F := X.F
  read := X.read
  frob := X.frob
  N := X.N
  chiType := chiType
  chiBit := bitChar
  trace_mul := X.trace_mul
  det_orbit := X.det_orbit
  two_fresh := X.two_fresh
  trace_one := X.trace_one
  level U _ _ := X.level U
  N_anti := X.N_anti
  N_chi := X.N_chi
  kummer := X.kummer
  chi_surj := X.chi_surj htyp
  chebotarev := X.chebotarev
  t_class := X.t_class
  typ_frob := X.typ_frob htyp
  bit_frob := X.bit_frob
  reading := X.reading
  o12 := X.o12

/-- **Lane RC24's genuine constituent model gives a budgeted trace model, with no
`Unbudgeted`** (PROVED: through `GaloisConstituentModel.toGaloisTraceModel`). -/
def TraceModelBudget.ofGaloisConstituent {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} {B : ℕ} {chiType : GalQ →* Multiplicative L}
    (X : GaloisConstituentModel T R ap B chiType) (htyp : IsTypeChar T chiType)
    (hI : X.Inputs) : TraceModelBudget T R ap B :=
  TraceModelBudget.ofGaloisTrace (X.toGaloisTraceModel hI) htyp

/-! ## The constituent model on coefficientwise reduced expansions -/

section Operators

variable {G : Type} [Group G] {I K O : Type} [Field K] [CommRing O] [Algebra O K]

/-- `t(g)` on an integral module preserved by the scalar traces, over an abstract group (tex
9762–9771). Kind: definition. -/
def opT (ρ : I → G →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (g : G) : Λ →ₗ[O] Λ :=
  ((tV ρ g).restrictScalars O).restrict (hst g)

/-- `d(g)` on an integral module preserved by the determinants, over an abstract group (tex
9762–9771). Kind: definition. -/
def opD (ρ : I → G →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hsd : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ) (g : G) : Λ →ₗ[O] Λ :=
  ((dV ρ g).restrictScalars O).restrict (hsd g)

theorem opT_coe (ρ : I → G →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ) (g : G) (v : Λ) :
    (opT ρ Λ hst g v : I → K) = tV ρ g v := rfl

theorem opD_coe (ρ : I → G →* GL (Fin 2) K) (Λ : Submodule O (I → K))
    (hsd : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ) (g : G) (v : Λ) :
    (opD ρ Λ hsd g v : I → K) = dV ρ g v := rfl

/-- **A vector of `𝔪Λ` has vanishing reduced expansion** (PROVED: `le_ker_redExpOf`; the converse
is saturation, which the text does not assume, tex 9644–9646). -/
theorem redExpOf_eq_zero_of_mem (m : Ideal O) {Λ : Submodule O (I → K)} {C : Type}
    (expand : Λ →ₗ[O] (C → O)) {w : Λ}
    (hw : (w : I → K) ∈ (m • ⊤ : Submodule O Λ).map Λ.subtype) : redExpOf m expand w = 0 := by
  obtain ⟨y, hy, hyw⟩ := hw
  have e : y = w := Subtype.ext hyw
  rw [← e]
  exact le_ker_redExpOf m expand hy

end Operators

/-- **Lane RC0's constituent model on coefficientwise reduced expansions, within the operator
budget** (tex 9447–9468, 9638–9771). The fields are those of RC0's `ConstituentModelRel`, except:
* the integral Fourier expansion `C`, `coefK`, `expand`, `expand_spec` (definition, tex
  9655–9662: "finitely many Fourier coordinates inject this space into a finite coordinate
  space"; the translates remain integral);
* `read` is a functional of the reduced expansion (tex 9686–9695: the coefficient-one coefficient
  of `t(Fr_q)F_U`, reduced);
* `det_orbit`, `two_fresh`, `level_red` are identities of coefficientwise reduced expansions
  (tex 9639–9646, 9716–9717, 9728–9729, 9741–9745), with no membership in `𝔪Λ` (no saturation,
  tex 9644–9646);
* `det_orbit`, `two_fresh`, `level_red`, `kummer`, `chebotarev` are stated for `U` a set of good
  primes with `|U| + 1 ≤ B` (tex 9447–9468, 9649–9654, 9741–9745, 10533–10548).
Kinds: `stable_t`, `stable_d`, `level_red`, `kummer`, `chi_surj`, `typ_frob`, `bit_frob` GLUE;
`chebotarev` PRINT (Chebotarev in `G/N_U`, as lane RC24's model); `det_orbit`, `two_fresh`
ELLIOT; `N_anti`, `N_chi` definition. The inputs `reading`, `o12` are `Inputs`. Owner: RC12
(App F). -/
structure ConstituentModelRed (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ)
    (B : ℕ) where
  /-- the joint Galois group -/
  G : Type
  [instG : Group G]
  /-- the constituents (with multiplicities and degeneracies) -/
  I : Type
  /-- the characteristic-zero coefficient field -/
  K : Type
  [instK : Field K]
  /-- the coefficient ring and its maximal ideal -/
  O : Type
  [instO : CommRing O]
  [instAlg : Algebra O K]
  m : Ideal O
  two_mem : (2 : O) ∈ m
  /-- the Galois representations of the constituents -/
  ρ : I → G →* GL (Fin 2) K
  /-- the integral module generated by the translates -/
  Λ : Submodule O (I → K)
  /-- GLUE (tex 9663–9669): `Λ` is preserved by the trace operators -/
  stable_t : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ
  /-- GLUE (tex 9663–9669): `Λ` is preserved by the determinant operators -/
  stable_d : ∀ g, ∀ v ∈ Λ, dV ρ g v ∈ Λ
  /-- the Fourier indices of the coordinates (tex 9661–9662) -/
  C : Type
  /-- the Fourier expansion of the characteristic-zero space (tex 9655–9662) -/
  coefK : (I → K) →ₗ[K] (C → K)
  /-- the integral Fourier coefficients of the integral module (tex 9655–9662) -/
  expand : Λ →ₗ[O] (C → O)
  /-- definition: `expand` records the Fourier coefficients in `𝒪` -/
  expand_spec : ∀ (v : Λ) (n : C), algebraMap O K (expand v n) = coefK v n
  /-- the integral forms `F_U = θ H_U` -/
  F : Finset ℕ → Λ
  /-- the coefficient-one functionals on reduced expansions (tex 9686–9695) -/
  read : Finset ℕ → (C → O ⧸ m) →+ ZMod 2
  /-- Frobenius elements -/
  frob : ℕ → G
  /-- the subgroup fixing the `U`-extension -/
  N : Finset ℕ → Subgroup G
  /-- the type characters -/
  chiType : G →* Multiplicative L
  /-- the character of `ℚ(√s*)` -/
  chiBit : ℕ → G →* Multiplicative (ZMod 2)
  /-- ELLIOT (tex 9711–9733: "the conclusion is an identity of coefficientwise reduced
  expansions"), within the budget: `d(u)t(v)F_U` and `t(v)F_U` have the same reduced
  expansion -/
  det_orbit : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ u v,
    redExpOf m expand (opD ρ Λ stable_d u (opT ρ Λ stable_t v (F U))) =
      redExpOf m expand (opT ρ Λ stable_t v (F U))
  /-- ELLIOT (tex 9741–9745: "`t(g)t(h)F_U = 0` after reduction"), within the budget -/
  two_fresh : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h,
    redExpOf m expand (opT ρ Λ stable_t g (opT ρ Λ stable_t h (F U))) = 0
  /-- GLUE (level and continuity, tex 9524–9548, 9663–9669), within the budget: for `n ∈ N_U`
  the reduced expansions of `t(gn)F_U` and `t(g)F_U` agree -/
  level_red : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g, ∀ n ∈ N U,
    redExpOf m expand (opT ρ Λ stable_t (g * n) (F U)) =
      redExpOf m expand (opT ρ Λ stable_t g (F U))
  /-- definition: the `U'`-extension lies in the `U`-extension for `U' ⊆ U` -/
  N_anti : ∀ U U', U' ⊆ U → N U ≤ N U'
  /-- definition: the `U`-extension contains the type fields and `ℚ(√s*)`, `s ∈ U` -/
  N_chi : ∀ U, ∀ n ∈ N U, chiType n = 1 ∧ ∀ s ∈ U, chiBit s n = 1
  /-- GLUE (Kummer detection of the elementary quotient, tex 9745–9750), within the budget -/
  kummer : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g, chiType g = 1 →
    (∀ s ∈ U, chiBit s g = 1) → g ∈ Subgroup.closure (sqSet G) ⊔ N U
  /-- GLUE (independence of the quadratic characters at a set of good primes) -/
  chi_surj : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (ℓ : L) (b : ℕ → ZMod 2), ∃ g,
    chiType g = Multiplicative.ofAdd ℓ ∧ ∀ s ∈ U, chiBit s g = Multiplicative.ofAdd (b s)
  /-- PRINT (Chebotarev in the finite group `G/N_U`, tex 9666–9668, 9919–9921), within the
  budget -/
  chebotarev : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ (g : G)
    (avoid : Finset ℕ), ∃ q h, ∃ n ∈ N U, T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹ * n
  /-- GLUE (Frobenius dictionary): the type of `q` is `χ_type(Fr_q)` -/
  typ_frob : ∀ q, T.Good q → chiType (frob q) = Multiplicative.ofAdd (T.typ q)
  /-- GLUE (Frobenius dictionary): `(q/s) = χ_s(Fr_q)` -/
  bit_frob : ∀ q s, T.Good q → T.Good s → q ≠ s →
    chiBit s (frob q) = Multiplicative.ofAdd (legBit q s)

namespace ConstituentModelRed

variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
  (X : ConstituentModelRed T R ap B)

attribute [instance] ConstituentModelRed.instG ConstituentModelRed.instK
  ConstituentModelRed.instO ConstituentModelRed.instAlg

/-- `t(g)` on `Λ`. Kind: definition. -/
abbrev tΛ (g : X.G) : X.Λ →ₗ[X.O] X.Λ := opT X.ρ X.Λ X.stable_t g

/-- `d(g)` on `Λ`. Kind: definition. -/
abbrev dΛ (g : X.G) : X.Λ →ₗ[X.O] X.Λ := opD X.ρ X.Λ X.stable_d g

/-- Coefficientwise reduction of the integral expansion (tex 9639–9641). Kind: definition. -/
abbrev redE : X.Λ →ₗ[X.O] (X.C → X.O ⧸ X.m) := redExpOf X.m X.expand

/-- **The two ELLIOT inputs**, on reduced expansions (tex 9671–9704, 9905–9918): the
coefficient-one reading of a fresh vertex and (O.12) at coefficient one. Kind: definition. -/
def Inputs : Prop :=
  (∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
      (insert q U).card ≤ B → R (insert q U) = X.read U (X.redE (X.tΛ (X.frob q) (X.F U)))) ∧
  (∀ (U : Finset ℕ) (p : ℕ), p ∈ U → (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g : X.G,
      ∃ (τ φ : X.G) (κ0 : ℤ), (κ0 = 1 ∨ κ0 = -1) ∧
        X.chiType τ = 1 ∧ (∀ s ∈ U, s ≠ p → X.chiBit s τ = 1) ∧
        X.chiBit p τ = Multiplicative.ofAdd 1 ∧
        X.chiType φ = Multiplicative.ofAdd (T.typ p) ∧
        (∀ s ∈ U, s ≠ p → X.chiBit s φ = Multiplicative.ofAdd (legBit p s)) ∧
        ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) *
            X.read (U.erase p) (X.redE (X.tΛ (g * τ * φ) (X.F (U.erase p)))) -
          ((Cp (ap p) κ0 : ℤ) : ZMod 2) *
            X.read (U.erase p) (X.redE (X.tΛ (g * φ) (X.F (U.erase p)))) =
        X.read U (X.redE (X.tΛ (g * τ) (X.F U))) - X.read U (X.redE (X.tΛ g (X.F U))))

/-! ### Exact identities on `Λ` (characteristic zero) -/

theorem tΛ_dΛ (g h : X.G) (v : X.Λ) : X.tΛ g (X.dΛ h v) = X.dΛ h (X.tΛ g v) := by
  apply Subtype.ext
  funext i
  simp only [opT_coe, opD_coe, tV, dV, scalarOp_apply]
  ring

theorem tΛ_mul (g h : X.G) (v : X.Λ) :
    X.tΛ g (X.tΛ h v) = X.tΛ (g * h) v + X.dΛ h (X.tΛ (g * h⁻¹) v) :=
  Subtype.ext (tV_mul X.ρ g h (v : X.I → X.K))

theorem dΛ_mul (g h : X.G) (v : X.Λ) : X.dΛ (g * h) v = X.dΛ g (X.dΛ h v) := by
  apply Subtype.ext
  funext i
  simp only [opD_coe, dV, scalarOp_apply, map_mul, Units.val_mul, Matrix.det_mul]
  ring

theorem tΛ_one (v : X.Λ) : X.tΛ 1 v = (2 : ℕ) • v := by
  apply Subtype.ext
  show tV X.ρ 1 (v : X.I → X.K) = (((2 : ℕ) • v : X.Λ) : X.I → X.K)
  rw [tV_one, two_smul]
  simp [two_nsmul]

theorem tΛ_conj (g h : X.G) : X.tΛ (h * g * h⁻¹) = X.tΛ g := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show tV X.ρ (h * g * h⁻¹) (v : X.I → X.K) = tV X.ρ g v
  rw [tV_conj]

/-! ### The largest operator-stable submodule of the reduction kernel -/

/-- The submodules of the reduction kernel stable under every `t(g)` and `d(g)`. -/
def StableKer : Set (Submodule X.O X.Λ) :=
  {P | P ≤ LinearMap.ker X.redE ∧ (∀ g, P ≤ P.comap (X.tΛ g)) ∧ ∀ g, P ≤ P.comap (X.dΛ g)}

/-- **The largest operator-stable submodule of the kernel of coefficientwise reduction.** -/
def Kst : Submodule X.O X.Λ := sSup X.StableKer

theorem Kst_le_ker : X.Kst ≤ LinearMap.ker X.redE := sSup_le fun _ hP => hP.1

theorem Kst_stable_t (g : X.G) : X.Kst ≤ X.Kst.comap (X.tΛ g) :=
  sSup_le fun _ hP => (hP.2.1 g).trans (Submodule.comap_mono (le_sSup hP))

theorem Kst_stable_d (g : X.G) : X.Kst ≤ X.Kst.comap (X.dΛ g) :=
  sSup_le fun _ hP => (hP.2.2 g).trans (Submodule.comap_mono (le_sSup hP))

theorem le_Kst {P : Submodule X.O X.Λ} (h1 : P ≤ LinearMap.ker X.redE)
    (h2 : ∀ g, P ≤ P.comap (X.tΛ g)) (h3 : ∀ g, P ≤ P.comap (X.dΛ g)) : P ≤ X.Kst :=
  le_sSup ⟨h1, h2, h3⟩

theorem mLam_le_Kst : (X.m • ⊤ : Submodule X.O X.Λ) ≤ X.Kst := by
  refine X.le_Kst (le_ker_redExpOf X.m X.expand) (fun g => ?_) (fun g => ?_) <;>
  · rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact smul_mono_right _ le_top

/-- The generators of the determinant and two-trace identities for `F_U`. -/
def orbitGens (U : Finset ℕ) : Set X.Λ :=
  {x | (∃ a b, x = X.dΛ a (X.tΛ b (X.F U)) - X.tΛ b (X.F U)) ∨
    ∃ g h, x = X.tΛ g (X.tΛ h (X.F U))}

/-- The submodule generated by the two identities at `U` (tex 9712–9745). -/
def detSpan (U : Finset ℕ) : Submodule X.O X.Λ := Submodule.span X.O (X.orbitGens U)

theorem gen1_mem (U : Finset ℕ) (a b : X.G) :
    X.dΛ a (X.tΛ b (X.F U)) - X.tΛ b (X.F U) ∈ X.detSpan U :=
  Submodule.subset_span (Or.inl ⟨a, b, rfl⟩)

theorem gen2_mem (U : Finset ℕ) (g h : X.G) : X.tΛ g (X.tΛ h (X.F U)) ∈ X.detSpan U :=
  Submodule.subset_span (Or.inr ⟨g, h, rfl⟩)

theorem dsub_tt_mem (U : Finset ℕ) (a x y : X.G) :
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

theorem detSpan_stable_t (U : Finset ℕ) (k : X.G) :
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

theorem detSpan_stable_d (U : Finset ℕ) (k : X.G) :
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

/-- **The span lies in the reduction kernel** within the budget (the coefficientwise fields). -/
theorem detSpan_le_ker (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) :
    X.detSpan U ≤ LinearMap.ker X.redE := by
  rw [detSpan, Submodule.span_le]
  rintro x (⟨a, b, rfl⟩ | ⟨g, h, rfl⟩)
  · show X.redE _ = 0
    rw [map_sub, sub_eq_zero]
    exact X.det_orbit U hU hUB a b
  · exact X.two_fresh U hU hUB g h

theorem detSpan_le_Kst (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) :
    X.detSpan U ≤ X.Kst :=
  X.le_Kst (X.detSpan_le_ker U hU hUB) (X.detSpan_stable_t U) (X.detSpan_stable_d U)

/-- The vectors `t(gn)F_U − t(g)F_U`, `n ∈ N_U`, with the identities at `U`. -/
def levelSpan (U : Finset ℕ) : Submodule X.O X.Λ :=
  Submodule.span X.O {x | ∃ g, ∃ n ∈ X.N U, x = X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U)} ⊔
    X.detSpan U

/-- **`t(gn)F_U − t(g)F_U` lies in `Kst`** for `n ∈ N_U`, within the budget (PROVED: the span is
operator-stable by the exact identities and the class-function property of `t`, and lies in the
kernel by `level_red` and the coefficientwise identities; no normality of `N_U` is used). -/
theorem level_mem_Kst (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B)
    (g n : X.G) (hn : n ∈ X.N U) : X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U) ∈ X.Kst := by
  have hgen : ∀ g, ∀ n ∈ X.N U, X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U) ∈ X.levelSpan U :=
    fun g n hn => Submodule.mem_sup_left (Submodule.subset_span ⟨g, n, hn, rfl⟩)
  have hdet : ∀ x ∈ X.detSpan U, x ∈ X.levelSpan U := fun x hx => Submodule.mem_sup_right hx
  refine X.le_Kst (P := X.levelSpan U) ?_ (fun k => ?_) (fun k => ?_) (hgen g n hn)
  · refine sup_le ?_ (X.detSpan_le_ker U hU hUB)
    rw [Submodule.span_le]
    rintro x ⟨g, n, hn, rfl⟩
    show X.redE _ = 0
    rw [map_sub, sub_eq_zero]
    exact X.level_red U hU hUB g n hn
  · refine sup_le ?_ ((X.detSpan_stable_t U k).trans (Submodule.comap_mono le_sup_right))
    rw [Submodule.span_le]
    rintro x ⟨g, n, hn, rfl⟩
    show X.tΛ k (X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U)) ∈ X.levelSpan U
    have hn' : n⁻¹ ∈ X.N U := inv_mem hn
    have c1 : X.tΛ (k * (g * n)⁻¹) = X.tΛ (g⁻¹ * k * n⁻¹) := by
      rw [← X.tΛ_conj (g⁻¹ * k * n⁻¹) g]
      congr 1
      group
    have c2 : X.tΛ (k * g⁻¹) = X.tΛ (g⁻¹ * k) := by
      rw [← X.tΛ_conj (g⁻¹ * k) g]
      congr 1
      group
    have e : X.tΛ k (X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U)) =
        (X.tΛ (k * g * n) (X.F U) - X.tΛ (k * g) (X.F U)) +
          (X.tΛ (g⁻¹ * k * n⁻¹) (X.F U) - X.tΛ (g⁻¹ * k) (X.F U)) +
          ((X.dΛ (g * n) (X.tΛ (k * (g * n)⁻¹) (X.F U)) - X.tΛ (k * (g * n)⁻¹) (X.F U)) -
            (X.dΛ g (X.tΛ (k * g⁻¹) (X.F U)) - X.tΛ (k * g⁻¹) (X.F U))) := by
      rw [map_sub, X.tΛ_mul, X.tΛ_mul, ← c1, ← c2]
      have h1 : k * (g * n) = k * g * n := by group
      rw [h1]
      abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.add_mem _ (hgen _ _ hn) (hgen _ _ hn')) ?_
    exact Submodule.sub_mem _ (hdet _ (X.gen1_mem U _ _)) (hdet _ (X.gen1_mem U _ _))
  · refine sup_le ?_ ((X.detSpan_stable_d U k).trans (Submodule.comap_mono le_sup_right))
    rw [Submodule.span_le]
    rintro x ⟨g, n, hn, rfl⟩
    show X.dΛ k (X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U)) ∈ X.levelSpan U
    have e : X.dΛ k (X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U)) =
        (X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U)) +
          ((X.dΛ k (X.tΛ (g * n) (X.F U)) - X.tΛ (g * n) (X.F U)) -
            (X.dΛ k (X.tΛ g (X.F U)) - X.tΛ g (X.F U))) := by
      rw [map_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (hgen _ _ hn)
      (Submodule.sub_mem _ (hdet _ (X.gen1_mem U _ _)) (hdet _ (X.gen1_mem U _ _)))

/-! ### The module of the trace model -/

/-- **The module of the trace model**: `Λ` modulo the largest operator-stable submodule of the
reduction kernel (no congruence property of the operators, tex 9639–9646, 9898–9900). -/
abbrev Mst : Type := X.Λ ⧸ X.Kst

theorem two_nsmul_Mst (x : X.Mst) : 2 • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    show 2 • X.Kst.mkQ v = 0
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← Nat.cast_smul_eq_nsmul X.O]
    exact X.mLam_le_Kst (Submodule.smul_mem_smul (by exact_mod_cast X.two_mem) trivial)

/-- The `𝔽₂`-structure of `Mst`. -/
abbrev modMst : Module (ZMod 2) X.Mst := AddCommGroup.zmodModule X.two_nsmul_Mst

attribute [local instance] ConstituentModelRed.modMst

/-- `t(g)` on `Mst`. -/
def tK (g : X.G) : X.Mst →ₗ[ZMod 2] X.Mst :=
  (X.Kst.mapQ X.Kst (X.tΛ g) (X.Kst_stable_t g)).toAddMonoidHom.toZModLinearMap 2

/-- `d(g)` on `Mst`. -/
def dK (g : X.G) : X.Mst →ₗ[ZMod 2] X.Mst :=
  (X.Kst.mapQ X.Kst (X.dΛ g) (X.Kst_stable_d g)).toAddMonoidHom.toZModLinearMap 2

/-- The forms `F_U` in `Mst`. -/
def FK (U : Finset ℕ) : X.Mst := Submodule.Quotient.mk (X.F U)

/-- The coefficient-one functionals, through coefficientwise reduction. -/
def readK (U : Finset ℕ) : X.Mst →ₗ[ZMod 2] ZMod 2 :=
  ((X.read U).comp (X.Kst.liftQ X.redE X.Kst_le_ker).toAddMonoidHom).toZModLinearMap 2

theorem tK_mk (g : X.G) (v : X.Λ) :
    X.tK g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (X.tΛ g v) := rfl

theorem dK_mk (g : X.G) (v : X.Λ) :
    X.dK g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (X.dΛ g v) := rfl

theorem readK_mk (U : Finset ℕ) (v : X.Λ) :
    X.readK U (Submodule.Quotient.mk v) = X.read U (X.redE v) := rfl

theorem mk_eq_mk_iff (v w : X.Λ) :
    (Submodule.Quotient.mk v : X.Mst) = Submodule.Quotient.mk w ↔ v - w ∈ X.Kst :=
  Submodule.Quotient.eq _

theorem trace_mul (g h : X.G) (x : X.Mst) :
    X.tK g (X.tK h x) = X.tK (g * h) x + X.dK h (X.tK (g * h⁻¹) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [tK_mk, tK_mk, tK_mk, tK_mk, dK_mk, ← Submodule.Quotient.mk_add, X.tΛ_mul]

theorem det_orbit' (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) (u v : X.G) :
    X.dK u (X.tK v (X.FK U)) = X.tK v (X.FK U) := by
  rw [FK, tK_mk, dK_mk, mk_eq_mk_iff]
  exact X.detSpan_le_Kst U hU hUB (X.gen1_mem U u v)

theorem two_fresh' (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) (g h : X.G) :
    X.tK g (X.tK h (X.FK U)) = 0 := by
  rw [FK, tK_mk, tK_mk, Submodule.Quotient.mk_eq_zero]
  exact X.detSpan_le_Kst U hU hUB (X.gen2_mem U g h)

theorem trace_one (x : X.Mst) : X.tK 1 x = (2 : ZMod 2) • x := by
  rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [tK_mk, X.tΛ_one]
    show X.Kst.mkQ ((2 : ℕ) • v) = 0
    rw [map_nsmul]
    exact X.two_nsmul_Mst _

theorem t_class (g h : X.G) : X.tK (h * g * h⁻¹) = X.tK g := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H v => rw [tK_mk, tK_mk, X.tΛ_conj]

theorem level (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s) (hUB : U.card + 1 ≤ B) (g n : X.G)
    (hn : n ∈ X.N U) : X.tK (g * n) (X.FK U) = X.tK g (X.FK U) := by
  rw [FK, tK_mk, tK_mk, mk_eq_mk_iff]
  exact X.level_mem_Kst U hU hUB g n hn

/-- `Mst` is nonzero as soon as some vector of `Λ` has a nonzero reduced expansion. -/
theorem nontrivial_Mst (v : X.Λ) (hv : X.redE v ≠ 0) : Nontrivial X.Mst :=
  ⟨⟨Submodule.Quotient.mk v, 0, fun h => hv (by
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact X.Kst_le_ker h)⟩⟩

/-- **The budgeted trace model of a reduced constituent model** (PROVED: `Mst` with the induced
operators, forms and functionals; tex 9638–9771). -/
def toTraceModelBudget (hI : X.Inputs) : TraceModelBudget T R ap B where
  G := X.G
  M := X.Mst
  instMod := X.modMst
  t := X.tK
  d := X.dK
  F := X.FK
  read := X.readK
  frob := X.frob
  N := X.N
  chiType := X.chiType
  chiBit := X.chiBit
  trace_mul := X.trace_mul
  det_orbit := X.det_orbit'
  two_fresh := X.two_fresh'
  trace_one := X.trace_one
  level := X.level
  N_anti := X.N_anti
  N_chi := X.N_chi
  kummer := X.kummer
  chi_surj := X.chi_surj
  chebotarev := X.chebotarev
  t_class := X.t_class
  typ_frob := X.typ_frob
  bit_frob := X.bit_frob
  reading := hI.1
  o12 := hI.2

/-! ### The two hypotheses of the converse (not supplied by the text) -/

/-- **Saturation** (NOT assumed by the text, tex 9644–9646): a vector of `Λ` whose reduced
expansion vanishes lies in `𝔪Λ`. Kind: definition (hypothesis of the converse only). -/
def Saturated : Prop :=
  ∀ v : X.Λ, X.redE v = 0 → (v : X.I → X.K) ∈ (X.m • ⊤ : Submodule X.O X.Λ).map X.Λ.subtype

/-- **The unbudgeted forms** of the budgeted fields (NOT given by the text off the budget, tex
9447–9468, 9649–9654, 9741–9745). Kind: definition (hypothesis of the converse only). -/
def Unbudgeted : Prop :=
  (∀ (U : Finset ℕ) (u v : X.G), X.redE (X.dΛ u (X.tΛ v (X.F U))) = X.redE (X.tΛ v (X.F U))) ∧
    (∀ (U : Finset ℕ) (g h : X.G), X.redE (X.tΛ g (X.tΛ h (X.F U))) = 0) ∧
    (∀ (U : Finset ℕ) (g : X.G), ∀ n ∈ X.N U,
      X.redE (X.tΛ (g * n) (X.F U)) = X.redE (X.tΛ g (X.F U))) ∧
    (∀ (U : Finset ℕ) (g : X.G), X.chiType g = 1 → (∀ s ∈ U, X.chiBit s g = 1) →
      g ∈ Subgroup.closure (sqSet X.G) ⊔ X.N U) ∧
    (∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (g : X.G) (avoid : Finset ℕ),
      ∃ q h, ∃ n ∈ X.N U, T.Good q ∧ q ∉ avoid ∧ X.frob q = h * g * h⁻¹ * n)

/-- **The converse: a reduced constituent model is lane RC0's `ConstituentModelRel`, given
saturation and the unbudgeted forms** (PROVED; the readings of `Λ/𝔪Λ` are those of the reduced
expansions, through `Λ/𝔪Λ → (C → 𝒪/𝔪)`). -/
def toConstituentModelRel (hsat : X.Saturated) (hunb : X.Unbudgeted) :
    ConstituentModelRel T R ap B where
  G := X.G
  I := X.I
  K := X.K
  O := X.O
  m := X.m
  two_mem := X.two_mem
  ρ := X.ρ
  Λ := X.Λ
  stable_t := X.stable_t
  stable_d := X.stable_d
  F := X.F
  read U := (X.read U).comp
    ((X.m • ⊤ : Submodule X.O X.Λ).liftQ X.redE (le_ker_redExpOf X.m X.expand)).toAddMonoidHom
  frob := X.frob
  N := X.N
  chiType := X.chiType
  chiBit := X.chiBit
  det_orbit U u v := hsat (X.dΛ u (X.tΛ v (X.F U)) - X.tΛ v (X.F U)) (by
    rw [map_sub, sub_eq_zero]
    exact hunb.1 U u v)
  two_fresh U g h := hsat _ (hunb.2.1 U g h)
  level_red U g n hn := hsat (X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U)) (by
    rw [map_sub, sub_eq_zero]
    exact hunb.2.2.1 U g n hn)
  N_anti := X.N_anti
  N_chi := X.N_chi
  kummer := hunb.2.2.2.1
  chi_surj := X.chi_surj
  chebotarev := hunb.2.2.2.2
  typ_frob := X.typ_frob
  bit_frob := X.bit_frob

/-- The inputs carry over to the converse (PROVED: the readings agree definitionally). -/
theorem toConstituentModelRel_inputs (hsat : X.Saturated) (hunb : X.Unbudgeted)
    (hI : X.Inputs) : (X.toConstituentModelRel hsat hunb).Inputs := by
  have key : ∀ (U : Finset ℕ) (g : X.G), (X.toConstituentModelRel hsat hunb).readM U
      ((X.toConstituentModelRel hsat hunb).tM g ((X.toConstituentModelRel hsat hunb).FM U)) =
        X.read U (X.redE (X.tΛ g (X.F U))) := fun _ _ => rfl
  obtain ⟨h1, h2⟩ := hI
  refine ⟨fun U q hU hq hqU hc => by
    have h := h1 U q hU hq hqU hc
    rw [← key] at h
    exact h, fun U p hp hU hc g => ?_⟩
  obtain ⟨τ, φ, κ0, hκ, a1, a2, a3, a4, a5, hO⟩ := h2 U p hp hU hc g
  exact ⟨τ, φ, κ0, hκ, a1, a2, a3, a4, a5, hO⟩

end ConstituentModelRed

/-! ## RC2's rules from reduced constituent models -/

/-- **RC2's rules within a budget from a reduced constituent model** (the odd source at one
stage; PROVED). The replacement of RC0's `rulesUpTo_of_constituentsRel`. -/
theorem rulesUpTo_of_constituentsRed {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    {W : ℕ} (X : ConstituentModelRed T R ap (W + 1)) (hI : X.Inputs) (hap : ApEven T ap) :
    RulesUpTo ε (symb T R) W :=
  (X.toTraceModelBudget hI).rulesUpTo_of_model hap

/-- **RC2's coefficient rules from reduced constituent models at every budget** (the even
source; PROVED). The replacement of RC0's `coefficientRules_of_constituentsRel`. -/
theorem coefficientRules_of_constituentsRed {T : TypeData L ε} {R : Finset ℕ → ZMod 2}
    {ap : ℕ → ℤ} (X : ∀ B, ConstituentModelRed T R ap B) (hI : ∀ B, (X B).Inputs)
    (hap : ApEven T ap) : CoefficientRules ε (symb T R) :=
  coefficientRules_of_modelBudget (fun B => (X B).toTraceModelBudget (hI B)) hap

/-! ## Lane RC24's genuine model, with no bridge hypothesis -/

section Galois

variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
  {chiType : GalQ →* Multiplicative L}

/-- **Lane RC24's genuine constituent model is a reduced constituent model** (PROVED, with no
`Unbudgeted` and no `Saturated`): `G = G_ℚ`, `chiBit = bitChar`, `N = consN`; `level_red`,
`N_anti`, `N_chi`, `chi_surj`, `typ_frob`, `bit_frob` are the theorems of lane RC24, the other
fields are its fields (tex 9638–9797). -/
def ConstituentModelRed.ofGalois (X : GaloisConstituentModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) : ConstituentModelRed T R ap B where
  G := GalQ
  I := X.I
  K := X.K
  O := X.O
  m := X.m
  two_mem := X.two_mem
  ρ := X.ρ
  Λ := X.Λ
  stable_t := X.stable_t
  stable_d := X.stable_d
  C := X.C
  coefK := X.coefK
  expand := X.expand
  expand_spec := X.expand_spec
  F := X.F
  read := X.read
  frob := X.frob
  N := X.N
  chiType := chiType
  chiBit := bitChar
  det_orbit := X.det_orbit
  two_fresh := X.two_fresh
  level_red U _ _ g n hn := X.level_red U g n hn
  N_anti := X.N_anti
  N_chi := X.N_chi
  kummer := X.kummer
  chi_surj := X.chi_surj htyp
  chebotarev := X.chebotarev
  typ_frob := X.typ_frob htyp
  bit_frob := X.bit_frob

/-- **The inputs carry over** (PROVED: they are the same statements). -/
theorem ConstituentModelRed.ofGalois_inputs (X : GaloisConstituentModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) (hI : X.Inputs) :
    (ConstituentModelRed.ofGalois X htyp).Inputs :=
  hI

/-- Lane RC24's saturation hypothesis is the saturation of the reduced model (PROVED). -/
theorem ConstituentModelRed.ofGalois_saturated (X : GaloisConstituentModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) (hsat : X.Saturated) :
    (ConstituentModelRed.ofGalois X htyp).Saturated :=
  hsat

/-- Lane RC24's unbudgeted forms give those of the reduced model (PROVED; `level_red` holds at
every `U` by the definition of `consN`). -/
theorem ConstituentModelRed.ofGalois_unbudgeted (X : GaloisConstituentModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) (hX : X.Unbudgeted) :
    (ConstituentModelRed.ofGalois X htyp).Unbudgeted :=
  ⟨hX.1, hX.2.1, fun U g n hn => X.level_red U g n hn, hX.2.2.1, hX.2.2.2⟩

/-- **The odd conjunct from lane RC24's constituent models** (PROVED): genuine constituent
models within every cutoff on an eventually-true set of stages, with type characters reading the
types there, give reduced constituent models with their inputs. -/
theorem oddModelsRed_of_galois {L₁ : Type*} [AddCommGroup L₁] {ε₁ : L₁ →+ ZMod 2}
    (l : Filter ℕ) (T₁ : ℕ → TypeData L₁ ε₁) (R₁ : ℕ → Finset ℕ → ZMod 2) (ap₁ : ℕ → ℕ → ℤ)
    (chi : ℕ → GalQ →* Multiplicative L₁) (htyp : ∀ᶠ θ in l, IsTypeChar (T₁ θ) (chi θ))
    (h : ∀ Wc : ℕ, ∀ᶠ θ in l,
      ∃ X : GaloisConstituentModel (T₁ θ) (R₁ θ) (ap₁ θ) (Wc + 1) (chi θ), X.Inputs) :
    ∀ Wc : ℕ, ∀ᶠ θ in l, ∃ X : ConstituentModelRed (T₁ θ) (R₁ θ) (ap₁ θ) (Wc + 1), X.Inputs :=
  fun Wc => ((h Wc).and htyp).mono fun _ ⟨⟨X, hX⟩, hθ⟩ =>
    ⟨ConstituentModelRed.ofGalois X hθ, ConstituentModelRed.ofGalois_inputs X hθ hX⟩

/-- **The even conjunct from lane RC24's constituent models** (PROVED). -/
theorem evenModelsRed_of_galois (htyp : IsTypeChar T chiType)
    (h : ∀ B, ∃ X : GaloisConstituentModel T R ap B chiType, X.Inputs) :
    ∀ B, ∃ X : ConstituentModelRed T R ap B, X.Inputs :=
  fun B => match h B with
    | ⟨X, hX⟩ =>
      ⟨ConstituentModelRed.ofGalois X htyp, ConstituentModelRed.ofGalois_inputs X htyp hX⟩

end Galois

/-! ## Relation to lane RC0's `ConstituentModelRel` -/

section Rel

variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}

/-- **Lane RC0's constituent model, with an integral expansion, is a reduced constituent model**
(PROVED): the data supplied by the text are the integral Fourier coordinates (tex 9655–9662) and
the readings as functionals of the reduced expansion (tex 9686–9695, `hread` in
`ofConstituentModelRel_inputs`). Only `𝔪Λ ≤ ker` of the reduction is used
(`redExpOf_eq_zero_of_mem`), and the budget guards are dropped hypotheses. -/
def ConstituentModelRed.ofConstituentModelRel (X : ConstituentModelRel T R ap B) {C : Type}
    (coefK : (X.I → X.K) →ₗ[X.K] (C → X.K)) (expand : X.Λ →ₗ[X.O] (C → X.O))
    (expand_spec : ∀ (v : X.Λ) (n : C), algebraMap X.O X.K (expand v n) = coefK v n)
    (read : Finset ℕ → (C → X.O ⧸ X.m) →+ ZMod 2) : ConstituentModelRed T R ap B where
  G := X.G
  I := X.I
  K := X.K
  O := X.O
  m := X.m
  two_mem := X.two_mem
  ρ := X.ρ
  Λ := X.Λ
  stable_t := X.stable_t
  stable_d := X.stable_d
  C := C
  coefK := coefK
  expand := expand
  expand_spec := expand_spec
  F := X.F
  read := read
  frob := X.frob
  N := X.N
  chiType := X.chiType
  chiBit := X.chiBit
  det_orbit U _ _ u v := by
    have h := redExpOf_eq_zero_of_mem X.m expand
      (w := X.dΛ u (X.tΛ v (X.F U)) - X.tΛ v (X.F U)) (X.det_orbit U u v)
    rw [map_sub, sub_eq_zero] at h
    exact h
  two_fresh U _ _ g h := redExpOf_eq_zero_of_mem X.m expand
    (w := X.tΛ g (X.tΛ h (X.F U))) (X.two_fresh U g h)
  level_red U _ _ g n hn := by
    have h := redExpOf_eq_zero_of_mem X.m expand
      (w := X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U)) (X.level_red U g n hn)
    rw [map_sub, sub_eq_zero] at h
    exact h
  N_anti := X.N_anti
  N_chi := X.N_chi
  kummer U _ _ := X.kummer U
  chi_surj := X.chi_surj
  chebotarev U hU _ := X.chebotarev U hU
  typ_frob := X.typ_frob
  bit_frob := X.bit_frob

/-- **The inputs carry over** when the readings of `Λ/𝔪Λ` are those of the reduced expansions
(PROVED). -/
theorem ConstituentModelRed.ofConstituentModelRel_inputs (X : ConstituentModelRel T R ap B)
    {C : Type} (coefK : (X.I → X.K) →ₗ[X.K] (C → X.K)) (expand : X.Λ →ₗ[X.O] (C → X.O))
    (expand_spec : ∀ (v : X.Λ) (n : C), algebraMap X.O X.K (expand v n) = coefK v n)
    (read : Finset ℕ → (C → X.O ⧸ X.m) →+ ZMod 2)
    (hread : ∀ (U : Finset ℕ) (v : X.Λ),
      X.read U (Submodule.Quotient.mk v) = read U (redExpOf X.m expand v))
    (hI : X.Inputs) :
    (ConstituentModelRed.ofConstituentModelRel X coefK expand expand_spec read).Inputs := by
  have key : ∀ (U : Finset ℕ) (g : X.G), X.readM U (X.tM g (X.FM U)) =
      read U (redExpOf X.m expand (X.tΛ g (X.F U))) := fun U g => hread U (X.tΛ g (X.F U))
  obtain ⟨h1, h2⟩ := hI
  refine ⟨fun U q hU hq hqU hc => ?_, fun U p hp hU hc (g : X.G) => ?_⟩
  · have h := h1 U q hU hq hqU hc
    rw [key] at h
    exact h
  · obtain ⟨τ, φ, κ0, hκ, a1, a2, a3, a4, a5, hO⟩ := h2 U p hp hU hc g
    rw [key, key, key, key] at hO
    exact ⟨τ, φ, κ0, hκ, a1, a2, a3, a4, a5, hO⟩

end Rel

/-! ## Non-vacuity -/

section NonVacuity

variable {L₀ : Type} [AddCommGroup L₀] {ε₀ : L₀ →+ ZMod 2}

/-- **The zero reduced constituent model** (PROVED: lane RC0's `ConstituentModelRel.zero`, with
the empty Fourier expansion). -/
def ConstituentModelRed.zero (T : TypeData L₀ ε₀) (ap : ℕ → ℤ) (B : ℕ) :
    ConstituentModelRed T (fun _ => 0) ap B :=
  ConstituentModelRed.ofConstituentModelRel (ConstituentModelRel.zero T ap B) (C := Empty) 0 0
    (fun _ n => n.elim) (fun _ => 0)

theorem ConstituentModelRed.zero_inputs (T : TypeData L₀ ε₀) (ap : ℕ → ℤ) (B : ℕ) :
    (ConstituentModelRed.zero T ap B).Inputs :=
  ConstituentModelRed.ofConstituentModelRel_inputs (ConstituentModelRel.zero T ap B)
    (C := Empty) 0 0 (fun _ n => n.elim) (fun _ => 0) (fun _ _ => rfl)
    (ConstituentModelRel.zero_inputs T ap B)

end NonVacuity

section Tate

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) [NeZero m] (hm : 0 < m) (h4 : 4 ∣ m)
  (ap : ℕ → ℤ) (B : ℕ)

include E in
/-- **The reduced constituent model is inhabited by a genuine Galois representation, with no
hypothesis** (PROVED): one constituent, the `2`-adic Tate representation of an elliptic curve
`E/ℚ`, over the genuine type data `typeData m` and `G_ℚ`, with its inputs (lane RC24's
`tateConstituentModel'`; no `Unbudgeted`, no `Saturated`). The constituents of the actual forms
`F_U = θ H_U` are weight-two newforms and Eisenstein pairs (tex 9647–9654, 9762–9771). -/
theorem tateConstituentModelRed :
    ∃ X : ConstituentModelRed (typeData m hm h4) (fun _ => 0) ap B, X.Inputs :=
  ⟨ConstituentModelRed.ofGalois (tateConstituentModel' E m hm h4 ap B)
      (isTypeChar_typeData m hm h4),
    ConstituentModelRed.ofGalois_inputs _ _ (tateConstituentModel'_inputs E m hm h4 ap B)⟩

/-- **The module of the Tate reduced model is nonzero** (PROVED: `intOne_red_ne_zero`). -/
theorem tateConstituentModelRed_nontrivial :
    Nontrivial (ConstituentModelRed.ofGalois (tateConstituentModel' E m hm h4 ap B)
      (isTypeChar_typeData m hm h4)).Mst :=
  ConstituentModelRed.nontrivial_Mst _ intOne intOne_red_ne_zero

include E in
/-- **The budgeted trace model is inhabited by the reduced expansions of a genuine Galois
representation, with no hypothesis** (PROVED). -/
theorem tateTraceModelBudget :
    Nonempty (TraceModelBudget (typeData m hm h4) (fun _ => 0) ap B) :=
  ⟨(ConstituentModelRed.ofGalois (tateConstituentModel' E m hm h4 ap B)
      (isTypeChar_typeData m hm h4)).toTraceModelBudget
    (tateConstituentModel'_inputs E m hm h4 ap B)⟩

/-- **The Tate constituent model with its integral coordinate doubled** (expansion `2·x`,
characteristic-zero expansion `2·id`): lane RC24's zero-form model on the genuine `2`-adic Tate
representation. Kind: PROVED (definition). -/
def tateDoubled : GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m) :=
  GaloisConstituentModel.zeroForms frobeniusExists (typeData m hm h4) ap B (typChar m)
    (isTypeChar_typeData m hm h4) (IsLocalRing.maximalIdeal ℤ_[2]) two_mem_maximalIdeal_padicInt
    (fun _ : Unit => tateRhoQ E) intLattice (tate_stable_t E) (tate_stable_d E)
    ((2 : ℚ_[2]) • LinearMap.id) ((2 : ℤ_[2]) • intCoord) (fun v n => by
      simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_ofNat,
        intCoord_spec])

/-- **Saturation depends on the integral coordinates and is not automatic for genuine data**
(PROVED): for the doubled coordinate, the vector `1` of the integral lattice has vanishing
reduced expansion but does not lie in `𝔪Λ` (its standard reduced coordinate is `1 ≠ 0`). So
lane RC24's bridge hypothesis `Saturated` fails here, while `tateDoubled` is a genuine
`GaloisConstituentModel` and hence a reduced constituent model (`ConstituentModelRed.ofGalois`). -/
theorem tateDoubled_not_saturated : ¬ (tateDoubled E m hm h4 ap B).Saturated := by
  intro hsat
  have h0 : (tateDoubled E m hm h4 ap B).redE intOne = 0 := by
    funext n
    show Ideal.Quotient.mk (IsLocalRing.maximalIdeal ℤ_[2]) ((2 : ℤ_[2]) * intCoord intOne n) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_right _ _ two_mem_maximalIdeal_padicInt)
  obtain ⟨y, hy, hyw⟩ := hsat intOne h0
  have e : (y : intLattice) = intOne := Subtype.ext hyw
  have hk : redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord (y : intLattice) = 0 :=
    LinearMap.mem_ker.mp (le_ker_redExpOf (IsLocalRing.maximalIdeal ℤ_[2]) intCoord hy)
  rw [e] at hk
  exact intOne_red_ne_zero hk

include E in
/-- **The reduced bridge applies where lane RC24's saturated bridge does not** (PROVED): a genuine
constituent model on the Tate representation with its inputs, NOT saturated, whose reduced model
has its inputs. -/
theorem exists_galois_not_saturated :
    ∃ X : GaloisConstituentModel (typeData m hm h4) (fun _ => 0) ap B (typChar m),
      ¬ X.Saturated ∧ X.Inputs ∧
        (ConstituentModelRed.ofGalois X (isTypeChar_typeData m hm h4)).Inputs :=
  have hI : (tateDoubled E m hm h4 ap B).Inputs :=
    GaloisConstituentModel.zeroForms_inputs frobeniusExists _ ap B _ _ _ _ _ _ _ _ _ _ _
  ⟨tateDoubled E m hm h4 ap B, tateDoubled_not_saturated E m hm h4 ap B, hI,
    ConstituentModelRed.ofGalois_inputs _ _ hI⟩

end Tate

end ZInQ.Contrib.RC53Assist.RelBridge
