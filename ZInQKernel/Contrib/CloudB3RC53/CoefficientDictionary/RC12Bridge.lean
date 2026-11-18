import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.Rules

/-!
# The coefficient dictionary, part 3: RC12's trace readings in the dictionary's form

**DEPRECATED.** `TraceModel` is uninhabitable (`traceModel_false`, `RC/Wiring/TraceModelRel.lean`):
its field `chebotarev` asks for exact conjugacy of Frobenius in `G` for every `g`, which together
with `bit_frob` contradicts CRT, Dirichlet and reciprocity (exact conjugacy holds only in a
finite quotient, tex 9749–9750; in general Frobenius classes are only dense, tex 9666–9668).
The theorems over it (`fixedU_of_model`, `primary_of_model`, `o12_of_model`,
`rulesUpTo_of_model`, `coefficientRules_of_model`) are vacuous. Use RC0's corrected `TraceModelRel`
and `coefficientRules_of_modelRel` / `TraceModelRel.rulesUpTo_of_model`, whose consistency witness
is `TraceModelRel.zero` (`traceModelRel_zero_nonempty`). This file is kept because
`TraceModelInstance.lean` (the operators `tV`, `dV`) and RC0's Rel files import it (`sqSet`).

Manuscript `diophantine_zq.tex`, App F, proof of Proposition `ex:app-coefficient-rules`: the
integral trace module and its operators (L9641–9762), the trace identities (L9729–9750), (O.12)
(L9763–9905), the coefficient-one readings and the omission rule (L9905–9953).

Lane RC12 proves the algebra of these readings (`Odd/Traces.lean`): the identity
`t(g)t(h) = t(gh) + d(h)t(gh⁻¹)` gives `t(gh²)F = t(g)F` (`trace_square_invariance`), and
`omission_rule` turns `hO12, hV, hc` into the `𝔽₂` omission identity. This file puts that algebra
into the form consumed by `coefficientRules_symb` / `rulesUpTo_symb`:

* `TraceModel T R ap B`: the reduced integral trace module `M` with RC12's operators `t, d` and
  forms `F_U` (fields `trace_mul`, `det_orbit`, `two_fresh`, `trace_one` are exactly the
  hypotheses of RC12's `trace_square_invariance` / `primary_isolation_reading`); the
  coefficient-one functionals `read U`; Frobenius elements `frob q` of a finite joint Galois
  quotient `G`; and its quadratic characters `chiType` (the type) and `chiBit s` (the character
  of `ℚ(√s*)`). The remaining inputs are fields named after the facts: the coefficient-one reading
  (INPUT, App F L9672–9690), (O.12) at coefficient one (INPUT, RC12's `O12_diag` with the Hecke
  formula, L9905–9918), and GLUE: level (`F_U` unramified outside `S ∪ U`), Kummer detection of the
  elementary quotient, Chebotarev, independence of the characters, `t` a class function, and the
  Frobenius character dictionary `typ q = χ_type(Fr_q)`, `(q/s) = χ_s(Fr_q)`.
* PROVED: `fixedU_of_model` (from RC12's `trace_square_invariance`), `primary_of_model`,
  `o12_of_model`, hence `rulesUpTo_of_model` and `coefficientRules_of_model`, in which RC12's
  `hV` and `hc` are no longer hypotheses (they are proved in `symb_contraction` from the fixed-`U`
  factorization and `cp_sum_odd`).

The trace module, Frobenius elements and characters are not in Mathlib (they come from the Galois
representations of the actual theta forms), so they enter as the data of `TraceModel`; no field
asserts a coefficient rule.
-/

namespace ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd Finset

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- The squares of a group. -/
def sqSet (G : Type*) [Group G] : Set G := {x | ∃ h, x = h ^ 2}

/-- **The trace-module model of RC12's readings**, within the budget `B` (see the module
docstring). **DEPRECATED (uninhabitable; see `TraceModelRel`/`ConstituentModelRel` in `RC/Wiring/`; the theorems over it are vacuous).** -/
structure TraceModel (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ) where
  /-- the finite joint Galois quotient -/
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
  /-- the subgroup acting trivially on the `U`-extension -/
  N : Finset ℕ → Subgroup G
  /-- the type characters -/
  chiType : G →* Multiplicative L
  /-- the character of `ℚ(√s*)` -/
  chiBit : ℕ → G →* Multiplicative (ZMod 2)
  /-- RC12 (tex L9734–9737): `t(g)t(h) = t(gh) + d(h)t(gh⁻¹)` -/
  trace_mul : ∀ g h (x : M), t g (t h x) = t (g * h) x + d h (t (g * h⁻¹) x)
  /-- RC12 (tex L9719–9733): `d` acts trivially on the trace orbit of `F_U` -/
  det_orbit : ∀ U u v, d u (t v (F U)) = t v (F U)
  /-- RC12 (tex L9741–9745): two fresh traces vanish -/
  two_fresh : ∀ U g h, t g (t h (F U)) = 0
  /-- RC12 (tex L9739): `t(1) = 2` -/
  trace_one : ∀ x, t 1 x = (2 : ZMod 2) • x
  /-- GLUE (level, tex L9524–9548): `F_U` is unramified outside `S ∪ U` -/
  level : ∀ U g n, n ∈ N U → t (g * n) (F U) = t g (F U)
  /-- GLUE (Kummer): an element with trivial type and trivial `U`-characters lies in the subgroup
  generated by the squares and `N_U` (the elementary quotient of the `U`-extension is detected by
  these quadratic characters) -/
  kummer : ∀ U g, chiType g = 1 → (∀ s ∈ U, chiBit s g = 1) →
    g ∈ Subgroup.closure (sqSet G) ⊔ N U
  /-- GLUE (independence of the quadratic characters) -/
  chi_surj : ∀ (U : Finset ℕ) (ℓ : L) (b : ℕ → ZMod 2), ∃ g,
    chiType g = Multiplicative.ofAdd ℓ ∧ ∀ s ∈ U, chiBit s g = Multiplicative.ofAdd (b s)
  /-- GLUE (Chebotarev): every element is conjugate to the Frobenius of a good prime outside any
  finite set -/
  chebotarev : ∀ (g : G) (avoid : Finset ℕ), ∃ q h, T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹
  /-- GLUE (`t(g)` is a limit of Hecke operators `T_q`, `Fr_q` in the class of `g`) -/
  t_class : ∀ g h, t (h * g * h⁻¹) = t g
  /-- GLUE (Frobenius dictionary): the type of `q` is `χ_type(Fr_q)` -/
  typ_frob : ∀ q, T.Good q → chiType (frob q) = Multiplicative.ofAdd (T.typ q)
  /-- GLUE (Frobenius dictionary): `(q/s) = (s*/q) = χ_s(Fr_q)` -/
  bit_frob : ∀ q s, T.Good q → T.Good s → q ≠ s → chiBit s (frob q) = Multiplicative.ofAdd (legBit q s)
  /-- INPUT (App F L9672–9690): the reading of a fresh vertex `q` adjoining `U` is the
  coefficient-one coefficient of `t(Fr_q) F_U` -/
  reading : ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
    (insert q U).card ≤ B → R (insert q U) = read U (t (frob q) (F U))
  /-- INPUT ((O.12) at coefficient one, tex L9905–9918: RC12's `O12_diag` and the Hecke formula
  `H_U[pr] ≡ η(p) C_p(vr) 2^{−n_V−1} a(vr)`): for `p ∈ U` and every `g`, with `τ` the inertia
  (flipping only the character of `p`) and `φ` a Frobenius at `p` (carrying the labels of `p`) and
  `κ₀ = ±1` the Legendre sign of `vr₀` at `p` -/
  o12 : ∀ (U : Finset ℕ) (p : ℕ), p ∈ U → (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g : G,
    ∃ (τ φ : G) (κ0 : ℤ), (κ0 = 1 ∨ κ0 = -1) ∧
      chiType τ = 1 ∧ (∀ s ∈ U, s ≠ p → chiBit s τ = 1) ∧
      chiBit p τ = Multiplicative.ofAdd 1 ∧
      chiType φ = Multiplicative.ofAdd (T.typ p) ∧
      (∀ s ∈ U, s ≠ p → chiBit s φ = Multiplicative.ofAdd (legBit p s)) ∧
      ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) * read (U.erase p) (t (g * τ * φ) (F (U.erase p))) -
          ((Cp (ap p) κ0 : ℤ) : ZMod 2) * read (U.erase p) (t (g * φ) (F (U.erase p))) =
        read U (t (g * τ) (F U)) - read U (t g (F U))

namespace TraceModel

variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
  (X : TraceModel T R ap B)

attribute [instance] TraceModel.instG TraceModel.instM TraceModel.instMod

include X

/-- Invariance of `g ↦ t(g)F_U` under the subgroup generated by the squares and `N_U` (RC12's
`trace_square_invariance` for the squares, the level for `N_U`). -/
theorem trace_join (U : Finset ℕ) (g x : X.G)
    (hx : x ∈ Subgroup.closure (sqSet X.G) ⊔ X.N U) : X.t (g * x) (X.F U) = X.t g (X.F U) := by
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

theorem chiType_conj (g h : X.G) : X.chiType (h * g * h⁻¹) = X.chiType g := by
  rw [map_mul, map_mul, map_inv, mul_comm (X.chiType h), mul_inv_cancel_right]

theorem chiBit_conj (s : ℕ) (g h : X.G) : X.chiBit s (h * g * h⁻¹) = X.chiBit s g := by
  rw [map_mul, map_mul, map_inv, mul_comm (X.chiBit s h), mul_inv_cancel_right]

/-- **The fixed-`U` factorization from RC12's square invariance** (tex L9745–9750). -/
theorem fixedU_of_model : FixedUFactorization T R B := by
  intro W p p' hcard hW hp hp' hpW hp'W ht hb
  have hcard' : (insert p' W).card ≤ B := by
    rwa [card_insert_of_notMem hp'W, ← card_insert_of_notMem hpW]
  rw [X.reading W p hW hp hpW hcard, X.reading W p' hW hp' hp'W hcard']
  congr 1
  have hx : (X.frob p)⁻¹ * X.frob p' ∈ Subgroup.closure (sqSet X.G) ⊔ X.N W := by
    refine X.kummer W _ ?_ fun s hs => ?_
    · rw [map_mul, map_inv, X.typ_frob p hp, X.typ_frob p' hp', ht, inv_mul_cancel]
    · have hps : p ≠ s := fun h => hpW (h ▸ hs)
      have hp's : p' ≠ s := fun h => hp'W (h ▸ hs)
      rw [map_mul, map_inv, X.bit_frob p s hp (hW s hs) hps, X.bit_frob p' s hp' (hW s hs) hp's,
        hb s hs, inv_mul_cancel]
  have := X.trace_join W (X.frob p) _ hx
  rw [mul_inv_cancel_left] at this
  rw [this]

/-- **Primary isolation from RC12's square invariance and `t(1) = 2`** (tex L9739, L9947–9948). -/
theorem primary_of_model : PrimaryReading T R B := by
  intro W q hW hq hqW hcard ht hb
  rw [X.reading W q hW hq hqW hcard]
  have hx : X.frob q ∈ Subgroup.closure (sqSet X.G) ⊔ X.N W := by
    refine X.kummer W _ ?_ fun s hs => ?_
    · rw [X.typ_frob q hq, ht, ofAdd_zero]
    · rw [X.bit_frob q s hq (hW s hs) (fun h => hqW (h ▸ hs)), hb s hs, ofAdd_zero]
  have := X.trace_join W 1 _ hx
  rw [one_mul] at this
  rw [this, X.trace_one, show (2 : ZMod 2) = 0 from rfl, zero_smul, map_zero]

/-- **The (O.12) reading from the module-level identity and Chebotarev representatives**
(tex L9905–9945): fresh primes with Frobenius in the classes of `g, gτ, gφ, gτφ`, `g` with the
prescribed characters, carry exactly the labels of `O12Reading` (product-label rule from the
multiplicativity of the characters). -/
theorem o12_of_model : O12Reading T R ap B := by
  intro U p hpU hU hUB ℓ bq
  obtain ⟨g, hgT, hgB⟩ := X.chi_surj U ℓ bq
  obtain ⟨τ, φ, κ0, hκ, hτT, hτB, hτp, hφT, hφB, hO⟩ := X.o12 U p hpU hU hUB g
  obtain ⟨q, h1, hq, hqU, hfq⟩ := X.chebotarev g U
  obtain ⟨qτ, h2, hqτ, hqτU, hfqτ⟩ := X.chebotarev (g * τ) U
  obtain ⟨r0, h3, hr0, hr0U, hfr0⟩ := X.chebotarev (g * φ) U
  obtain ⟨r1, h4, hr1, hr1U, hfr1⟩ := X.chebotarev (g * τ * φ) U
  have hpG : T.Good p := hU p hpU
  have ne_of : ∀ {x s : ℕ}, x ∉ U → s ∈ U → x ≠ s := fun hx hs h => hx (h ▸ hs)
  -- types
  have htq : T.typ q = ℓ := by
    have := X.typ_frob q hq
    rw [hfq, X.chiType_conj, hgT] at this
    exact (Multiplicative.ofAdd.injective this).symm
  have htqτ : T.typ qτ = ℓ := by
    have := X.typ_frob qτ hqτ
    rw [hfqτ, X.chiType_conj, map_mul, hgT, hτT, mul_one] at this
    exact (Multiplicative.ofAdd.injective this).symm
  have htr0 : T.typ r0 = T.typ p + ℓ := by
    have := X.typ_frob r0 hr0
    rw [hfr0, X.chiType_conj, map_mul, hgT, hφT, ← ofAdd_add, add_comm] at this
    exact (Multiplicative.ofAdd.injective this).symm
  have htr1 : T.typ r1 = T.typ p + ℓ := by
    have := X.typ_frob r1 hr1
    rw [hfr1, X.chiType_conj, map_mul, map_mul, hgT, hτT, mul_one, hφT, ← ofAdd_add,
      add_comm] at this
    exact (Multiplicative.ofAdd.injective this).symm
  -- bits
  have bit_of : ∀ {x : ℕ} {y : X.G} {h : X.G}, T.Good x → x ∉ U → X.frob x = h * y * h⁻¹ →
      ∀ s ∈ U, Multiplicative.ofAdd (legBit x s) = X.chiBit s y := by
    intro x y h hx hxU hf s hs
    rw [← X.bit_frob x s hx (hU s hs) (ne_of hxU hs), hf, X.chiBit_conj]
  refine ⟨q, qτ, r0, r1, κ0, hq, hqτ, hr0, hr1, hqU, hqτU, hr0U, hr1U, htq, htqτ,
    fun s hs => ?_, fun s hs hsp => ?_, ?_, htr0, htr1, fun s hs hsp => ⟨?_, ?_⟩, ?_, hκ, ?_⟩
  · have := bit_of hq hqU hfq s hs
    rw [hgB s hs] at this
    exact Multiplicative.ofAdd.injective this
  · have := bit_of hqτ hqτU hfqτ s hs
    rw [map_mul, hgB s hs, hτB s hs hsp, mul_one] at this
    exact Multiplicative.ofAdd.injective this
  · have := bit_of hqτ hqτU hfqτ p hpU
    rw [map_mul, hgB p hpU, hτp, ← ofAdd_add] at this
    exact Multiplicative.ofAdd.injective this
  · have := bit_of hr0 hr0U hfr0 s hs
    rw [map_mul, hgB s hs, hφB s hs hsp, ← ofAdd_add, add_comm] at this
    exact Multiplicative.ofAdd.injective this
  · have := bit_of hr1 hr1U hfr1 s hs
    rw [map_mul, map_mul, hgB s hs, hτB s hs hsp, mul_one, hφB s hs hsp, ← ofAdd_add,
      add_comm] at this
    exact Multiplicative.ofAdd.injective this
  · have e1 := bit_of hr1 hr1U hfr1 p hpU
    have e0 := bit_of hr0 hr0U hfr0 p hpU
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
      (hcardU hqU), hfr1, hfr0, hfqτ, hfq, X.t_class, X.t_class, X.t_class, X.t_class]
    exact hO

omit X in
/-- **RC2's rules within a budget from RC12's readings** (the odd source at one stage).
**DEPRECATED (vacuous: `TraceModel` is uninhabitable; use `TraceModelRel.rulesUpTo_of_model`).** -/
theorem rulesUpTo_of_model {W : ℕ} (X : TraceModel T R ap (W + 1)) (hap : ApEven T ap) :
    RulesUpTo ε (symb T R) W :=
  rulesUpTo_symb T R ap W X.fixedU_of_model X.o12_of_model hap X.primary_of_model

end TraceModel

/-- **RC2's coefficient rules from RC12's readings** (the even source: a model at every
budget). **DEPRECATED (vacuous: `TraceModel` is uninhabitable; use
`coefficientRules_of_modelRel`).** -/
theorem coefficientRules_of_model {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (X : ∀ B, TraceModel T R ap B) (hap : ApEven T ap) : CoefficientRules ε (symb T R) :=
  coefficientRules_symb T R ap (fun B => (X B).fixedU_of_model) (fun B => (X B).o12_of_model)
    hap (fun B => (X B).primary_of_model)

end ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
