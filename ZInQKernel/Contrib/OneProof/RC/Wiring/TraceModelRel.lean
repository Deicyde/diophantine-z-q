import ZInQKernel.Contrib.CloudB3RC53.CoefficientDictionary.TraceModelInstance

/-!
# Theorem 5.3, Lane RC0 round 3: the trace model with Chebotarev relative to `N_U`

Manuscript `diophantine_zq.tex`, App F, proof of Proposition `ex:app-coefficient-rules`: the
integral trace module and its operators (tex 9641–9771), the reading of an added vertex
(9671–9704), the trace identities and the elementary quadratic quotient (9705–9750), (O.12) and
the readings on prime sets (9905–9953).

**Batch 3's `TraceModel` and `ConstituentModel` are inconsistent** (`traceModel_false`,
`constituentModel_false`, PROVED from batch 3's `realizeNat` and reciprocity). Their field
`chebotarev` asserts *exact* conjugacy `frob q = h g h⁻¹` in the group `G` for every `g`, while
`bit_frob` asserts `χ_s(frob q) = (q/s)` for *every* good `s ≠ q`. At `g = 1` the first gives a good
prime `q` with `frob q = 1`, so `(q/s) = 1` for every good `s ≠ q`; CRT and Dirichlet give a good
`s` with `(q/s) = −1`. (Exact conjugacy holds in a finite quotient, tex 9749–9750: "Over `ℚ` this
quotient is finite"; infinitely many independent characters `χ_s` live only on an infinite
group, where every conjugacy class is merely a limit of Frobenius classes, tex 9666–9668.) Hence
batch 3's `coefficientRules_of_model` and `coefficientRules_of_constituents` hold vacuously: a
leaf asking for a `TraceModel` can never be discharged. They are not wired into the address
package.

`TraceModelRel` is the minimal correction, faithful to tex 9666–9668 and 9745–9750: Chebotarev in
the finite quotient `G/N_U` (`frob q = h g h⁻¹ n` with `n ∈ N_U`, for `U` a set of good primes),
`N_U` fixing the `U`-extension (it contains the type fields and the fields `ℚ(√s*)`, `s ∈ U`:
`N_chi`), and `N_{U} ≤ N_{U'}` for `U' ⊆ U` (`N_anti`; the `U'`-extension lies in the
`U`-extension). `chi_surj` (independence of the characters) is also restricted to sets `U` of
good primes: stated for every `U` it fails for the genuine characters (`χ₁` is trivial, lane
RC24's `not_chi_surj_all`), and the proofs use it only at the good set of `O12Reading`. All other
fields are those of `TraceModel`, verbatim. PROVED here, exactly as
batch 3 proves them for `TraceModel` (the proofs of the first two do not use Chebotarev): the
fixed-`U` factorization (`fixedU_of_model`, RC12's `trace_square_invariance`), primary isolation
(`primary_of_model`), the (O.12) reading on prime sets with the product-label rule
(`o12_of_model`), hence `rulesUpTo_of_model` and `coefficientRules_of_model` (batch 3's
`rulesUpTo_symb`, `coefficientRules_symb`). The corrected structure is consistent:
`TraceModelRel.zero` is a model of the zero reading for every type data (PROVED; the group is
`L × (ℕ → 𝔽₂)` with the type and Legendre characters, Chebotarev by CRT and Dirichlet).

For the genuine objects (tex 9641–9771): `G = G_ℚ`, `frob q` a Frobenius element at `q`, `N_U` the
open normal subgroup fixing the compositum of the fields cut out by the reduced trace action on
the forms `F_{U'}`, `U' ⊆ U`, the type fields and `ℚ(√s*)`, `s ∈ U` (finite by continuity of
the scalar traces on the finite integral module, tex 9663–9669); Chebotarev in the finite group
`G_ℚ/N_U` is then exact.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Finset

/-! ## Batch 3's models are inconsistent -/

section Inconsistent

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- **Every good prime is a nonresidue modulo some other good prime** (PROVED: batch 3's
`realizeNat`, i.e. CRT and Dirichlet, gives a good `s ≠ q` of type `0` with `(s/q) = −1`, and
reciprocity with `ε(0) = 0` gives `(q/s) = −1`). -/
theorem exists_good_legBit_eq_one (T : TypeData L ε) {q : ℕ} (hq : T.Good q) :
    ∃ s : ℕ, T.Good s ∧ s ≠ q ∧ legBit q s = 1 := by
  obtain ⟨x, -, hx, hold, -⟩ := realizeNat T {q} ∅ (by simpa using hq) (fun _ => 0)
    (fun _ _ => 1) (fun _ _ => 0) 1
  obtain ⟨hs, hsq, -, hts⟩ := hx 0 (by norm_num)
  have hne : x 0 ≠ q := fun h => hsq (by simp [h])
  refine ⟨x 0, hs, hne, ?_⟩
  rw [T.legBit_rev hq hs (Ne.symm hne), hold 0 (by norm_num) q (mem_singleton_self q), hts,
    map_zero, mul_zero, add_zero]

/-- **Batch 3's `TraceModel` is inconsistent** (PROVED): its `chebotarev` at `g = 1` gives a good
prime `q` with `frob q = 1`; its `bit_frob` then forces `(q/s) = 1` at every good `s ≠ q`,
contradicting `exists_good_legBit_eq_one`. -/
theorem traceModel_false {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
    (X : TraceModel T R ap B) : False := by
  obtain ⟨q, h, hq, -, hf⟩ := X.chebotarev 1 ∅
  rw [mul_one, mul_inv_cancel] at hf
  obtain ⟨s, hs, hsq, hbit⟩ := exists_good_legBit_eq_one T hq
  have h1 := X.bit_frob q s hq hs (Ne.symm hsq)
  rw [hf, map_one, hbit, ← ofAdd_zero] at h1
  exact absurd (Multiplicative.ofAdd.injective h1) (by decide)

/-- **Batch 3's `ConstituentModel` is inconsistent** (PROVED; the same two fields). -/
theorem constituentModel_false {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    {B : ℕ} (X : ConstituentModel T R ap B) : False := by
  obtain ⟨q, h, hq, -, hf⟩ := X.chebotarev 1 ∅
  rw [mul_one, mul_inv_cancel] at hf
  obtain ⟨s, hs, hsq, hbit⟩ := exists_good_legBit_eq_one T hq
  have h1 := X.bit_frob q s hq hs (Ne.symm hsq)
  rw [hf, map_one, hbit, ← ofAdd_zero] at h1
  exact absurd (Multiplicative.ofAdd.injective h1) (by decide)

end Inconsistent

/-! ## The corrected trace model -/

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}

/-- **The trace-module model of lane RC12's readings, with Chebotarev in the finite quotients
`G/N_U`**, within the budget `B` (tex 9641–9771, 9905–9953). The fields are those of batch 3's
`TraceModel`, except `chebotarev` (relative to `N_U`, for `U` a set of good primes), `chi_surj`
(for `U` a set of good primes) and the two added fields `N_anti`, `N_chi` (definition of `N_U` as
the subgroup fixing the `U`-extension).
Kinds: `trace_mul`, `det_orbit`, `two_fresh`, `trace_one` are lane RC12's trace identities on the
reduced module (ELLIOT, tex 9705–9745); `level`, `kummer`, `chi_surj`, `chebotarev`, `t_class`,
`typ_frob`, `bit_frob` are GLUE (tex 9524–9548, 9663–9669, 9745–9750); `N_anti`, `N_chi` are
definition; `reading` (tex 9671–9704) and `o12` (tex 9905–9918) are ELLIOT inputs. Owner: RC12
(App F), batch 3 CoefficientDictionary. -/
structure TraceModelRel (T : TypeData L ε) (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ) where
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
  /-- the (open, normal) subgroup fixing the `U`-extension -/
  N : Finset ℕ → Subgroup G
  /-- the type characters -/
  chiType : G →* Multiplicative L
  /-- the character of `ℚ(√s*)` -/
  chiBit : ℕ → G →* Multiplicative (ZMod 2)
  /-- RC12 (tex 9734–9737): `t(g)t(h) = t(gh) + d(h)t(gh⁻¹)` -/
  trace_mul : ∀ g h (x : M), t g (t h x) = t (g * h) x + d h (t (g * h⁻¹) x)
  /-- RC12 (tex 9719–9733): `d` acts trivially on the trace orbit of `F_U` -/
  det_orbit : ∀ U u v, d u (t v (F U)) = t v (F U)
  /-- RC12 (tex 9741–9745): two fresh traces vanish -/
  two_fresh : ∀ U g h, t g (t h (F U)) = 0
  /-- RC12 (tex 9739): `t(1) = 2` -/
  trace_one : ∀ x, t 1 x = (2 : ZMod 2) • x
  /-- GLUE (level and continuity, tex 9524–9548, 9663–9669): `t(·)F_U` factors through `G/N_U` -/
  level : ∀ U g n, n ∈ N U → t (g * n) (F U) = t g (F U)
  /-- definition: the `U'`-extension lies in the `U`-extension for `U' ⊆ U` -/
  N_anti : ∀ U U', U' ⊆ U → N U ≤ N U'
  /-- definition: the `U`-extension contains the type fields and `ℚ(√s*)`, `s ∈ U` -/
  N_chi : ∀ U, ∀ n ∈ N U, chiType n = 1 ∧ ∀ s ∈ U, chiBit s n = 1
  /-- GLUE (Kummer, tex 9745–9750): an element with trivial type and trivial `U`-characters lies
  in the subgroup generated by the squares and `N_U` -/
  kummer : ∀ U g, chiType g = 1 → (∀ s ∈ U, chiBit s g = 1) →
    g ∈ Subgroup.closure (sqSet G) ⊔ N U
  /-- GLUE (independence of the quadratic characters at a set of good primes; for a non-good
  `s` the character of `ℚ(√s*)` need not be independent, e.g. `χ₁ = 1`) -/
  chi_surj : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (ℓ : L) (b : ℕ → ZMod 2), ∃ g,
    chiType g = Multiplicative.ofAdd ℓ ∧ ∀ s ∈ U, chiBit s g = Multiplicative.ofAdd (b s)
  /-- GLUE (Chebotarev in the finite group `G/N_U`): every class of `G/N_U` is the Frobenius class
  of a good prime outside any finite set -/
  chebotarev : ∀ (U : Finset ℕ), (∀ s ∈ U, T.Good s) → ∀ (g : G) (avoid : Finset ℕ),
    ∃ q h, ∃ n ∈ N U, T.Good q ∧ q ∉ avoid ∧ frob q = h * g * h⁻¹ * n
  /-- GLUE (`t(g)` is a limit of Hecke operators `T_q`, `Fr_q` in the class of `g`) -/
  t_class : ∀ g h, t (h * g * h⁻¹) = t g
  /-- GLUE (Frobenius dictionary): the type of `q` is `χ_type(Fr_q)` -/
  typ_frob : ∀ q, T.Good q → chiType (frob q) = Multiplicative.ofAdd (T.typ q)
  /-- GLUE (Frobenius dictionary): `(q/s) = (s*/q) = χ_s(Fr_q)` -/
  bit_frob : ∀ q s, T.Good q → T.Good s → q ≠ s →
    chiBit s (frob q) = Multiplicative.ofAdd (legBit q s)
  /-- ELLIOT (tex 9671–9704): the reading of a fresh vertex `q` adjoining `U` is the
  coefficient-one coefficient of `t(Fr_q) F_U` -/
  reading : ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
    (insert q U).card ≤ B → R (insert q U) = read U (t (frob q) (F U))
  /-- ELLIOT ((O.12) at coefficient one, tex 9905–9918), as in batch 3's `TraceModel.o12` -/
  o12 : ∀ (U : Finset ℕ) (p : ℕ), p ∈ U → (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g : G,
    ∃ (τ φ : G) (κ0 : ℤ), (κ0 = 1 ∨ κ0 = -1) ∧
      chiType τ = 1 ∧ (∀ s ∈ U, s ≠ p → chiBit s τ = 1) ∧
      chiBit p τ = Multiplicative.ofAdd 1 ∧
      chiType φ = Multiplicative.ofAdd (T.typ p) ∧
      (∀ s ∈ U, s ≠ p → chiBit s φ = Multiplicative.ofAdd (legBit p s)) ∧
      ((Cp (ap p) (-κ0) : ℤ) : ZMod 2) * read (U.erase p) (t (g * τ * φ) (F (U.erase p))) -
          ((Cp (ap p) κ0 : ℤ) : ZMod 2) * read (U.erase p) (t (g * φ) (F (U.erase p))) =
        read U (t (g * τ) (F U)) - read U (t g (F U))

namespace TraceModelRel

variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
  (X : TraceModelRel T R ap B)

attribute [instance] TraceModelRel.instG TraceModelRel.instM TraceModelRel.instMod

include X

/-- Invariance of `g ↦ t(g)F_U` under the subgroup generated by the squares and `N_U` (PROVED as
batch 3's `TraceModel.trace_join`). -/
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

/-- **The fixed-`U` factorization from RC12's square invariance** (tex 9745–9750; PROVED as batch
3's `TraceModel.fixedU_of_model`). -/
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

/-- **Primary isolation from RC12's square invariance and `t(1) = 2`** (tex 9739, 9947–9948;
PROVED as batch 3's `TraceModel.primary_of_model`). -/
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

/-- **The (O.12) reading from the module-level identity and Chebotarev representatives in
`G/N_U`** (tex 9905–9945; PROVED, batch 3's `TraceModel.o12_of_model` with the representatives'
Frobenius in the classes of `g, gτ, gφ, gτφ` modulo `N_U`; `N_U` does not move the labels at `U`
(`N_chi`) nor the traces on `F_U`, `F_{U∖p}` (`level`, `N_anti`)). -/
theorem o12_of_model : O12Reading T R ap B := by
  intro U p hpU hU hUB ℓ bq
  obtain ⟨g, hgT, hgB⟩ := X.chi_surj U hU ℓ bq
  obtain ⟨τ, φ, κ0, hκ, hτT, hτB, hτp, hφT, hφB, hO⟩ := X.o12 U p hpU hU hUB g
  obtain ⟨q, h1, n1, hn1, hq, hqU, hfq⟩ := X.chebotarev U hU g U
  obtain ⟨qτ, h2, n2, hn2, hqτ, hqτU, hfqτ⟩ := X.chebotarev U hU (g * τ) U
  obtain ⟨r0, h3, n3, hn3, hr0, hr0U, hfr0⟩ := X.chebotarev U hU (g * φ) U
  obtain ⟨r1, h4, n4, hn4, hr1, hr1U, hfr1⟩ := X.chebotarev U hU (g * τ * φ) U
  have ne_of : ∀ {x s : ℕ}, x ∉ U → s ∈ U → x ≠ s := fun hx hs h => hx (h ▸ hs)
  -- types
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
  -- bits
  have bit_of : ∀ {x : ℕ} {y h n : X.G}, n ∈ X.N U → T.Good x → x ∉ U →
      X.frob x = h * y * h⁻¹ * n → ∀ s ∈ U, Multiplicative.ofAdd (legBit x s) = X.chiBit s y := by
    intro x y h n hn hx hxU hf s hs
    rw [← X.bit_frob x s hx (hU s hs) (ne_of hxU hs), hf, map_mul, (X.N_chi U n hn).2 s hs,
      mul_one, X.chiBit_conj]
  -- traces
  have t_of : ∀ {U' : Finset ℕ} {x : ℕ} {y h n : X.G}, U' ⊆ U → n ∈ X.N U →
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
/-- **RC2's rules within a budget from the corrected model** (the odd source at one stage;
PROVED from batch 3's `rulesUpTo_symb`). -/
theorem rulesUpTo_of_model {W : ℕ} (X : TraceModelRel T R ap (W + 1)) (hap : ApEven T ap) :
    RulesUpTo ε (symb T R) W :=
  rulesUpTo_symb T R ap W X.fixedU_of_model X.o12_of_model hap X.primary_of_model

end TraceModelRel

/-- **RC2's coefficient rules from the corrected model at every budget** (the even source;
PROVED from batch 3's `coefficientRules_symb`). -/
theorem coefficientRules_of_modelRel {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ}
    (X : ∀ B, TraceModelRel T R ap B) (hap : ApEven T ap) : CoefficientRules ε (symb T R) :=
  coefficientRules_symb T R ap (fun B => (X B).fixedU_of_model) (fun B => (X B).o12_of_model)
    hap (fun B => (X B).primary_of_model)

/-! ## The corrected model is consistent -/

section Zero

variable {L₀ : Type} [AddCommGroup L₀] {ε₀ : L₀ →+ ZMod 2}

/-- The type character of the witness group `L × (ℕ → 𝔽₂)`. -/
def zeroChiType (L₀ : Type) [AddCommGroup L₀] :
    Multiplicative (L₀ × (ℕ → ZMod 2)) →* Multiplicative L₀ :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.fst L₀ (ℕ → ZMod 2))

/-- The Legendre characters of the witness group. -/
def zeroChiBit (L₀ : Type) [AddCommGroup L₀] (s : ℕ) :
    Multiplicative (L₀ × (ℕ → ZMod 2)) →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative
    ((Pi.evalAddMonoidHom (fun _ : ℕ => ZMod 2) s).comp (AddMonoidHom.snd L₀ (ℕ → ZMod 2)))

theorem zeroChiType_apply (x : Multiplicative (L₀ × (ℕ → ZMod 2))) :
    zeroChiType L₀ x = Multiplicative.ofAdd (Multiplicative.toAdd x).1 := rfl

theorem zeroChiBit_apply (s : ℕ) (x : Multiplicative (L₀ × (ℕ → ZMod 2))) :
    zeroChiBit L₀ s x = Multiplicative.ofAdd ((Multiplicative.toAdd x).2 s) := rfl

/-- The subgroup `N_U` of the witness: trivial type and trivial characters at `U`. -/
def zeroN (L₀ : Type) [AddCommGroup L₀] (U : Finset ℕ) :
    Subgroup (Multiplicative (L₀ × (ℕ → ZMod 2))) :=
  (zeroChiType L₀).ker ⊓ ⨅ s ∈ U, (zeroChiBit L₀ s).ker

theorem mem_zeroN {U : Finset ℕ} {n : Multiplicative (L₀ × (ℕ → ZMod 2))} :
    n ∈ zeroN L₀ U ↔ zeroChiType L₀ n = 1 ∧ ∀ s ∈ U, zeroChiBit L₀ s n = 1 := by
  simp only [zeroN, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]

/-- **Non-vacuity of `TraceModelRel`** (PROVED): for every type data, budget and `a_p`, a model
of the zero reading. The group is `L × (ℕ → 𝔽₂)` with `frob q = (type of q, s ↦ (q/s))`, the
module is trivial; Chebotarev in `G/N_U` is batch 3's `realizeNat` (CRT and Dirichlet). -/
def TraceModelRel.zero (T : TypeData L₀ ε₀) (ap : ℕ → ℤ) (B : ℕ) :
    TraceModelRel T (fun _ => 0) ap B where
  G := Multiplicative (L₀ × (ℕ → ZMod 2))
  M := PUnit
  t _ := 0
  d _ := 0
  F _ := PUnit.unit
  read _ := 0
  frob q := Multiplicative.ofAdd (T.typ q, fun s => legBit q s)
  N := zeroN L₀
  chiType := zeroChiType L₀
  chiBit := zeroChiBit L₀
  trace_mul _ _ _ := Subsingleton.elim _ _
  det_orbit _ _ _ := Subsingleton.elim _ _
  two_fresh _ _ _ := Subsingleton.elim _ _
  trace_one _ := Subsingleton.elim _ _
  level _ _ _ _ := Subsingleton.elim _ _
  N_anti U U' hU' n hn := by
    rw [mem_zeroN] at hn ⊢
    exact ⟨hn.1, fun s hs => hn.2 s (hU' hs)⟩
  N_chi U n hn := mem_zeroN.mp hn
  kummer U g h1 h2 := Subgroup.mem_sup_right (mem_zeroN.mpr ⟨h1, h2⟩)
  chi_surj U _ ℓ b := ⟨Multiplicative.ofAdd (ℓ, b), rfl, fun _ _ => rfl⟩
  chebotarev U hU g avoid := by
    obtain ⟨x, -, hx, hold, -⟩ := realizeNat T U avoid hU
      (fun _ => (Multiplicative.toAdd g).1) (fun _ s => (Multiplicative.toAdd g).2 s)
      (fun _ _ => 0) 1
    obtain ⟨hq, hqU, hqa, htq⟩ := hx 0 (by norm_num)
    refine ⟨x 0, 1, g⁻¹ * Multiplicative.ofAdd (T.typ (x 0), fun s => legBit (x 0) s),
      mem_zeroN.mpr ⟨?_, fun s hs => ?_⟩, hq, hqa, by group⟩
    · rw [map_mul, map_inv, zeroChiType_apply, zeroChiType_apply, toAdd_ofAdd, htq,
        inv_mul_cancel]
    · rw [map_mul, map_inv, zeroChiBit_apply, zeroChiBit_apply, toAdd_ofAdd]
      dsimp only
      rw [hold 0 (by norm_num) s hs, inv_mul_cancel]
  t_class _ _ := rfl
  typ_frob _ _ := rfl
  bit_frob _ _ _ _ _ := rfl
  reading _ _ _ _ _ _ := rfl
  o12 U p _ _ _ g := by
    refine ⟨Multiplicative.ofAdd (0, Pi.single p 1),
      Multiplicative.ofAdd (T.typ p, fun s => legBit p s), 1, Or.inl rfl, ?_,
      fun s _ hsp => ?_, ?_, rfl, fun _ _ _ => rfl, ?_⟩
    · rw [zeroChiType_apply, toAdd_ofAdd, ofAdd_zero]
    · rw [zeroChiBit_apply, toAdd_ofAdd]
      dsimp only
      rw [Pi.single_eq_of_ne hsp, ofAdd_zero]
    · rw [zeroChiBit_apply, toAdd_ofAdd]
      dsimp only
      rw [Pi.single_eq_same]
    · simp

/-- The corrected model of the zero reading at every budget (PROVED). -/
theorem traceModelRel_zero_nonempty (T : TypeData L₀ ε₀) (ap : ℕ → ℤ) (B : ℕ) :
    Nonempty (TraceModelRel T (fun _ => 0) ap B) :=
  ⟨TraceModelRel.zero T ap B⟩

end Zero

end ZInQ.Manuscript.RC.Wiring
