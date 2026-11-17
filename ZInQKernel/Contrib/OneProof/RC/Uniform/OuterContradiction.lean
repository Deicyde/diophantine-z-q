import Mathlib

/-!
# Lane RC16: the outer-DVR contradiction behind the uniform lower bound (5.5)

Manuscript (11/5), Proposition `ex:limits-uniform-lower-bound`, proof, tex lines 4935–4972:

> Suppose no uniform lower bound exists. Choose instances with `v₂u_j → −∞`, `ω(k_j) ≤ A`, and write
> their minimal completed models as `[𝒪_jⁿ --D_j--> 𝒪_jⁿ]`, fixing the bounded `n` on an outer-large
> set. [...] There can be only finitely many drops. [...] At terminal outer dimension one a maximal
> boundary minor `Δ` is nonzero. Its inner minors have one finite valuation `b` on an outer-large set.
> Determinant-one Schur operations in a square two-term rank-one-kernel complex give `u = ±αβ/Δ`,
> where `α` is an integral surviving cycle coordinate and `β` has valuation at least `−a`.
> Consequently `v₂u_j ≥ −a−b`, the required contradiction.

What is formalized here (all `PROVED`):

* `OuterNegligible`: the ideal of (5.3) (tex 4706–4712): sequences whose valuation tends to infinity
  along the outer ultrafilter; a sequence is a nonzero element of `𝒪_∞` iff it is not negligible.
* `exists_eventually_valuation_eq`: "A nonzero element has valuation one fixed nonnegative integer on
  a set in `𝒰`" (tex 4713–4714), for the sequence of inner minors.
* `terminal_lower_bound`: from `u_j Δ_j = ±α_jβ_j` (the Cramer/Schur formula, proved in
  `Determinant.lean` for every nonzero maximal minor), `α_j` integral, `v β_j ≥ −a` and `Δ` nonzero
  in `𝒪_∞`, one gets `v u_j ≥ −a−b` on an outer-large set.
* `switch_descent`: the bookkeeping of the switches: the outer dimension drops by two at each switch
  (tex 4940–4945), never reaches zero (tex 4950–4952), and each switch keeps the inner valuation
  (tex 4947–4950, the switch lemma), so finitely many switches reach outer dimension one
  ("There can be only finitely many drops", tex 4953).
* `outer_contradiction` and `uniform_lower_bound_of_switchProcess`: the proof by contradiction of (5.5).
* `outerNonzero_needed`: Elliot's remark "Bounded matrix size alone would not prove it: `[2^j]` is a
  counterexample to that inference" (tex 4970–4972): without the outer nonvanishing of the minor all
  other terminal hypotheses hold while `v u_j → −∞`.

The cohomological inputs (the finite free models of bounded size from (5.1), the outer DVR (5.3), the
evaluation injection, rank-two detection (5.4) and the switch triangles) are collected as the fields of
the structure `OuterSwitchProcess`, each with its tex lines: they are Elliot's steps (`ELLIOT`), whose
algebraic cores are proved in the companion files `KernelDetection.lean`, `Switch.lean`,
`QuadraticCase.lean` and `Determinant.lean` of this lane.

`DEPARTURE` (form only): the valuation `v₂` of `𝒪` is an arbitrary additive valuation
`v : AddValuation K (WithTop ℤ)` on a field `K` (in the text `K` is the fraction field of
`𝒪 = (ℤ₂[[t]]_{(2)})^`, all `𝒪_j` being copies of `𝒪`); the outer quotient (5.3) enters only through
its ideal `OuterNegligible`, which is all the argument uses. The ring `𝒪_∞` itself and its DVR property
are lane RC6.
-/

namespace ZInQ.Manuscript.RC.Uniform

open Filter

section Outer

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) {ι : Type*} (𝒰 : Ultrafilter ι)

/-- The ideal of the outer quotient (5.3), tex 4706–4712:
`𝒪_∞ = (∏_𝒰 𝒪_j) / {(x_j) : v₂(x_j) →_𝒰 ∞}`. A sequence `x` represents zero in `𝒪_∞` iff
`OuterNegligible v 𝒰 x`. Kind: definition. -/
def OuterNegligible (x : ι → K) : Prop :=
  ∀ N : ℤ, ∀ᶠ j in (𝒰 : Filter ι), (N : WithTop ℤ) ≤ v (x j)

/-- Helper: an ultrafilter-eventual bound `0 ≤ v < M` on integer-valued data pins one value. -/
theorem exists_eventually_eq_of_bounded (f : ι → WithTop ℤ) :
    ∀ M : ℕ, (∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ f j ∧ f j < ((M : ℤ) : WithTop ℤ)) →
      ∃ b : ℕ, b < M ∧ ∀ᶠ j in (𝒰 : Filter ι), f j = ((b : ℤ) : WithTop ℤ) := by
  intro M
  induction M with
  | zero =>
    intro h
    obtain ⟨j, hj0, hj1⟩ := h.exists
    exact absurd (lt_of_le_of_lt hj0 hj1) (by simp)
  | succ M ih =>
    intro h
    rcases (Ultrafilter.eventually_or).1
        (Eventually.of_forall (fun j => em (f j = ((M : ℤ) : WithTop ℤ))) :
          ∀ᶠ j in (𝒰 : Filter ι), f j = ((M : ℤ) : WithTop ℤ) ∨ ¬ f j = ((M : ℤ) : WithTop ℤ))
      with hM | hM
    · exact ⟨M, Nat.lt_succ_self M, hM⟩
    · obtain ⟨b, hb, hbe⟩ := ih (by
        filter_upwards [h, hM] with j hj hjM
        refine ⟨hj.1, ?_⟩
        have hlt := hj.2
        -- `f j < M + 1` and `f j ≠ M` give `f j < M`
        induction hfj : f j using WithTop.recTopCoe with
        | top => rw [hfj] at hlt; exact absurd hlt (by simp)
        | coe m =>
          rw [hfj] at hlt hjM
          have h1 : m < ((M + 1 : ℕ) : ℤ) := by exact_mod_cast hlt
          have h2 : m ≠ (M : ℤ) := fun e => hjM (by rw [e])
          have : m < (M : ℤ) := by push_cast at h1; omega
          exact_mod_cast this)
      exact ⟨b, Nat.lt_succ_of_lt hb, hbe⟩

/-- tex 4713–4714 ("A nonzero element has valuation one fixed nonnegative integer on a set in `𝒰`"),
for an integral sequence: if `x` is integral on an outer-large set and is not negligible (a nonzero
element of `𝒪_∞`), then its valuation is one fixed natural number `b` on an outer-large set.
This is "Its inner minors have one finite valuation `b` on an outer-large set" (tex 4958–4959).
Kind: PROVED. -/
theorem exists_eventually_valuation_eq (x : ι → K)
    (hint : ∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (x j))
    (hx : ¬ OuterNegligible v 𝒰 x) :
    ∃ b : ℕ, ∀ᶠ j in (𝒰 : Filter ι), v (x j) = ((b : ℤ) : WithTop ℤ) := by
  simp only [OuterNegligible, not_forall] at hx
  obtain ⟨N, hN⟩ := hx
  have hlt : ∀ᶠ j in (𝒰 : Filter ι), v (x j) < (N : WithTop ℤ) := by
    have h' : ∀ᶠ j in (𝒰 : Filter ι), ¬ (N : WithTop ℤ) ≤ v (x j) :=
      (Ultrafilter.eventually_not).2 hN
    filter_upwards [h'] with j hj
    exact lt_of_not_ge hj
  obtain ⟨b, -, hb⟩ := exists_eventually_eq_of_bounded 𝒰 (fun j => v (x j)) N.toNat (by
    filter_upwards [hint, hlt] with j hj0 hj1
    refine ⟨hj0, lt_of_lt_of_le hj1 ?_⟩
    exact_mod_cast Int.self_le_toNat N)
  exact ⟨b, hb⟩

/-- Valuation of a sign `±1`. -/
theorem valuation_sign {s : K} (hs : s = 1 ∨ s = -1) : v s = 0 := by
  rcases hs with rfl | rfl
  · exact AddValuation.map_one v
  · rw [AddValuation.map_neg, AddValuation.map_one]

/-- The terminal estimate, tex 4957–4962: at terminal outer dimension one, with the Schur/Cramer formula
`u_j = ±α_jβ_j/Δ_j` in the multiplied-out form `u_j Δ_j = ±α_jβ_j` (proved for every nonzero maximal
minor in `Determinant.lean`, `classFunctionalCoord_cramer`), `α_j` an integral surviving cycle
coordinate, `v β_j ≥ −a` (the fixed functional exponent of `ex:arith-paired-functional`, kept after the
switches, gap B2-b), and the inner minors `Δ_j` integral and nonzero in `𝒪_∞`, one gets
`v₂ u_j ≥ −a − b` on an outer-large set. Kind: PROVED. -/
theorem terminal_lower_bound (a : ℕ) (u α β Δ s : ι → K) (hs : ∀ j, s j = 1 ∨ s j = -1)
    (hcr : ∀ᶠ j in (𝒰 : Filter ι), u j * Δ j = s j * (α j * β j))
    (hα : ∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (α j))
    (hβ : ∀ᶠ j in (𝒰 : Filter ι), (((-a : ℤ)) : WithTop ℤ) ≤ v (β j))
    (hΔint : ∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (Δ j))
    (hΔ : ¬ OuterNegligible v 𝒰 Δ) :
    ∃ b : ℕ, ∀ᶠ j in (𝒰 : Filter ι), (((-a - b : ℤ)) : WithTop ℤ) ≤ v (u j) := by
  obtain ⟨b, hb⟩ := exists_eventually_valuation_eq v 𝒰 Δ hΔint hΔ
  refine ⟨b, ?_⟩
  filter_upwards [hcr, hα, hβ, hb] with j hj hαj hβj hbj
  have key : v (u j) + v (Δ j) = v (α j) + v (β j) := by
    have := congrArg v hj
    rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul,
      valuation_sign v (hs j), zero_add] at this
    exact this
  rw [hbj] at key
  -- work in `WithTop ℤ`
  induction hu : v (u j) using WithTop.recTopCoe with
  | top => exact le_top
  | coe m =>
    rw [hu] at key
    induction hA : v (α j) using WithTop.recTopCoe with
    | top =>
      rw [hA] at key
      exact absurd key (by rw [top_add]; exact WithTop.coe_ne_top)
    | coe p =>
      rw [hA] at key hαj
      induction hB : v (β j) using WithTop.recTopCoe with
      | top =>
        rw [hB] at key
        exact absurd key (by rw [add_top]; exact WithTop.coe_ne_top)
      | coe q =>
        rw [hB] at key hβj
        have hkey : m + (b : ℤ) = p + q := by exact_mod_cast key
        have hp : (0 : ℤ) ≤ p := by exact_mod_cast hαj
        have hq : -(a : ℤ) ≤ q := by exact_mod_cast hβj
        have : -(a : ℤ) - b ≤ m := by omega
        exact_mod_cast this

/-- The outer switching process along one sequence of ring instances and one outer ultrafilter
(tex 4935–4964). Each field is one of Elliot's steps, taken as an input here (`ELLIOT`); the algebra
behind each is proved in the companion files of this lane:

* `outerDim S` is the outer kernel dimension `s` of the configuration `S` (the dimension of the generic
  kernel of the outer minimal model over the fraction field of `𝒪_∞`), and `coord S j` is the inner
  class-functional coordinate `u_j` at that configuration.
* `pos`: tex 4938–4940 and 4950–4952 — the inner kernels have primitive vectors whose outer image is
  nonzero, "so the outer kernel dimension `s` is at least one"; "a proposed drop to zero is already a
  contradiction".
* `switch`: tex 4940–4950 — if `s > 1`, one new derivative prime gives a rank-two localization including
  the primitive vector (`KernelDetection.lean`), the relaxed image equals the finite plane
  (`Switch.lean`, `relaxed_image_eq_span`), the new outer dimension is `s − 2`, and "exact switch
  preservation therefore keeps each inner determinant valuation" (`Switch.lean`,
  `switch_equal_valuation`) on an outer-large set. (5.1) bounds the models for each fixed number of
  switches (tex 4953–4955), which is why the outer model of the next configuration exists.
* `terminal`: tex 4957–4961 — at terminal outer dimension one a maximal boundary minor `Δ` is nonzero in
  `𝒪_∞`, and `u_j Δ_j = ±α_jβ_j` (`Determinant.lean`) with `α_j` integral and `v β_j ≥ −a`.
-/
structure OuterSwitchProcess (a : ℕ) where
  /-- The configurations reached by successive switches. -/
  Stage : Type
  /-- The outer kernel dimension `s` of a configuration. -/
  outerDim : Stage → ℕ
  /-- The inner class-functional coordinates `u_j` of a configuration. -/
  coord : Stage → ι → K
  /-- tex 4938–4940, 4950–4952: the outer kernel dimension is at least one. -/
  pos : ∀ S, 1 ≤ outerDim S
  /-- tex 4940–4950: a switch lowers the outer dimension by two and keeps the inner valuations. -/
  switch : ∀ S, 1 < outerDim S → ∃ S', outerDim S' + 2 = outerDim S ∧
    ∀ᶠ j in (𝒰 : Filter ι), v (coord S' j) = v (coord S j)
  /-- tex 4957–4961: the terminal Schur/Cramer data. -/
  terminal : ∀ S, outerDim S = 1 → ∃ (α β Δ s : ι → K), (∀ j, s j = 1 ∨ s j = -1) ∧
    (∀ᶠ j in (𝒰 : Filter ι), coord S j * Δ j = s j * (α j * β j)) ∧
    (∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (α j)) ∧
    (∀ᶠ j in (𝒰 : Filter ι), (((-a : ℤ)) : WithTop ℤ) ≤ v (β j)) ∧
    (∀ᶠ j in (𝒰 : Filter ι), (0 : WithTop ℤ) ≤ v (Δ j)) ∧
    ¬ OuterNegligible v 𝒰 Δ

/-- The switch descent (tex 4940–4955): along a switching process, from any configuration whose inner
valuations agree on an outer-large set with a given sequence `u₀`, finitely many switches reach outer
dimension one with the same valuations; at that point the terminal estimate applies. Hence
`v u₀ j ≥ −a − b` on an outer-large set for some `b`. Kind: PROVED (strong induction on `s`). -/
theorem switch_descent {a : ℕ} (P : OuterSwitchProcess v 𝒰 a) (u₀ : ι → K) :
    ∀ m : ℕ, ∀ S : P.Stage, P.outerDim S = m →
      (∀ᶠ j in (𝒰 : Filter ι), v (P.coord S j) = v (u₀ j)) →
      ∃ b : ℕ, ∀ᶠ j in (𝒰 : Filter ι), (((-a - b : ℤ)) : WithTop ℤ) ≤ v (u₀ j) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hS hval
    rcases lt_trichotomy (P.outerDim S) 1 with h | h | h
    · exact absurd (P.pos S) (by omega)
    · obtain ⟨α, β, Δ, s, hs, hcr, hα, hβ, hΔi, hΔ⟩ := P.terminal S h
      obtain ⟨b, hb⟩ := terminal_lower_bound v 𝒰 a (P.coord S) α β Δ s hs hcr hα hβ hΔi hΔ
      refine ⟨b, ?_⟩
      filter_upwards [hb, hval] with j hj hj'
      rw [← hj']
      exact hj
    · obtain ⟨S', hS', hval'⟩ := P.switch S h
      exact ih (P.outerDim S') (by omega) S' rfl (by
        filter_upwards [hval', hval] with j h1 h2
        rw [h1, h2])

/-- The proof by contradiction of (5.5) along one sequence (tex 4935–4964): if `v₂ u_j → −∞` along
the outer ultrafilter, and the inner coordinates of some configuration of a switching process have the
same valuations as the `u_j` on an outer-large set, we reach a contradiction. Kind: PROVED. -/
theorem outer_contradiction {a : ℕ} (P : OuterSwitchProcess v 𝒰 a) (u : ι → K)
    (S₀ : P.Stage) (hstart : ∀ᶠ j in (𝒰 : Filter ι), v (P.coord S₀ j) = v (u j))
    (hdiv : ∀ N : ℤ, ∀ᶠ j in (𝒰 : Filter ι), v (u j) ≤ (N : WithTop ℤ)) : False := by
  obtain ⟨b, hb⟩ := switch_descent v 𝒰 P u (P.outerDim S₀) S₀ rfl hstart
  have h1 := hdiv (-(a : ℤ) - b - 1)
  obtain ⟨j, hj1, hj2⟩ := (hb.and h1).exists
  have h3 := le_trans hj1 hj2
  have h4 : -(a : ℤ) - b ≤ -(a : ℤ) - b - 1 := by exact_mod_cast h3
  omega

/-- (5.5), tex 4909–4964: `v₂ u_prim ≥ −C(E,A)` uniformly over the known simple-zero ring instances with
`ω(k) ≤ A`. The input `inputs` says: for every sequence of such instances, along the fixed nonprincipal
ultrafilter `hyperfilter ℕ` there is a switching process whose starting configuration has the primitive
coordinates' valuations (the starting configuration is the minimal model itself; its outer kernel
dimension is at least one because the inner generic kernels have rank one, tex 4927–4940). The constant
is not effective (it comes from an ultrafilter contradiction; map D6). Kind: PROVED from the inputs. -/
theorem uniform_lower_bound_of_switchProcess {Inst : Type*} (uprim : Inst → K)
    (inputs : ∀ inst : ℕ → Inst, ∃ (a : ℕ) (P : OuterSwitchProcess v (Filter.hyperfilter ℕ) a)
      (S₀ : P.Stage), ∀ᶠ j in ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
        v (P.coord S₀ j) = v (uprim (inst j))) :
    ∃ C : ℕ, ∀ i, (((-C : ℤ)) : WithTop ℤ) ≤ v (uprim i) := by
  by_contra hcon
  simp only [not_exists, not_forall, not_le] at hcon
  choose inst hinst using hcon
  obtain ⟨a, P, S₀, hS₀⟩ := inputs inst
  refine outer_contradiction v (Filter.hyperfilter ℕ) P (fun j => uprim (inst j)) S₀ hS₀ ?_
  intro N
  have hcof : ∀ᶠ j in (Filter.cofinite : Filter ℕ), v (uprim (inst j)) ≤ (N : WithTop ℤ) := by
    rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
    refine ⟨(-N).toNat, fun j hj => ?_⟩
    refine le_of_lt (lt_of_lt_of_le (hinst j) ?_)
    have : -(j : ℤ) ≤ N := by
      have := Int.self_le_toNat (-N)
      have h2 : ((-N).toNat : ℤ) ≤ j := by exact_mod_cast hj
      omega
    exact_mod_cast this
  exact Filter.hyperfilter_le_cofinite hcof

end Outer

section Examples

/-- Non-vacuity of `OuterSwitchProcess`: over `ℚ₂` with its 2-adic valuation, the one-configuration
process with outer dimension one, coordinate `1` and terminal data `α = β = Δ = 1` satisfies every
field. Kind: PROVED. -/
noncomputable def trivialSwitchProcess {ι : Type*} (𝒰 : Ultrafilter ι) :
    OuterSwitchProcess (Padic.addValuation (p := 2)) 𝒰 0 where
  Stage := Unit
  outerDim := fun _ => 1
  coord := fun _ _ => 1
  pos := fun _ => le_rfl
  switch := fun _ h => absurd h (lt_irrefl 1)
  terminal := fun _ _ => by
    refine ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => Or.inl rfl,
      Eventually.of_forall (fun _ => by ring), ?_, ?_, ?_, ?_⟩
    · exact Eventually.of_forall (fun _ => by rw [AddValuation.map_one])
    · exact Eventually.of_forall (fun _ => by rw [AddValuation.map_one]; simp)
    · exact Eventually.of_forall (fun _ => by rw [AddValuation.map_one])
    · intro h
      obtain ⟨j, hj⟩ := (h 1).exists
      rw [AddValuation.map_one] at hj
      exact absurd hj (by exact_mod_cast (by norm_num : ¬ (1 : ℤ) ≤ 0))

/-- tex 4970–4972, "Bounded matrix size alone would not prove it: `[2^j]` is a counterexample to that
inference." Over `ℚ₂`, the terminal data `Δ_j = 2^j` (the minor of the two-by-two complexes
`diag(2^j, 0)`), `α_j = β_j = 1`, `u_j = 2^{−j}` satisfy the Cramer relation, the integrality of `α`, `Δ`
and `v β ≥ 0`, while `v₂ u_j = −j → −∞`. So the outer nonvanishing of the minor (`¬ OuterNegligible`)
cannot be dropped from `OuterSwitchProcess.terminal`: here the minors are negligible. Kind: PROVED. -/
theorem outerNonzero_needed :
    let v := (Padic.addValuation (p := 2))
    let u : ℕ → ℚ_[2] := fun j => ((2 : ℚ_[2]) ^ j)⁻¹
    let Δ : ℕ → ℚ_[2] := fun j => (2 : ℚ_[2]) ^ j
    (∀ j, u j * Δ j = 1 * (1 * 1)) ∧ (∀ j, (0 : WithTop ℤ) ≤ v (Δ j)) ∧
      OuterNegligible v (Filter.hyperfilter ℕ) Δ ∧
      (∀ N : ℤ, ∀ᶠ j in ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
        v (u j) ≤ (N : WithTop ℤ)) := by
  intro v u Δ
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have hv2 : v (2 : ℚ_[2]) = 1 := by
    show Padic.addValuation (2 : ℚ_[2]) = 1
    rw [Padic.addValuation.apply h2]
    have : (2 : ℚ_[2]).valuation = 1 := by
      have := Padic.valuation_p (p := 2)
      exact_mod_cast this
    rw [this]; rfl
  have hvΔ : ∀ j : ℕ, v (Δ j) = ((j : ℤ) : WithTop ℤ) := by
    intro j
    show v ((2 : ℚ_[2]) ^ j) = _
    rw [AddValuation.map_pow, hv2]
    simp
  have hvu : ∀ j : ℕ, v (u j) = (((-(j : ℤ) : ℤ)) : WithTop ℤ) := by
    intro j
    have hm : v (u j) + v (Δ j) = 0 := by
      rw [← AddValuation.map_mul]
      have : u j * Δ j = 1 := inv_mul_cancel₀ (pow_ne_zero j h2)
      rw [this, AddValuation.map_one]
    rw [hvΔ j] at hm
    induction h : v (u j) using WithTop.recTopCoe with
    | top => rw [h] at hm; exact absurd hm (by simp)
    | coe m =>
      rw [h] at hm
      have : m + j = 0 := by exact_mod_cast hm
      have : m = -(j : ℤ) := by omega
      exact congrArg _ this
  refine ⟨fun j => by simp [u, Δ], fun j => ?_, ?_, ?_⟩
  · rw [hvΔ j]; exact_mod_cast (Int.natCast_nonneg j)
  · intro N
    have hcof : ∀ᶠ j in (Filter.cofinite : Filter ℕ), (N : WithTop ℤ) ≤ v (Δ j) := by
      rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
      refine ⟨N.toNat, fun j hj => ?_⟩
      rw [hvΔ j]
      have := Int.self_le_toNat N
      have h3 : (N.toNat : ℤ) ≤ j := by exact_mod_cast hj
      exact_mod_cast (by omega : N ≤ (j : ℤ))
    exact Filter.hyperfilter_le_cofinite hcof
  · intro N
    have hcof : ∀ᶠ j in (Filter.cofinite : Filter ℕ), v (u j) ≤ (N : WithTop ℤ) := by
      rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
      refine ⟨(-N).toNat, fun j hj => ?_⟩
      rw [hvu j]
      have := Int.self_le_toNat (-N)
      have h3 : ((-N).toNat : ℤ) ≤ j := by exact_mod_cast hj
      exact_mod_cast (by omega : -(j : ℤ) ≤ N)
    exact Filter.hyperfilter_le_cofinite hcof

end Examples

end ZInQ.Manuscript.RC.Uniform
