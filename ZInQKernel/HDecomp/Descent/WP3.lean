import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.Conductor.I6Base

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-wp3/WP3.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-wp3: glue-descent's `LeafHasse`, `LeafLocalTwo` from the announced leaves T14-T15

The leaf bundle (`scratch/h-decomposition/Leaves.lean`, `HSyn` bundle fields `t14a`, `t14b`,
`t15`) announces the Brauer facts as pkg-I6's cochain forms I6.2a′-c′
(`PkgI6.BrauerHasse2C`, `PkgI6.BrauerReciprocity2C`, `PkgI6.LocalH2CardC`: continuous
inhomogeneous cochains `G × G → ZMod 2`, all places including `∞`).  glue-descent proved B2-B3
(`GlueDescent.B3Q.b3_degree_le_QM`) from its own forms `GlueDescent.B2Q.LeafHasse`,
`LeafLocalTwo` (locally constant `ℂˣ`-valued cochains with square `1`, finite places only).

This file proves (no sorry; axioms propext, Classical.choice, Quot.sound):

* `leafHasse_of_T14 : BrauerHasse2C → BrauerReciprocity2C → LeafHasse`
* `leafLocalTwo_of_T15 : LocalH2CardC → LeafLocalTwo`
* `b3_degree_le_QM_of_T14_T15`: glue-descent's B2-B3 theorem with `LeafHasse`, `LeafLocalTwo`
  replaced by the announced T14-T15.

The glue is (i) the dictionary `±1 ⊂ ℂˣ` ↔ `ZMod 2` (`sgn`, `unsgn`) between the two cochain
languages, compatible with cocycles, coboundaries and restriction along `G_{ℚ_p} → G_ℚ` (both
sides use the same Mathlib map `Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])`), and
(ii) the real place: a class trivial at every finite prime is trivial at `∞` by reciprocity
(the parity of the number of ramified places).

The definitions of `PkgI6` below are verbatim copies of `scratch/pkg-I6/I6.lean` (identical to
the copies in `scratch/h-decomposition/Leaves.lean`, L4155-4194); `GlueDescent.*` comes from
verbatim copies of glue-descent's files in this directory.
-/

/-! The `PkgI6` cochain definitions and leaves are imported from
`ZInQKernel.HDecomp.Conductor.I6Base`. -/

noncomputable section

namespace GlueWP3

open GlueDescent.B2 GlueDescent.B2Q PkgI6

/-! ## The dictionary `ZMod 2` ↔ `±1 ⊂ ℂˣ` -/

/-- `ZMod 2 → ±1 ⊂ ℂˣ`, `0 ↦ 1`, `1 ↦ -1`. -/
def sgn (a : ZMod 2) : ℂˣ := if a = 0 then 1 else -1

/-- `±1 → ZMod 2`, `1 ↦ 0`, anything else `↦ 1`. -/
def unsgn (s : ℂˣ) : ZMod 2 := if s = 1 then 0 else 1

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

theorem sgn_one : sgn 1 = -1 := by simp [sgn]

theorem neg_one_ne_one : (-1 : ℂˣ) ≠ 1 := by
  intro h
  have := congrArg (fun u : ℂˣ => (u : ℂ)) h
  norm_num at this

theorem sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [sgn]
  · simp [sgn]
  · simp [sgn]
  · have : (1 + 1 : ZMod 2) = 0 := by decide
    rw [this, sgn_zero, sgn_one]; simp

theorem sgn_neg (a : ZMod 2) : sgn (-a) = sgn a := by
  rcases zmod2_cases a with rfl | rfl
  · simp
  · have : (-1 : ZMod 2) = 1 := by decide
    rw [this]

theorem sgn_sub (a b : ZMod 2) : sgn (a - b) = sgn a * sgn b := by
  rw [sub_eq_add_neg, sgn_add, sgn_neg]

theorem sgn_sq (a : ZMod 2) : sgn a ^ 2 = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp [sgn]

theorem sgn_inv (a : ZMod 2) : (sgn a)⁻¹ = sgn a := by
  rw [inv_eq_iff_mul_eq_one, ← sq, sgn_sq]

theorem sgn_injective : Function.Injective sgn := by
  intro a b h
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · rfl
  · rw [sgn_zero, sgn_one] at h; exact absurd h.symm neg_one_ne_one
  · rw [sgn_zero, sgn_one] at h; exact absurd h neg_one_ne_one
  · rfl

theorem sgn_eq_one_iff (a : ZMod 2) : sgn a = 1 ↔ a = 0 := by
  rw [← sgn_zero]; exact sgn_injective.eq_iff

/-- A unit of `ℂ` with square `1` is `±1`. -/
theorem sq_eq_one_cases {s : ℂˣ} (h : s ^ 2 = 1) : s = 1 ∨ s = -1 := by
  have h' : (s : ℂ) * s = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h
    simpa [sq] using this
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · left; exact Units.ext h1
  · right; exact Units.ext (by simpa using h1)

theorem sgn_unsgn {s : ℂˣ} (h : s ^ 2 = 1) : sgn (unsgn s) = s := by
  rcases sq_eq_one_cases h with rfl | rfl
  · simp [unsgn, sgn]
  · simp [unsgn, sgn]

/-! ## Cocycles and coboundaries correspond -/

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Push a `ZMod 2` cochain to a sign cochain. -/
def sgnC (ε : G → G → ZMod 2) : G → G → ℂˣ := fun x y => sgn (ε x y)

/-- Pull a sign cochain back to a `ZMod 2` cochain. -/
def unsgnC (η : G → G → ℂˣ) : G → G → ZMod 2 := fun x y => unsgn (η x y)

theorem sgnC_unsgnC {η : G → G → ℂˣ} (h : ∀ x y, η x y ^ 2 = 1) : sgnC (unsgnC η) = η := by
  funext x y; exact sgn_unsgn (h x y)

theorem isCocycle2_iff (ε : G → G → ZMod 2) : IsCocycle2 ε ↔ IsSignCocycle (sgnC ε) := by
  constructor
  · rintro ⟨hc, hcoc⟩
    refine ⟨?_, fun x y => sgn_sq _, fun x y z => ?_⟩
    · have : IsLocallyConstant (fun x : G × G => ε x.1 x.2) :=
        (IsLocallyConstant.iff_continuous _).mpr hc
      exact this.comp sgn
    · -- `ε y z - ε (xy) z + ε x (yz) - ε x y = 0`
      have h := congrArg sgn (hcoc x y z)
      rw [sgn_sub, sgn_add, sgn_sub, sgn_zero] at h
      simp only [sgnC]
      have e1 := sgn_inv (ε (x * y) z)
      have e2 := sgn_inv (ε x y)
      calc sgn (ε (x * y) z) * sgn (ε x y)
          = sgn (ε (x * y) z) * sgn (ε x y) *
            (sgn (ε y z) * sgn (ε (x * y) z) * sgn (ε x (y * z)) * sgn (ε x y)) := by
            rw [h, mul_one]
        _ = sgn (ε y z) * sgn (ε x (y * z)) *
            ((sgn (ε (x * y) z) * sgn (ε (x * y) z)) * (sgn (ε x y) * sgn (ε x y))) := by ac_rfl
        _ = sgn (ε y z) * sgn (ε x (y * z)) := by
            rw [← sq, ← sq, sgn_sq, sgn_sq, one_mul, mul_one]
  · rintro ⟨hl, -, hcoc⟩
    refine ⟨?_, fun a b c => ?_⟩
    · have hl' : IsLocallyConstant (fun x : G × G => ε x.1 x.2) := by
        have := hl.comp unsgn
        have e : (unsgn ∘ Function.uncurry (sgnC ε)) = fun x : G × G => ε x.1 x.2 := by
          funext ⟨x, y⟩
          show unsgn (sgn (ε x y)) = ε x y
          rcases zmod2_cases (ε x y) with h | h <;> rw [h] <;> simp [sgn, unsgn]
        rwa [e] at this
      exact hl'.continuous
    · apply sgn_injective
      rw [sgn_sub, sgn_add, sgn_sub, sgn_zero]
      have h := hcoc a b c
      simp only [sgnC] at h
      calc sgn (ε b c) * sgn (ε (a * b) c) * sgn (ε a (b * c)) * sgn (ε a b)
          = (sgn (ε b c) * sgn (ε a (b * c))) * (sgn (ε (a * b) c) * sgn (ε a b)) := by ac_rfl
        _ = (sgn (ε (a * b) c) * sgn (ε a b)) * (sgn (ε (a * b) c) * sgn (ε a b)) := by rw [h]
        _ = 1 := by rw [← sq, mul_pow, sgn_sq, sgn_sq, mul_one]

theorem isCoboundary2_iff (ε : G → G → ZMod 2) : IsCoboundary2 ε ↔ SignCob (sgnC ε) := by
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨fun x => sgn (f x), ((IsLocallyConstant.iff_continuous f).mpr hf).comp sgn,
      fun x => sgn_sq _, fun x y => ?_⟩
    simp only [sgnC, dB, he, sgn_add, sgn_sub, sgn_inv]
    ac_rfl
  · rintro ⟨γ, hγl, hγs, he⟩
    refine ⟨fun x => unsgn (γ x), (hγl.comp unsgn).continuous, fun a b => ?_⟩
    apply sgn_injective
    have h := he a b
    simp only [sgnC, dB] at h
    have hi : (γ (a * b))⁻¹ = γ (a * b) :=
      inv_eq_of_mul_eq_one_right (by rw [← sq, hγs])
    rw [h, sgn_add, sgn_sub, sgn_unsgn (hγs a), sgn_unsgn (hγs b), sgn_unsgn (hγs (a * b)), hi]
    ac_rfl

/-- Every sign cocycle is `sgnC` of a `ZMod 2` cocycle. -/
theorem exists_of_isSignCocycle {η : G → G → ℂˣ} (h : IsSignCocycle η) :
    ∃ ε : G → G → ZMod 2, IsCocycle2 ε ∧ η = sgnC ε :=
  ⟨unsgnC η, by rw [isCocycle2_iff, sgnC_unsgnC h.2.1]; exact h, (sgnC_unsgnC h.2.1).symm⟩

end Generic

/-- Restriction commutes with the dictionary: glue-descent's `pull (resp p)` is pkg-I6's
`resC ℚ_[p]` (the same Mathlib map). -/
theorem pull_resp_sgnC (p : Nat.Primes) (ε : GQ → GQ → ZMod 2) :
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    pull (resp p) (sgnC ε) = sgnC (resC ℚ_[(p : ℕ)] ε) := rfl

/-! ## The two leaves -/

/-- The real place from reciprocity: a `ZMod 2` cocycle of `G_ℚ` that is a coboundary at every
finite prime is a coboundary at `∞` (the number of places where it is locally nontrivial is
even, and there are none at finite primes). -/
theorem real_of_finite (hR : BrauerReciprocity2C) (ε : GQ → GQ → ZMod 2) (hε : IsCocycle2 ε)
    (hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε)) :
    IsCoboundary2 (resC ℝ ε) := by
  classical
  obtain ⟨-, hev⟩ := hR ε hε
  have hempty : {q : Nat.Primes | haveI : Fact (q : ℕ).Prime := ⟨q.2⟩;
      ¬ IsCoboundary2 (resC ℚ_[(q : ℕ)] ε)} = ∅ := by
    ext q
    have : Fact (q : ℕ).Prime := ⟨q.2⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hp q
  rw [hempty, Set.ncard_empty, zero_add] at hev
  by_contra hne
  rw [if_neg hne] at hev
  exact Nat.not_even_one hev

/-- **glue-descent's `LeafHasse` from T14** (`BrauerHasse2C` and `BrauerReciprocity2C`). -/
theorem leafHasse_of_T14 (hH : BrauerHasse2C) (hR : BrauerReciprocity2C) : LeafHasse := by
  intro η hη hloc
  obtain ⟨ε, hε, rfl⟩ := exists_of_isSignCocycle hη
  have hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε) := by
    intro p hpp
    rw [isCoboundary2_iff]
    exact hloc ⟨p, hpp.out⟩
  rw [← isCoboundary2_iff]
  exact hH ε hε (real_of_finite hR ε hε hp) hp

/-- **glue-descent's `LeafLocalTwo` from T15** (`LocalH2CardC`, its finite-place half; the
existence of a nontrivial class and the real place are not used). -/
theorem leafLocalTwo_of_T15 (hC : LocalH2CardC) : LeafLocalTwo := by
  intro p η₁ η₂ h₁ h₂ hn₁ hn₂
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨ε₁, hε₁, rfl⟩ := exists_of_isSignCocycle h₁
  obtain ⟨ε₂, hε₂, rfl⟩ := exists_of_isSignCocycle h₂
  rw [← isCoboundary2_iff] at hn₁ hn₂
  have h := (hC.1 p).2 ε₁ ε₂ hε₁ hε₂ hn₁ hn₂
  rw [isCoboundary2_iff] at h
  have e : (fun x y => sgnC ε₁ x y * (sgnC ε₂ x y)⁻¹) = sgnC (ε₁ - ε₂) := by
    funext x y
    simp only [sgnC, Pi.sub_apply, sgn_sub, sgn_inv]
  rw [e]
  exact h

/-! ## Converses: glue-descent's forms say no more than the announced leaves -/

/-- `LeafHasse` (finite places only) implies `BrauerHasse2C` outright. -/
theorem brauerHasse2C_of_leafHasse (h : LeafHasse) : BrauerHasse2C := by
  intro ε hε _ hp
  rw [isCoboundary2_iff]
  rw [isCocycle2_iff] at hε
  refine h _ hε fun p => ?_
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  rw [pull_resp_sgnC, ← isCoboundary2_iff]
  exact hp p

/-- Given reciprocity, `LeafHasse ↔ BrauerHasse2C`. -/
theorem leafHasse_iff (hR : BrauerReciprocity2C) : LeafHasse ↔ BrauerHasse2C :=
  ⟨brauerHasse2C_of_leafHasse, fun hH => leafHasse_of_T14 hH hR⟩

/-- `LeafLocalTwo` is exactly the second half of `H2TwoClasses (G_{ℚ_p})` for every `p`. -/
theorem leafLocalTwo_iff : LeafLocalTwo ↔ ∀ (p : ℕ) [Fact p.Prime],
    ∀ ε₁ ε₂, IsCocycle2 (G := Field.absoluteGaloisGroup ℚ_[p]) ε₁ → IsCocycle2 ε₂ →
      ¬ IsCoboundary2 ε₁ → ¬ IsCoboundary2 ε₂ → IsCoboundary2 (ε₁ - ε₂) := by
  have e : ∀ {G : Type} [Group G] [TopologicalSpace G] (ε₁ ε₂ : G → G → ZMod 2),
      (fun x y => sgnC ε₁ x y * (sgnC ε₂ x y)⁻¹) = sgnC (ε₁ - ε₂) := by
    intro G _ _ ε₁ ε₂
    funext x y
    simp only [sgnC, Pi.sub_apply, sgn_sub, sgn_inv]
  constructor
  · intro h p hp ε₁ ε₂ h₁ h₂ hn₁ hn₂
    rw [isCocycle2_iff] at h₁ h₂
    rw [isCoboundary2_iff] at hn₁ hn₂ ⊢
    rw [← e]
    exact h ⟨p, hp.out⟩ _ _ h₁ h₂ hn₁ hn₂
  · intro h p η₁ η₂ h₁ h₂ hn₁ hn₂
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    obtain ⟨ε₁, hε₁, rfl⟩ := exists_of_isSignCocycle h₁
    obtain ⟨ε₂, hε₂, rfl⟩ := exists_of_isSignCocycle h₂
    rw [← isCoboundary2_iff] at hn₁ hn₂
    rw [e, ← isCoboundary2_iff]
    exact h p ε₁ ε₂ hε₁ hε₂ hn₁ hn₂

/-! ## B2-B3 from the announced leaves -/

/-- **B2-B3 with the constants from the announced leaves**: glue-descent's
`GlueDescent.B3Q.b3_degree_le_QM` with `LeafHasse`, `LeafLocalTwo` replaced by T14-T15
(`BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`).  The remaining hypotheses
`LeafSqrtCrit` (L-B2c, T16) and `LeafUnramified` (L-B2d) are glue-descent's other leaves. -/
theorem b3_degree_le_QM_of_T14_T15 (hH : BrauerHasse2C) (hR : BrauerReciprocity2C)
    (hC : LocalH2CardC) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ)
    (hRD : (ZInQ.heightD : ℝ) ≤ R) (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R)
    (u : ℚ)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD)
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ GlueDescent.ramSet S u → UnramifiedAt L p)
    (η : GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
      (L' : IntermediateField ℚ (AlgebraicClosure ℚ)),
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GlueDescent.B3Q.GQL L' ↔ σ ∈ GlueDescent.B3Q.GQL L ∧ β σ = 1) ∧
      (Module.finrank ℚ L' : ℝ) ≤ ZInQ.heightQ R * ZInQ.contactSupport S u :=
  GlueDescent.B3Q.b3_degree_le_QM (leafHasse_of_T14 hH hR) (leafLocalTwo_of_T15 hC) hSq hUnr
    S hS R hRD hRS hR12 u L hLD ε hε hinf h11 hram η hη hηl

end GlueWP3

end

