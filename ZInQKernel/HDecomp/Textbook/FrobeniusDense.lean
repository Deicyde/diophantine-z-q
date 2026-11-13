import Mathlib
import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.Conductor.LadicCond

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt5b from
`scratch/t-skolem-kw/FrobeniusDense.lean` (T18 from `ChebotarevExists`).
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-!
# t-skolem-kw: leaf T18 (Frobenius density) reduced to its finite form

`HSyn.FrobeniusDense` (verbatim below as `HS.FrobeniusDense`, over `HSyn`'s `Qbar`, `GQ`,
`LiesOver`, `IsArithFrob`, also verbatim) is proved from `PkgI6.ChebotarevExists`
(= `GlueC10.ChebotarevExists`, verbatim).  So T18 rests on the finite (existence) form of
Chebotarev's theorem alone.

Part C10 is copied verbatim from `scratch/h-decomposition/Leaves.lean`, section `GlueC10Sec`
(lines 11328-11333, 11375-11630, 11747-11750 at base 01267822): the lift of a finite-level
Frobenius to `G_ℚ` at a prime of `\bar ℤ`.  New here (`HS` section): the localization of `\bar ℤ`
at a prime `𝔓` is a valuation subring of `\bar ℚ` (`zbarLoc`, via the DVR `(𝓞_E)_{𝔓 ∩ 𝓞_E}` of
each finite layer), an arithmetic Frobenius at `𝔓` is an `IsArithFrob` at this place, and the
Krull-topology step.
-/

open NumberField

/-! Part C10 of the draft (glue-c10's Frobenius lift, a verbatim copy in namespace
`TSkolemKW.C10`) is `GlueC10`'s, from `ZInQKernel.HDecomp.C10.C10`. -/

/-! ## `HSyn.FrobeniusDense` from the finite form -/

namespace TSkolemKW.HS

open scoped Pointwise
open GlueC10 (ChebotarevExists FrobDense IsFrobAt Zbar toZbar toZbar_coe frobDense)
/-! `Qbar`, `GQ`, `LiesOver`, `IsArithFrob` (verbatim copies of `HSyn`'s in the
draft) are `PkgI4`'s, from `ZInQKernel.HDecomp.Conductor.LadicCond`. -/
open PkgI4 (Qbar GQ LiesOver IsArithFrob)

/-! ### Definitions (verbatim from `HSyn` §0-§1 of `scratch/h-decomposition/Leaves.lean`) -/

/-- **L18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-! ### The localization of `\bar ℤ` at a prime is a valuation subring of `\bar ℚ` -/

variable (P : Ideal Zbar) [hP : P.IsPrime]

/-- Membership in `\bar ℤ_𝔓`. -/
def LocMem (x : Qbar) : Prop := ∃ a s : Zbar, s ∉ P ∧ x * (s : Qbar) = a

theorem one_notMem : (1 : Zbar) ∉ P := (Ideal.ne_top_iff_one P).1 hP.ne_top

omit hP in
theorem natCast_mem (p : ℕ) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) : (p : Zbar) ∈ P := by
  have h1 : (p : ℤ) ∈ P.under ℤ := by rw [hPp]; exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ Zbar (p : ℤ) ∈ P := h1
  simpa using h2

omit hP in
/-- In a number field `K`, for a nonzero prime `Q` of `𝓞_K`, every `x ∈ K` or its inverse is a
fraction `r / s` with `s ∉ Q` (the localization `(𝓞_K)_Q` is a DVR, hence a valuation ring). -/
theorem exists_frac_or_inv (K : Type) [Field K] [NumberField K] (Q : Ideal (𝓞 K)) [Q.IsPrime]
    (hQ0 : Q ≠ ⊥) (x : K) (hx0 : x ≠ 0) :
    ∃ r s : 𝓞 K, s ∉ Q ∧ (x * (s : K) = r ∨ x⁻¹ * (s : K) = r) := by
  let Aₘ := Localization.AtPrime Q
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hQ0 Aₘ
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : (b : K) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have ha0 : (a : K) ≠ 0 := by
    intro h
    apply hx0
    rw [← hab]
    change (a : K) / (b : K) = 0
    rw [h, zero_div]
  obtain ⟨c, hc⟩ := PreValuationRing.cond (algebraMap (𝓞 K) Aₘ a) (algebraMap (𝓞 K) Aₘ b)
  obtain ⟨⟨r, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl c
  have hinj := IsLocalization.injective Aₘ Q.primeCompl_le_nonZeroDivisors
  refine ⟨r, s, hs, ?_⟩
  rcases hc with hc | hc
  · right
    have e : a * r = b * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc]
      congr 1
      exact (IsLocalization.mk'_spec Aₘ r ⟨s, hs⟩).symm
    have eE : (a : K) * (r : K) = (b : K) * (s : K) := by
      exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) e
    rw [← hab]
    change ((a : K) / (b : K))⁻¹ * (s : K) = (r : K)
    field_simp
    linear_combination eE.symm
  · left
    have e : b * r = a * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc]
      congr 1
      exact (IsLocalization.mk'_spec Aₘ r ⟨s, hs⟩).symm
    have eE : (b : K) * (r : K) = (a : K) * (s : K) := by
      exact_mod_cast congrArg (fun z : 𝓞 K => (z : K)) e
    rw [← hab]
    change (a : K) / (b : K) * (s : K) = (r : K)
    field_simp
    linear_combination eE.symm

/-- Every `x ∈ \bar ℚ` or its inverse lies in `\bar ℤ_𝔓`: pass to the DVR `(𝓞_E)_{𝔓 ∩ 𝓞_E}`
for `E = ℚ(x)`. -/
theorem locMem_or_inv (p : ℕ) (hp : p.Prime) (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (x : Qbar) : LocMem P x ∨ LocMem P x⁻¹ := by
  by_cases hx0 : x = 0
  · left
    exact ⟨0, 1, one_notMem P, by simp [hx0]⟩
  have hxi : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral _
  let E := IntermediateField.adjoin ℚ ({x} : Set Qbar)
  have : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hxi
  have : NumberField E := ⟨⟩
  let Q := P.comap (toZbar E)
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hpQ : ((p : ℤ) : 𝓞 E) ∈ Q := by
    change toZbar E ((p : ℤ) : 𝓞 E) ∈ P
    simpa using natCast_mem P p hPp
  have hQ0 : Q ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpQ
    exact (by exact_mod_cast hp.ne_zero : ((p : ℤ) : 𝓞 E) ≠ 0) hpQ
  let x' : E := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  have hx'0 : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨r, s, hs, h | h⟩ := exists_frac_or_inv E Q hQ0 x' hx'0
  · left
    refine ⟨toZbar E r, toZbar E s, hs, ?_⟩
    rw [toZbar_coe, toZbar_coe]
    have := congrArg (fun z : E => (z : Qbar)) h
    simpa using this
  · right
    refine ⟨toZbar E r, toZbar E s, hs, ?_⟩
    rw [toZbar_coe, toZbar_coe]
    have := congrArg (fun z : E => (z : Qbar)) h
    simpa using this

/-- `\bar ℤ_𝔓` as a valuation subring of `\bar ℚ`. -/
def zbarLoc (p : ℕ) (hp : p.Prime) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) :
    ValuationSubring Qbar where
  carrier := {x | LocMem P x}
  mul_mem' := by
    rintro x y ⟨a, s, hs, ha⟩ ⟨b, t, ht, hb⟩
    refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    push_cast
    linear_combination (y * (t : Qbar)) * ha + (a : Qbar) * hb
  one_mem' := ⟨1, 1, one_notMem P, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, ha⟩ ⟨b, t, ht, hb⟩
    refine ⟨a * t + b * s, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
    push_cast
    linear_combination (t : Qbar) * ha + (s : Qbar) * hb
  zero_mem' := ⟨0, 1, one_notMem P, by simp⟩
  neg_mem' := by
    rintro x ⟨a, s, hs, ha⟩
    refine ⟨-a, s, hs, ?_⟩
    push_cast
    linear_combination -ha
  mem_or_inv_mem' := locMem_or_inv P p hp hPp

theorem mem_zbarLoc {p : ℕ} {hp : p.Prime} {hPp : P.under ℤ = Ideal.span {(p : ℤ)}} {x : Qbar} :
    x ∈ zbarLoc P p hp hPp ↔ LocMem P x := Iff.rfl

/-! ### An arithmetic Frobenius at `𝔓` is an `IsArithFrob` at `\bar ℤ_𝔓` -/

/-- `g ∈ G_ℚ` maps `\bar ℤ` to itself. -/
def gZ (g : GQ) (z : Zbar) : Zbar :=
  ⟨g z, (z.2 : IsIntegral ℤ (z : Qbar)).map ((g : Qbar →ₐ[ℚ] Qbar).restrictScalars ℤ)⟩

@[simp] theorem gZ_coe (g : GQ) (z : Zbar) : ((gZ g z : Zbar) : Qbar) = g z := rfl

theorem liesOver_and_isArithFrob (h : GQ) (p : ℕ) (hp : p.Prime)
    (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    LiesOver (zbarLoc P p hp hPp) p ∧ IsArithFrob h (zbarLoc P p hp hPp) p := by
  have hcong : ∀ z : Zbar, gZ h z - z ^ p ∈ P := fun z => hh z _ (by push_cast; rfl)
  have hmemP : ∀ z : Zbar, gZ h z ∈ P ↔ z ∈ P := by
    intro z
    constructor
    · intro hz
      have : z ^ p ∈ P := by
        have := P.sub_mem hz (hcong z)
        rwa [sub_sub_cancel] at this
      exact hP.mem_of_pow_mem p this
    · intro hz
      have := P.add_mem (hcong z) (P.pow_mem_of_mem hz p hp.pos)
      rwa [sub_add_cancel] at this
  have hpP := natCast_mem P p hPp
  refine ⟨?_, ?_, ?_⟩
  · -- `p` is a nonunit
    rw [LiesOver, ValuationSubring.mem_nonunits_iff_or]
    right
    rintro ⟨a, s, hs, ha⟩
    apply hs
    have : s = (p : Zbar) * a := by
      apply Subtype.ext
      push_cast
      rw [← ha, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hp.ne_zero), one_mul]
    rw [this]
    exact P.mul_mem_right _ hpP
  · -- `h` stabilizes the place
    refine MulAction.mem_stabilizer_iff.2 (SetLike.ext fun x => ?_)
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    constructor
    · rintro ⟨a, s, hs, ha⟩
      refine ⟨gZ h a, gZ h s, fun h' => hs ((hmemP s).1 h'), ?_⟩
      have := congrArg h ha
      rw [map_mul] at this
      simpa [AlgEquiv.aut_inv] using this
    · rintro ⟨a, s, hs, ha⟩
      have hts : gZ h (gZ h⁻¹ s) = s := by
        apply Subtype.ext
        simp [AlgEquiv.aut_inv]
      refine ⟨gZ h⁻¹ a, gZ h⁻¹ s, fun h' => hs (hts ▸ (hmemP _).2 h'), ?_⟩
      have := congrArg (fun y => (h⁻¹ : GQ) y) ha
      simp only [map_mul] at this
      simpa using this
  · -- the Frobenius congruence on the place
    rintro x ⟨a, s, hs, ha⟩
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_cases hd : h x - x ^ p = 0
    · exact Or.inl hd
    right
    rintro ⟨a', s', hs', hd'⟩
    let n : Zbar := gZ h a * s ^ p - a ^ p * gZ h s
    have hn : n ∈ P := by
      have : n = (gZ h a - a ^ p) * s ^ p - a ^ p * (gZ h s - s ^ p) := by ring
      rw [this]
      exact P.sub_mem (P.mul_mem_right _ (hcong a)) (P.mul_mem_left _ (hcong s))
    have e1 : h x * h (s : Qbar) = h (a : Qbar) := by rw [← map_mul, ha]
    have e2 : x ^ p * (s : Qbar) ^ p = (a : Qbar) ^ p := by rw [← mul_pow, ha]
    have e3 : (h x - x ^ p) * (h (s : Qbar) * (s : Qbar) ^ p) = (n : Qbar) := by
      simp only [n]
      push_cast
      simp only [gZ_coe]
      linear_combination ((s : Qbar) ^ p) * e1 - (h (s : Qbar)) * e2
    have e4 : (s' : Qbar) = (h x - x ^ p) * (a' : Qbar) := by
      rw [← hd', ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
    have e5 : s' * (gZ h s * s ^ p) = a' * n := by
      apply Subtype.ext
      push_cast
      simp only [gZ_coe]
      rw [e4, ← e3]
      ring
    have hmem : s' * (gZ h s * s ^ p) ∈ P := e5 ▸ P.mul_mem_left _ hn
    rcases hP.mem_or_mem hmem with h1 | h1
    · exact hs' h1
    rcases hP.mem_or_mem h1 with h2 | h2
    · exact hs ((hmemP s).1 h2)
    · exact hs (hP.mem_of_pow_mem p h2)

/-! ### The reduction -/

/-- **T18 from its finite form, via `FrobDense` (GLUE, proved).** -/
theorem frobeniusDense_of_frobDense (hD : ∀ S, FrobDense S) : FrobeniusDense := by
  intro U hU σ S
  obtain ⟨E, hE, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff ℚ Qbar (U : Set GQ)).1 (hU.mem_nhds U.one_mem)
  obtain ⟨h, p, hp, hpS, ⟨P, hP, hPp, hh⟩, hhE⟩ := hD S E hE σ
  obtain ⟨hL, hF⟩ := liesOver_and_isArithFrob P h p hp hPp hh
  refine ⟨p, hp, hpS, zbarLoc P p hp hPp, h, hL, hF, hEU ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, ← hhE x hx, AlgEquiv.symm_apply_apply]

/-- **T18 (`HSyn.FrobeniusDense`) from the finite form `PkgI6.ChebotarevExists` (GLUE,
proved).** -/
theorem frobeniusDense_of_chebotarev (hC : ChebotarevExists) : FrobeniusDense :=
  frobeniusDense_of_frobDense fun S => frobDense hC S

end TSkolemKW.HS
