import ZInQKernel.Contrib.OneProof.TYZThm11Genus
import ZInQKernel.Contrib.OneProof.TYZThm21Span.FDelta

/-!
# h21c-steps: `h21C` from TYZ Theorem 2.1 over `π^U = ⊕_δ ℂ f_δ` (Theorem 2.4(1))

Task h21c-steps; report `docs/research/h21c-steps.md`, log `scratch/h21c-steps/log.md`. TYZ = Tian–Yuan–Zhang,
*Genus periods, genus points and congruent number problem*, Asian J. Math. 21 (2017), arXiv:1411.4728v1; line
numbers `Lnnnn` refer to the arXiv source.

`h21C = TYZGenusFold.TYZThm21PairsC` quantifies over test vectors `IsTestVector n τ f`, generators of `InPiZ`, which
describes `π_ℤ^{U_n}` by two 8-term sums (orthogonality to `1` and `χ₀`); identifying that with TYZ's `π_ℤ^{U_n}`
used `π ⊂ 𝒜₀` (L715–720), Lemma 2.5 with its measure (L643–661) and L722–727. Here:

* `InPiSpan n τ f`: `f` is integer valued, equals on `B̂^×` a complex combination of TYZ's six forms `f_δ`
  (`fDelta`, Theorem 2.4(1), L615–623: `π^U = ⊕_δ ℂ f_δ`), and is right `U_n`-invariant. Since `ℚ̂^× U ⊂ ⟨U_n, ℚ̂^×⟩`
  (`GU_le_HgrpN`) and `π` has trivial central character, `π_ℤ^{U_n} = {f ∈ π^U : ℤ-valued, U_n-invariant}`: this is
  `InPiSpan`, with `π^U` read through Theorem 2.4(1).
* `inPiZ_iff_inPiSpan`: `InPiZ n τ f ↔ InPiSpan n τ f`, proved (Lemma 2.5's bijectivity, the character
  orthogonality of the `ψ_δ`, `1`, `χ₀` by `decide`); no measure is used.
* `TYZThm21Span`: TYZ Theorem 2.1 (L554–559) as `TYZThm21PairsC`, with `f_n` a `ℤ`-generator of `InPiSpan`
  (`IsTestVectorSpan`).
* `tyzThm21PairsC_of_span : TYZThm21Span → TYZThm21PairsC` (and the converse, `tyzThm21Span_of_pairsC`).

No `sorry`, no `axiom`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.H21CSteps

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp
open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus NumberField
open ZInQ.Contrib.TYZGenus.TYZ35 (gchar divSet)
open ZInQ.Contrib.T21Proof ZInQ.Contrib.HfxProof ZInQ.Contrib.TYZGenusFold
open scoped Quaternion

/-- **TYZ's `π_ℤ^{U_n}`, with `π^U` as Theorem 2.4(1) prints it** (L536–550, L615–623): the functions `f`
with integer values on `B̂^×` that agree on `B̂^×` with an element `Σ_δ c_δ f_δ` of `π^U = ⊕_δ ℂ f_δ`
(`fDelta`, `δ ∈ Δ/{±1}`) and are right `U_n`-invariant (`U_n = R̂_n^× K_{n,2}^×`, L543, `Un`). Values off `B̂^×`
are not used. -/
def InPiSpan (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) : Prop :=
  (∃ c : Fin 6 → ℂ, ∀ x : ℍ[AQ]ˣ, ((f x : ℤ) : ℂ) = ∑ δ : Fin 6, c δ * ((fDelta δ x : ℤ) : ℂ)) ∧
    (∀ x : ℍ[AQ]ˣ, ∀ u ∈ Un n τ, f ((x : ℍ[AQ]) * u) = f x)

/-- **TYZ's test vector `f_n`** (L550): a `ℤ`-generator of `π_ℤ^{U_n}` (`InPiSpan`). -/
def IsTestVectorSpan (n : ℕ) [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) : Prop :=
  InPiSpan n τ f ∧ ∀ g, InPiSpan n τ g → ∃ c : ℤ, ∀ x : ℍ[AQ]ˣ, g x = c * f x

/-- **TYZ Theorem 2.1 (L554–559), with `π^U` as printed in Theorem 2.4(1) (L615–623), for every
decomposition, odd classes, complex sign choices.** For squarefree `1 < n ≡ 1, 3 (mod 8)`, every admissible
embedding `τ` (L527–534), every test vector `f_n` (a `ℤ`-generator of `π_ℤ^{U_n}`, `IsTestVectorSpan`), every
complex sign choice `ℓ` of `𝓛` (`ℓ(m)² = 𝓛(m)²`, L338–353) and every `n = d₁d₂`: the quadratic period
`P(d₁, d₂) = Σ_{t ∈ Cl_n} f_n(t)χ_{d₁,d₂}(t)` (L551–552, `quadPeriod`) vanishes when neither factor is `≡ 1 (mod 8)`,
and for `d₂ ≡ 1 (mod 8)`, `P(d₁, d₂) = ±2^{k−a} w_K 𝓛(d₁)𝓛(d₂)` (`k − a = #{p ∣ n} − 1` for odd `n`, `2w_K` the
number of roots of unity of `K_n`, Mathlib's `torsionOrder`). The same statement as `TYZThm21PairsC` (tyz-genus),
whose restrictions it keeps (odd classes, `n > 1`, the first assertion only for pairs with no factor
`≡ 1 (mod 8)`), with `π_ℤ^{U_n}` read through Theorem 2.4(1) instead of through `InPiZ`. -/
def TYZThm21Span : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVectorSpan n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignC ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriod n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          (quadPeriod n τ f d₂ : ℂ) = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

/-! ## Fourier analysis on the 8 classes -/

/-- A function on the 8 classes orthogonal to `1` and `χ₀` is `Σ_δ c_δ ψ_δ`, `c_δ = (1/8) Σ_s F(s) ψ_δ(s)`. -/
theorem fourier8 (F : T8 → ℂ) (h1 : ∑ s, F s = 0) (h2 : ∑ s, (chi0Rep s : ℂ) * F s = 0) (t : T8) :
    F t = ∑ δ : Fin 6, ((1 / 8 : ℂ) * ∑ s, F s * (psiDelta δ s : ℂ)) * (psiDelta δ t : ℂ) := by
  have horth : ∀ s, (∑ δ : Fin 6, (psiDelta δ s : ℂ) * (psiDelta δ t : ℂ)) =
      (if s = t then (8 : ℂ) else 0) - 1 - (chi0Rep s : ℂ) * (chi0Rep t : ℂ) := by
    intro s
    have hc : ((∑ δ : Fin 6, psiDelta δ s * psiDelta δ t + 1 + chi0Rep s * chi0Rep t : ℤ) : ℂ) =
        ((if s = t then 8 else 0 : ℤ) : ℂ) := by rw [psi_orth]
    push_cast at hc
    split_ifs at hc ⊢ <;> linear_combination hc
  have key : ∑ δ : Fin 6, ((1 / 8 : ℂ) * ∑ s, F s * (psiDelta δ s : ℂ)) * (psiDelta δ t : ℂ) =
      (1 / 8) * ∑ s, F s * ∑ δ : Fin 6, ((psiDelta δ s : ℂ) * (psiDelta δ t : ℂ)) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun δ _ => by ring
  rw [key]
  simp only [horth, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, mul_one]
  have e3 : ∑ s, F s * ((chi0Rep s : ℂ) * (chi0Rep t : ℂ)) = (∑ s, (chi0Rep s : ℂ) * F s) * (chi0Rep t : ℂ) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [e3, h1, h2]
  ring

/-! ## The dictionary `InPiZ ↔ InPiSpan` -/

section Dict

variable {n : ℕ} [NeZero n] {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]}

theorem inPiSpan_of_inPiZ {f : ℍ[AQ] → ℤ} (hf : InPiZ n τ f) : InPiSpan n τ f := by
  refine ⟨?_, hf.2.1⟩
  set F : T8 → ℂ := fun t => ((f (twoRep v2 t) : ℤ) : ℂ) with hF
  obtain ⟨hs1, hs2⟩ := hf.2.2.2 v2 v2_spec
  have h1 : ∑ s, F s = 0 := by simp only [hF]; exact_mod_cast hs1
  have h2 : ∑ s, (chi0Rep s : ℂ) * F s = 0 := by simp only [hF]; exact_mod_cast hs2
  refine ⟨fun δ => (1 / 8 : ℂ) * ∑ s, F s * (psiDelta δ s : ℂ), fun x => ?_⟩
  have hx : f x = f (twoRep v2 (clsIdx x)) :=
    inPiZ_eq_of_mem_DC (x := twoRepU v2 (clsIdx x)) (y := x) hf (DCU_sub_DC n τ (clsIdx_spec x))
  rw [hx]
  simp only [fDelta_unit]
  exact fourier8 F h1 h2 (clsIdx x)

theorem inPiZ_of_inPiSpan {f : ℍ[AQ] → ℤ} (hf : InPiSpan n τ f) : InPiZ n τ f := by
  obtain ⟨⟨c, hc⟩, hU⟩ := hf
  have hinv : ∀ x y : ℍ[AQ]ˣ, (y : ℍ[AQ]) ∈ DCU x → f y = f x := by
    intro x y h
    apply Int.cast_injective (α := ℂ)
    rw [hc y, hc x]
    simp only [fDelta_eq_of_mem _ h]
  have hrep : ∀ v, IsPlaceTwo v → ∀ t, ((f (twoRep v t) : ℤ) : ℂ) = ∑ δ : Fin 6, c δ * (psiDelta δ t : ℂ) := by
    intro v hv t
    rw [← twoRepU_coe, hc]
    simp only [twoRepU_coe, fDelta_twoRep _ hv]
  have hψ : ∀ δ, ∑ t : T8, (psiDelta δ t : ℂ) = 0 := fun δ => by
    have := psi_sum δ; exact_mod_cast this
  have hψ0 : ∀ δ, ∑ t : T8, (chi0Rep t : ℂ) * (psiDelta δ t : ℂ) = 0 := fun δ => by
    have := psi_sum_chi0 δ; exact_mod_cast this
  refine ⟨fun γ hγ x => ?_, hU, fun x z => ?_, fun v hv => ⟨?_, ?_⟩⟩
  · have e : qι γ * (x : ℍ[AQ]) = ((qιU γ hγ * x : ℍ[AQ]ˣ) : ℍ[AQ]) := rfl
    rw [e]
    exact hinv x _ ⟨γ, hγ, 1, Subgroup.one_mem _, by simp [qιU]⟩
  · have e : (x : ℍ[AQ]) * algebraMap AQ ℍ[AQ] (z : AQ) =
        ((x * Units.map (algebraMap AQ ℍ[AQ]).toMonoidHom z : ℍ[AQ]ˣ) : ℍ[AQ]) := rfl
    rw [e]
    exact hinv x _ ⟨1, one_ne_zero, _, Subgroup.subset_closure (Or.inr ⟨z, rfl⟩), by simp⟩
  · apply Int.cast_injective (α := ℂ)
    push_cast
    simp only [hrep v hv]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hψ, mul_zero, Finset.sum_const_zero]
  · apply Int.cast_injective (α := ℂ)
    push_cast
    simp only [hrep v hv, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ δ : Fin 6, ∑ t : T8, (chi0Rep t : ℂ) * (c δ * (psiDelta δ t : ℂ)) =
        c δ * ∑ t : T8, (chi0Rep t : ℂ) * (psiDelta δ t : ℂ) := fun δ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
    simp only [this, hψ0, mul_zero, Finset.sum_const_zero]

/-- **The dictionary**: `InPiZ` (hfx-proof's `π_ℤ^{U_n}`, by two 8-term sums) is `InPiSpan` (`π^U` of Theorem 2.4(1)). -/
theorem inPiZ_iff_inPiSpan {f : ℍ[AQ] → ℤ} : InPiZ n τ f ↔ InPiSpan n τ f :=
  ⟨inPiSpan_of_inPiZ, inPiZ_of_inPiSpan⟩

theorem isTestVector_iff_span {f : ℍ[AQ] → ℤ} : IsTestVector n τ f ↔ IsTestVectorSpan n τ f := by
  simp only [IsTestVector, IsTestVectorSpan, inPiZ_iff_inPiSpan]

end Dict

/-- Non-vacuity: for squarefree `1 < n ≡ 1, 3 (mod 8)` and admissible `τ`, a test vector `f_n` of
`IsTestVectorSpan` exists and is nonzero (hfx-proof's `tyzTestVectorExists` through the dictionary). -/
theorem exists_testVectorSpan {n : ℕ} [NeZero n] (hsq : Squarefree n) (h1 : 1 < n) (hcl : n % 8 = 1 ∨ n % 8 = 3)
    {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau n τ) :
    ∃ f : ℍ[AQ] → ℤ, IsTestVectorSpan n τ f ∧ ∃ x : ℍ[AQ]ˣ, f x ≠ 0 := by
  obtain ⟨f, hf, hx⟩ := ZInQ.Contrib.HfxProof.tyzTestVectorExists n hsq h1 hcl τ hτ
  exact ⟨f, isTestVector_iff_span.mp hf, hx⟩

/-- **`h21C` from TYZ Theorem 2.1 over `π^U` of Theorem 2.4(1).** -/
theorem tyzThm21PairsC_of_span (h : TYZThm21Span) : TYZThm21PairsC := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h n hsq h1 hcl τ hτ f (isTestVector_iff_span.mp hf) ℓ hℓ d₁ d₂ hd

/-- The converse: the two statements are equivalent. -/
theorem tyzThm21Span_of_pairsC (h : TYZThm21PairsC) : TYZThm21Span := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h n hsq h1 hcl τ hτ f (isTestVector_iff_span.mpr hf) ℓ hℓ d₁ d₂ hd

end ZInQ.Contrib.H21CSteps
