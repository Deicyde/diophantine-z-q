
/-! ## Shimura's Theorem 5.4 with "analytic isomorphism" read as a biholomorphism -/

namespace HCMW

open WeierstrassCurve.Affine (Point)
open scoped PeriodPair
open ZInQ.Contrib.HCMDict (IsAnalyticUnif conjPt ShimuraThm54)

instance isShortNF_map (W : WeierstrassCurve ℂ) [W.IsShortNF] (σ : ℂ →+* ℂ) :
    (W.map σ).IsShortNF :=
  ⟨by simp [WeierstrassCurve.IsShortNF.a₁ (W := W)], by simp [WeierstrassCurve.IsShortNF.a₂ (W := W)],
    by simp [WeierstrassCurve.IsShortNF.a₃ (W := W)]⟩

section Printed

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise T5Glue

/-- **LEAF SHIMURA-5.4-BIHOLO (the main theorem of complex multiplication, Shimura 1971 Thm 5.4, with
"analytic isomorphism" read as a biholomorphism of complex manifolds).** As
`ZInQ.Contrib.HCMDict.ShimuraThm54`, with the clause form `IsAnalyticUnif` replaced by `IsAnalyticIso`:
`E(ℂ) = E.toAffine.Point` carries the complex structure given by the coordinate charts `x`, `y` and
`t = -x/y` (`HCMW.isManifoldPoint`; topology: the one-point compactification of the affine points, i.e.
the subspace topology of `ℙ²(ℂ)`), and `ξ : ℂ → E(ℂ)` is an analytic isomorphism `ℂ/𝔞 → E(ℂ)` when its
fibres are the cosets of `κ(𝔞)`, it is onto, and it is a local biholomorphism `ℂ → E(ℂ)`.

Let `K = ℚ(√−m) ⊂ ℂ` (through `κ`), `e : Kˢ → ℚ̄` normalized, `σ ∈ Aut(ℂ)` and `s ∈ 𝔸_K^×` with `σ = [s, K]`
on `K^ab` (`ArtinCond`). Let `𝔞` be a lattice in `K`, `E` an elliptic curve over `ℂ` in short Weierstrass
form and `ξ : ℂ/𝔞 → E(ℂ)` an analytic isomorphism with `ξ(0) = O`. Then there is an analytic isomorphism
`ξ' : ℂ/s⁻¹𝔞 → E^σ(ℂ)` with `ξ(u)^σ = ξ'(s⁻¹u)` for all `u ∈ K/𝔞`.

Source: G. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), Thm. 5.4;
S. Lang, *Elliptic functions*, Ch. 10, Thm. 3 (numbers UNVERIFIED, from memory; not read here).
Differences from the print, each making this statement weaker or equal, in either reading of
"analytic isomorphism" (with or without the group law): the hypothesis asks `ξ(0) = O` (a group
isomorphism satisfies it); the conclusion does not ask `ξ'` to be a group homomorphism; the uniqueness of
`ξ'` is dropped; `E` ranges over short Weierstrass models only; `𝔞` comes with a period pair. -/
def ShimuraThm54Biholo : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
  ∀ (𝔞 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔞) →
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic] [E.IsShortNF],
  ∀ ξ : ℂ → E.toAffine.Point, IsAnalyticIso E (kappa m '' 𝔞) ξ → ξ 0 = 0 →
    ∃ ξ' : ℂ → (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticIso (E.map (σ : ℂ →+* ℂ)) (kappa m '' sInvLat m s 𝔞) ξ' ∧
      ∀ u v : QNeg m,
        finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞 →
        conjPt (σ : ℂ →+* ℂ) (ξ (kappa m u)) = ξ' (kappa m v)

/-- **`ShimuraThm54` from the biholomorphic reading of Shimura's theorem.** -/
theorem shimuraThm54_of_biholo (h : ShimuraThm54Biholo) : ShimuraThm54 := by
  intro m _ hm e he σ s hs 𝔞 h𝔞 E _ h₁ h₂ h₃ ξ hξ
  haveI : E.IsShortNF := ⟨h₁, h₂, h₃⟩
  rw [isAnalyticUnif_iff_isAnalyticIso_zero] at hξ
  obtain ⟨ξ', hξ', hcomm⟩ := h m hm e he σ s hs 𝔞 h𝔞 E ξ hξ.1 hξ.2
  refine ⟨ξ', isAnalyticUnif_iff_isAnalyticIso_zero.2 ⟨hξ', ?_⟩, hcomm⟩
  have hk0 : kappa m 0 = 0 := by
    have := kappa_rat (m := m) 0
    simpa using this
  have h0𝔞 : (0 : QNeg m) ∈ 𝔞 := by
    obtain ⟨L, hL⟩ := h𝔞
    have : (0 : ℂ) ∈ kappa m '' 𝔞 := by rw [← hL]; exact zero_mem _
    obtain ⟨a, ha, ha0⟩ := this
    rw [← hk0] at ha0
    rwa [kappa_injective ha0] at ha
  have h0 : finPart s * algebraMap (QNeg m) (AfK m) 0 - algebraMap (QNeg m) (AfK m) 0 ∈
      latHat m 𝔞 := by
    simp only [map_zero, mul_zero, sub_zero]
    exact subset_closure ⟨0, h0𝔞, map_zero _⟩
  have := hcomm 0 0 h0
  rw [hk0, hξ.2] at this
  exact this.symm

end Printed

end HCMW
