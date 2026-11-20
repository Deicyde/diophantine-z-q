import ZInQKernel.Contrib.OneProof.BShFamilySections
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import ZInQKernel.Contrib.OneProof.BShFamilySplittingCriterion
import Mathlib.FieldTheory.SplittingField.Construction

/-! ON THE SPOT (provenance (c)): lift the pointwise root exhaustion to a
factorization over the meromorphic germ field. Monic remainders transfer through
the germ quotient, even when a division polynomial has repeated roots. -/

noncomputable section

namespace BShFamily

open Filter Polynomial UpperHalfPlane PeriodPair T5Glue X1Igusa.Weber
open BShTraces ShimuraPointDict LeafModCurves AlgebraicGeometry CategoryTheory
open scoped Topology

/-- Restrict a meromorphic germ to the upper half-plane. -/
def restrict (τ : ℍ) : MeromorphicGerm (τ : ℂ) →+* Germ (𝓝[≠] τ) ℂ where
  toFun m := (meromorphicIncl _ m).compTendsto ((↑) : ℍ → ℂ) (map_punctured_coe τ).le
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := by
    rw [map_add]
    generalize meromorphicIncl _ a = f, meromorphicIncl _ b = g
    induction f using Germ.inductionOn
    induction g using Germ.inductionOn
    rfl
  map_mul' a b := by
    rw [map_mul]
    generalize meromorphicIncl _ a = f, meromorphicIncl _ b = g
    induction f using Germ.inductionOn
    induction g using Germ.inductionOn
    rfl

theorem restrict_eq_coe {τ : ℍ} {r : MeromorphicGerm (τ : ℂ)} {f : ℂ → ℂ}
    (h : meromorphicIncl _ r = (f : PuncturedGerm (τ : ℂ))) :
    restrict τ r = ((fun s : ℍ => f s) : Germ (𝓝[≠] τ) ℂ) := by
  change (meromorphicIncl _ r).compTendsto ((↑) : ℍ → ℂ) (map_punctured_coe τ).le = _
  rw [h]
  rfl

/-- Restriction detects equality of punctured germs. -/
theorem restrict_punctured_injective (τ : ℍ) :
    Function.Injective (fun m : PuncturedGerm (τ : ℂ) =>
      m.compTendsto ((↑) : ℍ → ℂ) (map_punctured_coe τ).le) := by
  intro a b
  induction a using Germ.inductionOn with | _ a =>
  induction b using Germ.inductionOn with | _ b =>
  intro h
  apply Germ.coe_eq.mpr
  rw [← map_punctured_coe τ, Filter.EventuallyEq, Filter.eventually_map]
  exact Germ.coe_eq.mp h

/-- The division of two germs is represented by pointwise division when the
chosen denominator is nonzero eventually. -/
theorem restrict_div {τ : ℍ} {a b : MeromorphicGerm (τ : ℂ)}
    {f g : ℍ → ℂ} (hf : restrict τ a = (f : Germ (𝓝[≠] τ) ℂ))
    (hg : restrict τ b = (g : Germ (𝓝[≠] τ) ℂ)) (hn : ∀ᶠ s in 𝓝[≠] τ, g s ≠ 0) :
    restrict τ (a / b) = ((fun s : ℍ => f s / g s) : Germ (𝓝[≠] τ) ℂ) := by
  have hb : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hg
    have h0 := (Germ.coe_eq.mp hg : (fun _ => 0) =ᶠ[𝓝[≠] τ] g)
    obtain ⟨s, h, h'⟩ := (hn.and h0).exists
    exact h h'.symm
  obtain ⟨h, hh⟩ := Quotient.exists_rep (restrict τ (a / b))
  change (h : Germ (𝓝[≠] τ) ℂ) = _ at hh
  have hm : (h : Germ (𝓝[≠] τ) ℂ) * (g : Germ (𝓝[≠] τ) ℂ) = (f : Germ (𝓝[≠] τ) ℂ) := by
    rw [hh, ← hg, ← map_mul, div_mul_cancel₀ _ hb, hf]
  rw [← hh]
  apply Germ.coe_eq.mpr
  have hm' := (Germ.coe_eq.mp hm : (fun s => h s * g s) =ᶠ[𝓝[≠] τ] f)
  filter_upwards [hm', hn] with s hs hn'
  exact (eq_div_iff hn').mpr hs

/-- A nonzero meromorphic germ is eventually represented by nonzero values. -/
theorem restrict_eventually_ne_zero {τ : ℍ} {a : MeromorphicGerm (τ : ℂ)}
    {f : ℍ → ℂ} (hf : restrict τ a = (f : Germ (𝓝[≠] τ) ℂ)) (ha : a ≠ 0) :
    ∀ᶠ s in 𝓝[≠] τ, f s ≠ 0 := by
  obtain ⟨g, hg⟩ := Quotient.exists_rep (restrict τ a⁻¹)
  change (g : Germ (𝓝[≠] τ) ℂ) = _ at hg
  have he : (f : Germ (𝓝[≠] τ) ℂ) * (g : Germ (𝓝[≠] τ) ℂ) = 1 := by
    rw [← hf, hg, ← map_mul, mul_inv_cancel₀ ha, map_one]
  have hev := (Germ.coe_eq.mp he : (fun s => f s * g s) =ᶠ[𝓝[≠] τ] (fun _ => 1))
  exact hev.mono fun s hs hs₀ => by simp [hs₀] at hs

/-- In the pointwise germ ring, division of the meromorphic classes agrees
with the germ of pointwise division, including the zero-denominator case. -/
theorem restrict_div_eq (τ : ℍ) (a b : MeromorphicGerm (τ : ℂ)) :
    restrict τ (a / b) = restrict τ a / restrict τ b := by
  obtain ⟨f,hf⟩ := Quotient.exists_rep (restrict τ a)
  obtain ⟨g,hg⟩ := Quotient.exists_rep (restrict τ b)
  change (f : Germ (𝓝[≠] τ) ℂ) = _ at hf
  change (g : Germ (𝓝[≠] τ) ℂ) = _ at hg
  by_cases hb : b = 0
  · subst b
    rw [div_zero, map_zero, ← hf]
    change 0 = ((fun s : ℍ => f s / 0) : Germ (𝓝[≠] τ) ℂ)
    simp only [div_zero]
    rfl
  · rw [restrict_div hf.symm hg.symm (restrict_eventually_ne_zero hg.symm hb), ← hf, ← hg]
    rfl

/-- At every punctured parameter, both generic normalization tests eventually
hold. -/
theorem eventually_good (τ : ℍ) :
    ∀ᶠ σ in 𝓝[≠] τ, (pp σ).g₂ ≠ 0 ∧ (pp σ).g₃ ≠ 0 := by
  let F : ℂ → ℂ := fun z => G2f z * G3f z
  have hF : DifferentiableOn ℂ F Hs := diffOn_G2f.mul diffOn_G3f
  have ha := hF.analyticOnNhd isOpen_Hs (τ : ℂ) τ.coe_im_pos
  rcases ha.meromorphicAt.eventually_eq_zero_or_eventually_ne_zero with h | h
  · obtain ⟨z, hz, h2, h3⟩ := exists_good_point
    exact (mul_ne_zero h2 h3 (eq_zero_of_eventually hF τ.coe_im_pos
      ((ha.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp h)
      z hz)).elim
  · filter_upwards [Tendsto.eventually (map_punctured_coe τ).le h] with σ hσ
    have hn : (pp σ).g₂ * (pp σ).g₃ ≠ 0 := by simpa [F, G2f, G3f, ofComplex_apply] using hσ
    exact ⟨fun h => hn (by rw [h, zero_mul]), fun h => hn (by rw [h, mul_zero])⟩

#print axioms restrict_eq_coe
#print axioms restrict_punctured_injective
#print axioms restrict_div
#print axioms restrict_eventually_ne_zero
#print axioms restrict_div_eq
#print axioms eventually_good

end BShFamily
