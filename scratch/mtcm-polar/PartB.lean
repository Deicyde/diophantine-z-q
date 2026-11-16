import Mathlib

open NumberField

namespace MainCMPolar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open scoped ComplexConjugate

theorem conj_emb (φ : E →+* ℂ) (x : E) : φ (IsCMField.complexConj E x) = conj (φ x) :=
  IsCMField.complexEmbedding_complexConj E φ x

/-- A nonzero totally imaginary element: `β̄ = −β`, `β ≠ 0`. -/
theorem exists_imag : ∃ β : E, IsCMField.complexConj E β = -β ∧ β ≠ 0 := by
  have hne := IsCMField.complexConj_ne_one E
  obtain ⟨α, hα⟩ : ∃ α : E, IsCMField.complexConj E α ≠ α := by
    by_contra h
    push Not at h
    exact hne (AlgEquiv.ext h)
  refine ⟨α - IsCMField.complexConj E α, ?_, ?_⟩
  · rw [map_sub, IsCMField.complexConj_apply_apply]; ring
  · exact sub_ne_zero.2 (Ne.symm hα)

/-- **Step (2), the Riemann-form element** (weak approximation at the infinite places of `E`): for a CM type `Φ`
there is `ζ ∈ E` with `ζ̄ = −ζ` and `Im φᵢ(ζ) > 0` for all `i`. -/
theorem exists_zeta {g : ℕ} (Φ : Fin g → E →+* ℂ)
    (hinj : Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i))) :
    ∃ ζ : E, IsCMField.complexConj E ζ = -ζ ∧ ∀ i, 0 < (Φ i ζ).im := by
  obtain ⟨β, hβc, hβ0⟩ := exists_imag (E := E)
  let w : Fin g → InfinitePlace E := fun i => InfinitePlace.mk (Φ i)
  have hw : Function.Injective w := by
    intro i j hij
    rcases InfinitePlace.mk_eq_iff.1 hij with h | h
    · exact Sum.inl_injective (hinj (by simpa using h))
    · have : (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) (Sum.inr i) =
          (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) (Sum.inl j) := by
        simp only [Sum.elim_inr, Sum.elim_inl]
        rw [← h]; rfl
      exact absurd (hinj this) (by simp)
  let v : Fin g → AbsoluteValue E ℝ := fun i => (w i).1
  have hdense := AbsoluteValue.denseRange_algebraMap_pi (F := E) (v := v)
    (fun i => (w i).isNontrivial)
    (fun i j hij => by
      intro he
      exact hij (hw ((InfinitePlace.eq_iff_isEquiv (K := E)).2 he)))
  -- imaginary parts of `φᵢ(β)`
  have hre : ∀ i, (Φ i β).re = 0 := by
    intro i
    have h1 : conj (Φ i β) = -Φ i β := by rw [← conj_emb, hβc, map_neg]
    have h2 := congrArg Complex.re h1
    simp only [Complex.conj_re, Complex.neg_re] at h2
    linarith
  have him : ∀ i, (Φ i β).im ≠ 0 := by
    intro i h
    apply hβ0
    have : Φ i β = 0 := Complex.ext (hre i) h
    exact (map_eq_zero_iff _ (Φ i).injective).1 this
  let sβ : Fin g → E := fun i => if 0 < (Φ i β).im then β else -β
  have hsβ : ∀ i, (Φ i (sβ i)).im = |(Φ i β).im| := by
    intro i
    by_cases h : 0 < (Φ i β).im
    · simp [sβ, h, abs_of_pos h]
    · have h' : (Φ i β).im < 0 := lt_of_le_of_ne (not_lt.1 h) (him i)
      simp [sβ, h, abs_of_neg h']
  let z : (i : Fin g) → WithAbs (v i) := fun i => WithAbs.toAbs (v i) (sβ i)
  let U : Set ((i : Fin g) → WithAbs (v i)) :=
    Set.pi Set.univ fun i => Metric.ball (z i) (|(Φ i β).im| / 2)
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ fun i _ => Metric.isOpen_ball
  have hUne : U.Nonempty := ⟨z, fun i _ => Metric.mem_ball_self (by
    have := abs_pos.2 (him i); linarith)⟩
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hU hUne
  have hxi : ∀ i, 0 < (Φ i x).im := by
    intro i
    have h := hx i (Set.mem_univ i)
    rw [Metric.mem_ball, dist_eq_norm] at h
    have e : ‖(algebraMap E ((i : Fin g) → WithAbs (v i)) x) i - z i‖ = ‖Φ i x - Φ i (sβ i)‖ := by
      show v i (x - sβ i) = _
      show (InfinitePlace.mk (Φ i)) (x - sβ i) = _
      rw [InfinitePlace.apply, map_sub]
    rw [e] at h
    have h2 : |(Φ i x - Φ i (sβ i)).im| ≤ ‖Φ i x - Φ i (sβ i)‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hsβ] at h2
    have := abs_pos.2 (him i)
    have h3 := (abs_le.1 (h2.trans h.le)).1
    linarith
  refine ⟨x - IsCMField.complexConj E x, ?_, fun i => ?_⟩
  · rw [map_sub, IsCMField.complexConj_apply_apply]; ring
  · rw [map_sub, conj_emb, Complex.sub_im, Complex.conj_im]
    linarith [hxi i]

end MainCMPolar
