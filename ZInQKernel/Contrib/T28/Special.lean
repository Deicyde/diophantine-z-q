import ZInQKernel.Contrib.T28.Covariance
import ZInQKernel.Contrib.T28.Special.NormalForm

/-!
# T28: the special locus `det yv = 0` (task igusa-special)

`T28Special.separationBothSpecial : T28.SeparationBothSpecial`: over an algebraically closed
field of characteristic `0`, two binary sextics `f, g` with `J₁₀ ≠ 0`, both on Clebsch's special
locus `det (yv f) = det (yv g) = 0`, and with equal Igusa invariants `J₂, J₄, J₆, J₁₀`, are
`GL₂ × 𝔾_m`-equivalent.

Proof (Bolza 1888, made explicit):
1. `exists_Nr`: `f ≅ Nr l m n = x(x-1)(x-l)(x-m)(x-n)`;
2. `det yv` is a relative invariant (`T28.det_yv_actC`, task igusa-generic), so
   `det yv (Nr l m n) = 0`; this determinant is the product over the fifteen synthemes of the
   roots (`det_yv_Nr`), so some syntheme is swapped by an involution, and `f ≅ E a b =
   x⁶ + a x⁴ + b x² + 1` (`special_Nr`);
3. inside the family, equal invariants up to weighted scaling give equivalence (`E_sep`), including
   the `D₄`-sub-family where the two non-conjugate involution classes give two normal forms.
No `sorry`, no `axiom`.
-/

namespace T28Special
open PkgI1

theorem Eqv.det_yv {K : Type*} [Field K] [CharZero K] {f g : Fin 7 → K} (h : Eqv f g) (hf : (Matrix.of (yv f)).det = 0) :
    (Matrix.of (yv g)).det = 0 := by
  obtain ⟨a, b, c, d, e, hd, -, rfl⟩ := h
  rw [T28.det_yv_actC f a b c d e hd, hf, mul_zero]

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Bolza's criterion**: a sextic with `J₁₀ ≠ 0` on the special locus `det yv = 0` is equivalent
to some `x⁶ + a x⁴ + b x² + 1`. -/
theorem special_to_E (f : Fin 7 → K) (hJ : J10 f ≠ 0) (hdet : (Matrix.of (yv f)).det = 0) :
    ∃ a b : K, Eqv f (E a b) := by
  obtain ⟨l, m, n, hN⟩ := exists_Nr f hJ
  obtain ⟨a, b, hE⟩ := special_Nr l m n (hN.det_yv hdet) (hN.J10_ne_zero hJ)
  exact ⟨a, b, hN.trans hE⟩

/-- **The special half of T28**: two sextics on the special locus with equal Igusa invariants
are equivalent. -/
theorem separationBothSpecial : T28.SeparationBothSpecial := by
  intro L _ _ _ f g hf hg hdf hdg h2 h4 h6 h10
  obtain ⟨a, b, hfa⟩ := special_to_E f hf hdf
  obtain ⟨a', b', hga⟩ := special_to_E g hg hdg
  obtain ⟨ρ, hρ, j2, j4, j6, j10⟩ := hfa.J
  obtain ⟨ρ', hρ', j2', j4', j6', j10'⟩ := hga.J
  have hE : Eqv (E a b) (E a' b') := by
    refine E_sep a b a' b' ((ρ' / ρ) ^ 2) (pow_ne_zero 2 (div_ne_zero hρ' hρ)) ?_ ?_ ?_ ?_
    · rw [j2', j2, h2]; field_simp
    · rw [j4', j4, h4]; field_simp
    · rw [j6', j6, h6]; field_simp
    · rw [j10', j10, h10]; field_simp
  exact (hfa.trans (hE.trans hga.symm)).sexticAct

end T28Special
