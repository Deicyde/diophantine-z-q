import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Local
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! The local comparison on a unit cell, tex 8809–8815, 8837–8858 and
8925–8936. Matching the three lifts is on-the-spot (c) group algebra. -/

noncomputable section

namespace ZInQ.Manuscript.RC.RelativeAction

open OldStageLaw Visibility Matrix.SpecialLinearGroup
open scoped MatrixGroups BigOperators

variable {G V V₀ : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V₀] [Module ℂ V₀]

/-- Conjugation fixes a vector if the middle operator fixes its Weyl transform.
This also allows a scalar in the Weyl operator, since its inverse is used. -/
theorem conjugate_fixes (R : G →* Module.End ℂ V) (s t : G) (v : V)
    (h : R t (R s v) = R s v) : R (s⁻¹ * t * s) v = v := by
  rw [mul_assoc, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h,
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

/-- For two actions on the same cover, the central scalar cancels from the
relative action of the triangular factors. The hypothesis on the kernel is
an operator identity independent of the vectors or the congruence level. -/
theorem triangular_pair {k : Type*} [Field k] (π : G →* SL(2, k))
    (R : G →* Module.End ℂ V) (R₀ : G →* Module.End ℂ V₀)
    (hkernel : ∀ z : G, π z = 1 → ∃ e : ℂ,
      (∀ x, R z x = e • x) ∧ (∀ x, R₀ z x = e • x))
    (g lower diag upper : G) (u : kˣ) (b c d : k)
    (hg : (π g).val = !![(u : k), b; c, d])
    (hl : (π lower).val = !![1, 0; c / (u : k), 1])
    (hd : (π diag).val = !![(u : k), 0; 0, (u : k)⁻¹])
    (hu : (π upper).val = !![1, b / (u : k); 0, 1])
    (v : V) (v₀ : V₀) (χ z₀ : ℂ)
    (hlu : R lower v = v) (hlu₀ : R₀ lower v₀ = v₀)
    (huu : R upper v = v) (huu₀ : R₀ upper v₀ = v₀)
    (hdu : R diag v = (χ * z₀) • v) (hdu₀ : R₀ diag v₀ = z₀ • v₀) :
    ∃ lam : ℂ, R₀ g v₀ = lam • v₀ ∧ R g v = (χ * lam) • v := by
  let t := lower * diag * upper
  have hdet : (u : k) * d - b * c = 1 := by
    have h := (π g).property
    rw [hg, Matrix.det_fin_two_of] at h
    exact h
  have hproj : π t = π g := by
    apply Subtype.ext
    simp only [t, map_mul, coe_mul, hl, hd, hu, hg]
    exact diagonal_factorization (Units.ne_zero u) hdet
  let z := g * t⁻¹
  have hz : π z = 1 := by dsimp [z]; rw [map_mul, map_inv, hproj, mul_inv_cancel]
  obtain ⟨e, he, he₀⟩ := hkernel z hz
  have ht : g = z * (lower * diag * upper) := by
    change g = (g * t⁻¹) * t
    group
  refine ⟨e * z₀, ?_, ?_⟩
  · rw [ht]
    simp only [map_mul, Module.End.mul_apply, huu₀, hdu₀, LinearMap.map_smul, hlu₀,
      he₀, smul_smul]
  · rw [ht]
    simp only [map_mul, Module.End.mul_apply, huu, hdu, LinearMap.map_smul, hlu, he, smul_smul]
    rw [show e * (χ * z₀) = χ * (e * z₀) by ring]

/-- The Weyl conjugate of the upper phase at minus z projects to
the lower unipotent at z. -/
theorem conjugate_lower_matrix {k : Type*} [Field k] (π : G →* SL(2, k))
    (weyl phase : G) (z : k) (hw : (π weyl).val = !![0, 1; -1, 0])
    (hp : (π phase).val = !![1, -z; 0, 1]) :
    (π (weyl⁻¹ * phase * weyl)).val = !![1, 0; z, 1] := by
  simp only [map_mul, map_inv, coe_mul, hp, hw]
  rw [SL2_inv_expl]
  change (!![(π weyl).val 1 1, -(π weyl).val 0 1;
    -(π weyl).val 1 0, (π weyl).val 0 0] : Matrix (Fin 2) (Fin 2) k) * _ * _ = _
  rw [hw]
  simp

/-- A vector fixed by a set of operators is fixed by the generated subgroup. -/
theorem fixes_of_generators (R : G →* Module.End ℂ V) (v : V) (generators : Set G)
    (hf : ∀ s ∈ generators, R s v = v) {g : G} (hg : g ∈ Subgroup.closure generators) : R g v = v := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hf x hx
  | one => rw [map_one]; rfl
  | mul x y _ _ hx hy => rw [map_mul, Module.End.mul_apply, hy, hx]
  | inv x _ hx =>
    calc
      R x⁻¹ v = R x⁻¹ (R x v) := congrArg (R x⁻¹) hx.symm
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

/-- Outside the support, generators fixing the two spherical vectors give
relative scalar one for every lift of a matrix they generate. -/
theorem spherical_pair {k : Type*} [Field k] (π : G →* SL(2, k))
    (R : G →* Module.End ℂ V) (R₀ : G →* Module.End ℂ V₀)
    (hkernel : ∀ z : G, π z = 1 → ∃ e : ℂ,
      (∀ x, R z x = e • x) ∧ (∀ x, R₀ z x = e • x))
    (v : V) (v₀ : V₀) (generators : Set G)
    (hf : ∀ x ∈ generators, R x v = v) (hf₀ : ∀ x ∈ generators, R₀ x v₀ = v₀)
    (g t : G) (ht : t ∈ Subgroup.closure generators) (hproj : π t = π g) :
    ∃ e : ℂ, R₀ g v₀ = e • v₀ ∧ R g v = e • v := by
  let z := g * t⁻¹
  have hz : π z = 1 := by dsimp [z]; rw [map_mul, map_inv, hproj, mul_inv_cancel]
  obtain ⟨e, he, he₀⟩ := hkernel z hz
  have heq : g = z * t := by dsimp [z]; group
  refine ⟨e, ?_, ?_⟩
  · rw [heq, map_mul, Module.End.mul_apply, fixes_of_generators R₀ v₀ generators hf₀ ht, he₀]
  · rw [heq, map_mul, Module.End.mul_apply, fixes_of_generators R v generators hf ht, he]

/-- Apply the existing Weil-index calculation to the two diagonal actions,
then combine the factors with a common central scalar. The result applies
over a field of any residue characteristic where the hypotheses are supplied. -/
theorem extracted_unit_cell {k X X₀ : Type*} [Field k]
    {γ : kˣ → ℂˣ} {hs : kˣ → kˣ → ℂˣ} (hW : WeilIndexAxioms γ hs)
    (π : G →* SL(2, k))
    (R : G →* Module.End ℂ (X → ℂ)) (R₀ : G →* Module.End ℂ (X₀ → ℂ))
    (hkernel : ∀ z : G, π z = 1 → ∃ e : ℂ,
      (∀ x, R z x = e • x) ∧ (∀ x, R₀ z x = e • x))
    (g weyl lowerPhase diag upper : G) (a b m u : kˣ) (v c d : k)
    (hg : (π g).val = !![(u : k), v; c, d])
    (hw : (π weyl).val = !![0, 1; -1, 0])
    (hp : (π lowerPhase).val = !![1, -(c / (u : k)); 0, 1])
    (hd : (π diag).val = !![(u : k), 0; 0, (u : k)⁻¹])
    (hu : (π upper).val = !![1, v / (u : k); 0, 1])
    (φ : X → ℂ) (φ₀ : X₀ → ℂ) (scale : X → X) (scale₀ : X₀ → X₀) (αu : ℂˣ)
    (hlu : R lowerPhase (R weyl φ) = R weyl φ)
    (hlu₀ : R₀ lowerPhase (R₀ weyl φ₀) = R₀ weyl φ₀)
    (huu : R upper φ = φ) (huu₀ : R₀ upper φ₀ = φ₀)
    (hscale : ∀ x, φ (scale x) = (αu : ℂ) * φ x)
    (hscale₀ : ∀ x, φ₀ (scale₀ x) = φ₀ x)
    (hdiag : ∀ x, R diag φ x = (rQ γ (scaleForm m⁻¹ [a, b, a * b]) u : ℂ) * φ (scale x))
    (hdiag₀ : ∀ x, R₀ diag φ₀ x = (rQ γ [1, 1, 1] u : ℂ) * φ₀ (scale₀ x)) :
    ∃ lam : ℂ, R₀ g φ₀ = lam • φ₀ ∧ R g φ = (((αu : ℂ) * (hs u m : ℂ)) * lam) • φ := by
  refine triangular_pair π R R₀ hkernel g (weyl⁻¹ * lowerPhase * weyl) diag upper u v c d
    hg (conjugate_lower_matrix π weyl lowerPhase _ hw hp) hd hu φ φ₀ ((αu : ℂ) * (hs u m : ℂ)) (rQ γ [1, 1, 1] u : ℂ)
    (conjugate_fixes R weyl lowerPhase φ hlu) (conjugate_fixes R₀ weyl lowerPhase φ₀ hlu₀)
    huu huu₀ ?_ ?_
  · funext x
    rw [hdiag, Pi.smul_apply, smul_eq_mul]
    exact extracted_unit_action hW a b m u scale φ αu hscale x
  · funext x
    rw [hdiag₀, hscale₀, Pi.smul_apply, smul_eq_mul]

/-- The upper-left entry of the inverse is the lower-right entry used in the
classical character. No assumption on the sign of that integral entry is needed. -/
theorem inverse_upper_left {k : Type*} [CommRing k] (g : SL(2, k)) :
    (g⁻¹ : SL(2, k)).val 0 0 = g.val 1 1 := by
  rw [SL2_inv_expl]
  rfl

/-- The unit argument of the old character admits a positive odd
representative, even when the original matrix entry is negative. -/
theorem positive_odd_representative {N : ℕ} [NeZero N] (hfour : 4 ∣ N) (u : (ZMod N)ˣ) :
    ∃ d : ℕ, 0 < d ∧ Odd d ∧ d.Coprime N ∧ (d : ZMod N) = (u : ZMod N) := by
  let d := (u : ZMod N).val
  have hc : d.Coprime N := ZMod.val_coe_unit_coprime u
  have hc₂ := hc.of_dvd_right (dvd_trans (by decide : 2 ∣ 4) hfour)
  have ho : Odd d := Nat.odd_iff.mpr (Nat.mod_two_ne_zero.mp (fun e =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hc₂.symm (Nat.dvd_of_mod_eq_zero e)))
  have hp : 0 < d := by obtain ⟨j, hj⟩ := ho; omega
  exact ⟨d, hp, ho, hc, ZMod.natCast_zmod_val _⟩

private theorem jacobi_prod_den (d : ℤ) (s : Finset ℕ)
    (hn : ∀ p ∈ s, p ≠ 0) :
    jacobiSym d (∏ p ∈ s, p) = ∏ p ∈ s, jacobiSym d p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp,
      jacobiSym.mul_right' d (hn p (Finset.mem_insert_self p s))
        (Finset.prod_ne_zero_iff.mpr fun q hq => hn q (Finset.mem_insert_of_mem hq))]
    rw [ih fun q hq => hn q (Finset.mem_insert_of_mem hq)]

/-- For the squarefree discriminant magnitude, combine the signs at the
prime divisors with the separate dyadic sign (tex 8893–8915). -/
theorem extracted_squarefree_symbols (m d : ℕ) (hm : m % 4 = 3)
    (hsq : Squarefree m) (hd : Odd d) :
    jacobiSym (-1) d * (∏ p ∈ m.primeFactors, jacobiSym (d : ℤ) p) = jacobiSym (m : ℤ) d := by
  have h := jacobi_prod_den (d : ℤ) m.primeFactors
    (fun _ hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
  rw [Nat.prod_primeFactors_of_squarefree hsq] at h
  rw [← h, ← extracted_reciprocity m d hm hd]

/-- Separate the root, relative index and reference scalars, then apply the
Jacobi reciprocity calculation (tex 8893–8915). The product hypothesis
identifies the manuscript's local Hilbert values and contain no operator law. -/
theorem extracted_product_scalar {P : Type*} (places : Finset P) (α h lam : P → ℂ)
    (m d : ℕ) (hm : m % 4 = 3) (hd : Odd d)
    (hh : (∏ p ∈ places, h p) =
      (jacobiSym (-1) d : ℂ) * (jacobiSym (d : ℤ) m : ℂ)) :
    (∏ p ∈ places, α p * h p * lam p) =
      ((∏ p ∈ places, α p) * (jacobiSym (m : ℤ) d : ℂ)) * (∏ p ∈ places, lam p) := by
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hh, extracted_reciprocity m d hm hd]
  push_cast
  rfl

#print axioms conjugate_fixes
#print axioms triangular_pair
#print axioms conjugate_lower_matrix
#print axioms fixes_of_generators
#print axioms spherical_pair
#print axioms extracted_unit_cell
#print axioms inverse_upper_left
#print axioms positive_odd_representative
#print axioms jacobi_prod_den
#print axioms extracted_squarefree_symbols
#print axioms extracted_product_scalar

end ZInQ.Manuscript.RC.RelativeAction
