import ZInQKernel.HDecomp.Descent.B2Glue

/-!
# T31, abstract part: sign cocycles inflated through a cyclic quotient of even index

Let `ψ : G →* H` be a homomorphism with open kernel from a topological group onto a finite
cyclic group `H = ⟨φ⟩` of order `2f`, with `φ = ψ g₁`. A sign `2`-cocycle `η` on `G` which only
depends on the classes of its arguments modulo `ψ⁻¹⟨φ^f⟩` is the coboundary of a locally
constant sign cochain.

This is the elementary fact that `H²(ℤ/f, ±1) → H²(ℤ/2f, ±1)` (inflation) is zero: the class
of a cocycle of a cyclic group `⟨φ⟩` of order `n` with trivial coefficients is the norm
`∏_{i<n} η(φ, φ^i)`, and inflation from `ℤ/f` to `ℤ/2f` squares it.
-/

namespace ZInQ.Contrib.T31

open GlueDescent.B2

variable {G H U : Type*} [Group G] [Group H] [CommGroup U]

/-- `u k = ∏_{i<k} η(g, g^i)`. -/
def uProd (η : G → G → U) (g : G) (k : ℕ) : U :=
  ∏ i ∈ Finset.range k, η g (g ^ i)

theorem eta_one_left (η : G → G → U)
    (hc : ∀ x y z, η (x * y) z * η x y = η y z * η x (y * z)) (z : G) : η 1 z = η 1 1 := by
  have h := hc 1 1 z
  simp only [one_mul] at h
  exact (mul_left_cancel h).symm

/-- `η(g^a, g^b) = η(1,1) · u(a+b) · u(a)⁻¹ · u(b)⁻¹`. -/
theorem eta_pow_pow (η : G → G → U)
    (hc : ∀ x y z, η (x * y) z * η x y = η y z * η x (y * z)) (g : G) (a b : ℕ) :
    η (g ^ a) (g ^ b) =
      η 1 1 * uProd η g (a + b) * (uProd η g a)⁻¹ * (uProd η g b)⁻¹ := by
  induction a with
  | zero =>
    simp only [pow_zero, zero_add, uProd, Finset.range_zero, Finset.prod_empty, inv_one,
      mul_one]
    rw [eta_one_left η hc, mul_inv_cancel_right]
  | succ a ih =>
    have h := hc g (g ^ a) (g ^ b)
    rw [← pow_succ', ← pow_add, ih] at h
    have hu1 : uProd η g (a + 1) = uProd η g a * η g (g ^ a) := Finset.prod_range_succ _ _
    have hu2 : uProd η g (a + 1 + b) = uProd η g (a + b) * η g (g ^ (a + b)) := by
      rw [show a + 1 + b = (a + b) + 1 by omega]; exact Finset.prod_range_succ _ _
    rw [hu1, hu2]
    have h' := congrArg (· * (η g (g ^ a))⁻¹) h
    simp only [mul_inv_cancel_right] at h'
    rw [h']
    simp only [mul_inv]
    ac_rfl

theorem uProd_add (η : G → G → U) (g : G) (k n : ℕ) :
    uProd η g (k + n) = uProd η g k * ∏ i ∈ Finset.range n, η g (g ^ (k + i)) :=
  Finset.prod_range_add _ _ _

section Main

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Main abstract lemma.** -/
theorem signCob_of_cyclic_even (ψ : G →* H) (hker : IsOpen (ψ.ker : Set G)) (φ : H)
    (hpow : ∀ h : H, ∃ k : ℕ, φ ^ k = h) (g₁ : G) (hg₁ : ψ g₁ = φ) (f : ℕ)
    (hord : orderOf φ = 2 * f) (η : G → G → U)
    (hη : IsSignCocycle η)
    (hinv : ∀ σ σ' τ τ' : G, (∃ i : ℕ, ψ σ' = ψ σ * (φ ^ f) ^ i) →
      (∃ j : ℕ, ψ τ' = ψ τ * (φ ^ f) ^ j) → η σ τ = η σ' τ') :
    SignCob η := by
  obtain ⟨-, hsq, hc⟩ := hη
  classical
  set u := uProd η g₁ with hu_def
  -- `u` is `2f`-periodic.
  have hshift : ∀ j : ℕ, η g₁ (g₁ ^ (j + f)) = η g₁ (g₁ ^ j) := fun j =>
    (hinv g₁ g₁ (g₁ ^ j) (g₁ ^ (j + f)) ⟨0, by simp⟩ ⟨1, by simp [hg₁, pow_add]⟩).symm
  have hper : ∀ k, u (k + 2 * f) = u k := by
    intro k
    rw [hu_def, uProd_add, two_mul, Finset.prod_range_add]
    have : ∏ i ∈ Finset.range f, η g₁ (g₁ ^ (k + (f + i))) =
        ∏ i ∈ Finset.range f, η g₁ (g₁ ^ (k + i)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [show k + (f + i) = (k + i) + f by omega, hshift]
    rw [this, ← sq, ← Finset.prod_pow]
    simp [hsq]
  have hper' : ∀ k j, u (k + 2 * f * j) = u k := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih => rw [mul_add, mul_one, ← add_assoc, hper, ih]
  have hmod : ∀ a b, a ≡ b [MOD 2 * f] → u a = u b := by
    intro a b hab
    rw [← Nat.mod_add_div a (2 * f), ← Nat.mod_add_div b (2 * f), hper', hper', hab]
  -- The exponent of `ψ σ`.
  let kH : H → ℕ := fun h => Classical.choose (hpow h)
  have hkH : ∀ h, φ ^ kH h = h := fun h => Classical.choose_spec (hpow h)
  let γ : G → U := fun σ => η 1 1 * (u (kH (ψ σ)))⁻¹
  have hred : ∀ σ τ, η σ τ = η (g₁ ^ kH (ψ σ)) (g₁ ^ kH (ψ τ)) := fun σ τ =>
    hinv σ _ τ _ ⟨0, by simp [map_pow, hg₁, hkH]⟩ ⟨0, by simp [map_pow, hg₁, hkH]⟩
  have hsqu : ∀ k, u k ^ 2 = 1 := by
    intro k
    rw [hu_def, uProd, ← Finset.prod_pow]
    simp [hsq]
  refine ⟨γ, ?_, ?_, ?_⟩
  · refine GlueDescent.B2Q.isLocallyConstant_of_openSubgroup ψ.ker hker γ fun σ k hk => ?_
    simp only [γ, map_mul, MonoidHom.mem_ker.1 hk, mul_one]
  · intro σ
    simp only [γ, mul_pow, inv_pow, hsq, hsqu, inv_one, mul_one]
  · intro σ τ
    rw [hred, eta_pow_pow η hc]
    have hk : kH (ψ (σ * τ)) ≡ kH (ψ σ) + kH (ψ τ) [MOD 2 * f] := by
      rw [← hord, ← pow_eq_pow_iff_modEq, hkH, pow_add, hkH, hkH, map_mul]
    simp only [dB, γ]
    rw [hmod _ _ hk]
    have h1 : η 1 1 * η 1 1 = 1 := by rw [← sq, hsq]
    simp only [mul_inv, inv_inv]
    calc η 1 1 * u (kH (ψ σ) + kH (ψ τ)) * (u (kH (ψ σ)))⁻¹ * (u (kH (ψ τ)))⁻¹
        = (η 1 1 * η 1 1) * η 1 1 * u (kH (ψ σ) + kH (ψ τ)) * (u (kH (ψ σ)))⁻¹ *
            (u (kH (ψ τ)))⁻¹ := by rw [h1, one_mul]
      _ = _ := by
          have h2 : (η 1 1)⁻¹ = η 1 1 := by
            rw [inv_eq_iff_mul_eq_one, h1]
          rw [h2]; ac_rfl

end Main

end ZInQ.Contrib.T31
