import FrobLift.WildImageV001

/-!
# The exact Frobenius–tame relation on the fixed space of the wild image

Let `ρ : Gal(Ω/K) →* (End_F V)ˣ` be a linear representation. The subspace `V^{ρ(W)}` of vectors
fixed by the wild image is stable under the decomposition group (which normalizes `ρ(W)`), and on
it the Frobenius–tame relation is exact: for a Frobenius lift `φ` with exponent `q` and an inertia
element `τ`, `ρφ ρτ ρφ⁻¹ v = (ρτ)^q v` for every `v ∈ V^{ρ(W)}`.
-/

noncomputable section

namespace FrobLift

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {w : ValuationSubring Ω}
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  (ρ : (Ω ≃ₐ[K] Ω) →* (Module.End F V)ˣ)

/-- The vectors fixed by the wild image. -/
def wildFixed (w : ValuationSubring Ω) : Submodule F V where
  carrier := {v | ∀ g ∈ wildImage ρ w, (g : Module.End F V) v = v}
  add_mem' := by
    intro a b ha hb g hg
    rw [map_add, ha g hg, hb g hg]
  zero_mem' := by
    intro g _
    exact map_zero _
  smul_mem' := by
    intro c v hv g hg
    rw [map_smul, hv g hg]

variable {ρ}

theorem mem_wildFixed_iff (v : V) :
    v ∈ wildFixed ρ w ↔ ∀ g ∈ wildImage ρ w, (g : Module.End F V) v = v := Iff.rfl

/-- **The fixed space of the wild image is stable under the decomposition group.** -/
theorem wildFixed_stable [Algebra.IsAlgebraic K Ω] {g : Ω ≃ₐ[K] Ω}
    (hg : g ∈ w.decompositionSubgroup K) {v : V} (hv : v ∈ wildFixed ρ w) :
    ((ρ g : (Module.End F V)ˣ) : Module.End F V) v ∈ wildFixed ρ w := by
  intro h hh
  have hc : (ρ g)⁻¹ * h * ((ρ g)⁻¹)⁻¹ ∈ wildImage ρ w := by
    have := conj_mem_wildImage (ρ := ρ) (inv_mem hg) hh
    rwa [map_inv] at this
  have hfix := hv _ hc
  rw [inv_inv] at hfix
  have e : (h : Module.End F V) (((ρ g : (Module.End F V)ˣ) : Module.End F V) v) =
      ((ρ g : (Module.End F V)ˣ) : Module.End F V)
        ((((ρ g)⁻¹ * h * ρ g : (Module.End F V)ˣ) : Module.End F V) v) := by
    simp only [Units.val_mul, Module.End.mul_apply]
    rw [← Module.End.mul_apply (((ρ g : (Module.End F V)ˣ) : Module.End F V)), ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Module.End.one_apply]
  rw [e, hfix]

/-- **The exact Frobenius–tame relation on `V^{ρ(W)}`.** -/
theorem frob_tame_exact_on_wildFixed [Algebra.IsAlgebraic K Ω] {φ : Ω ≃ₐ[K] Ω}
    (hD : φ ∈ w.decompositionSubgroup K) {q : ℕ} (hcong : ∀ x ∈ w, w.valuation (φ x - x ^ q) < 1)
    {τ : Ω ≃ₐ[K] Ω} (hτ : PkgI2.IsInertia w τ) {v : V} (hv : v ∈ wildFixed ρ w) :
    ((ρ φ * ρ τ * (ρ φ)⁻¹ : (Module.End F V)ˣ) : Module.End F V) v =
      ((ρ τ ^ q : (Module.End F V)ˣ) : Module.End F V) v := by
  have hw := hv _ (frob_tame_mem_wildImage (ρ := ρ) hD hcong hτ)
  calc ((ρ φ * ρ τ * (ρ φ)⁻¹ : (Module.End F V)ˣ) : Module.End F V) v
      = ((ρ φ * ρ τ * (ρ φ)⁻¹ : (Module.End F V)ˣ) : Module.End F V)
          ((((ρ φ * ρ τ * (ρ φ)⁻¹)⁻¹ * ρ τ ^ q : (Module.End F V)ˣ) : Module.End F V) v) := by
        rw [hw]
    _ = (((ρ φ * ρ τ * (ρ φ)⁻¹) * ((ρ φ * ρ τ * (ρ φ)⁻¹)⁻¹ * ρ τ ^ q) : (Module.End F V)ˣ) :
          Module.End F V) v := by
        rw [Units.val_mul (ρ φ * ρ τ * (ρ φ)⁻¹), Module.End.mul_apply]
    _ = ((ρ τ ^ q : (Module.End F V)ˣ) : Module.End F V) v := by
        rw [mul_inv_cancel_left]

end FrobLift
