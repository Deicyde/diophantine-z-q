/-
S1 — scalar twist. Private isolated source, scaled/semisimplicity.

Content: a pointwise NONZERO SCALAR twist of a representation leaves the invariant-subspace
condition, the `Subrepresentation` lattice and therefore semisimplicity unchanged.

Scope discipline:
  * no averaging / finite-index argument (S2 is a separate writer's task);
  * no continuity, no topology, no finite-image claim, no finite-dimensionality;
  * the nonvanishing of the twisting scalar is PROVED from the group-representation structure
    (`scalar_ne_zero_of_group_rep`), not assumed, wherever the twisted family is a representation
    of a group on a nontrivial carrier;
  * nothing about `B`, matrix units, Tate modules or Faltings appears here: this file is the
    lattice fact alone, stated for an arbitrary field, monoid and module, which is exactly the
    generality at which `GlueC10Link.rhoL` and `GlueDescent.rho` are defined.

Pinned environment: Lean 4.35.0, Mathlib 56a005855ea1 (read-only, already built).
-/

import Mathlib.RepresentationTheory.Semisimple

namespace ScaledS1

open Representation

section Lattice

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- A submodule is stable under `χ • f` iff it is stable under `f`, for a nonzero scalar `χ`. -/
theorem le_comap_smul_iff {W : Submodule k V} {f : V →ₗ[k] V} {χ : k} (hχ : χ ≠ 0) :
    W ≤ W.comap (χ • f) ↔ W ≤ W.comap f := by
  constructor
  · intro h v hv
    have hv' : χ • f v ∈ W := h hv
    have := W.smul_mem χ⁻¹ hv'
    rwa [smul_smul, inv_mul_cancel₀ hχ, one_smul] at this
  · intro h v hv
    exact W.smul_mem χ (h hv)

/-- **The invariant-subspace condition is unchanged by a pointwise nonzero scalar twist.** -/
theorem forall_le_comap_iff_of_smul_twist (ρ τ : Representation k G V) (χ : G → k)
    (hχ : ∀ g, χ g ≠ 0) (hρτ : ∀ g, ρ g = χ g • τ g) (W : Submodule k V) :
    (∀ g, W ≤ W.comap (ρ g)) ↔ (∀ g, W ≤ W.comap (τ g)) := by
  constructor
  · intro h g
    exact (le_comap_smul_iff (W := W) (f := τ g) (hχ g)).mp (by rw [← hρτ g]; exact h g)
  · intro h g
    rw [hρτ g]
    exact (le_comap_smul_iff (W := W) (f := τ g) (hχ g)).mpr (h g)

/-- **The two subrepresentation lattices have the same carriers**, and the identity on carriers
is an order isomorphism. -/
def twistOrderIso (ρ τ : Representation k G V) (χ : G → k) (hχ : ∀ g, χ g ≠ 0)
    (hρτ : ∀ g, ρ g = χ g • τ g) : Subrepresentation ρ ≃o Subrepresentation τ where
  toFun p :=
    ⟨p.toSubmodule, fun g _v hv =>
      (forall_le_comap_iff_of_smul_twist ρ τ χ hχ hρτ p.toSubmodule).mp
        (fun g _ hw => p.apply_mem_toSubmodule g hw) g hv⟩
  invFun q :=
    ⟨q.toSubmodule, fun g _v hv =>
      (forall_le_comap_iff_of_smul_twist ρ τ χ hχ hρτ q.toSubmodule).mpr
        (fun g _ hw => q.apply_mem_toSubmodule g hw) g hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- **S1.** Semisimplicity is invariant under a pointwise nonzero scalar twist. -/
theorem isSemisimpleRepresentation_iff_of_smul_twist (ρ τ : Representation k G V) (χ : G → k)
    (hχ : ∀ g, χ g ≠ 0) (hρτ : ∀ g, ρ g = χ g • τ g) :
    ρ.IsSemisimpleRepresentation ↔ τ.IsSemisimpleRepresentation :=
  OrderIso.complementedLattice_iff (twistOrderIso ρ τ χ hχ hρτ)

/-- **S1, the direction the C10 route uses.** -/
theorem isSemisimpleRepresentation_of_smul_twist (ρ τ : Representation k G V) (χ : G → k)
    (hχ : ∀ g, χ g ≠ 0) (hρτ : ∀ g, ρ g = χ g • τ g)
    (h : τ.IsSemisimpleRepresentation) : ρ.IsSemisimpleRepresentation :=
  (isSemisimpleRepresentation_iff_of_smul_twist ρ τ χ hχ hρτ).mpr h

end Lattice

section Nonvanishing

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **The twisting scalar of a group representation never vanishes** (on a nontrivial carrier).
No hypothesis on the scalars is needed: `ρ g` is invertible because `ρ` is a representation of a
group, so a vanishing scalar would force `(1 : Module.End k V) = 0`.

This is what supplies `ι₃ (a g) ≠ 0` in the C10 application without adding an input: the
manuscript's `a σ = (deg μ_σ)^{-1/4} > 0` is not needed. -/
theorem scalar_ne_zero_of_group_rep [Nontrivial V] (ρ : Representation k G V)
    (T : G → Module.End k V) (χ : G → k) (hρ : ∀ g, ρ g = χ g • T g) (g : G) : χ g ≠ 0 := by
  intro h0
  have hzero : ρ g = 0 := by rw [hρ g, h0, zero_smul]
  have hone : (1 : Module.End k V) = 0 := by
    have : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [hzero, zero_mul] at this
    exact this.symm
  exact one_ne_zero hone

end Nonvanishing

end ScaledS1

namespace ScaledS1

section Comp

variable {k G G' V : Type*} [Field k] [Monoid G] [Monoid G'] [AddCommGroup V] [Module k V]

/-- Pulling a representation back along a **surjective** monoid map does not change the
subrepresentation lattice. (Carrier-level fact, in the same family as the twist; no averaging.) -/
def compOrderIso (φ : G' →* G) (hφ : Function.Surjective φ) (ρ : Representation k G V) :
    Subrepresentation ρ ≃o Subrepresentation (ρ.comp φ) where
  toFun p := ⟨p.toSubmodule, fun g' _v hv => p.apply_mem_toSubmodule (φ g') hv⟩
  invFun q := ⟨q.toSubmodule, fun g _v hv => by
    obtain ⟨g', rfl⟩ := hφ g
    exact q.apply_mem_toSubmodule g' hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Semisimplicity transfers along a surjective change of group. -/
theorem isSemisimpleRepresentation_of_comp_surjective (φ : G' →* G) (hφ : Function.Surjective φ)
    (ρ : Representation k G V)
    (h : Representation.IsSemisimpleRepresentation (ρ.comp φ)) :
    ρ.IsSemisimpleRepresentation :=
  (OrderIso.complementedLattice_iff (compOrderIso φ hφ ρ)).mpr h

/-- …and back. -/
theorem isSemisimpleRepresentation_comp_of_surjective (φ : G' →* G) (hφ : Function.Surjective φ)
    (ρ : Representation k G V) (h : ρ.IsSemisimpleRepresentation) :
    Representation.IsSemisimpleRepresentation (ρ.comp φ) :=
  (OrderIso.complementedLattice_iff (compOrderIso φ hφ ρ)).mp h

end Comp

section Transport

variable {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- A representation carried along a linear equivalence of the carrier. -/
def transport (e : W ≃ₗ[k] V) (ρ : Representation k G V) : Representation k G W where
  toFun g := e.symm.toLinearMap ∘ₗ (ρ g) ∘ₗ e.toLinearMap
  map_one' := by ext w; simp
  map_mul' g h := by
    ext w
    simp [Module.End.mul_eq_comp]

@[simp] theorem transport_apply (e : W ≃ₗ[k] V) (ρ : Representation k G V) (g : G) (w : W) :
    transport e ρ g w = e.symm (ρ g (e w)) := rfl

end Transport

end ScaledS1
