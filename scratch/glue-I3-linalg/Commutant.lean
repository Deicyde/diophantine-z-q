/-
glue-I3-linalg: the commutant argument of step C2 (N5 L731-734), as linear algebra over
Mathlib's `Representation`, `IsSemisimpleRepresentation` and `IsIrreducible`.

`isIrreducible_of_commutant_scalar`: a nonzero semisimple representation whose equivariant
endomorphisms are all scalars is irreducible.
-/
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Projection

namespace GlueI3

open Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The projection onto a subrepresentation along an invariant complement is equivariant. -/
lemma projection_comm {ρ : Representation k G V} (W W' : Subrepresentation ρ)
    (h : IsCompl W.toSubmodule W'.toSubmodule) (g : G) :
    W.toSubmodule.projection W'.toSubmodule h ∘ₗ ρ g =
      ρ g ∘ₗ W.toSubmodule.projection W'.toSubmodule h := by
  apply LinearMap.ext
  intro v
  set p := W.toSubmodule.projection W'.toSubmodule h
  have hv := Submodule.projection_add_projection_eq_self h v
  set a := p v with ha
  set b := W'.toSubmodule.projection W.toSubmodule h.symm v
  have haW : a ∈ W.toSubmodule := by apply Submodule.projection_apply_mem
  have hbW : b ∈ W'.toSubmodule := by apply Submodule.projection_apply_mem
  simp only [LinearMap.coe_comp, Function.comp_apply]
  conv_lhs => rw [← hv, map_add, map_add]
  rw [Submodule.projection_apply_of_mem_right h (W'.apply_mem_toSubmodule g hbW), add_zero,
    Submodule.projection_apply_of_mem_left h (W.apply_mem_toSubmodule g haW)]

/-- **The commutant argument (GLUE, proved).** A semisimple representation on a nonzero space
whose `G`-equivariant endomorphisms are all scalars is irreducible. -/
theorem isIrreducible_of_commutant_scalar (ρ : Representation k G V) [Nontrivial V]
    (hss : ρ.IsSemisimpleRepresentation)
    (hcomm : ∀ φ : V →ₗ[k] V, (∀ g, φ ∘ₗ ρ g = ρ g ∘ₗ φ) → ∃ c : k, φ = c • LinearMap.id) :
    ρ.IsIrreducible := by
  refine { toNontrivial := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at this
    exact hx ((Submodule.mem_bot k).mp this)
  · intro W
    obtain ⟨W', hW'⟩ := hss.exists_isCompl W
    have h : IsCompl W.toSubmodule W'.toSubmodule := by
      constructor
      · rw [disjoint_iff]
        have := congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot
        simp only [Subrepresentation.toSubmodule_inf] at this
        exact this
      · rw [codisjoint_iff]
        have := congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
        simp only [Subrepresentation.toSubmodule_sup] at this
        exact this
    obtain ⟨c, hc⟩ := hcomm _ (projection_comm W W' h)
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    -- some nonzero `w ∈ W` gives `c = 1`
    have hne : W.toSubmodule ≠ ⊥ := by
      intro h0; apply hW; apply Subrepresentation.toSubmodule_injective; rw [h0]; rfl
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := congrArg (fun f => f w) hc
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h1
    rw [Submodule.projection_apply_of_mem_left h hwW] at h1
    have hc1 : c = 1 := by
      have : (c - 1) • w = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hw0)
    -- then `W' = 0`
    have hW'0 : W'.toSubmodule = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have h2 := congrArg (fun f => f y) hc
      simp only [LinearMap.id_apply, hc1, one_smul] at h2
      rw [Submodule.projection_apply_of_mem_right h hy] at h2
      exact (Submodule.mem_bot k).mpr h2.symm
    apply Subrepresentation.toSubmodule_injective
    have := h.sup_eq_top
    rw [hW'0, sup_bot_eq] at this
    exact this

end GlueI3

#print axioms GlueI3.isIrreducible_of_commutant_scalar
