/-
glue-I3-linalg: the commutant argument of step C2 (N5 L731-734), as linear algebra over
Mathlib's `Representation`, `IsSemisimpleRepresentation` and `IsIrreducible`.

`isIrreducible_of_commutant_scalar`: a nonzero semisimple representation whose equivariant
endomorphisms are all scalars is irreducible.
-/
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

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

/-- The commutant of a family of endomorphisms. -/
def commOf {W : Type*} [AddCommGroup W] [Module k W] (r : G → W →ₗ[k] W) :
    Submodule k (W →ₗ[k] W) where
  carrier := {φ | ∀ g, φ ∘ₗ r g = r g ∘ₗ φ}
  add_mem' := by
    intro φ ψ hφ hψ g
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, hφ g, hψ g]
  zero_mem' := by intro g; simp
  smul_mem' := by
    intro c φ hφ g
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ g]

/-- `(a, b, c, d) ↦ [[a, b], [c, d]]`, an injective linear map
`End_G(V)⁴ → End_G(V ⊕ V)`. -/
def blockMap (ρ : Representation k G V) :
    (commOf (k := k) (fun g => ρ g)) × (commOf (k := k) (fun g => ρ g)) ×
      (commOf (k := k) (fun g => ρ g)) × (commOf (k := k) (fun g => ρ g)) →ₗ[k]
      commOf (k := k) (fun g => (ρ g).prodMap (ρ g)) where
  toFun t := ⟨((t.1 : V →ₗ[k] V).coprod (t.2.1 : V →ₗ[k] V)).prod
      ((t.2.2.1 : V →ₗ[k] V).coprod (t.2.2.2 : V →ₗ[k] V)), by
    intro g
    have ha : ∀ v, (t.1 : V →ₗ[k] V) (ρ g v) = ρ g ((t.1 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.1.2 g)
    have hb : ∀ v, (t.2.1 : V →ₗ[k] V) (ρ g v) = ρ g ((t.2.1 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.2.1.2 g)
    have hc : ∀ v, (t.2.2.1 : V →ₗ[k] V) (ρ g v) = ρ g ((t.2.2.1 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.2.2.1.2 g)
    have hd : ∀ v, (t.2.2.2 : V →ₗ[k] V) (ρ g v) = ρ g ((t.2.2.2 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.2.2.2.2 g)
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp [ha, hb, hc, hd]⟩
  map_add' s t := by
    apply Subtype.ext; apply LinearMap.ext; rintro ⟨x, y⟩
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
    simp [add_add_add_comm]
  map_smul' c t := by
    apply Subtype.ext; apply LinearMap.ext; rintro ⟨x, y⟩
    simp

lemma blockMap_injective (ρ : Representation k G V) : Function.Injective (blockMap ρ) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  rintro ⟨a, b, c, d⟩ h
  have h' := congrArg Subtype.val h
  have hx : ∀ x, (blockMap ρ (a, b, c, d) : V × V →ₗ[k] V × V) (x, 0) = 0 :=
    fun x => by rw [h']; rfl
  have hy : ∀ y, (blockMap ρ (a, b, c, d) : V × V →ₗ[k] V × V) (0, y) = 0 :=
    fun y => by rw [h']; rfl
  simp only [blockMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.prod_apply, Function.prod,
    LinearMap.coprod_apply, map_zero, add_zero, zero_add, Prod.mk_eq_zero] at hx hy
  refine Prod.ext (Subtype.ext (LinearMap.ext fun x => (hx x).1))
    (Prod.ext (Subtype.ext (LinearMap.ext fun y => (hy y).1))
      (Prod.ext (Subtype.ext (LinearMap.ext fun x => (hx x).2))
        (Subtype.ext (LinearMap.ext fun y => (hy y).2))))

set_option backward.isDefEq.respectTransparency false in
/-- **C2 over the splitting field (GLUE, proved).** N5 L731-734: over a field `E` splitting `B`,
`V_ℓ(A) ⊗ E ≅ r ⊕ r` and `dim_E End_G(V_ℓ A ⊗ E) = 4`. If the commutant of `r ⊕ r` has
dimension at most `4` and `r` is semisimple and nonzero, then `r` is irreducible, and its
commutant is the scalars. -/
theorem isIrreducible_of_finrank_commOf_prod_le_four (ρ : Representation k G V) [Nontrivial V]
    (hss : ρ.IsSemisimpleRepresentation)
    [FiniteDimensional k V]
    (h4 : Module.finrank k (commOf (k := k) (fun g => (ρ g).prodMap (ρ g))) ≤ 4) :
    ρ.IsIrreducible ∧ ∀ φ ∈ commOf (k := k) (fun g => ρ g), ∃ c : k, φ = c • LinearMap.id := by
  have hinj := blockMap_injective ρ
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_prod] at hle
  have hC1 : Module.finrank k (commOf (k := k) (fun g => ρ g)) ≤ 1 := by omega
  set C := commOf (k := k) (fun g => ρ g)
  have hid : (LinearMap.id : V →ₗ[k] V) ∈ C := by intro g; simp
  have hid0 : (⟨LinearMap.id, hid⟩ : C) ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact hx (by simpa using congrArg (fun f : C => (f : V →ₗ[k] V) x) h0)
  have hscalar : ∀ φ ∈ C, ∃ c : k, φ = c • LinearMap.id := by
    intro φ hφ
    have hpos : 0 < Module.finrank k C :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hid0⟩
    have h1 : Module.finrank k C = 1 := by omega
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨LinearMap.id, hid⟩ : C) hid0).mp
      h1 ⟨φ, hφ⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
  exact ⟨isIrreducible_of_commutant_scalar ρ hss (fun φ hφ => hscalar φ hφ), hscalar⟩

end GlueI3

#print axioms GlueI3.isIrreducible_of_commutant_scalar
#print axioms GlueI3.isIrreducible_of_finrank_commOf_prod_le_four
