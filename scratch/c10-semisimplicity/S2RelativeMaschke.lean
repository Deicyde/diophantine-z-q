/-
S2 — relative Maschke. Private isolated source, scaled/semisimplicity.

  Field `k`, group `G`, subgroup `H ≤ G` whose index is finite AND invertible in `k`,
  representation `ρ`. If the restriction `ρ|_H` is semisimple then `ρ` is semisimple.

Constructive: the averaged projector over the finite LEFT COSET space `G ⧸ H`, with
representative-independence coming from `H`-linearity of the projector, `G`-equivariance from
the fact that left translation permutes the cosets, and the retraction property from
`(H.index : k) ≠ 0`.

NOT used, and deliberately absent:
  * `[Finite G]` (Mathlib's Maschke needs it; `G_ℚ` is infinite);
  * normality of `H` (the coset-independence step needs only `H`-linearity of the projector);
  * finite-dimensionality of `V`;
  * any assumed semisimplicity of the goal, any topology, any finite-image claim.

Mathlib `56a005855ea1` has no relative Maschke and no Clifford theory; this is new.

Pinned environment: Lean 4.35.0, Mathlib 56a005855ea1 (read-only, prebuilt). No other dependency.
-/

import Mathlib.RepresentationTheory.Semisimple
import Mathlib.LinearAlgebra.Projection
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

namespace ScaledS2

open Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-! ## 1. Conjugation of a linear map by the representation -/

/-- `conj ρ π g = ρ g ∘ π ∘ ρ g⁻¹`. -/
def conj (ρ : Representation k G V) (π : V →ₗ[k] V) (g : G) : V →ₗ[k] V :=
  (ρ g) ∘ₗ π ∘ₗ (ρ g⁻¹)

@[simp] theorem conj_apply (ρ : Representation k G V) (π : V →ₗ[k] V) (g : G) (v : V) :
    conj ρ π g v = ρ g (π (ρ g⁻¹ v)) := rfl

/-- **Representative independence.** If `π` commutes with `ρ h` for every `h ∈ H`, then
`conj ρ π g` depends only on the left coset `gH`. Normality of `H` is not used. -/
theorem conj_mul_of_mem (ρ : Representation k G V) (π : V →ₗ[k] V) {H : Subgroup G}
    (hπ : ∀ h ∈ H, π ∘ₗ ρ h = ρ h ∘ₗ π) (g : G) {h : G} (hh : h ∈ H) :
    conj ρ π (g * h) = conj ρ π g := by
  ext v
  have hinv : π (ρ h⁻¹ (ρ g⁻¹ v)) = ρ h⁻¹ (π (ρ g⁻¹ v)) :=
    LinearMap.congr_fun (hπ h⁻¹ (H.inv_mem hh)) (ρ g⁻¹ v)
  simp only [conj_apply, mul_inv_rev, map_mul, Module.End.mul_apply, hinv]
  rw [← Module.End.mul_apply (ρ h) (ρ h⁻¹), ← map_mul, mul_inv_cancel, map_one]
  simp

/-! ## 2. The coset-indexed family and its average -/

variable (ρ : Representation k G V) (π : V →ₗ[k] V) (H : Subgroup G)

/-- `cosetConj` at the coset `x` is `conj ρ π` at any representative of `x`
(`cosetConj_mk` below). -/
noncomputable def cosetConj (x : G ⧸ H) : V →ₗ[k] V := conj ρ π x.out

variable {ρ π H}

/-- The value of `cosetConj` at `↑g` is computed by **any** representative, by `conj_mul_of_mem`. -/
theorem cosetConj_mk (hπ : ∀ h ∈ H, π ∘ₗ ρ h = ρ h ∘ₗ π) (g : G) :
    cosetConj ρ π H (g : G ⧸ H) = conj ρ π g := by
  have hmem : g⁻¹ * (g : G ⧸ H).out ∈ H := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have key := conj_mul_of_mem ρ π hπ g hmem
  rw [mul_inv_cancel_left] at key
  exact key

/-- Left translation carries the coset family to itself. -/
theorem conj_cosetConj (hπ : ∀ h ∈ H, π ∘ₗ ρ h = ρ h ∘ₗ π) (y : G) (x : G ⧸ H) :
    (ρ y) ∘ₗ (cosetConj ρ π H x) ∘ₗ (ρ y⁻¹) = cosetConj ρ π H (y • x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    have hy : (y • (g : G ⧸ H)) = ((y * g : G) : G ⧸ H) := rfl
    rw [hy, cosetConj_mk hπ, cosetConj_mk hπ]
    ext v
    simp only [conj_apply, LinearMap.coe_comp, Function.comp_apply, mul_inv_rev, map_mul,
      Module.End.mul_apply]

variable (ρ π H)

/-- The averaged projector `|G:H|⁻¹ ∑_{x ∈ G/H} ρ(x) π ρ(x)⁻¹`. -/
noncomputable def avg [Fintype (G ⧸ H)] : V →ₗ[k] V :=
  ((H.index : k))⁻¹ • ∑ x : G ⧸ H, cosetConj ρ π H x

variable {ρ π H}

theorem avg_apply [Fintype (G ⧸ H)] (v : V) :
    avg ρ π H v = ((H.index : k))⁻¹ • ∑ x : G ⧸ H, cosetConj ρ π H x v := by
  simp [avg, LinearMap.sum_apply]

/-- **`G`-equivariance of the average.** Left translation by `y` permutes `G ⧸ H`, and each
summand is carried to the summand at the translated coset. -/
theorem avg_comm [Fintype (G ⧸ H)] (hπ : ∀ h ∈ H, π ∘ₗ ρ h = ρ h ∘ₗ π) (y : G) :
    avg ρ π H ∘ₗ ρ y = ρ y ∘ₗ avg ρ π H := by
  ext v
  have hv : ρ y⁻¹ (ρ y v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; simp
  have step : ∀ x : G ⧸ H, ρ y ((cosetConj ρ π H x) v) = (cosetConj ρ π H (y • x)) (ρ y v) := by
    intro x
    have hx := LinearMap.congr_fun (conj_cosetConj hπ y x) (ρ y v)
    simpa [hv] using hx
  have hsum : ∑ x : G ⧸ H, (cosetConj ρ π H (y • x)) (ρ y v)
      = ∑ x : G ⧸ H, (cosetConj ρ π H x) (ρ y v) :=
    Fintype.sum_bijective (fun x : G ⧸ H => y • x) (MulAction.bijective y) _ _ (fun _ => rfl)
  simp only [LinearMap.coe_comp, Function.comp_apply, avg_apply, map_smul, map_sum]
  rw [← hsum]
  exact congrArg (fun z : V => ((H.index : k))⁻¹ • z)
    (Finset.sum_congr rfl fun x _ => (step x).symm)

/-! ## 3. From an `H`-stable complement to a `G`-stable complement -/

set_option linter.style.haveILetI false in
/-- **S2, relative Maschke.** `H ≤ G` with `(H.index : k) ≠ 0` (so the index is finite and
invertible in `k`): a representation whose restriction to `H` is semisimple is semisimple.

No `[Finite G]`, no normality, no finite-dimensionality. -/
theorem isSemisimpleRepresentation_of_subgroup (H : Subgroup G) (ρ : Representation k G V)
    (hidx : ((H.index : k)) ≠ 0)
    (hH : Representation.IsSemisimpleRepresentation (ρ.comp H.subtype)) :
    ρ.IsSemisimpleRepresentation := by
  classical
  have hne : H.index ≠ 0 := fun h0 => hidx (by rw [h0]; simp)
  haveI : H.FiniteIndex := Subgroup.finiteIndex_iff.mpr hne
  letI : Fintype (G ⧸ H) := Fintype.ofFinite _
  haveI := hH
  refine ⟨fun p => ?_⟩
  -- the same carrier, as a subrepresentation of the restriction
  let p' : Subrepresentation (ρ.comp H.subtype) :=
    ⟨p.toSubmodule, fun h _v hv => p.apply_mem_toSubmodule (h : G) hv⟩
  obtain ⟨q', hq'⟩ := ComplementedLattice.exists_isCompl p'
  have hinf : p.toSubmodule ⊓ q'.toSubmodule = (⊥ : Submodule k V) :=
    congrArg Subrepresentation.toSubmodule (disjoint_iff.mp hq'.disjoint)
  have hsup : p.toSubmodule ⊔ q'.toSubmodule = (⊤ : Submodule k V) :=
    congrArg Subrepresentation.toSubmodule (codisjoint_iff.mp hq'.codisjoint)
  have hcompl : IsCompl p.toSubmodule q'.toSubmodule :=
    ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  -- the `H`-equivariant projector onto `p` along the `H`-stable complement
  set π : V →ₗ[k] V := p.toSubmodule.projection q'.toSubmodule hcompl with hπdef
  have hπ_mem : ∀ v, π v ∈ p.toSubmodule := fun v => Submodule.projection_apply_mem hcompl v
  have hπ_id : ∀ v ∈ p.toSubmodule, π v = v := fun v hv =>
    Submodule.projection_apply_of_mem_left hcompl hv
  have hπ : ∀ h ∈ H, π ∘ₗ ρ h = ρ h ∘ₗ π := by
    intro h hh
    ext v
    have hsplit := Submodule.projection_add_projection_eq_self hcompl v
    set x := π v with hx
    set y := q'.toSubmodule.projection p.toSubmodule hcompl.symm v with hy
    have hxp : x ∈ p.toSubmodule := hπ_mem v
    have hyq : y ∈ q'.toSubmodule := Submodule.projection_apply_mem hcompl.symm v
    have hxp' : ρ h x ∈ p.toSubmodule := p.apply_mem_toSubmodule h hxp
    have hyq' : ρ h y ∈ q'.toSubmodule := q'.apply_mem_toSubmodule ⟨h, hh⟩ hyq
    simp only [LinearMap.coe_comp, Function.comp_apply]
    conv_lhs => rw [← hsplit]
    rw [map_add, map_add, Submodule.projection_apply_of_mem_left hcompl hxp',
      Submodule.projection_apply_of_mem_right hcompl hyq', add_zero]
  -- the averaged projector
  set Pavg := avg ρ π H with hPavg
  have hPavg_mem : ∀ v, Pavg v ∈ p.toSubmodule := by
    intro v
    rw [hPavg, avg_apply]
    refine p.toSubmodule.smul_mem _ (Submodule.sum_mem _ fun x _ => ?_)
    exact p.apply_mem_toSubmodule _ (hπ_mem _)
  have hPavg_id : ∀ v ∈ p.toSubmodule, Pavg v = v := by
    intro v hv
    have hterm : ∀ x : G ⧸ H, cosetConj ρ π H x v = v := by
      intro x
      have hmem : ρ (x.out)⁻¹ v ∈ p.toSubmodule := p.apply_mem_toSubmodule _ hv
      show ρ x.out (π (ρ (x.out)⁻¹ v)) = v
      rw [hπ_id _ hmem, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      simp
    rw [hPavg, avg_apply]
    simp only [hterm, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, ← Nat.cast_smul_eq_nsmul k,
      smul_smul, inv_mul_cancel₀ hidx, one_smul]
  have hPavg_comm : ∀ g : G, Pavg ∘ₗ ρ g = ρ g ∘ₗ Pavg := fun g => avg_comm hπ g
  -- the complement
  refine ⟨⟨LinearMap.ker Pavg, fun g v hv => ?_⟩, ?_⟩
  · have := LinearMap.congr_fun (hPavg_comm g) v
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mem_ker] at this hv ⊢
    rw [this, hv, map_zero]
  · have hproj : IsCompl p.toSubmodule (LinearMap.ker (Pavg.codRestrict p.toSubmodule hPavg_mem)) :=
      LinearMap.isCompl_of_proj (f := Pavg.codRestrict p.toSubmodule hPavg_mem)
        (fun x => Subtype.ext (hPavg_id x.1 x.2))
    rw [LinearMap.ker_codRestrict] at hproj
    constructor
    · rw [disjoint_iff]
      exact Subrepresentation.toSubmodule_injective (disjoint_iff.mp hproj.disjoint)
    · rw [codisjoint_iff]
      exact Subrepresentation.toSubmodule_injective (codisjoint_iff.mp hproj.codisjoint)

/-! ## 4. Checks -/

#check @isSemisimpleRepresentation_of_subgroup
#print axioms isSemisimpleRepresentation_of_subgroup
#print axioms conj_mul_of_mem
#print axioms cosetConj_mk
#print axioms conj_cosetConj
#print axioms avg_comm

end ScaledS2
