import ZInQKernel.HDecomp.Faltings.HodgeData

/-!
# Coefficients of a lattice in a one-dimensional vector space

A nonzero vector identifies an `L`-line with `L`. The inverse image of an integral lattice
under this map is its coefficient submodule. No generator over the ring of integers is chosen.

Locators: Mathlib, `finrank_eq_one_iff_of_nonzero'`, `Submodule.fg_of_fg_map_injective`,
`AddSubgroup.relIndex_map_map_of_injective`; `HodgeData.secIndex`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal

open NumberField
open ZInQ.DefFaltings

variable {L : Type*} [Field L]
variable {V : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
  [IsScalarTower (𝓞 L) L V]

/-- DEFINITION. The coefficient map `a ↦ a • η`.
Locator: Mathlib, `LinearMap.toSpanSingleton`, `LinearMap.restrictScalars`. -/
def coordinateMap (η : V) : L →ₗ[𝓞 L] V :=
  (LinearMap.toSpanSingleton L V η).restrictScalars (𝓞 L)

/-- THEOREM. The coefficient map has the stipulated value.
Locator: `coordinateMap`, Mathlib, `LinearMap.toSpanSingleton_apply`. -/
@[simp] theorem coordinateMap_apply (η : V) (a : L) : coordinateMap (L := L) η a = a • η := rfl

/-- DEFINITION. The coefficients belonging to the original lattice.
Locator: Mathlib, `Submodule.comap`. -/
def coefficientSubmodule (M : Submodule (𝓞 L) V) (η : V) : Submodule (𝓞 L) L :=
  M.comap (coordinateMap (L := L) η)

/-- THEOREM. Membership is exactly the original lattice condition.
Locator: `coefficientSubmodule`, Mathlib, `Submodule.mem_comap`. -/
@[simp] theorem mem_coefficientSubmodule (M : Submodule (𝓞 L) V) (η : V) (a : L) :
    a ∈ coefficientSubmodule M η ↔ a • η ∈ M := Iff.rfl

/-- THEOREM. A nonzero vector has unique scalar coefficients.
Locator: Mathlib, `smul_eq_zero`, `sub_smul`. -/
theorem coordinateMap_injective (η : V) (hη : η ≠ 0) :
    Function.Injective (coordinateMap (L := L) η) := by
  intro a b hab
  have hzero : (a - b) • η = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr hab
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hη)

/-- THEOREM. Every vector in an `L`-line is a multiple of any nonzero vector.
Locator: Mathlib, `finrank_eq_one_iff_of_nonzero'`. -/
theorem coordinateMap_surjective (hV : Module.finrank L V = 1) (η : V) (hη : η ≠ 0) :
    Function.Surjective (coordinateMap (L := L) η) :=
  (finrank_eq_one_iff_of_nonzero' η hη).mp hV

/-- THEOREM. Reconstruction of the original lattice from its coefficients.
Locator: `coordinateMap_surjective`, Mathlib, `Submodule.mem_map`. -/
theorem coefficientSubmodule_map (hV : Module.finrank L V = 1) (η : V) (hη : η ≠ 0)
    (M : Submodule (𝓞 L) V) : M = (coefficientSubmodule M η).map (coordinateMap (L := L) η) := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := coordinateMap_surjective hV η hη v
    exact ⟨a, by change coordinateMap (L := L) η a ∈ M; rwa [ha], ha⟩
  · rintro ⟨a, ha, rfl⟩
    exact ha

/-- THEOREM. Every lattice vector has one and only one admissible coefficient.
Locator: `coordinateMap_surjective`, `coordinateMap_injective`. -/
theorem existsUnique_coefficient (hV : Module.finrank L V = 1) (η : V) (hη : η ≠ 0)
    (M : Submodule (𝓞 L) V) (v : V) (hv : v ∈ M) :
    ∃! a : L, a ∈ coefficientSubmodule M η ∧ a • η = v := by
  obtain ⟨a, ha⟩ := coordinateMap_surjective hV η hη v
  refine ⟨a, ⟨?_, ha⟩, ?_⟩
  · change coordinateMap (L := L) η a ∈ M
    rwa [ha]
  · intro b hb
    exact coordinateMap_injective (L := L) η hη (hb.2.trans ha.symm)

/-- DEFINITION. The coefficient submodule and the lattice are isomorphic over `𝓞_L`.
Locator: Mathlib, `LinearEquiv.ofBijective`, `LinearMap.restrict`. -/
def coefficientEquiv (hV : Module.finrank L V = 1) (η : V) (hη : η ≠ 0)
    (M : Submodule (𝓞 L) V) : coefficientSubmodule M η ≃ₗ[𝓞 L] M :=
  LinearEquiv.ofBijective ((coordinateMap (L := L) η).restrict (fun _ hx => hx)) ⟨by
    intro a b hab
    apply Subtype.ext
    exact coordinateMap_injective (L := L) η hη (congrArg Subtype.val hab), by
    rintro ⟨v, hv⟩
    obtain ⟨a, ha⟩ := coordinateMap_surjective hV η hη v
    refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
    change coordinateMap (L := L) η a ∈ M
    rwa [ha]⟩

/-- THEOREM. The lattice isomorphism is the actual coefficient map.
Locator: `coefficientEquiv`, Mathlib, `LinearEquiv.ofBijective_apply`. -/
@[simp] theorem coefficientEquiv_apply (hV : Module.finrank L V = 1) (η : V) (hη : η ≠ 0)
    (M : Submodule (𝓞 L) V) (a : coefficientSubmodule M η) :
    (coefficientEquiv hV η hη M a : V) = (a : L) • η := rfl

/-- THEOREM. A finitely generated lattice has a finitely generated coefficient submodule.
Locator: Mathlib, `Submodule.fg_of_fg_map_injective`; `coefficientSubmodule_map`. -/
theorem coefficientSubmodule_fg (hV : Module.finrank L V = 1) (η : V) (hη : η ≠ 0)
    (M : Submodule (𝓞 L) V) (hfg : M.FG) : (coefficientSubmodule M η).FG := by
  apply Submodule.fg_of_fg_map_injective (coordinateMap (L := L) η)
    (coordinateMap_injective (L := L) η hη)
  rw [← coefficientSubmodule_map hV η hη M]
  exact hfg

/-- THEOREM. A nonzero lattice gives a nonzero coefficient submodule.
Locator: Mathlib, `Submodule.exists_mem_ne_zero_of_ne_bot`; `coordinateMap_surjective`. -/
theorem coefficientSubmodule_ne_bot (hV : Module.finrank L V = 1) (η : V) (hη : η ≠ 0)
    (M : Submodule (𝓞 L) V) (hM : M ≠ ⊥) : coefficientSubmodule M η ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  obtain ⟨a, ha⟩ := coordinateMap_surjective hV η hη v
  have haI : a ∈ coefficientSubmodule M η := by
    change coordinateMap (L := L) η a ∈ M
    rwa [ha]
  intro hbot
  have ha0 : a = 0 := by
    have : a ∈ (⊥ : Submodule (𝓞 L) L) := hbot ▸ haI
    exact this
  apply hv0
  rw [← ha, ha0, map_zero]

/-- THEOREM. A nonzero coefficient submodule spans the field over itself.
Locator: Mathlib, `Submodule.exists_mem_ne_zero_of_ne_bot`, `inv_mul_cancel₀`. -/
theorem submodule_spans_of_ne_bot (I : Submodule (𝓞 L) L) (hI : I ≠ ⊥) :
    Submodule.span L (I : Set L) = ⊤ := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [eq_top_iff]
  intro x _
  have hm := Submodule.smul_mem (Submodule.span L (I : Set L)) (x * a⁻¹)
    (Submodule.subset_span ha)
  simpa only [smul_eq_mul, mul_assoc, inv_mul_cancel₀ ha0, mul_one] using hm

/-- THEOREM. The section index retains the original orientation under coefficients.
Locator: `HodgeData.secIndex`; Mathlib, `AddSubgroup.relIndex_map_map_of_injective`. -/
theorem secIndex_coordinate (hV : Module.finrank L V = 1) (η : V) (hη : η ≠ 0)
    (M : Submodule (𝓞 L) V) (a : L) :
    secIndex M (a • η) = secIndex (coefficientSubmodule M η) a := by
  have hM := coefficientSubmodule_map hV η hη M
  have hspan : Submodule.span (𝓞 L) {a • η} =
      (Submodule.span (𝓞 L) {a}).map (coordinateMap (L := L) η) := by
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  have hi := AddSubgroup.relIndex_map_map_of_injective
    (Submodule.span (𝓞 L) {a}).toAddSubgroup (coefficientSubmodule M η).toAddSubgroup
    (f := (coordinateMap (L := L) η : L →+ V)) (coordinateMap_injective (L := L) η hη)
  rw [← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, ← hM, ← hspan] at hi
  exact hi

end ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal
