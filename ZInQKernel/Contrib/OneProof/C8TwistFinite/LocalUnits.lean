import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap

/-! # C8 without Conrad, local part 1: the unit part of a character of `G_{ℚ_p}`

Step C8 (diophantine_zq.tex L758-766) needs only that the global twist `ψ` has finite image.
This file is the local class field theory input of a proof of that statement which uses no
statement about locally algebraic characters.

For a continuous character `f : G_{ℚ_p} → M` into a commutative `T₁` group, `unitChar f` is
the continuous character `ℤ_p^× → M` with `f σ = unitChar f (χ σ)` for every `σ` representing
the local Artin symbol of a unit (`χ` the cyclotomic character). It is built on the inertia
group `I` of `ℚ_p` (Tau Ceti's `inertiaSubgroup`): every element of `I` represents the Artin
symbol of a unit `u`, and then `χ σ = u⁻¹` (Tau Ceti's local class field theory of `ℚ_p`); so
`f` is constant on the fibres of `χ|_I`, which is onto `ℤ_p^×` and, `I` being compact, a quotient
map. The definitions `unitsQp'` and `IsArtinLift'` repeat `C8Conrad.unitsQp` and
`C8Conrad.IsArtinLift` word for word, so that this file avoids that module's imports. -/

noncomputable section

namespace ZInQ.Contrib.C8TwistFinite

open Topology

variable (p : ℕ) [Fact p.Prime]

/-- A unit of `ℤ_p` as a unit of `ℚ_p` (as `C8Conrad.unitsQp`). -/
def unitsQp' (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom u

/-- `σ` represents the local Artin symbol of `x` (as `C8Conrad.IsArtinLift`). -/
def IsArtinLift' (σ : PkgI4.GQp p) (x : ℚ_[p]ˣ) : Prop :=
  (QuotientGroup.mk (show Field.absoluteGaloisGroup ℚ_[p] from σ) :
      Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
    TauCeti.ClassFieldTheory.artinMap ℚ_[p] x

/-- The cyclotomic character of `G_{ℚ_p}`, as a monoid homomorphism. -/
def cycL : PkgI4.GQp p →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (PkgI4.GQp p) (PadicAlgCl p))

theorem cycL_apply (σ : PkgI4.GQp p) :
    cycL p σ = cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv := rfl

theorem continuous_cycL : Continuous (cycL p) :=
  cyclotomicCharacter.continuous p ℚ_[p] (PadicAlgCl p)

/-- The cyclotomic character of a representative of the Artin symbol of a unit `u` is `u⁻¹`
(Tau Ceti). -/
theorem cycL_of_isArtinLift (σ : PkgI4.GQp p) (u : ℤ_[p]ˣ)
    (h : IsArtinLift' p σ (unitsQp' p u)) : cycL p σ = u⁻¹ :=
  TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic p u σ h

/-- The inertia group of `ℚ_p`. -/
abbrev inertia : Subgroup (PkgI4.GQp p) := TauCeti.inertiaSubgroup ℚ_[p]

theorem norm_eq_one_of_valuation_eq_one' (x : ℚ_[p]ˣ)
    (h : ValuativeRel.valuation ℚ_[p] (x : ℚ_[p]) = 1) : ‖(x : ℚ_[p])‖ = 1 := by
  have h1 : Padic.mulValuation (x : ℚ_[p]) = 1 := by
    have he : (ValuativeRel.valuation ℚ_[p]).IsEquiv (Padic.mulValuation (p := p)) :=
      ValuativeRel.isEquiv _ _
    exact (he.eq_one_iff_eq_one).1 h
  rw [Padic.norm_eq_zpow_log_mulValuation x.ne_zero, h1]
  simp

theorem valuation_unitsQp' (u : ℤ_[p]ˣ) :
    ValuativeRel.valuation ℚ_[p] ((unitsQp' p u : ℚ_[p]ˣ) : ℚ_[p]) = 1 := by
  have hn : ‖((unitsQp' p u : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
    change ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1
    rw [PadicInt.norm_coe]
    exact PadicInt.isUnit_iff.1 u.isUnit
  have h1 : Padic.mulValuation ((unitsQp' p u : ℚ_[p]ˣ) : ℚ_[p]) = 1 := by
    have hlt := (Padic.norm_lt_norm_iff_mulValuation_lt (p := p)
      (x := ((unitsQp' p u : ℚ_[p]ˣ) : ℚ_[p])) (y := 1))
    have hgt := (Padic.norm_lt_norm_iff_mulValuation_lt (p := p)
      (x := 1) (y := ((unitsQp' p u : ℚ_[p]ˣ) : ℚ_[p])))
    rw [hn, norm_one, map_one] at hlt hgt
    exact le_antisymm (not_lt.1 fun h => (lt_irrefl _) (hgt.2 h))
      (not_lt.1 fun h => (lt_irrefl _) (hlt.2 h))
  have he : (ValuativeRel.valuation ℚ_[p]).IsEquiv (Padic.mulValuation (p := p)) :=
    ValuativeRel.isEquiv _ _
  exact (he.eq_one_iff_eq_one).2 h1

/-- Every element of the inertia group represents the Artin symbol of a unit (Tau Ceti). -/
theorem exists_unit_isArtinLift' (σ : PkgI4.GQp p) (hσ : σ ∈ inertia p) :
    ∃ u : ℤ_[p]ˣ, IsArtinLift' p σ (unitsQp' p u) := by
  have hmem : (QuotientGroup.mk' _ (show Field.absoluteGaloisGroup ℚ_[p] from σ) :
      Field.absoluteGaloisGroupAbelianization ℚ_[p]) ∈
      (TauCeti.inertiaSubgroup ℚ_[p]).map (QuotientGroup.mk' _) := ⟨_, hσ, rfl⟩
  rw [← TauCeti.ClassFieldTheory.map_artinMap_unitFiltration_zero] at hmem
  obtain ⟨y, hy, hyσ⟩ := hmem
  have hn : ‖(y : ℚ_[p])‖ = 1 :=
    norm_eq_one_of_valuation_eq_one' p y ((TauCeti.mem_unitFiltration_zero y).1 hy)
  let u : ℤ_[p]ˣ := PadicInt.mkUnits hn
  refine ⟨u, ?_⟩
  have hyu : unitsQp' p u = y := Units.ext rfl
  rw [IsArtinLift', hyu, hyσ]
  rfl

/-- The Artin symbol of every unit is represented by an element of the inertia group. -/
theorem exists_inertia_isArtinLift (u : ℤ_[p]ˣ) :
    ∃ τ : PkgI4.GQp p, τ ∈ inertia p ∧ IsArtinLift' p τ (unitsQp' p u) := by
  have hu : unitsQp' p u ∈ TauCeti.unitFiltration ℚ_[p] 0 :=
    (TauCeti.mem_unitFiltration_zero _).2 (valuation_unitsQp' p u)
  have hmem : TauCeti.ClassFieldTheory.artinMap ℚ_[p] (unitsQp' p u) ∈
      (TauCeti.inertiaSubgroup ℚ_[p]).map (QuotientGroup.mk' _) := by
    rw [← TauCeti.ClassFieldTheory.map_artinMap_unitFiltration_zero]
    exact ⟨_, hu, rfl⟩
  obtain ⟨τ, hτ, hτu⟩ := hmem
  exact ⟨τ, hτ, hτu⟩

/-- A continuous homomorphism to a commutative `T₁` group takes the same value on two
representatives of one Artin symbol. -/
theorem eq_of_isArtinLift {M : Type*} [CommGroup M] [TopologicalSpace M] [T1Space M]
    (f : PkgI4.GQp p →* M) (hf : Continuous f) {σ τ : PkgI4.GQp p} {x : ℚ_[p]ˣ}
    (hσ : IsArtinLift' p σ x) (hτ : IsArtinLift' p τ x) : f σ = f τ := by
  have hq : (QuotientGroup.mk (σ : Field.absoluteGaloisGroup ℚ_[p]) :
      Field.absoluteGaloisGroupAbelianization ℚ_[p]) =
      QuotientGroup.mk (τ : Field.absoluteGaloisGroup ℚ_[p]) :=
    hσ.trans hτ.symm
  have hq' := QuotientGroup.eq.mp hq
  have hker : (commutator (Field.absoluteGaloisGroup ℚ_[p])).topologicalClosure ≤ f.ker := by
    have hclosed : IsClosed (f.ker : Set (PkgI4.GQp p)) := by
      have : (f.ker : Set (PkgI4.GQp p)) = f ⁻¹' {1} := by ext; simp
      rw [this]
      exact isClosed_singleton.preimage hf
    refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
    exact Abelianization.commutator_subset_ker f
  have h1 : f (σ⁻¹ * τ) = 1 := hker hq'
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

section UnitChar

variable {M : Type*} [CommGroup M] [TopologicalSpace M] [T1Space M]
  (f : PkgI4.GQp p →* M) (hf : Continuous f)

include hf in
/-- On the inertia group, `f` factors through the cyclotomic character. -/
theorem eq_of_cycL_eq {σ τ : PkgI4.GQp p} (hσ : σ ∈ inertia p) (hτ : τ ∈ inertia p)
    (h : cycL p σ = cycL p τ) : f σ = f τ := by
  obtain ⟨u, hu⟩ := exists_unit_isArtinLift' p σ hσ
  obtain ⟨v, hv⟩ := exists_unit_isArtinLift' p τ hτ
  have huv : u = v := by
    have := (cycL_of_isArtinLift p σ u hu).symm.trans (h.trans (cycL_of_isArtinLift p τ v hv))
    exact inv_injective this
  subst huv
  exact eq_of_isArtinLift p f hf hu hv

/-- The inertia group is compact. -/
theorem isCompact_inertia : IsCompact ((inertia p : Subgroup (PkgI4.GQp p)) : Set (PkgI4.GQp p)) :=
  (TauCeti.isClosed_inertiaSubgroup ℚ_[p]).isCompact

/-- A chosen inertia element with cyclotomic character `u`. -/
theorem exists_inertia_cycL (u : ℤ_[p]ˣ) : ∃ τ : PkgI4.GQp p, τ ∈ inertia p ∧ cycL p τ = u := by
  obtain ⟨τ, hτ, hτu⟩ := exists_inertia_isArtinLift p u⁻¹
  exact ⟨τ, hτ, by rw [cycL_of_isArtinLift p τ u⁻¹ hτu, inv_inv]⟩

/-- The cyclotomic character is onto `ℤ_p^×`. -/
theorem cycL_surjective : Function.Surjective (cycL p) := fun u =>
  let ⟨τ, _, h⟩ := exists_inertia_cycL p u
  ⟨τ, h⟩

/-- **The unit part of `f`**: `u ↦ f τ` for an inertia element `τ` with `χ τ = u`. -/
def unitChar : ℤ_[p]ˣ →* M where
  toFun u := f (exists_inertia_cycL p u).choose
  map_one' := by
    have h := (exists_inertia_cycL p 1).choose_spec
    rw [← map_one f]
    exact eq_of_cycL_eq p f hf h.1 (one_mem _) (by rw [h.2, map_one])
  map_mul' u v := by
    have hu := (exists_inertia_cycL p u).choose_spec
    have hv := (exists_inertia_cycL p v).choose_spec
    have huv := (exists_inertia_cycL p (u * v)).choose_spec
    rw [← map_mul f]
    exact eq_of_cycL_eq p f hf huv.1 (mul_mem hu.1 hv.1) (by rw [huv.2, map_mul, hu.2, hv.2])

theorem unitChar_cycL {τ : PkgI4.GQp p} (hτ : τ ∈ inertia p) :
    unitChar p f hf (cycL p τ) = f τ := by
  have h := (exists_inertia_cycL p (cycL p τ)).choose_spec
  exact eq_of_cycL_eq p f hf h.1 hτ h.2

/-- **The defining property**: on representatives of Artin symbols of units, `f` is its unit
part composed with the cyclotomic character. -/
theorem unitChar_cycL_of_isArtinLift {σ : PkgI4.GQp p} {u : ℤ_[p]ˣ}
    (hσ : IsArtinLift' p σ (unitsQp' p u)) : unitChar p f hf (cycL p σ) = f σ := by
  obtain ⟨τ, hτ, hτu⟩ := exists_inertia_isArtinLift p u
  rw [cycL_of_isArtinLift p σ u hσ, ← cycL_of_isArtinLift p τ u hτu, unitChar_cycL p f hf hτ]
  exact eq_of_isArtinLift p f hf hτu hσ

/-- The unit part is continuous: `χ|_I` is a quotient map (a continuous surjection from a
compact space onto a Hausdorff one). -/
theorem continuous_unitChar : Continuous (unitChar p f hf) := by
  let q : inertia p → ℤ_[p]ˣ := fun τ => cycL p τ
  have : CompactSpace (inertia p) := isCompact_iff_compactSpace.1 (isCompact_inertia p)
  have hqc : Continuous q := (continuous_cycL p).comp continuous_subtype_val
  have hqs : Function.Surjective q := fun u =>
    let ⟨τ, hτ, h⟩ := exists_inertia_cycL p u
    ⟨⟨τ, hτ⟩, h⟩
  have hQ : IsQuotientMap q := (hqc.isClosedMap).isQuotientMap hqc hqs
  rw [hQ.continuous_iff]
  have : (unitChar p f hf ∘ q) = fun τ : inertia p => f τ := by
    funext τ
    exact unitChar_cycL p f hf τ.2
  rw [this]
  exact hf.comp continuous_subtype_val

end UnitChar

end ZInQ.Contrib.C8TwistFinite
