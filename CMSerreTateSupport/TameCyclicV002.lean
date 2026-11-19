import TameCharacterV005
import Mathlib.RingTheory.IntegralDomain

/-!
# Inertia modulo wild inertia is cyclic in a discretely valued finite situation

Let `w` be a valuation subring of `L` whose nonzero valuations are the integral powers of
`v(π)`, and let `G` be a finite group of `K`-automorphisms of `L` satisfying the inertia
conditions (valuation preserved, residues of units fixed). The tame character
`σ ↦ (σ π / π mod principal units)` is a homomorphism from `G` into the units of the residue
field whose kernel is exactly the set of wild elements of `G`; hence `G` modulo its wild
elements is cyclic (`tameQuotient_isCyclic`, `mem_ker_tameCharacter_iff`).
-/

noncomputable section
set_option autoImplicit false

namespace WildTameCharacter

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {w : ValuationSubring L}

theorem Cong.inv_of_one {a : L} (ha : w.valuation a = 1) (h : Cong w a 1) : Cong w a⁻¹ 1 := by
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at ha
    exact zero_ne_one ha
  unfold Cong at *
  have e : a⁻¹ - 1 = (1 - a) * a⁻¹ := by field_simp
  rw [e, Valuation.map_mul, Valuation.map_inv, ha, _root_.inv_one, mul_one, Valuation.map_sub_swap]
  exact h

/-- In a discretely valued field, an automorphism satisfying the inertia conditions is
wild as soon as `σ π ≡ π`. -/
theorem isWild_of_cong_uniformizer {σ : L ≃ₐ[K] L} (hv : Preserves w σ)
    (hres : ∀ u : L, w.valuation u = 1 → Cong w (σ u) u) {π : L} (hπ0 : π ≠ 0)
    (hπ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, w.valuation x = w.valuation π ^ k)
    (h : Cong w (σ π / π) 1) : IsWild w σ := by
  have hpow : ∀ n : ℕ, Cong w (σ (π ^ n) / π ^ n) 1 := by
    intro n
    have e : σ (π ^ n) / π ^ n = (σ π / π) ^ n := by rw [map_pow, div_pow]
    rw [e]
    have c := Cong.pow (val_ratio hv hπ0) (Valuation.map_one w.valuation) h n
    rwa [one_pow] at c
  have hall : ∀ x : L, x ≠ 0 → Cong w (σ x / x) 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hπ x hx
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · have hxn : w.valuation (π ^ n) = w.valuation x := by
        rw [hk, Valuation.map_pow, zpow_natCast]
      exact (ratio_cong hv hres (pow_ne_zero n hπ0) hx hxn).trans (hpow n)
    · have hx' : x⁻¹ ≠ 0 := inv_ne_zero hx
      have hxn : w.valuation (π ^ n) = w.valuation x⁻¹ := by
        rw [Valuation.map_inv, hk, Valuation.map_pow, zpow_neg, zpow_natCast, inv_inv]
      have c := (ratio_cong hv hres (pow_ne_zero n hπ0) hx' hxn).trans (hpow n)
      have e : σ x⁻¹ / x⁻¹ = (σ x / x)⁻¹ := by
        rw [map_inv₀, inv_div_inv, inv_div]
      rw [e] at c
      have c2 := Cong.inv_of_one (by rw [Valuation.map_inv, val_ratio hv hx, inv_one]) c
      rwa [inv_inv] at c2
  intro x hx
  have h2 : Cong w (σ x / x) (x / x) := by
    rw [div_self hx]
    exact hall x hx
  exact lt_of_cong_div hx h2

/-- Conversely a wild automorphism satisfies `σ π ≡ π`. -/
theorem cong_uniformizer_of_isWild {σ : L ≃ₐ[K] L} (h : IsWild w σ) {π : L} (hπ0 : π ≠ 0) :
    Cong w (σ π / π) 1 := by
  have h1 := h π hπ0
  unfold Cong
  have e : σ π / π - 1 = (σ π - π) / π := by field_simp
  rw [e, Valuation.map_div]
  exact (div_lt_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hπ0))).2 h1

variable (w)

/-- The residue ratio `σ π / π` as an element of the unit group of `w`. -/
def ratioUnit {σ : L ≃ₐ[K] L} (hv : Preserves w σ) {π : L} (hπ0 : π ≠ 0) : w.unitGroup :=
  ⟨Units.mk0 (σ π / π) (div_ne_zero ((map_ne_zero σ).mpr hπ0) hπ0), by
    rw [ValuationSubring.mem_unitGroup_iff, Units.val_mk0]
    exact val_ratio hv hπ0⟩

/-- The principal-unit subgroup of the unit group. -/
abbrev principalInUnits : Subgroup w.unitGroup :=
  w.principalUnitGroup.comap w.unitGroup.subtype

variable {w}

theorem mem_principalInUnits_iff (x : w.unitGroup) :
    x ∈ principalInUnits w ↔ Cong w ((x : Lˣ) : L) 1 :=
  Iff.rfl

/-- **The tame character** of a group of automorphisms satisfying the inertia conditions,
with values in units modulo principal units. -/
def tameCharacter (G : Subgroup (L ≃ₐ[K] L))
    (hG : ∀ σ ∈ G, Preserves w σ ∧ ∀ u : L, w.valuation u = 1 → Cong w (σ u) u)
    {π : L} (hπ0 : π ≠ 0) : G →* w.unitGroup ⧸ principalInUnits w where
  toFun σ := QuotientGroup.mk (ratioUnit w (hG σ σ.2).1 hπ0)
  map_one' := by
    apply (QuotientGroup.eq_one_iff _).2
    rw [mem_principalInUnits_iff]
    change Cong w (((1 : G) : L ≃ₐ[K] L) π / π) 1
    rw [OneMemClass.coe_one, AlgEquiv.one_apply, div_self hπ0]
    exact Cong.refl 1
  map_mul' σ τ := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_principalInUnits_iff]
    obtain ⟨hσv, hσr⟩ := hG σ σ.2
    obtain ⟨hτv, hτr⟩ := hG τ τ.2
    have hτπ : (τ : L ≃ₐ[K] L) π ≠ 0 := (map_ne_zero (τ : L ≃ₐ[K] L)).mpr hπ0
    set x : L := ((σ * τ : G) : L ≃ₐ[K] L) π / π with hx
    set y : L := ((σ : L ≃ₐ[K] L) π / π) * ((τ : L ≃ₐ[K] L) π / π) with hy
    have hxv : w.valuation x = 1 := val_ratio (hσv.mul hτv) hπ0
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hxv
      exact zero_ne_one hxv
    have hxe : x = ((σ : L ≃ₐ[K] L) ((τ : L ≃ₐ[K] L) π) / (τ : L ≃ₐ[K] L) π) *
        ((τ : L ≃ₐ[K] L) π / π) := by
      rw [hx]
      change (σ : L ≃ₐ[K] L) ((τ : L ≃ₐ[K] L) π) / π = _
      field_simp
    have cxy : Cong w x y := by
      rw [hxe, hy]
      exact Cong.mul (val_ratio hσv hτπ) (val_ratio hτv hπ0)
        (ratio_cong hσv hσr hπ0 hτπ (hτv π).symm) (Cong.refl _)
    change Cong w (x⁻¹ * y) 1
    unfold Cong at cxy ⊢
    have e : x⁻¹ * y - 1 = x⁻¹ * (y - x) := by field_simp
    rw [e, Valuation.map_mul, Valuation.map_inv, hxv, inv_one, one_mul, Valuation.map_sub_swap]
    exact cxy

/-- **Kernel of the tame character = wild elements** (discretely valued case). -/
theorem mem_ker_tameCharacter_iff (G : Subgroup (L ≃ₐ[K] L))
    (hG : ∀ σ ∈ G, Preserves w σ ∧ ∀ u : L, w.valuation u = 1 → Cong w (σ u) u)
    {π : L} (hπ0 : π ≠ 0)
    (hπ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, w.valuation x = w.valuation π ^ k) (σ : G) :
    σ ∈ (tameCharacter G hG hπ0).ker ↔ IsWild w (σ : L ≃ₐ[K] L) := by
  rw [MonoidHom.mem_ker]
  change (QuotientGroup.mk _ : w.unitGroup ⧸ principalInUnits w) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, mem_principalInUnits_iff]
  change Cong w ((σ : L ≃ₐ[K] L) π / π) 1 ↔ _
  constructor
  · intro h
    exact isWild_of_cong_uniformizer (hG σ σ.2).1 (hG σ σ.2).2 hπ0 hπ h
  · intro h
    exact cong_uniformizer_of_isWild h hπ0

/-- **Inertia modulo wild inertia is cyclic** for a finite group satisfying the inertia
conditions over a discretely valued field: the tame character lands, after the canonical
isomorphism, in the units of the residue field, and finite subgroups of the units of a field
are cyclic. -/
theorem tameQuotient_isCyclic (G : Subgroup (L ≃ₐ[K] L)) [Finite G]
    (hG : ∀ σ ∈ G, Preserves w σ ∧ ∀ u : L, w.valuation u = 1 → Cong w (σ u) u)
    {π : L} (hπ0 : π ≠ 0) : IsCyclic (G ⧸ (tameCharacter G hG hπ0).ker) := by
  set χ := tameCharacter G hG hπ0
  let θ : G →* (IsLocalRing.ResidueField w)ˣ :=
    w.unitsModPrincipalUnitsEquivResidueFieldUnits.toMonoidHom.comp χ
  have hker : θ.ker = χ.ker := by
    ext σ
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change w.unitsModPrincipalUnitsEquivResidueFieldUnits (χ σ) = 1 ↔ χ σ = 1
    exact MulEquiv.map_eq_one_iff _
  have hfin : Finite θ.range := Finite.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hcyc : IsCyclic θ.range := inferInstance
  let e : G ⧸ χ.ker ≃* θ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange θ)
  exact isCyclic_of_surjective e.symm e.symm.surjective

end WildTameCharacter
