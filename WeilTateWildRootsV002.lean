import ZInQKernel.HDecomp.Objects

/-!
# Wild inertia fixes the roots of unity of order invertible at the place

Setting of `SZRaynaud.ElliotWildInertiaTrivial`: `K` a field, `O ⊆ K` a valuation subring, `Ω` a field over
`K`, `w ⊆ Ω` a valuation subring lying over `O` (`w.comap (algebraMap K Ω) = O`), `m` a natural number
invertible in `O`, and `σ ∈ Aut_K(Ω)` wild in the literal sense `v_w(σx - x) < v_w(x)` for every `x ≠ 0`.

Main results (all on the actual objects, no hypothesis beyond the displayed ones):

* `isUnit_natCast_of_comap`: `m` invertible in `O` makes `m` a unit of `w`;
* `isUnit_sub_one_of_pow_eq_one`: if `ξ^m = 1`, `ξ ≠ 1` and `m` is a unit of `w`, then `ξ - 1` is a unit of
  `w` (the identity `m = (1 - ξ) · Σ_{i<m} Σ_{j<i} ξ^j`);
* `wild_fix_of_pow_eq_one`: a wild `σ` fixes every `ζ ∈ Ω` with `ζ^m = 1`;
* `galTMu_eq_self_of_wild`: a wild `σ` acts trivially on `T_ℓ(μ(Ω)) = lim μ_{ℓⁿ}(Ω)` (the kernel's
  `PkgI3.Tate.T ℓ (Additive Ωˣ)`) for every prime `ℓ` invertible in `O`.

`IsWildInertia` below has, word for word, the body of `SZRaynaud.IsWildInertia`
(`ZInQKernel/Contrib/OneProof/SZRaynaud.lean`); it is restated because that module is not in the ready
import frame.
-/

noncomputable section

namespace WeilTate

/-- Wild inertia, with the body of `SZRaynaud.IsWildInertia`. -/
def IsWildInertia {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
    (σ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x

section Units

variable {K : Type} [Field K] (O : ValuationSubring K) {Ω : Type} [Field Ω] [Algebra K Ω]
  (w : ValuationSubring Ω)

/-- A natural number invertible in `O` is a unit of every `w` over `O`. -/
theorem isUnit_natCast_of_comap (hw : w.comap (algebraMap K Ω) = O) {m : ℕ} (hm : IsUnit (m : O)) :
    IsUnit (m : w) := by
  obtain ⟨u, hu⟩ := hm
  have hv : ((u⁻¹ : Oˣ) : O) * (m : O) = 1 := by rw [← hu]; exact u.inv_mul
  have hvK : (((u⁻¹ : Oˣ) : O) : K) * (m : K) = 1 := by
    have := congrArg (fun z : O => (z : K)) hv
    simpa using this
  have hvw : algebraMap K Ω (((u⁻¹ : Oˣ) : O) : K) ∈ w := by
    have h : (((u⁻¹ : Oˣ) : O) : K) ∈ w.comap (algebraMap K Ω) := by
      rw [hw]
      exact ((u⁻¹ : Oˣ) : O).2
    exact h
  refine ⟨Units.mkOfMulEqOne _ ⟨algebraMap K Ω (((u⁻¹ : Oˣ) : O) : K), hvw⟩ ?_, rfl⟩
  apply Subtype.ext
  change (m : Ω) * algebraMap K Ω (((u⁻¹ : Oˣ) : O) : K) = 1
  rw [← map_natCast (algebraMap K Ω) m, ← map_mul, mul_comm, hvK, map_one]

end Units

section Roots

variable {Ω : Type} [Field Ω] (w : ValuationSubring Ω)

/-- A root of unity lies in every valuation subring. -/
theorem mem_of_pow_eq_one {ξ : Ω} {m : ℕ} (hm : m ≠ 0) (hξ : ξ ^ m = 1) : ξ ∈ w := by
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hξ
    exact zero_ne_one hξ
  rcases w.mem_or_inv_mem ξ with h | h
  · exact h
  · have : ξ = (ξ⁻¹) ^ (m - 1) := by
      rw [inv_pow]
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]
      exact hξ
    rw [this]
    exact pow_mem h _

/-- `m = (1 - ξ) · Σ_{i<m} Σ_{j<i} ξ^j` when `ξ^m = 1` and `ξ ≠ 1`. -/
theorem natCast_eq_mul_of_pow_eq_one {ξ : Ω} {m : ℕ} (hξ : ξ ^ m = 1) (h1 : ξ ≠ 1) :
    (m : Ω) = (1 - ξ) * ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range i, ξ ^ j := by
  have hS : ∑ i ∈ Finset.range m, ξ ^ i = 0 := by
    have h := geom_sum_mul ξ m
    rw [hξ, sub_self] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) h1
  rw [Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range m, (1 - ξ) * ∑ j ∈ Finset.range i, ξ ^ j = 1 - ξ ^ i := by
    intro i _
    rw [mul_comm, ← neg_sub, mul_neg, geom_sum_mul, neg_sub]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hS, sub_zero]
  simp

/-- If `ξ^m = 1`, `ξ ≠ 1` and `m` is a unit of `w`, then `ξ - 1` is a unit of `w`. -/
theorem isUnit_sub_one_of_pow_eq_one {ξ : Ω} {m : ℕ} (hξ : ξ ^ m = 1) (h1 : ξ ≠ 1)
    (hm : IsUnit (m : w)) : w.valuation (ξ - 1) = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hξw : ξ ∈ w := mem_of_pow_eq_one w hm0 hξ
  have hTw : (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range i, ξ ^ j) ∈ w :=
    sum_mem fun i _ => sum_mem fun j _ => pow_mem hξw j
  have h1w : (1 - ξ) ∈ w := sub_mem (one_mem w) hξw
  have hprod : (⟨1 - ξ, h1w⟩ : w) * ⟨_, hTw⟩ = (m : w) := by
    apply Subtype.ext
    change (1 - ξ) * _ = (m : Ω)
    rw [natCast_eq_mul_of_pow_eq_one hξ h1]
  have hu : IsUnit (⟨1 - ξ, h1w⟩ : w) := isUnit_of_mul_isUnit_left (hprod ▸ hm)
  have hv : w.valuation (1 - ξ) = 1 := (w.valuation_eq_one_iff _).1 hu
  rw [← neg_sub, Valuation.map_neg, hv]

/-- **Wild inertia fixes the roots of unity of order invertible in `w`.** -/
theorem wild_fix_of_pow_eq_one' {K : Type} [Field K] [Algebra K Ω] (σ : Ω ≃ₐ[K] Ω)
    (hσ : IsWildInertia w σ) {ζ : Ω} {m : ℕ} (hζ : ζ ^ m = 1) (hm : IsUnit (m : w)) : σ ζ = ζ := by
  by_contra hne
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0] at hζ
    exact zero_ne_one hζ
  set ξ : Ω := σ ζ * ζ⁻¹ with hξdef
  have hξm : ξ ^ m = 1 := by
    rw [hξdef, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, mul_one]
  have hξ1 : ξ ≠ 1 := by
    intro h
    apply hne
    rw [hξdef, mul_inv_eq_one₀ hζ0] at h
    exact h
  have hv := isUnit_sub_one_of_pow_eq_one w hξm hξ1 hm
  have hdiff : σ ζ - ζ = ζ * (ξ - 1) := by
    rw [hξdef, mul_sub, mul_one, mul_comm (σ ζ), ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  have hlt := hσ ζ hζ0
  rw [hdiff, Valuation.map_mul, hv, mul_one] at hlt
  exact lt_irrefl _ hlt

end Roots

section Place

variable {K : Type} [Field K] (O : ValuationSubring K) {Ω : Type} [Field Ω] [Algebra K Ω]
  (w : ValuationSubring Ω)

/-- **Wild inertia over `O` fixes every root of unity of order invertible in `O`.** -/
theorem wild_fix_of_pow_eq_one (hw : w.comap (algebraMap K Ω) = O) (σ : Ω ≃ₐ[K] Ω)
    (hσ : IsWildInertia w σ) {m : ℕ} (hmO : IsUnit (m : O)) {ζ : Ω} (hζ : ζ ^ m = 1) : σ ζ = ζ :=
  wild_fix_of_pow_eq_one' w σ hσ hζ (isUnit_natCast_of_comap O w hw hmO)

/-- The units version: `σ` fixes every `u ∈ Ωˣ` with `u^m = 1`. -/
theorem wild_units_fix (hw : w.comap (algebraMap K Ω) = O) (σ : Ω ≃ₐ[K] Ω)
    (hσ : IsWildInertia w σ) {m : ℕ} (hmO : IsUnit (m : O)) {u : Ωˣ} (hu : u ^ m = 1) :
    Units.map (σ : Ω →* Ω) u = u := by
  apply Units.ext
  change σ (u : Ω) = u
  apply wild_fix_of_pow_eq_one O w hw σ hσ hmO
  rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]

/-- `T_ℓ(μ(Ω)) = lim μ_{ℓⁿ}(Ω)`, the kernel's Tate module of the group `Ωˣ`. -/
abbrev TMu (Ω : Type) [Field Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  PkgI3.Tate.T ℓ (Additive Ωˣ)

/-- The action of `σ ∈ Aut_K(Ω)` on `T_ℓ(μ(Ω))`. -/
def galTMu (ℓ : ℕ) [Fact ℓ.Prime] (σ : Ω ≃ₐ[K] Ω) : TMu Ω ℓ →ₗ[ℤ_[ℓ]] TMu Ω ℓ :=
  PkgI3.Tate.map (MonoidHom.toAdditive (Units.map (σ : Ω →* Ω)))

/-- **A wild `σ` acts trivially on `T_ℓ(μ(Ω))` for a prime `ℓ` invertible in `O`.** -/
theorem galTMu_eq_self_of_wild (hw : w.comap (algebraMap K Ω) = O) (σ : Ω ≃ₐ[K] Ω)
    (hσ : IsWildInertia w σ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O)) (t : TMu Ω ℓ) :
    galTMu ℓ σ t = t := by
  apply Subtype.ext
  funext n
  have hpow : IsUnit ((ℓ ^ n : ℕ) : O) := by
    rw [Nat.cast_pow]
    exact hℓ.pow n
  have htors : (Additive.toMul (t.1 n)) ^ (ℓ ^ n) = 1 := by
    have h := PkgI3.Tate.pow_smul_eq_zero t.2 n
    have h' := congrArg Additive.toMul h
    rwa [toMul_nsmul, toMul_zero] at h'
  change Additive.ofMul (Units.map (σ : Ω →* Ω) (Additive.toMul (t.1 n))) = t.1 n
  rw [wild_units_fix O w hw σ hσ hpow htors]
  rfl

end Place

end WeilTate

#check @WeilTate.isUnit_natCast_of_comap
#check @WeilTate.isUnit_sub_one_of_pow_eq_one
#check @WeilTate.wild_fix_of_pow_eq_one
#check @WeilTate.wild_units_fix
#check @WeilTate.galTMu_eq_self_of_wild
#print axioms WeilTate.wild_fix_of_pow_eq_one
#print axioms WeilTate.wild_units_fix
#print axioms WeilTate.galTMu_eq_self_of_wild
