import ZInQKernel.Contrib.OneProof.FowlerBridgesDiscriminant
import ZInQKernel.Contrib.OneProof.CMBranch.CoxProof
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.RayClass

/-!
# The proper ideal classes of an imaginary quadratic order

A fractional ideal is proper when its multiplier ring is the order. The quadratic-order converse
to "invertible implies proper" is Cox (1989), Proposition 7.4. We prove it with two generators
and a primitive quadratic equation; no maximal-order assumption is used.
-/

namespace HDec.CMBranch.FowlerBridges

open NumberField Module TauCeti.GlobalNumberFields FractionalIdeal
open scoped nonZeroDivisors

variable {k : Type} [Field k] [NumberField k]

/-- The Picard group of a finite-index imaginary quadratic order is finite. -/
theorem finite_pic (R : Subring k) (hR : IsImagQuadOrder k R) : Finite (CommRing.Pic R) := by
  let O := toOrder R hR
  exact Finite.of_equiv (Pic O) (ClassGroup.equivPic O.toSubalgebra).toEquiv

/-- The finite Picard group contains the identity, so its cardinal is positive. -/
theorem card_pic_pos (R : Subring k) (hR : IsImagQuadOrder k R) :
    0 < Nat.card (CommRing.Pic R) := by
  let := finite_pic R hR
  exact Nat.card_pos

/-- The integral lattice underlying a nonzero fractional ideal has rank two. -/
theorem exists_fractionalIdeal_basis (O : NumberFieldOrder k) (hk : finrank ℚ k = 2)
    (I : FractionalIdeal O.toSubalgebra⁰ k) (hI : I ≠ 0) : Nonempty (Basis (Fin 2) ℤ I) := by
  classical
  let e := (I.equivNumOfIsLocalization).restrictScalars ℤ
  let f := ((Submodule.subtype I.num).restrictScalars ℤ).comp e.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let : Module.Finite ℤ I := Module.Finite.of_injective f hf
  let : Module.Free ℤ I := Free.of_equiv (LinearEquiv.ofInjective f hf).symm
  have hO : finrank ℤ O.toSubalgebra = 2 := by
    let b := Free.chooseBasis ℤ O.toSubalgebra
    rw [finrank_eq_card_basis b, ← finrank_eq_card_basis (b.localizationLocalization ℚ ℤ⁰ k), hk]
  obtain ⟨x, hx, hx0⟩ : ∃ x : k, x ∈ I ∧ x ≠ 0 := by
    by_contra! h
    apply hI
    ext y
    rw [mem_zero_iff]
    exact ⟨h y, fun hy => hy.symm ▸ I.zero_mem⟩
  let g := (LinearMap.toSpanSingleton O.toSubalgebra I ⟨x, hx⟩).restrictScalars ℤ
  have hg : Function.Injective g := by
    intro a b hab
    have he : (a : k) * x = (b : k) * x := by
      simpa [g, Algebra.smul_def] using congrArg (fun z : I => (z : k)) hab
    exact Subtype.ext (mul_right_cancel₀ hx0 he)
  have hlo := LinearMap.finrank_le_finrank_of_injective hg
  have hhi := LinearMap.finrank_le_finrank_of_injective hf
  have hdim : finrank ℤ I = 2 := by omega
  let b := Free.chooseBasis ℤ I
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ I) = Fintype.card (Fin 2) := by
    rw [← finrank_eq_card_basis b, hdim, Fintype.card_fin]
  exact ⟨b.reindex (Fintype.equivOfCardEq hcard)⟩

private theorem exists_noninteger (O : NumberFieldOrder k) (hk : finrank ℚ k = 2) :
    ∃ θ : O.toSubalgebra, ∀ n : ℤ, θ ≠ n := by
  classical
  let b := Free.chooseBasis ℤ O.toSubalgebra
  have hdim : finrank ℤ O.toSubalgebra = 2 := by
    rw [finrank_eq_card_basis b, ← finrank_eq_card_basis (b.localizationLocalization ℚ ℤ⁰ k), hk]
  obtain ⟨c, hc⟩ := IsUnimodular.exists_basis_zero_eq hdim
    (Free.isUnimodular_one (R := ℤ) (A := O.toSubalgebra))
  refine ⟨c 1, fun n hn => ?_⟩
  have he : c 1 = n • c 0 := by simpa [hc] using hn
  have hr := congrArg (fun x => c.repr x 1) he
  change c.repr (c 1) 1 = c.repr (n • c 0) 1 at hr
  rw [map_smul, c.repr_self, c.repr_self] at hr
  simp at hr

private theorem mul_mem_of_mem_pair (O : NumberFieldOrder k)
    (J : FractionalIdeal O.toSubalgebra⁰ k) (τ x : k)
    (hgen : ∀ y : k, y ∈ J ↔ ∃ m n : ℤ, y = m + n * τ)
    (hx : x ∈ J) (hxt : x * τ ∈ J) :
    ∀ y ∈ J, x * y ∈ J := by
  intro y hy
  obtain ⟨m, n, rfl⟩ := (hgen y).mp hy
  have hmem : m • x + n • (x * τ) ∈ J :=
    J.val.add_mem (J.val.toAddSubgroup.zsmul_mem hx m) (J.val.toAddSubgroup.zsmul_mem hxt n)
  rw [show x * ((m : k) + n * τ) = m • x + n • (x * τ) by simp only [zsmul_eq_mul]; ring]
  exact hmem

/-- Cox, Proposition 7.4, for imaginary quadratic orders: proper fractional ideals are exactly
the invertible fractional ideals. After scaling a basis to `(1, τ)`, write
`a τ² + b τ + c = 0` with coprime coefficients. Then `a` and `-b - aτ` are in the
inverse ideal, and the product contains `a, b, c`, hence contains `1`. -/
theorem proper_iff_isUnit (O : NumberFieldOrder k) (hk : finrank ℚ k = 2)
    (I : FractionalIdeal O.toSubalgebra⁰ k) :
    O.IsProperFractionalIdeal I ↔ IsUnit I := by
  classical
  refine ⟨fun hI => ?_, O.isProperFractionalIdeal_of_isUnit⟩
  obtain ⟨B⟩ := exists_fractionalIdeal_basis O hk I hI.ne_zero
  let u : k := B 0
  let v : k := B 1
  have hu : u ≠ 0 := fun h => B.ne_zero 0 (Subtype.ext h)
  let τ := u⁻¹ * v
  let J := spanSingleton O.toSubalgebra⁰ u⁻¹ * I
  have hp : O.IsProperFractionalIdeal J := by
    rw [show J = I * spanSingleton _ u⁻¹ by exact mul_comm ..]
    exact (O.isProperFractionalIdeal_mul_spanSingleton I (inv_ne_zero hu)).mpr hI
  have hgenI : ∀ y : k, y ∈ I ↔ ∃ m n : ℤ, y = m * u + n * v := by
    intro y
    constructor
    · intro hy
      let z : I := ⟨y, hy⟩
      refine ⟨B.repr z 0, B.repr z 1, ?_⟩
      have hs := B.sum_repr z
      rw [Fin.sum_univ_two] at hs
      have he := congrArg (fun z : I => (z : k)) hs.symm
      simpa only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul] using he
    · rintro ⟨m, n, rfl⟩
      simpa [zsmul_eq_mul] using I.val.add_mem (I.val.toAddSubgroup.zsmul_mem (B 0).property m)
        (I.val.toAddSubgroup.zsmul_mem (B 1).property n)
  have hgen : ∀ y : k, y ∈ J ↔ ∃ m n : ℤ, y = m + n * τ := by
    intro y
    rw [mem_singleton_mul]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨m, n, rfl⟩ := (hgenI z).mp hz
      exact ⟨m, n, by dsimp [τ]; field_simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m * u + n * v, (hgenI _).mpr ⟨m, n, rfl⟩,
        by dsimp [τ]; field_simp⟩
  have h1 : (1 : k) ∈ J := (hgen _).mpr ⟨1, 0, by simp⟩
  have ht : τ ∈ J := (hgen _).mpr ⟨0, 1, by simp⟩
  obtain ⟨θ, hθ⟩ := exists_noninteger O hk
  have hmul (y : k) (hy : y ∈ J) : (θ : k) * y ∈ J :=
    (O.mem_multiplierRing_iff J θ).mp (O.order_le_multiplierRing J θ.property) y hy
  obtain ⟨m, n, hmn⟩ := (hgen _).mp (by simpa using hmul 1 h1)
  obtain ⟨p, q, hpq⟩ := (hgen _).mp (hmul τ ht)
  have hn : n ≠ 0 := by
    intro he
    apply hθ m
    apply Subtype.ext
    simpa [he] using hmn
  have hq0 : (n : k) * τ ^ 2 + ((m - q : ℤ) : k) * τ + ((-p : ℤ) : k) = 0 := by
    rw [hmn] at hpq
    push_cast
    linear_combination hpq
  let σ : k →+* ℂ := Classical.choice inferInstance
  have hqC := congrArg σ hq0
  simp only [map_add, map_mul, map_pow, map_intCast, map_zero] at hqC
  obtain ⟨a, b, c, _, hprim, hqC'⟩ := exists_prim hn hqC
  have hq : (a : k) * τ ^ 2 + b * τ + c = 0 := by
    apply σ.injective
    simpa only [map_add, map_mul, map_pow, map_intCast, map_zero] using hqC'
  have haτ : (a : k) * τ ∈ O.toSubalgebra := by
    change (a : k) * τ ∈ O.toSubalgebra.toSubring
    have hEq : O.multiplierRing J = O.toSubalgebra.toSubring := hp
    rw [← hEq, O.mem_multiplierRing_iff]
    apply mul_mem_of_mem_pair O J τ _ hgen ((hgen _).mpr ⟨0, a, by simp⟩)
    exact (hgen _).mpr ⟨-c, -b, by push_cast; linear_combination hq⟩
  have hy : -(b : k) - a * τ ∈ O.toSubalgebra :=
    O.toSubalgebra.sub_mem (by simpa only [Int.cast_neg] using O.toSubalgebra.intCast_mem (-b)) haτ
  have hyt : (-(b : k) - a * τ) * τ = (c : k) := by linear_combination -hq
  have hmem1 (x : k) : x ∈ (1 : FractionalIdeal O.toSubalgebra⁰ k) ↔ x ∈ O.toSubalgebra := by
    rw [mem_one_iff]
    exact ⟨by rintro ⟨x, rfl⟩; exact x.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hinv (x : k) (hx : x ∈ O.toSubalgebra) (hxt : x * τ ∈ O.toSubalgebra) :
      x ∈ 1 / J := by
    rw [mem_div_iff_of_ne_zero hp.ne_zero]
    intro y hy'
    obtain ⟨l, s, rfl⟩ := (hgen _).mp hy'
    apply (hmem1 _).mpr
    convert O.toSubalgebra.add_mem (O.toSubalgebra.mul_mem (O.toSubalgebra.intCast_mem l) hx)
      (O.toSubalgebra.mul_mem (O.toSubalgebra.intCast_mem s) hxt) using 1
    ring
  have haInv := hinv (a : k) (O.toSubalgebra.intCast_mem a) haτ
  have hyInv := hinv (-(b : k) - a * τ) hy (by rw [hyt]; exact O.toSubalgebra.intCast_mem c)
  let P := J * (1 / J)
  have haP : (a : k) ∈ P := by simpa only [one_mul] using FractionalIdeal.mul_mem_mul h1 haInv
  have hcP : (c : k) ∈ P := by
    simpa only [mul_comm τ, hyt] using FractionalIdeal.mul_mem_mul ht hyInv
  have hbP : (b : k) ∈ P := by
    have hsum := P.val.add_mem (FractionalIdeal.mul_mem_mul h1 hyInv)
      (FractionalIdeal.mul_mem_mul ht haInv)
    apply P.val.neg_mem at hsum
    change -(1 * (-(b : k) - a * τ) + τ * a) ∈ P at hsum
    rwa [show -(1 * (-(b : k) - a * τ) + τ * a) = b by ring] at hsum
  have gcd_mem (l s : ℤ) (hl : (l : k) ∈ P) (hs : (s : k) ∈ P) :
      ((Int.gcd l s : ℕ) : k) ∈ P := by
    have hsum : Int.gcdA l s • (l : k) + Int.gcdB l s • (s : k) ∈ P :=
      P.val.add_mem (P.val.toAddSubgroup.zsmul_mem hl (Int.gcdA l s))
        (P.val.toAddSubgroup.zsmul_mem hs (Int.gcdB l s))
    have he : ((Int.gcd l s : ℕ) : k) =
        Int.gcdA l s • (l : k) + Int.gcdB l s • (s : k) := by
      simp only [zsmul_eq_mul]
      have h := congrArg (fun t : ℤ => (t : k)) (Int.gcd_eq_gcd_ab l s)
      simpa only [Int.cast_natCast, Int.cast_add, Int.cast_mul, mul_comm] using h
    rw [he]
    exact hsum
  have h1P : (1 : k) ∈ P := by
    have h := gcd_mem (Int.gcd a b : ℕ) c (by simpa only [Int.cast_natCast] using gcd_mem a b haP hbP) hcP
    simpa only [hprim, Nat.cast_one] using h
  have hP : P = 1 := by
    apply le_antisymm
    · change J * (1 / J) ≤ 1
      rw [mul_comm, ← le_div_iff_mul_le hp.ne_zero]
    · simpa only [map_one] using (spanSingleton_le_iff_mem (x := (1 : k))).mpr h1P
  apply IsUnit.of_mul_eq_one (1 / J * spanSingleton _ u⁻¹)
  calc
    I * (1 / J * spanSingleton _ u⁻¹) = J * (1 / J) := by
      dsimp [J]
      ac_rfl
    _ = 1 := hP

end HDec.CMBranch.FowlerBridges
