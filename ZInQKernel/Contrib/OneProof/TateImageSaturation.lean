import ZInQKernel.Contrib.OneProof.GRUniformQuasiInverse

/-! The image of the integral Tate comparison map is saturated. -/

noncomputable section

open PkgI3.AbVar
open scoped TensorProduct CategoryTheory.MonObj

namespace ZInQ.Contrib.TateImageSaturation

private theorem padicInt_exists_nat_add_mul {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (n : ℕ)
    (a : ℤ_[ℓ]) : ∃ (k : ℕ) (b : ℤ_[ℓ]), a = (k : ℤ_[ℓ]) + (ℓ : ℤ_[ℓ]) ^ n * b := by
  let k := (PadicInt.toZModPow n a).val
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  have hmem : a - (k : ℤ_[ℓ]) ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ n} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast]
    rw [show (k : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a from ZMod.natCast_zmod_val _, sub_self]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨k, b, by rw [← hb]; ring⟩

/-- Modulo any power of ℓ, a tensor is represented by a single element of
the original abelian group. -/
theorem tensor_exists_one_tmul_add_nsmul {ℓ : ℕ} [Fact ℓ.Prime] (n : ℕ)
    {H : Type*} [AddCommGroup H] (ξ : ℤ_[ℓ] ⊗[ℤ] H) :
    ∃ (g : H) (ζ : ℤ_[ℓ] ⊗[ℤ] H), ξ = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] g + (ℓ ^ n : ℕ) • ζ := by
  induction ξ using TensorProduct.inductionOn with
  | tmul a g =>
    obtain ⟨k, b, rfl⟩ := padicInt_exists_nat_add_mul (ℓ := ℓ) n a
    refine ⟨k • g, b ⊗ₜ[ℤ] g, ?_⟩
    rw [TensorProduct.add_tmul]
    have hk : ((k : ℤ_[ℓ]) ⊗ₜ[ℤ] g) = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] (k • g) := by
      calc
        _ = (((k : ℤ) • (1 : ℤ_[ℓ])) ⊗ₜ[ℤ] g) := by simp
        _ = _ := by rw [TensorProduct.smul_tmul, natCast_zsmul]
    rw [hk, ← smul_eq_mul, ← TensorProduct.smul_tmul', ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  | add x y hx hy =>
    obtain ⟨f, ξ, rfl⟩ := hx
    obtain ⟨g, ζ, rfl⟩ := hy
    exact ⟨f + g, ξ + ζ, by rw [TensorProduct.tmul_add, nsmul_add]; abel⟩

private theorem tate_pow_nsmul_injective {ℓ : ℕ} [Fact ℓ.Prime] (n : ℕ)
    {M : Type*} [AddCommGroup M] : Function.Injective (fun x : PkgI3.Tate.T ℓ M => ℓ ^ n • x) := by
  intro x y h
  apply Subtype.ext
  funext j
  have hj := congrArg (fun v : PkgI3.Tate.T ℓ M => v.1 (j + n)) h
  change ℓ ^ n • x.1 (j + n) = ℓ ^ n • y.1 (j + n) at hj
  rwa [PkgI3.Tate.pow_smul_shift x.2 n j, PkgI3.Tate.pow_smul_shift y.2 n j] at hj

/-- An integral linear map whose `ℓ^n` multiple comes from an element of
`ℤ_ℓ ⊗ Hom(A,B)` already comes from an element of this tensor product. -/
theorem tateHomZl_saturated {K : Type} [Field K] [CharZero K] {A B : PkgI3.AbVar K}
    (ℓ n : ℕ) [Fact ℓ.Prime] (φ : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ)
    (h : (ℓ ^ n : ℕ) • φ ∈ Set.range (tateHomZl ℓ A B)) :
    φ ∈ Set.range (tateHomZl ℓ A B) := by
  obtain ⟨ξ, hξ⟩ := h
  obtain ⟨g, ζ, rfl⟩ := tensor_exists_one_tmul_add_nsmul (ℓ := ℓ) n ξ
  have hone (f : Hom A B) : tateHomZl ℓ A B ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] f) = homT f := by
    change (1 : ℤ_[ℓ]) • homT (ℓ := ℓ) f = homT (ℓ := ℓ) f
    exact one_smul _ _
  rw [map_add, hone, map_nsmul] at hξ
  have hh : homT (ℓ := ℓ) g = (ℓ ^ n : ℕ) • (φ - tateHomZl ℓ A B ζ) := by
    rw [smul_sub, ← hξ, add_sub_cancel_right]
  obtain ⟨u, hu⟩ := GRUniformQuasiInverse.exists_eq_nsmul_of_homT_dvd g ℓ n (fun x => by
    refine ⟨(φ - tateHomZl ℓ A B ζ) x, ?_⟩
    rw [hh]
    change (ℓ ^ n : ℕ) • (φ - tateHomZl ℓ A B ζ) x = _
    rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], Nat.cast_pow])
  have hgu : homT (ℓ := ℓ) g = (ℓ ^ n : ℕ) • homT u := by
    change tateHom ℓ A B g = (ℓ ^ n : ℕ) • tateHom ℓ A B u
    rw [hu, map_nsmul]
  refine ⟨(1 : ℤ_[ℓ]) ⊗ₜ[ℤ] u + ζ, ?_⟩
  rw [map_add, hone]
  apply LinearMap.ext
  intro x
  apply tate_pow_nsmul_injective (ℓ := ℓ) n
  have hx := LinearMap.congr_fun (hgu.symm.trans hh) x
  change (ℓ ^ n : ℕ) • homT (ℓ := ℓ) u x =
    (ℓ ^ n : ℕ) • (φ x - tateHomZl ℓ A B ζ x) at hx
  change (ℓ ^ n : ℕ) • (homT (ℓ := ℓ) u x + tateHomZl ℓ A B ζ x) = (ℓ ^ n : ℕ) • φ x
  rw [nsmul_add, hx, ← nsmul_add, sub_add_cancel]

/-- With injectivity supplied by `HomFreeFinite`, the integral comparison
reduces to finding algebraic representatives up to a power of the prime. -/
theorem faltingsTate_iff_exists_primePower_mul_mem_range (hH : PkgI3.HomFreeFinite) :
    PkgI3.FaltingsTate ↔
    ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
      (φ : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ), IsGalEquivariant φ →
        ∃ n : ℕ, (ℓ ^ n : ℕ) • φ ∈ Set.range (tateHomZl ℓ A B) := by
  constructor
  · intro h K _ _ A B ℓ _ φ hφ
    refine ⟨0, ?_⟩
    simpa only [pow_zero, one_nsmul, (h K A B ℓ).2, Set.mem_ofPred_eq] using hφ
  · intro h K _ _ A B ℓ hℓ
    have hcast : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.out.ne_zero
    refine ⟨(hH K A B).2.2.2 ℓ hcast, Set.Subset.antisymm
      (PkgI3.range_tateHomZl_subset A B ℓ) ?_⟩
    intro φ hφ
    obtain ⟨n, hn⟩ := h K A B ℓ φ hφ
    exact tateHomZl_saturated ℓ n φ hn

end ZInQ.Contrib.TateImageSaturation

#print axioms ZInQ.Contrib.TateImageSaturation.tateHomZl_saturated

#print axioms ZInQ.Contrib.TateImageSaturation.faltingsTate_iff_exists_primePower_mul_mem_range
