import ZInQKernel.OneProof.H.LPrefix

/-! A Tate tower whose components lie in a fixed finite subgroup is zero. -/

namespace PkgI3.Tate

variable {M : Type*} [AddCommGroup M] {ℓ : ℕ} [Fact ℓ.Prime]

theorem eq_zero_of_mem_finite_subgroup (H : AddSubgroup M) [Finite H]
    (y : T ℓ M) (hy : ∀ n, y.1 n ∈ H) : y = 0 := by
  apply Subtype.ext
  funext n
  change y.1 n = 0
  have hshift (d : ℕ) : ℓ ^ d • y.1 (n + d) = y.1 n := by
    induction d with
    | zero => simp
    | succ d ih =>
      rw [pow_succ, mul_smul]
      exact (congrArg (ℓ ^ d • ·) (y.2.2 (n + d))).trans ih
  let m := Nat.card H
  let x : H := ⟨y.1 (n + m), hy (n + m)⟩
  have hx : ℓ ^ (n + m) • x = 0 :=
    Subtype.ext (pow_smul_eq_zero y.2 (n + m))
  obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow (Fact.out : ℓ.Prime)).mp
    (addOrderOf_dvd_of_nsmul_eq_zero hx)
  have hd_card : ℓ ^ d ≤ m := by
    rw [← hd]
    exact Nat.le_of_dvd Nat.card_pos (addOrderOf_dvd_natCard x)
  have hd_le : d ≤ m :=
    (Nat.lt_two_pow_self (n := d)).le.trans
      ((Nat.pow_le_pow_left (Fact.out : ℓ.Prime).two_le _).trans hd_card)
  have hkill : ℓ ^ m • x = 0 := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [hd]
    exact pow_dvd_pow _ hd_le
  exact (hshift m).symm.trans (congrArg Subtype.val hkill)

/-- A Tate tower in the finite kernel of a multiplicative homomorphism is zero. -/
theorem eq_zero_of_apply_eq_one_of_finite_kernel {C : Type*} [Group C]
    (f : Multiplicative M →* C) (hf : {x : Multiplicative M | f x = 1}.Finite)
    (y : T ℓ M) (hy : ∀ n, f (Multiplicative.ofAdd (y.1 n)) = 1) : y = 0 := by
  let H : AddSubgroup M := f.ker.toAddSubgroup
  let e : H → {x : Multiplicative M // f x = 1} :=
    fun x => ⟨Multiplicative.ofAdd x.1, x.2⟩
  have : Finite {x : Multiplicative M // f x = 1} := hf.to_subtype
  have : Finite H := Finite.of_injective e fun x z h =>
    Subtype.ext (congrArg (fun a : {x : Multiplicative M // f x = 1} =>
      Multiplicative.toAdd a.1) h)
  exact eq_zero_of_mem_finite_subgroup H y hy

end PkgI3.Tate
