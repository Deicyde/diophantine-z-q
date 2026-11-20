import ZInQKernel.Contrib.OneProof.SZRaynaud

/-!
# Frobenius-fixed Tate towers over a finite field

An endomorphism whose fixed point group is finite has no nonzero fixed
vectors on an integral Tate module. The underlying group may be infinite.
-/

namespace SZRaynaud

variable {M : Type} [AddCommGroup M] {ℓ : ℕ} [Fact ℓ.Prime]

theorem tate_eq_zero_of_finite [Finite M] (t : PkgI3.Tate.T ℓ M) : t = 0 := by
  apply Subtype.ext
  funext n
  change t.1 n = 0
  let m := Nat.card M
  let x := t.1 (n + m)
  have hpow : ∀ k, (ℓ ^ k) • t.1 (n + k) = t.1 n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_smul]
      exact (congrArg ((ℓ ^ k) • ·) (t.2.2 (n + k))).trans ih
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : ℓ.Prime)).mp
    (addOrderOf_dvd_of_nsmul_eq_zero (pow_smul_tate t (n + m)))
  have hcard : ℓ ^ k ≤ m := by
    rw [← hk]
    exact Nat.le_of_dvd Nat.card_pos (addOrderOf_dvd_natCard x)
  have hk_le : k ≤ m :=
    ((show k < 2 ^ k from Nat.lt_two_pow_self).le.trans
      (Nat.pow_le_pow_left (Fact.out : ℓ.Prime).two_le _)).trans hcard
  have hx : (ℓ ^ m) • x = 0 := by
    apply (addOrderOf_dvd_iff_nsmul_eq_zero).mp
    rw [hk]
    exact pow_dvd_pow _ hk_le
  exact (hpow m).symm.trans hx

/-- Only the fixed points need be finite, even when the ambient group is
infinite. -/
theorem tate_eq_zero_of_finite_fixed (f : M →+ M)
    (hfin : Finite {x : M // f x = x}) (t : PkgI3.Tate.T ℓ M)
    (ht : ∀ n, f (t.1 n) = t.1 n) : t = 0 := by
  let G : AddSubgroup M := (f - AddMonoidHom.id M).ker
  have hG : ∀ x, x ∈ G ↔ f x = x := by
    intro x
    change f x - x = 0 ↔ f x = x
    exact sub_eq_zero
  let e : G → {x : M // f x = x} := fun x => ⟨x, (hG x).mp x.2⟩
  have : Finite G := Finite.of_injective e (fun x y h => Subtype.ext
    (congrArg (fun z : {x : M // f x = x} => z.1) h))
  let s : PkgI3.Tate.T ℓ G := ⟨fun n => ⟨t.1 n, (hG _).mpr (ht n)⟩,
    Subtype.ext t.2.1, fun n => Subtype.ext (t.2.2 n)⟩
  have hs := tate_eq_zero_of_finite s
  apply Subtype.ext
  funext n
  exact congrArg (fun u : PkgI3.Tate.T ℓ G => (u.1 n).1) hs

#print axioms tate_eq_zero_of_finite
#print axioms tate_eq_zero_of_finite_fixed

end SZRaynaud
