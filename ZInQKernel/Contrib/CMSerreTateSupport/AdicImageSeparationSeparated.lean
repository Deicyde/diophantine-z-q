import ZInQKernel.Contrib.CMSerreTateSupport.FiniteMatrixCongruenceResidues

/-!
# Adic separation of coprime finite-quotient images

The genuine integral congruence kernel has ell-group images at every
finite adic level. Those levels separate matrices. A group whose finite
level images are p-groups, with p distinct from ell, therefore has its
whole integral image injected into the finite residual image.
-/

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace IntegralCongruence

open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

def residual (ell : ℕ) [Fact ell.Prime] : GL d ℤ_[ell] →* GL d (ZMod ell) :=
  Matrix.GeneralLinearGroup.map PadicInt.toZMod

def level (ell n : ℕ) [Fact ell.Prime] : GL d ℤ_[ell] →* GL d (ZMod (ell ^ (n + 1))) :=
  Matrix.GeneralLinearGroup.map (PadicInt.toZModPow (n + 1))

theorem adic_kernel_principal (ell : ℕ) [Fact ell.Prime]
    (g : (residual (d := d) ell).ker) :
    ∃ B : Matrix d d ℤ_[ell], (g.1 : Matrix d d ℤ_[ell]) = 1 + (ell : Matrix d d ℤ_[ell]) * B := by
  classical
  let A : Matrix d d ℤ_[ell] := (g.1 : Matrix d d ℤ_[ell])
  let D := A - 1
  have hD : ∀ i j, (ell : ℤ_[ell]) ∣ D i j := by
    intro i j
    have hg := congrArg (fun u : GL d (ZMod ell) => (u : Matrix d d (ZMod ell)) i j) g.2
    have hz : PadicInt.toZMod (D i j) = 0 := by
      dsimp only [D]
      rw [Matrix.sub_apply, map_sub]
      apply sub_eq_zero.mpr
      by_cases hij : i = j
      · simpa [A, residual, Matrix.one_apply, hij] using hg
      · simpa [A, residual, Matrix.one_apply, hij] using hg
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at hz
    exact hz
  choose B hB using hD
  let C : Matrix d d ℤ_[ell] := B
  have hprod : (ell : Matrix d d ℤ_[ell]) * C = D := by
    apply Matrix.ext
    intro i j
    rw [← nsmul_eq_mul]
    change ell • C i j = D i j
    rw [nsmul_eq_mul]
    exact (hB i j).symm
  exact ⟨C, by rw [hprod]; dsimp [D]; abel⟩

/-- An explicit finite-level exponent bound for the actual congruence kernel. -/
theorem adic_kernel_level_power (ell n : ℕ) [Fact ell.Prime]
    (g : (residual (d := d) ell).ker) : level ell n g.1 ^ (ell ^ n) = 1 := by
  obtain ⟨B, hB⟩ := adic_kernel_principal ell g
  have hg : (level ell n g.1 : Matrix d d (ZMod (ell ^ (n + 1)))) =
      1 + (ell : Matrix d d (ZMod (ell ^ (n + 1)))) * B.map (PadicInt.toZModPow (n + 1)) := by
    change (RingHom.mapMatrix (PadicInt.toZModPow (n + 1))) (g.1 : Matrix d d ℤ_[ell]) = _
    rw [hB, map_add, map_one, map_mul, map_natCast]
    rfl
  exact principal_unit_power ell n
    (by
      rw [← Nat.cast_pow]
      ext i j
      simp [Matrix.natCast_apply, CharP.cast_eq_zero]) _ _ hg

/-- The canonical finite-level images of the actual kernel are ell-groups. -/
theorem adic_kernel_level_isPGroup (ell n : ℕ) [Fact ell.Prime] :
    IsPGroup ell ((residual (d := d) ell).ker.map (level ell n)) := by
  intro u
  obtain ⟨g, hg, hgu⟩ := u.2
  refine ⟨n, Subtype.ext ?_⟩
  change u.1 ^ (ell ^ n) = 1
  rw [← hgu]
  exact adic_kernel_level_power ell n ⟨g, hg⟩

/-- No nonidentity adic matrix is invisible at every finite level. -/
theorem level_separates (ell : ℕ) [Fact ell.Prime] (g : GL d ℤ_[ell])
    (hg : ∀ n, level ell n g = 1) : g = 1 := by
  apply Units.ext
  change g.val = (1 : Matrix d d ℤ_[ell])
  apply Matrix.ext
  intro i j
  change g.val i j = (1 : Matrix d d ℤ_[ell]) i j
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
    change (PadicInt.toZModPow 0 (g.val i j) : ZMod 1) = PadicInt.toZModPow 0 ((1 : Matrix d d ℤ_[ell]) i j)
    haveI : Subsingleton (ZMod (ell ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    have h := congrArg (fun u : GL d (ZMod (ell ^ (n + 1))) =>
      (u : Matrix d d (ZMod (ell ^ (n + 1)))) i j) (hg n)
    simpa [level, Matrix.one_apply] using h

section CoprimeImage

variable {G : Type*} [Group G]

/-- Generic intermediate statement: every actual finite-level image must
still be supplied as a p-group before this can be used on a representation. -/
theorem kernel_trivial_of_finite_level_pGroups (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hne : p ≠ ell) (rho : G →* GL d ℤ_[ell])
    (hP : ∀ n, IsPGroup p ((level ell n).comp rho).range)
    (g : G) (hg : residual ell (rho g) = 1) : rho g = 1 := by
  apply level_separates ell
  intro n
  let u : ((level ell n).comp rho).range := ⟨level ell n (rho g), ⟨g, rfl⟩⟩
  obtain ⟨j, hj⟩ := hP n u
  have hp : orderOf u ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj
  have he : orderOf u ∣ ell ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    exact adic_kernel_level_power ell n ⟨rho g, hg⟩
  have hu : u = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_pow_primes j n (Fact.out : p.Prime) (Fact.out : ell.Prime) hne) hp he)
  exact congrArg Subtype.val hu

/-- The whole image is finite, not merely each finite-level image. -/
theorem finite_image_of_finite_level_pGroups (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (hne : p ≠ ell) (rho : G →* GL d ℤ_[ell])
    (hP : ∀ n, IsPGroup p ((level ell n).comp rho).range) : (Set.range rho).Finite := by
  let f : rho.range →* GL d (ZMod ell) := (residual ell).comp rho.range.subtype
  have kill : ∀ x : rho.range, f x = 1 → x = 1 := by
    intro x hx
    obtain ⟨g, hg⟩ := x.2
    apply Subtype.ext
    rw [← hg]
    apply kernel_trivial_of_finite_level_pGroups p ell hne rho hP g
    simpa [f, hg] using hx
  have hf : Function.Injective f := by
    intro x y hxy
    apply inv_mul_eq_one.mp
    apply kill
    simp only [map_mul, map_inv, hxy, inv_mul_cancel]
  have hi : Set.InjOn (residual (d := d) ell) (Set.range rho) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hf (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  exact Set.Finite.of_injOn (t := Set.univ) (fun _ _ => Set.mem_univ _) hi (Set.toFinite _)

end CoprimeImage

#print axioms adic_kernel_principal
#print axioms adic_kernel_level_power
#print axioms adic_kernel_level_isPGroup
#print axioms level_separates
#check finite_image_of_finite_level_pGroups
#print axioms finite_image_of_finite_level_pGroups

end IntegralCongruence
