import ZInQKernel.Contrib.CMSerreTateSupport.NativeTateCongruenceMatrices
import ZInQKernel.Contrib.CMSerreTateSupport.AdicReductionTopologyContinuous

/-!
# Compact compatible Tate approximation

A spanning family in the actual first projection image generates the
whole compatible Tate module. The proof uses the constructed shift
quotient and compactness of finite products of padic integers, not a
supplied rank or a torsion-cardinality formula.
-/

noncomputable section
set_option autoImplicit false

namespace FiniteProjectionTate

open NativeTateCongruence Topology

variable {ell : ℕ} [Fact ell.Prime] {M : Type*} [AddCommGroup M]

abbrev TT := PkgI3.Tate.T ell M

theorem ell_smul_succ (t : TT (ell := ell) (M := M)) (n : ℕ) :
    ((ell : ℤ_[ell]) • t).1 (n + 1) = t.1 n := by
  rw [show (ell : ℤ_[ell]) = (ell : ℤ_[ell]) ^ 1 by simp, scalar_power_apply]
  simpa only [pow_one] using t.2.2 n

variable {r : ℕ} (X : Fin r → TT (ell := ell) (M := M))

/-- A first-projection span gives approximations at every actual level. -/
theorem approximate_level
    (hspan : ∀ t : TT (ell := ell) (M := M), ∃ a : Fin r → ℤ_[ell],
      (Fintype.linearCombination ℤ_[ell] X a).1 1 = t.1 1) (n : ℕ)
    (t : TT (ell := ell) (M := M)) :
    ∃ a : Fin r → ℤ_[ell], (Fintype.linearCombination ℤ_[ell] X a).1 n = t.1 n := by
  induction n generalizing t with
  | zero => exact ⟨0, by simpa using t.2.1.symm⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := hspan t
    let L := Fintype.linearCombination ℤ_[ell] X
    have hzero : (t - L a).1 1 = 0 := by
      change t.1 1 - (L a).1 1 = 0
      exact sub_eq_zero.mpr ha.symm
    obtain ⟨u, hu⟩ := (projection_zero_iff_divisible (t - L a) 1).mp hzero
    rw [pow_one] at hu
    have ht : t = L a + (ell : ℤ_[ell]) • u := by
      have h := sub_eq_iff_eq_add.mp hu
      simpa only [add_comm] using h
    obtain ⟨d, hd⟩ := ih u
    let c := a + (ell : ℤ_[ell]) • d
    have he : t - L c = (ell : ℤ_[ell]) • (u - L d) := by
      dsimp only [c]
      rw [ht, map_add, map_smul, smul_sub]
      abel
    have hz : (t - L c).1 (n + 1) = 0 := by
      rw [he, ell_smul_succ]
      change u.1 n - (L d).1 n = 0
      exact sub_eq_zero.mpr hd.symm
    refine ⟨c, ?_⟩
    change t.1 (n + 1) - (L c).1 (n + 1) = 0 at hz
    exact (sub_eq_zero.mp hz).symm

section Topology

variable [TopologicalSpace M] [DiscreteTopology M]

theorem linearCombination_continuous : Continuous (Fintype.linearCombination ℤ_[ell] X) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro n
  change Continuous (fun a : Fin r → ℤ_[ell] => (Fintype.linearCombination ℤ_[ell] X a).1 n)
  have he : (fun a : Fin r → ℤ_[ell] => (Fintype.linearCombination ℤ_[ell] X a).1 n) =
      (fun a => ∑ i, (PadicInt.toZModPow n (a i)).val • (X i).1 n) :=
    funext fun a => OriginalCompatibleTate.lc_apply X a n
  rw [he]
  apply continuous_finset_sum
  intro i hi
  have hact : Continuous (fun z : ZMod (ell ^ n) => z.val • (X i).1 n) :=
    continuous_of_discreteTopology
  exact hact.comp ((IntegralCongruence.toZModPow_continuous ell n).comp (continuous_apply i))

/-- Compact coefficients produce one genuine compatible Tate expansion. -/
theorem linearCombination_surjective
    (hspan : ∀ t : TT (ell := ell) (M := M), ∃ a : Fin r → ℤ_[ell],
      (Fintype.linearCombination ℤ_[ell] X a).1 1 = t.1 1) :
    Function.Surjective (Fintype.linearCombination ℤ_[ell] X) := by
  intro t
  let L := Fintype.linearCombination ℤ_[ell] X
  let S : ℕ → Set (Fin r → ℤ_[ell]) := fun n => {a | (L a).1 n = t.1 n}
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    have hc : Continuous (fun a => (L a).1 n) :=
      (continuous_apply n).comp (continuous_subtype_val.comp (linearCombination_continuous X))
    exact isClosed_eq hc continuous_const
  have hne : ∀ n, (S n).Nonempty := fun n => approximate_level X hspan n t
  have hdec : ∀ n, S (n + 1) ⊆ S n := by
    intro n a ha
    have h := congrArg (fun z : M => ell • z) ha
    rw [(L a).2.2 n, t.2.2 n] at h
    exact h
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hdec hne ((hcl 0).isCompact) hcl
  exact ⟨a, Subtype.ext (funext fun n => Set.mem_iInter.mp ha n)⟩

end Topology

/-- Independence in the actual first projection lifts to every level. -/
theorem lifted_coeff_dvd
    (hind : ∀ c : Fin r → ℤ, ∑ i, c i • (X i).1 1 = 0 → ∀ i, (ell : ℤ) ∣ c i) (n : ℕ) :
    ∀ c : Fin r → ℤ, ∑ i, c i • (X i).1 n = 0 → ∀ i, (ell : ℤ) ^ n ∣ c i := by
  induction n with
  | zero => intro c _ i; simp
  | succ n ih =>
    intro c hc
    have h1 : ∑ i, c i • (X i).1 1 = 0 := by
      have h := congrArg (fun z : M => ell ^ n • z) hc
      simp only [smul_zero, Finset.smul_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm, show n + 1 = 1 + n by omega,
        OriginalCompatibleTate.pow_smul_add (X i).2 1 n]
    choose d hd using fun i => hind c h1 i
    have h2 : ∑ i, d i • (X i).1 n = 0 := by
      rw [← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd i, mul_comm, mul_zsmul, natCast_zsmul, (X i).2.2 n]
    intro i
    obtain ⟨k, hk⟩ := ih d h2 i
    rw [hd i, hk, pow_succ]
    exact ⟨k, by ring⟩

theorem linearCombination_injective
    (hind : ∀ c : Fin r → ℤ, ∑ i, c i • (X i).1 1 = 0 → ∀ i, (ell : ℤ) ∣ c i) :
    Function.Injective (Fintype.linearCombination ℤ_[ell] X) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  funext i
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have h0 : ∑ j, (((PadicInt.toZModPow n (a j)).val : ℕ) : ℤ) • (X j).1 n = 0 := by
    have h := congrArg (fun t : TT (ell := ell) (M := M) => t.1 n) ha
    rw [OriginalCompatibleTate.lc_apply X] at h
    refine (Finset.sum_congr rfl fun j _ => natCast_zsmul _ _).trans ?_
    rw [h]
    rfl
  have hdiv := lifted_coeff_dvd X hind n _ h0 i
  have hnat : ell ^ n ∣ (PadicInt.toZModPow n (a i)).val := by exact_mod_cast hdiv
  have hz : PadicInt.toZModPow n (a i) = 0 := by
    have hv : ((PadicInt.toZModPow n (a i)).val : ZMod (ell ^ n)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hnat
    simpa only [ZMod.natCast_zmod_val] using hv
  simpa using hz

#print axioms approximate_level
#print axioms linearCombination_surjective
#print axioms linearCombination_injective

end FiniteProjectionTate
