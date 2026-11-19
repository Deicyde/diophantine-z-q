import ZInQKernel.Contrib.OneProof.RC.O12Formwise.Attachment
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Constituents
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! The good Fourier formula on the one form, with its diamond translate in
the existing integral lattice (tex 9660–9668, 9670–9674, 9719–9721). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Formwise

open ThetaCoeff AddressGenuine PrintsArith TraceLimits
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {I K O G L : Type} [Fintype I] [Field K] [TopologicalSpace K] [CommRing O] [IsDomain O]
  [CharZero O] [Algebra O K] [Group G] [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ} {m : Ideal O}
variable {M W R : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable {P : Window T.Good S W} {A : Basis I K G (Test T avoid)}
variable {E : Lift S} {D : Divisions E δ W R adm} {C : DiamondCharacters O G E.η}
variable {V : Blocks (P := P) A E D C} {N : BlockLevels V} {ρ₀ : Attachment (frob := frob) A}
variable (H : AtLevel N ρ₀)

include H in
/-- Sum the good recursion over the nonzero coordinates of the form. The
diamond term is written in terms of the scaled diamond, i.e. the determinant. -/
theorem seed_fourier_over_field {U : Finset ℕ} {q : ℕ} (hq : T.Good q) (hqU : q ∉ U)
    (hf : IsFrobAt (frob q) q) (n : ℕ) :
    A.eval n (tV ρ₀.ρ (frob q) (V.seed U)) =
      A.eval (q * n) (V.seed U) +
      if q ∣ n then A.eval (n / q) (dV ρ₀.ρ (frob q) (V.seed U)) else 0 := by
  classical
  simp only [Basis.eval, LinearMap.coe_mk, AddHom.coe_mk, tV, dV, scalarOp_apply]
  by_cases hn : q ∣ n
  · rw [ite_eq_left hn, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : V.seed U i = 0
    · simp [hi]
    · obtain ⟨ht, hd⟩ := good_values H hq (seed_level_coprime N hq hqU hi) hf
      have hr := seed_good_recursion H hq hqU hi n
      rw [show Odd.divCoeff (Odd.divCoeff (A.base i).a (A.degree i)) q n = _ by
        exact ite_eq_left hn] at hr
      rw [ht, hd]
      linear_combination V.seed U i * hr
  · rw [ite_eq_right hn, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : V.seed U i = 0
    · simp [hi]
    · have ht := (good_values H hq (seed_level_coprime N hq hqU hi) hf).1
      have hr := seed_good_recursion H hq hqU hi n
      rw [Odd.divCoeff_of_not_dvd _ hn, mul_zero, add_zero] at hr
      rw [ht]
      linear_combination V.seed U i * hr

variable [IsLocalRing O]

omit [IsDomain O] [CharZero O] in
/-- Every odd integer is a unit in the coefficient local ring with residue
characteristic two. On-the-spot (c). -/
theorem odd_unit (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) {q : ℕ} (hq : Odd q) :
    IsUnit (q : O) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  rw [← IsLocalRing.eq_maximalIdeal hm]
  intro h
  obtain ⟨k, rfl⟩ := hq
  have hk := m.mul_mem_right (k : O) h2
  have he : (1 : O) = ((2 * k + 1 : ℕ) : O) - 2 * (k : O) := by push_cast; ring
  apply (m.ne_top_iff_one.mp hm.ne_top)
  rw [he]
  exact m.sub_mem h hk

include H in
/-- The excluded good-prime comparison `hexcl` on the same seed and the
same integral lattice. The local diamond is a scaled determinant translate
in that lattice (on-the-spot (c)); it need not be an ambient good operator. -/
theorem seed_fourier (hinj : Function.Injective (algebraMap O K))
    (hm : m.IsMaximal) (h2 : (2 : O) ∈ m)
    (hst : ∀ g, ∀ v ∈ A.Λ (O := O) V.seed, tV ρ₀.ρ g v ∈ A.Λ (O := O) V.seed)
    (hsd : ∀ g, ∀ v ∈ A.Λ (O := O) V.seed, dV ρ₀.ρ g v ∈ A.Λ (O := O) V.seed)
    {U : Finset ℕ} {q : ℕ} (hq : T.Good q) (hqU : q ∉ U)
    (hf : IsFrobAt (frob q) q) :
    ∃ diamondF : A.Λ (O := O) V.seed,
      (q : O) • diamondF = latD ρ₀.ρ _ hsd (frob q) (V.F U) ∧
      (∀ i, (diamondF : I → K) i = (A.base i).χ q * V.seed U i) ∧
      ∀ n, V.coeff hinj n (latT ρ₀.ρ _ hst (frob q) (V.F U)) =
        V.coeff hinj (q * n) (V.F U) +
          if q ∣ n then (q : O) * V.coeff hinj (n / q) diamondF else 0 := by
  obtain ⟨u, hu⟩ := odd_unit hm h2 (hq.1.odd_of_ne_two hq.ne_two)
  let detF := latD ρ₀.ρ _ hsd (frob q) (V.F U)
  let diamondF := ((u⁻¹ : Oˣ) : O) • detF
  have he : (q : O) • diamondF = detF := by
    rw [← hu]
    simp [diamondF, smul_smul, ← Units.val_mul]
  have hqK : (q : K) ≠ 0 := by
    simpa only [hu, map_natCast] using (u.isUnit.map (algebraMap O K)).ne_zero
  have hχ (i : I) : (diamondF : I → K) i = (A.base i).χ q * V.seed U i := by
    have e := congrArg (fun v : A.Λ (O := O) V.seed => (v : I → K) i) he
    change ((q : O) • (diamondF : I → K)) i = dV ρ₀.ρ (frob q) (V.seed U) i at e
    rw [Pi.smul_apply, Algebra.smul_def, map_natCast, dV, scalarOp_apply] at e
    apply mul_left_cancel₀ hqK
    by_cases hi : V.seed U i = 0
    · simpa only [hi, mul_zero] using e
    · rw [(good_values H hq (seed_level_coprime N hq hqU hi) hf).2, mul_assoc] at e
      exact e
  refine ⟨diamondF, he, hχ, fun n => ?_⟩
  have hmul : (q : O) * V.coeff hinj (n / q) diamondF = V.coeff hinj (n / q) detF := by
    simpa only [map_smul, smul_eq_mul] using congrArg (V.coeff hinj (n / q)) he
  rw [hmul]
  apply hinj
  rw [map_add, A.coeff_spec, A.coeff_spec]
  rw [show algebraMap O K (ite (q ∣ n) (V.coeff hinj (n / q) detF) 0) =
    if q ∣ n then A.eval (n / q) (dV ρ₀.ρ (frob q) (V.seed U)) else 0 by
      split_ifs <;> simp only [map_zero, A.coeff_spec, detF, latD_coe, Blocks.F]]
  exact seed_fourier_over_field H hq hqU hf n

#print axioms seed_fourier_over_field
#print axioms odd_unit
#print axioms seed_fourier

end ZInQ.Manuscript.RC.O12Formwise
