import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Galois

/-! Assemble the finite common realization over the already chosen coefficient
extension of the same stage. No reduction modulo the coefficient maximal ideal
or choice of a different theta lift is involved. -/

noncomputable section

namespace ZInQ.Manuscript.RC.BlocksPerU

open ThetaCoeff O12Formwise AddressGenuine PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped BigOperators Classical

variable {I J K O L : Type} [Fintype I] [Field K] [TopologicalSpace K]
  [CommRing O] [IsDomain O] [CharZero O] [Algebra O K] [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ}
variable {M W R : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable {P : Window T.Good S W} {E : Lift S} {D : Divisions E δ W R adm}
variable {N : ℕ} [NeZero N]

/-- The old level and the choice of common testing domain. This records no
constituents, transformations, or Galois representations. -/
structure LevelSetup (P : Window T.Good S W) (avoid : Finset ℕ) (N : ℕ) where
  old : ℕ
  four_dvd : 4 ∣ old
  common : N = old * ∏ p ∈ P.pool, p
  old_good : ∀ q, T.Good q → q.Coprime old
  pool_avoided : P.pool ⊆ avoid

variable (Dₗ : LevelSetup P avoid N)

omit [NeZero N] [IsDomain O] [CharZero O] in
theorem LevelSetup.common_four (Dₗ : LevelSetup P avoid N) : 4 ∣ N :=
  Dₗ.common.symm ▸ Dₗ.four_dvd.trans (dvd_mul_right _ _)

omit [NeZero N] [IsDomain O] [CharZero O] in
theorem LevelSetup.test_coprime (Dₗ : LevelSetup P avoid N) (q : ℕ) (hq : Test T avoid q) : q.Coprime N := by
  rw [Dₗ.common]
  apply (Dₗ.old_good q hq.1).mul_right
  apply (Nat.Prime.coprime_iff_not_dvd hq.1.1).mpr
  intro h
  obtain ⟨p, hp, hqp⟩ := (hq.1.1.prime.dvd_finsetProd_iff _).mp h
  have e := (Nat.prime_dvd_prime_iff_eq hq.1.1 (P.type_good p hp).1).mp hqp
  exact hq.2 (Dₗ.pool_avoided (e.symm ▸ hp))

omit [NeZero N] [IsDomain O] [CharZero O] in
theorem LevelSetup.b_dvd {U : Finset ℕ} (hU : U ⊆ P.pool) :
    Dₗ.old * ∏ p ∈ U, p ∣ N := by
  exact (congrArg (fun x => (Dₗ.old * ∏ p ∈ U, p) ∣ x) Dₗ.common).mpr
    (Nat.mul_dvd_mul_left Dₗ.old (Finset.prod_dvd_prod_of_subset _ _ id hU))

omit [NeZero N] [IsDomain O] [CharZero O] in
theorem LevelSetup.unary_dvd {U : Finset ℕ} (hU : U ⊆ P.pool) {j : ℕ}
    (hj : j ∈ subscripts U) : Dₗ.old * j ∣ N := by
  obtain ⟨hsq, hsub⟩ := (mem_subscripts (fun p hp => (P.type_good p (hU hp)).1) j).mp hj
  apply dvd_trans _ (Dₗ.b_dvd hU)
  apply Nat.mul_dvd_mul_left
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  exact Finset.prod_dvd_prod_of_subset _ _ id hsub

/-- The manuscript's two transformation assertions, with the positive
Fourier coefficients of the fixed stage. The two levels are specified before
any constituent expansion or attachment is chosen. -/
structure BlockModularity (κ : K →+* ℂ) (Dₗ : LevelSetup P avoid N)
    (D : Divisions E δ W R adm) (C : DiamondCharacters O (ZMod N)ˣ E.η) : Prop where
  b : ∀ U (hU : U ⊆ P.pool),
    HasWeightTwoExpansion κ (Dₗ.b_dvd hU) (bCharacter C U)
      (fun n => algebraMap O K (E.FourierB D (P.admissible U hU) n))
  unary : ∀ U (hU : U ⊆ P.pool) j (hj : j ∈ subscripts U),
    HasWeightTwoExpansion κ (Dₗ.unary_dvd hU hj) (unaryCharacter C E.parity j)
      (fun n => algebraMap O K (E.FourierUnary j n))

omit [IsDomain O] [CharZero O] in
private theorem raw_zero (D : Divisions E δ W R adm) (U : Finset ℕ) : E.raw U 0 = 0 := by
  unfold Lift.raw
  generalize U.sort (· ≤ ·) = l
  induction l with
  | nil => exact D.zero
  | cons p l ih => simp [Odd.TL, Odd.Top, Odd.divCoeff, ih]

private theorem fourierB_zero (D : Divisions E δ W R adm) {U : Finset ℕ}
    (hU : Admissible S W U) : E.FourierB D hU 0 = 0 := by
  have hh := B_spec E D hU 0
  rw [raw_zero D U, mul_zero] at hh
  have hb := (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (by norm_num))
  simpa [Lift.FourierB, timesTheta] using hb

omit [IsDomain O] [CharZero O] in
private theorem fourierUnary_zero {j : ℕ} (hj : j ≠ 0) : E.FourierUnary j 0 = 0 := by
  suffices E.unary j 0 = 0 by simpa [Lift.FourierUnary, timesTheta]
  unfold Lift.unary
  rw [dite_eq_right]
  rintro ⟨k, hk, _, h⟩
  exact (Nat.mul_ne_zero hj (pow_ne_zero _ hk)) h.symm

/-- Supplies the two common-space witnesses and the two formwise inputs in
one realization of the identical stage and root pool. -/
theorem realize (Dₗ : LevelSetup P avoid N) (D : Divisions E δ W R adm)
    (η : (ZMod N)ˣ →* Oˣ) (η_eval : ∀ u, (η u : O) = E.η (representative u))
    (η_order : ∀ u, ∃ e : ℕ, (η u : O) ^ (2 ^ e : ℕ) = 1)
    (hodd : let C := diamondCharacters Dₗ.common_four η η_eval η_order
            (C.η C.minusOne : O) * ((C.symbol (-1) C.minusOne : ℤ) : O) ^ E.parity.val = -1)
    (κ : K →+* ℂ) (X : Inventory I J K T N) (hspan : SpansAt X κ)
    (hmod : BlockModularity κ Dₗ D (diamondCharacters Dₗ.common_four η η_eval η_order))
    (H : ∀ s : J, SourceAttachment (X.sourceLevel s) frob (X.source s))
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) :
    ∃ (A : Basis I K (ZMod N)ˣ (Test T avoid)) (C : DiamondCharacters O (ZMod N)ˣ E.η)
      (V : Blocks (P := P) A E D C) (ρ₀ : Attachment A frob)
      (levels : BlockLevels V), AtLevel levels ρ₀ := by
  classical
  let A := X.toBasis Dₗ.test_coprime
  let C := diamondCharacters Dₗ.common_four η η_eval η_order
  let ρ₀ := X.attachment Dₗ.test_coprime H hfrob
  have hb (U : Finset ℕ) (hU : U ⊆ P.pool) := coordinates_of_span X Dₗ.test_coprime
    (hspan _ (Dₗ.b_dvd hU) _ _ (by rw [fourierB_zero D _, map_zero]) (hmod.b U hU))
  have hu (U : Finset ℕ) (hU : U ⊆ P.pool) (j : ℕ) (hj : j ∈ subscripts U) :=
    coordinates_of_span X Dₗ.test_coprime
      (hspan _ (Dₗ.unary_dvd hU hj) _ _ (by
        rw [fourierUnary_zero, map_zero]
        exact ((mem_subscripts (fun p hp => (P.type_good p (hU hp)).1) j).mp hj).1.ne_zero)
        (hmod.unary U hU j hj))
  let un (U : Finset ℕ) (hU : U ⊆ P.pool) (j : ℕ) :=
    if hj : j ∈ subscripts U then (hu U hU j hj).choose else 0
  have un_eq (U hU j hj) : un U hU j = (hu U hU j hj).choose := dite_eq_left hj
  let V : Blocks (P := P) A E D C :=
    { level_support := fun p hp => by
        change p ∣ N
        exact (congrArg (fun x => p ∣ x) Dₗ.common).mpr
          ((Finset.dvd_prod_of_mem id hp).trans (dvd_mul_left _ _))
      good_coprime := Dₗ.test_coprime
      atPrime_rep := fun q => representative_modEq (N := N) q.val (Dₗ.test_coprime q.val q.property)
      unary_odd := hodd
      b := fun U hU => (hb U hU).choose
      unary := un
      b_eval := fun U hU => (hb U hU).choose_spec.1
      unary_eval := fun U hU j hj n => by rw [un_eq U hU j hj]; exact (hu U hU j hj).choose_spec.1 n
      b_diamond := fun U hU u => by
        have he := diamond_of_coordinates X Dₗ.test_coprime
          (fun i hi => ((hb U hU).choose_spec.2 i hi).2) u
        rw [bCharacter_value] at he
        rw [Algebra.smul_def]
        exact he
      unary_diamond := fun U hU j hj u => by
        rw [un_eq U hU j hj]
        have he := diamond_of_coordinates X Dₗ.test_coprime
          (fun i hi => ((hu U hU j hj).choose_spec.2 i hi).2) u
        rw [unaryCharacter_value] at he
        rw [Algebra.smul_def]
        exact he }
  let levels : BlockLevels V :=
    { oldLevel := Dₗ.old
      old_good := Dₗ.old_good
      level := X.level
      degree_dvd := fun i => dvd_mul_left _ _
      b_level := fun U hU i hi => ((hb U hU).choose_spec.2 i hi).1
      unary_level := fun U hU j hj i hi => by
        change un U hU j i ≠ 0 at hi
        rw [un_eq U hU j hj] at hi
        exact ((hu U hU j hj).choose_spec.2 i hi).1 }
  refine ⟨A, C, V, ρ₀, levels, ?_⟩
  constructor
  · intro i a χ hz hr he q hq _ hcop Q hQ hqQ σ hσ
    exact (H (X.origin i)).unramified q ⟨hq, hcop.of_dvd_right (dvd_mul_right _ _)⟩ Q hQ hqQ σ hσ
  · intro i a χ hz hr he q hq _ hcop
    exact (X.cusp_data Dₗ.test_coprime H he q hq hcop).2
  · intro i a χ hz hr he q hq _ hcop
    exact (X.cusp_data Dₗ.test_coprime H he q hq hcop).1
  · intro i α β he
    obtain ⟨Eχ, hEχ⟩ := X.eis_data Dₗ.test_coprime H he
    exact ⟨{ Eχ with
      left_dvd := Eχ.left_dvd.trans (dvd_mul_right _ _)
      right_dvd := Eχ.right_dvd.trans (dvd_mul_right _ _) }, hEχ⟩

#print axioms LevelSetup.common_four
#print axioms LevelSetup.test_coprime
#print axioms LevelSetup.b_dvd
#print axioms LevelSetup.unary_dvd
#print axioms raw_zero
#print axioms fourierB_zero
#print axioms fourierUnary_zero
#print axioms realize

end ZInQ.Manuscript.RC.BlocksPerU
