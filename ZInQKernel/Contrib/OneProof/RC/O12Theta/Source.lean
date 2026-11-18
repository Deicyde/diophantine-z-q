import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Forms

/-! The sign in (O.6) at the actual odd stage and the precision retained by
integer division (tex 8424–8426, 9634–9636, 9694–9704, 9908, 9916–9918). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Theta

open ZInQ.Manuscript.RC.Odd ThetaCoeff

variable {O K : Type} [CommRing O] [IsDomain O] [CharZero O]
  [Field K] [CharZero K] [Algebra O K]
variable {M W R : ℕ} {S : AppF.ThetaStage (StageRing O M)} {δ : ℤ} {adm : ℕ → Prop}
variable (E : Lift S)

/-- The actual sign of `ψ/η` used in the recurrence and in `C_p` is `(-1/p)`. -/
def ratio (p : ℕ) (hp : Nat.Prime p) : ℤ :=
  @legendreSym p ⟨hp⟩ (-1)

/-- The ratio at good primes is a sign. -/
theorem ratio_sign {p : ℕ} (hp : Nat.Prime p) :
    ratio p hp = 1 ∨ ratio p hp = -1 := by
  letI : Fact p.Prime := ⟨hp⟩
  exact legendreSym.eq_one_or_neg_one p (by simp : ((-1 : ℤ) : ZMod p) ≠ 0)

/-- The recurrence with the actual sign holds after reducing the very lifts
used in the expansions. The equality is in the stage ring. -/
theorem signed_recur_stage {p : ℕ} (hp : S.Good p) :
    @RecAt (StageRing O M) _ p ⟨S.good_prime p hp⟩
      (stageReduction O M (E.η p)) (ratio p (S.good_prime p hp)) (S.ap p)
      (fun n => stageReduction O M (E.aθ n)) := by
  simp only [E.phase, E.aθ_reduce]
  exact S.recAt hp

/-- Lift the truncated depth bound from the existing odd source. No exact
recurrence on the lifts is needed for this bound. -/
theorem lift_depth (D : Divisions E δ W R adm) {d : ℕ}
    (hd : Squarefree d) (ha : adm d) :
    (2 : O) ^ (min (budgetLevel δ W R : ℤ)
      (δ + ArithmeticFunction.cardDistinctFactors d)).toNat ∣ E.aθ d := by
  let k := (min (budgetLevel δ W R : ℤ) (δ + ArithmeticFunction.cardDistinctFactors d)).toNat
  have hk : k ≤ M := le_trans (by
    dsimp [k]
    have : min (budgetLevel δ W R : ℤ) (δ + ArithmeticFunction.cardDistinctFactors d) ≤
        (budgetLevel δ W R : ℤ) := min_le_left _ _
    omega) D.stage.1
  obtain ⟨y, hy⟩ := D.stage.2.depth d hd ha
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have he : stageReduction O M (E.aθ d - (2 : O) ^ k * c) = 0 := by
    rw [map_sub, map_mul, map_pow, map_ofNat, E.aθ_reduce, hy, sub_self]
  have hm := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)
  have := dvd_add (two_pow_dvd_of_le hk hm) (dvd_mul_right ((2 : O) ^ k) c)
  rwa [sub_add_cancel] at this

/-- Construct the exact-lift source from its core. In the odd application the
core's signed recurrence is stronger than the finite-stage recurrence. -/
theorem lift_source (D : Divisions E δ W R adm) {Good : ℕ → Prop}
    (core : SourceCore E.η Good adm S.ap E.aθ) :
    SourceHyp (budgetLevel δ W R) δ E.η Good adm S.ap E.aθ :=
  ⟨core, fun _ hd ha => lift_depth E D hd ha⟩

/-- If two undivided coefficients agree at stage precision, scaling them
by `2^{-e}` with `e < M` gives the same residue modulo integer two.
Both normalized coefficients are required to be integral. -/
theorem normalized_congr (hinj : Function.Injective (algebraMap O K))
    {e : ℤ} (he : e < (M : ℤ)) {x y b c : O}
    (h : stageReduction O M x = stageReduction O M y)
    (hb : algebraMap O K b = (2 : K) ^ (-e) * algebraMap O K x)
    (hc : algebraMap O K c = (2 : K) ^ (-e) * algebraMap O K y) :
    (2 : O) ∣ b - c := by
  have hz : (2 : O) ^ M ∣ x - y := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, h, sub_self]
  obtain ⟨t, ht⟩ := hz
  let k : ℕ := ((M : ℤ) - e).toNat
  have hk : (k : ℤ) = (M : ℤ) - e := Int.toNat_of_nonneg (by omega)
  have hz' : b - c = (2 : O) ^ k * t := by
    apply hinj
    have htwo : (2 : K) ≠ 0 := by norm_num
    rw [map_sub, hb, hc, ← mul_sub, ← map_sub, ht, map_mul, map_pow, map_ofNat,
      map_mul, map_pow, map_ofNat, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ htwo,
      ← zpow_natCast, hk]
    congr 2
    omega
  rw [hz']
  exact dvd_mul_of_dvd_left (by simpa using (pow_dvd_pow (2 : O) (show 1 ≤ k by omega))) _

#print axioms ratio
#print axioms ratio_sign
#print axioms signed_recur_stage
#print axioms lift_depth
#print axioms lift_source
#print axioms normalized_congr

end ZInQ.Manuscript.RC.O12Theta
