import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Assembly
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Coordinates
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.AdelicNorm
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Conjugation

/-! The specialized Appendix F constructor on the explicit level order,
with its actual norm idèle and rational ternary frame. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler O12StageVal ThetaCoeff LocalWeights ZInQ.Manuscript.RC.Odd

variable {O : Type} [CommRing O] {ell N M m : ℕ} [Fact ell.Prime]
variable (h : ell % 4 = 3) (hN : 0 < N) (hcop : N.Coprime ell)
variable (C : LevelRoots O N) (hne : 2 * m * N * ell ≠ 0)

/-- The finite discriminant character of the adelic reduced norm. -/
def levelNormCharacter : FiniteUnits (levelRing h hN) →* Oˣ :=
  normCharacter h hN ((phaseFor C hne).places.filter fun q => q.val ∣ m)

/-- The norm character on a one-place step of reduced norm valuation one. -/
theorem levelNormCharacter_single {p : ℕ} (hp : GoodPrime C hne p)
    (hm : m % 4 = 3) (hms : Squarefree m)
    (u : letI : Fact p.Prime := ⟨hp.1⟩; (Bp p (-1) (-(ell : ℚ)))ˣ)
    (hu : (valHom ⟨p, hp.1⟩ (localNormHom ⟨p, hp.1⟩ u)).toAdd = (1 : ℤ)) :
    (levelNormCharacter h hN C hne (single (levelRing h hN) ⟨p, hp.1⟩ u) : O) =
      (jacobiSym (-(m : ℤ)) p : O) := by
  classical
  let P : Prime := ⟨p, hp.1⟩
  let z := normIdeles h hN (single (levelRing h hN) P u)
  have hP : valHom P (z.val P) = valHom P (rationalToLocal P (rationalPrime P)) := by
    apply Multiplicative.toAdd.injective
    change (valHom P (localNormHom P ((single (levelRing h hN) P u).val P))).toAdd = _
    rw [single_same, hu, val_rationalPrime, ite_eq_left rfl]
  have haway (q : Prime) (hq : q ≠ P) : z.val q = 1 := by
    change localNormHom q ((single (levelRing h hN) P u).val q) = 1
    rw [single_away hq, map_one]
  have hz : rationalPart z = rationalPrime P := by
    apply div_eq_one.mp
    apply positive_rational_unit
    · change 0 < (rationalPart z).val / (p : ℚ)
      exact div_pos (rationalPart_pos z) (by exact_mod_cast hp.1.pos)
    · intro q
      rw [map_div, map_div, rationalPart_valuation, div_eq_one]
      by_cases hq : q = P
      · subst q
        exact hP
      · rw [haway q hq, map_one]
        change (1 : Multiplicative ℤ) =
          Multiplicative.ofAdd ((rationalToLocal q (rationalPrime P)).val.valuation)
        have he := val_rationalPrime q P
        rw [ite_eq_right (Ne.symm hq)] at he
        exact congrArg Multiplicative.ofAdd he.symm
  let S := (phaseFor C hne).places.filter fun q => q.val ∣ m
  let emb : Prime ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hS : S.map emb = m.primeFactors := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, S, phaseFor, schwartzPhase,
      mem_exceptionalPlaces, emb, Function.Embedding.coeFn_mk,
      Nat.mem_primeFactors]
    constructor
    · rintro ⟨q, ⟨_, hq⟩, rfl⟩
      exact ⟨q.prop, hq, by omega⟩
    · rintro ⟨hn, hd, _⟩
      exact ⟨⟨n, hn⟩, ⟨dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 2) N) ell, hd⟩, rfl⟩
  have hodd : Odd p := hp.1.odd_of_ne_two (good_not_two C hne hp)
  rw [negativeDiscriminant_unit_character m p hm hms hodd, ← hS, Finset.prod_map,
    Int.cast_prod]
  change ((∏ q ∈ S, legendreUnit q.val (localUnitPart q z) : Oˣ) : O) = _
  rw [Units.coe_prod]
  apply Finset.prod_congr rfl
  intro q hq
  have hd := (Finset.mem_filter.mp hq).2
  have hqP : q ≠ P := fun he => good_not_dvd_m C hne hp (by rwa [he] at hd)
  have hqp : ¬ q.val ∣ p := fun hdiv =>
    hqP (Subtype.ext ((Nat.dvd_prime hp.1).mp hdiv |>.resolve_left q.prop.ne_one))
  let v := PhaseData.natUnit q p hqp
  let f := Units.map (algebraMap ℤ_[q.val] ℚ_[q.val]).toMonoidHom
  have hv₀ : f v = rationalToLocal q (rationalPrime P) := by
    apply Units.ext
    change (↑(v.val) : ℚ_[q.val]) = _
    rw [PhaseData.natUnit_val]
    change (algebraMap ℤ_[q.val] ℚ_[q.val]) (p : ℤ_[q.val]) = _
    rw [map_natCast]
    simp [rationalToLocal, rationalPrime, P]
  have hv : localUnitPart q z = v⁻¹ := by
    apply Units.ext
    apply Subtype.val_injective
    rw [localUnitPart_val, hz, haway q hqP, one_div, ← hv₀, ← map_inv]
    rfl
  rw [hv, map_inv, legendreUnit_inv, legendreUnit_apply, PhaseData.natUnit_val,
    map_natCast]
  simpa only [legendreSym, Int.cast_natCast, emb,
    Function.Embedding.coeFn_mk] using
    congrArg (fun n : ℤ => (n : O)) (jacobiSym.legendreSym.to_jacobiSym q.val (p : ℤ))

/-- Disjointness of the ramified character primes from the other special cases. -/
def DisjointDiscriminant (m N ell : ℕ) : Prop :=
  ∀ q : Prime, q.val ∣ m → q.val ≠ ell ∧ ¬ q.val ∣ N ∧ q.val ≠ 2

theorem splitUnit_norm (q : Prime) (hq : q.val ≠ ell)
    (u : localUnits (levelRing h hN) q) :
    Matrix.GeneralLinearGroup.det (eichlerUnit (splitUnit h hN q hq u)) =
      normUnit h hN q u := by
  let U := splitUnit h hN q hq u
  apply Units.ext
  apply Subtype.val_injective
  rw [normUnit_val]
  change (↑(U.val.val.det) : ℚ_[q.val]) =
    (u.val.val * star u.val.val).re
  calc (↑(U.val.val.det) : ℚ_[q.val]) = (integralMat q.val U.val.val).det :=
        RingHom.map_det (algebraMap ℤ_[q.val] ℚ_[q.val]) U.val.val
    _ = (splitChart ell h q hq u.val.val).det :=
      congrArg Matrix.det (splitOrderEquiv_apply ell h N hN q hq ⟨u.val.val, u.prop.1⟩)
    _ = _ := (split_invariants _ _ (splitChart ell h q hq) u.val.val).2

/-- The actual right conjugation and rational diagonal laws of the same norm character. -/
def levelNormCovariance (hm : DisjointDiscriminant m N ell) :
    NormCovariance (phaseFor C hne) (localFactor h C m) (levelNormCharacter h hN C hne) where
  eps q u := if q.val ∣ m then legendreUnit q.val (normUnit h hN q u) else 1
  local_conj q _ u x := by
    by_cases he : q.val = ell
    · have he' : q = ⟨ell, Fact.out⟩ := Subtype.ext he
      subst q
      have hn : ¬ ell ∣ m := fun hh => (hm ⟨ell, Fact.out⟩ hh).1 rfl
      simpa only [localFactor, Subtype.coe_mk, eq_self, dite_true, ite_eq_right hn,
        inv_one, Units.val_one, one_mul] using divisionFactor_conj (O := O) h hN u x
    · simp only [localFactor, dite_eq_right he]
      have heq : splitConjSign (O := O) h hN m q he u =
          if q.val ∣ m then legendreUnit q.val (normUnit h hN q u) else 1 := by
        unfold splitConjSign
        by_cases hqm : q.val ∣ m
        · obtain ⟨_, hN', h₂⟩ := hm q hqm
          simp only [hN', h₂, or_self, ite_false, hqm, ite_true, splitUnit_norm]
        · simp only [ite_eq_right hqm, ite_self]
      rw [← heq]
      exact splitFactor_conj h hN C m q he u x
  diagonal := normCharacter_diagonal h hN _
  units r := by
    unfold levelNormCharacter
    rw [normCharacter_integral, Finset.prod_filter]

/-- Good-prime coordinates from the split chart used by the line indexing. -/
def levelFrameCoordinates : ActualFrameCoordinates h hN C hne := fun p hp z =>
  letI : Fact p.Prime := ⟨hp.1⟩
  let q : Prime := ⟨p, hp.1⟩
  let U := (LineIndex.chartAt (levelOrder_isEichler ell h N hN hcop)
    (good_away C hne hp) z).split
  GoodCoordinates.coordinates q (classRepresentative z) U
    (lattice_norm_integral h hN (classRepresentative z))

/-- The local join for the given level and discriminant, conditional on the
individually labelled local neighbour transport. -/
def levelPmLocal
    (hm : DisjointDiscriminant m N ell)
    (T : IndexedNeighbourTransport h hN hcop C hne (levelNormCharacter h hN C hne)
      (levelFrameCoordinates h hN hcop C hne)) : PMLocal O (levelRing h hN) M N ell :=
  let cov := levelNormCovariance h hN C hne hm
  pmLocal h hN hcop C hne _ cov _ (weightedNeighbour_of_transport h hN hcop C hne _ cov _ T)

variable {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K] [IsSepClosed K]
variable {Ebar : WeierstrassCurve (ZMod ell)} [Ebar.IsElliptic] {ap : ℕ → ℤ}
variable (G : PM.Geometry K (levelRing h hN) N Ebar ap) (d : PM.Evaluation K Ebar M) (L : ℕ)
variable (hm : DisjointDiscriminant m N ell)
variable (T : IndexedNeighbourTransport h hN hcop C hne (levelNormCharacter h hN C hne)
  (levelFrameCoordinates h hN hcop C hne))

/-- Apply the existing stage to the specialized local join. -/
def levelStage : AppF.ThetaStage (StageRing O M) :=
  pmStage G d L (levelPmLocal h hN hcop C hne hm T)

/-- Apply the existing valuation lift at the same stage. -/
def levelValLift : Lift (levelStage h hN hcop C hne G d L hm T) :=
  pmValLift G d L (levelPmLocal h hN hcop C hne hm T)

end ZInQ.Manuscript.RC.ThetaJoin
