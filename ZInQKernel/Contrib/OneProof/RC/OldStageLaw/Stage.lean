import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Series
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Transform
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.Sieve

/-! Read the finite coset vector from the given stage lift and identify its
expansion with `Lift.aθ`. No independent choice of local weights is made. -/

noncomputable section

namespace ZInQ.Manuscript.RC.OldStageLaw

open BlocksPerU ThetaCoeff UpperHalfPlane
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped BigOperators Quaternion MatrixGroups

set_option maxHeartbeats 800000

variable {O : Type} [CommRing O] {M : ℕ} {S : AppF.ThetaStage (Odd.StageRing O M)}

def coord {a : Fin 3 → ℕ} (p : GridPoint a) (i : Fin 3) : ℚ :=
  (intCoords p.2 i : ℚ) + ((p.1 i).val : ℚ) / (2 * a i)

def quatPoint {a : Fin 3 → ℕ} (h : ℚ) (p : GridPoint a) : ℍ[ℚ,S.qa,0,S.qb] :=
  ⟨0, h * coord p 0, h * coord p 1, h * coord p 2⟩

private theorem quatPoint_injective {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)] {h : ℚ}
    (hh : h ≠ 0) : Function.Injective (quatPoint (S := S) (a := a) h) := by
  intro p q hpq
  have hv (i : Fin 3) : coord p i = coord q i := by
    apply mul_left_cancel₀ hh
    fin_cases i
    · exact congrArg QuaternionAlgebra.imI hpq
    · exact congrArg QuaternionAlgebra.imJ hpq
    · exact congrArg QuaternionAlgebra.imK hpq
  have hc (i : Fin 3) : (p.1 i, intCoords p.2 i) = (q.1 i, intCoords q.2 i) := by
    apply (intResidues (2 * a i)).symm.injective
    have hi := congrArg (fun x : ℚ => ((2 * a i : ℕ) : ℚ) * x) (hv i)
    have hn : ((2 * a i : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
    have ht (u : GridPoint a) : ((2 * a i : ℕ) : ℚ) * coord u i =
        (((u.1 i).val : ℤ) + (2 * a i : ℕ) * intCoords u.2 i : ℤ) := by
      unfold coord
      push_cast at hn ⊢
      have h' : (a i : ℚ) ≠ 0 := by
        intro h0
        exact hn (by rw [h0, mul_zero])
      field_simp [h']
      ring
    rw [ht p, ht q] at hi
    exact_mod_cast hi
  apply Prod.ext
  · exact funext fun i => congrArg Prod.fst (hc i)
  · have h0 : p.2.1 = q.2.1 := congrArg Prod.snd (hc 0)
    have h1 : p.2.2.1 = q.2.2.1 := congrArg Prod.snd (hc 1)
    have h2 : p.2.2.2 = q.2.2.2 := by
      simpa [intCoords] using congrArg (fun r : ZMod (2 * a 2) × ℤ => r.2) (hc 2)
    exact Prod.ext h0 (Prod.ext h1 h2)

/-- A rectangular coset presentation for the given, already fixed-sieved
weights `E.geom.f`. The coefficient vector is read from the weights below.
`scaled` uses the positive diagonal entries of the extracted form `Q_B/m`. -/
structure StageGrid (E : Lift S) (a : Fin 3 → ℕ) (h : ℚ) : Prop where
  step_ne : h ≠ 0
  positive : ∀ i, 0 < a i
  m_ne : S.m ≠ 0
  scaled : (a 0 : ℚ) = -S.qa * h ^ 2 / S.m ∧
    (a 1 : ℚ) = -S.qb * h ^ 2 / S.m ∧ (a 2 : ℚ) = S.qa * S.qb * h ^ 2 / S.m
  constant : ∀ j (p : GridPoint a),
    E.geom.f j (quatPoint h p) = E.geom.f j (quatPoint h (p.1, 0, 0, 0))
  supported : ∀ j x, x.re = 0 → E.geom.f j x ≠ 0 → x ∈ Set.range (quatPoint (S := S) (a := a) h)
  extracts : ∀ j x, x.re = 0 → E.geom.f j x ≠ 0 → ∃ n : ℕ, Visibility.nrd x = (S.m * n : ℕ)

def mass (E : Lift S) (j : E.geom.X) : O :=
  ((Odd.c0 / Nat.card (E.geom.G j) : ℕ) : O) * (E.geom.P j : O) * E.geom.χN j

def stageWeight (E : Lift S) (ι : O →+* ℂ) (x : ℍ[ℚ,S.qa,0,S.qb]) : ℂ :=
  ∑ j, ι (mass E j * E.geom.f j x)

def stageGridWeight (E : Lift S) (ι : O →+* ℂ) (a : Fin 3 → ℕ) (h : ℚ) (r : Grid a) : ℂ :=
  stageWeight E ι (quatPoint h (r, 0, 0, 0))

private theorem exponent_eq {E : Lift S} {a : Fin 3 → ℕ} {h : ℚ}
    (G : StageGrid E a h) (p : GridPoint a) :
    exponent p = ((Visibility.nrd (quatPoint (S := S) h p) / S.m : ℚ) : ℝ) := by
  have he (i : Fin 3) : (coord p i : ℝ) = (intCoords p.2 i : ℝ) + offset p.1 i := by
    unfold coord offset
    push_cast
    rfl
  let t (i : Fin 3) : ℚ := (a i : ℚ) * coord p i ^ 2
  have ht (i : Fin 3) : (t i : ℝ) = (a i : ℝ) * ((intCoords p.2 i : ℝ) + offset p.1 i) ^ 2 := by
    simp only [t, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, he]
  have hq : (∑ i, t i) = Visibility.nrd (quatPoint (S := S) h p) / S.m := by
    unfold t
    rw [Fin.sum_univ_three, G.scaled.1, G.scaled.2.1, G.scaled.2.2, Visibility.nrd_apply]
    simp only [quatPoint, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    ring
  rw [← hq, Rat.cast_sum]
  simp only [exponent, ht]

private theorem stageWeight_nonzero {E : Lift S} {ι : O →+* ℂ} {x : ℍ[ℚ,S.qa,0,S.qb]}
    (hx : stageWeight E ι x ≠ 0) : ∃ j, E.geom.f j x ≠ 0 := by
  classical
  by_contra! h
  exact hx (by simp [stageWeight, h])

/-- The actual extracted support has integral phase for every translation. -/
theorem stageGrid_twist_eq {E : Lift S} {a : Fin 3 → ℕ} {h : ℚ}
    (G : StageGrid E a h) (ι : O →+* ℂ) (k : ℤ) :
    twist k (stageGridWeight E ι a h) = stageGridWeight E ι a h := by
  apply twist_eq_of_integral
  intro r hr
  let p : GridPoint a := (r, 0, 0, 0)
  obtain ⟨j, hj⟩ := stageWeight_nonzero (E := E) (ι := ι) (x := quatPoint h p) hr
  obtain ⟨n, hn⟩ := G.extracts j (quatPoint h p) rfl hj
  have hm : (S.m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr G.m_ne
  have hq : Visibility.nrd (quatPoint (S := S) h p) / S.m = (n : ℚ) := by
    apply (div_eq_iff hm).mpr
    rw [hn, Nat.cast_mul, mul_comm]
  have he : exponent p = energy r := by simp [exponent, energy, p, intCoords, Fin.sum_univ_three]
  refine ⟨(n : ℤ), ?_⟩
  rw [← he, exponent_eq G, hq, Rat.cast_natCast, Int.cast_natCast]

private theorem stage_weighted_sphere (E : Lift S) (ι : O →+* ℂ) (n : ℕ) :
    (∑' x : ℍ[ℚ,S.qa,0,S.qb],
      if x.re = 0 ∧ Visibility.nrd x = ((S.m * n : ℕ) : ℚ) then stageWeight E ι x else 0)
      = ι (E.aθ n) := by
  classical
  let t (j : E.geom.X) := (E.geom.finite_supp j (S.m * n : ℕ)).toFinset
  let U := Finset.univ.biUnion t
  have hmem (j : E.geom.X) (x : ℍ[ℚ,S.qa,0,S.qb]) :
      x ∈ t j ↔ x.re = 0 ∧ Visibility.nrd x = ((S.m * n : ℕ) : ℚ) ∧ E.geom.f j x ≠ 0 := by
    simp [t]
  have hU (j : E.geom.X) (x) (hx : x ∈ t j) : x ∈ U := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩
  have hvanish {x} (hx : x ∉ U) (hs : x.re = 0 ∧ Visibility.nrd x = ((S.m * n : ℕ) : ℚ)) :
      ∀ j, E.geom.f j x = 0 := by
    intro j
    by_contra h
    exact hx (hU j x ((hmem j x).mpr ⟨hs.1, hs.2, h⟩))
  rw [tsum_eq_sum (s := U) (fun x hx => ?_), Lift.aθ, Lift.H, Visibility.thetaCoeff, map_sum]
  · have he (x : ℍ[ℚ,S.qa,0,S.qb]) :
        (if x.re = 0 ∧ Visibility.nrd x = ((S.m * n : ℕ) : ℚ) then stageWeight E ι x else 0) =
          ∑ j, if x ∈ t j then ι (mass E j * E.geom.f j x) else 0 := by
      by_cases hs : x.re = 0 ∧ Visibility.nrd x = ((S.m * n : ℕ) : ℚ)
      · rw [ite_eq_left hs, stageWeight]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : E.geom.f j x = 0
        · simp [hmem, hj]
        · simp [hmem, hs.1, hs.2, hj]
      · rw [ite_eq_right hs]
        symm
        refine Finset.sum_eq_zero fun j _ => ?_
        exact ite_eq_right fun hj => hs ⟨((hmem j x).mp hj).1, ((hmem j x).mp hj).2.1⟩
    simp only [he]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, show U.filter (· ∈ t j) = t j by
      ext x; simp only [Finset.mem_filter, and_iff_right_iff_imp]; exact hU j x]
    have hs : (∑ᶠ x ∈ {x : ℍ[ℚ,S.qa,0,S.qb] | x.re = 0 ∧ Visibility.nrd x = ((S.m * n : ℕ) : ℚ)},
          E.geom.f j x) = ∑ x ∈ t j, E.geom.f j x := by
      apply finsum_cond_eq_sum_of_cond_iff
      intro x hx
      simp [hmem, hx]
    rw [hs, ← map_sum, ← Finset.mul_sum]
    rfl
  · split_ifs with hs
    · simp [stageWeight, hvanish hx hs]
    · rfl

/-- The coset vector of the supplied weighted stage has exactly the series
of `Lift.aθ`; rescaling the norm changes no coefficient. -/
theorem stageGrid_hasSum {E : Lift S} {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)] {h : ℚ}
    (G : StageGrid E a h) (ι : O →+* ℂ) (z : UpperHalfPlane) :
    HasSum (fun n => ι (E.aθ n) * Function.Periodic.qParam 1 (z : ℂ) ^ n)
      (gridTheta (stageGridWeight E ι a h) z) := by
  classical
  let Q (x : ℍ[ℚ,S.qa,0,S.qb]) : ℚ := Visibility.nrd x / S.m
  let term (x : ℍ[ℚ,S.qa,0,S.qb]) : ℂ :=
    if x.re = 0 then stageWeight E ι x * kernel z (Q x : ℝ) else 0
  have hterm (p : GridPoint a) : term (quatPoint h p) = stageGridWeight E ι a h p.1 * kernel z (exponent p) := by
    have hw : stageWeight E ι (quatPoint h p) = stageGridWeight E ι a h p.1 := by
      unfold stageGridWeight stageWeight
      exact Finset.sum_congr rfl fun j _ => by rw [G.constant j p]
    simp [term, exponent_eq G, Q, show (quatPoint (S := S) h p).re = 0 from rfl, hw]
  have hout (x) (hx : x ∉ Set.range (quatPoint (S := S) (a := a) h)) : term x = 0 := by
    by_cases hh : x.re = 0
    · have hz : stageWeight E ι x = 0 := by
        by_contra ht
        obtain ⟨j, hj⟩ := stageWeight_nonzero ht
        exact hx (G.supported j x hh hj)
      simp [term, hh, hz]
    · simp [term, hh]
  have total : HasSum term (gridTheta (stageGridWeight E ι a h) z) :=
    ((quatPoint_injective (S := S) (a := a) G.step_ne).hasSum_iff hout).mp <| by
      simpa only [Function.comp_def, hterm] using gridTheta_hasSum G.positive (stageGridWeight E ι a h) z
  let index (x : ℍ[ℚ,S.qa,0,S.qb]) := Nat.floor (Q x)
  have hb := total.tsum_fiberwise index
  have hm : (S.m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr G.m_ne
  convert hb using 1
  funext n
  rw [tsum_subtype, ← stage_weighted_sphere E ι n, ← tsum_mul_right]
  refine tsum_congr fun x => ?_
  by_cases hre : x.re = 0 <;> by_cases hw : stageWeight E ι x = 0
  · simp [term, hre, hw, Set.indicator_apply]
  · obtain ⟨j, hj⟩ := stageWeight_nonzero hw
    obtain ⟨k, hk⟩ := G.extracts j x hre hj
    have hQ : Q x = k := by
      unfold Q
      apply (div_eq_iff hm).mpr
      rw [hk, Nat.cast_mul, mul_comm]
    have he : index x = k := by simp [index, hQ]
    have hn : Visibility.nrd x = ((S.m * n : ℕ) : ℚ) ↔ k = n := by
      rw [hk, Nat.cast_inj, mul_right_inj' G.m_ne]
    have hQ' : (Q x : ℝ) = (k : ℝ) := by rw [hQ, Rat.cast_natCast]
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff, term, hre, ite_true,
      true_and, he, hn, hQ', kernel_nat]
    split_ifs with hkn
    · rw [hkn]
    · simp
  · simp [term, hre, Set.indicator_apply]
  · simp [term, hre, Set.indicator_apply]

variable {K L : Type} [Field K] [Algebra O K] [AddCommGroup L]
  {ε : L →+ ZMod 2} {T : TypeData L ε} {avoid : Finset ℕ} {W N : ℕ}
  {P : Window T.Good S W} {E : Lift S}

/-- Supplies the precise first input of `realize_of_stage`. `hchar` identifies
(O.5) with the empty moving-sieve character on the fixed pool. -/
theorem oldStageLaw_of_finiteAction (κ : K →+* ℂ) (Dₗ : LevelSetup P avoid N)
    (C : DiamondCharacters O (ZMod N)ˣ E.η) {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]
    {h : ℚ} (G : StageGrid E a h) (ξ : (ZMod Dₗ.old)ˣ →* ℂˣ)
    (hchar : ξ.comp (ZMod.unitsMap Dₗ.old_dvd) = (Units.map κ).comp (bCharacter (K := K) C ∅))
    (hfin : RelativeFiniteAction ξ (stageGridWeight E (κ.comp (algebraMap O K)) a h)) :
    OldStageLaw κ Dₗ C := by
  exact ⟨ξ, hchar, _, halfIntegral_of_finiteAction G.positive hfin,
    stageGrid_hasSum G (κ.comp (algebraMap O K))⟩

#print axioms quatPoint_injective
#print axioms exponent_eq
#print axioms stageWeight_nonzero
#print axioms stageGrid_twist_eq
#print axioms stage_weighted_sphere
#print axioms stageGrid_hasSum
#print axioms oldStageLaw_of_finiteAction

end ZInQ.Manuscript.RC.OldStageLaw
