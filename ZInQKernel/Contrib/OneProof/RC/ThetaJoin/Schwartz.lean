import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.LocalOrder
import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Global
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.SplitActions
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Coefficients

/-! The actual placewise factors of the finite Schwartz function in (O.4). -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler LocalWeights
open scoped Quaternion

variable {O : Type} [CommRing O]

/-- A finite residue character at each level prime. At an odd prime it factors
through reduction mod the prime, and at two it factors through reduction mod four. -/
def rootModulus (q : Prime) : ℕ :=
  q.val ^ (if q.val = 2 then 2 else 1 : ℕ)

structure LevelRoots (O : Type) [CommRing O] (N : ℕ) where
  alpha : (q : Prime) → q.val ∣ N → (ZMod (rootModulus q))ˣ →* Oˣ
  exponent : ℕ
  order : ∀ q hq v, alpha q hq v ^ (2 ^ exponent : ℕ) = 1

/-- (O.3) for the chosen Atkin--Lehner signs and the fixed discriminant. -/
def LevelRoots.ParityAt {N : ℕ} (C : LevelRoots O N) (m : ℕ) (sign : ℕ → Oˣ) : Prop :=
  ∀ q hq, (C.alpha q hq (-1) : O) =
    (sign q.val : O) * (jacobiSym (-(m : ℤ)) q.val : O) ^ N.factorization q.val

/-- The set of all exceptional primes in the unsieved Appendix F Schwartz function. -/
def exceptionalPlaces (m N ell : ℕ) (h : 2 * m * N * ell ≠ 0) : Finset Prime :=
  (finite_prime_dvd h).toFinset

theorem mem_exceptionalPlaces (m N ell : ℕ) (h : 2 * m * N * ell ≠ 0) (q : Prime) :
    q ∈ exceptionalPlaces m N ell h ↔ q.val ∣ 2 * m * N * ell := by
  simp [exceptionalPlaces]

variable {ell N : ℕ} [Fact ell.Prime] (h : ell % 4 = 3)
variable (C : LevelRoots O N) (m : ℕ)

private theorem levelExponent_pos (hN : 0 < N) (q : Prime) (hq : q.val ∣ N) :
    0 < N.factorization q.val :=
  q.prop.factorization_pos_of_dvd hN.ne' hq

/-- The local scalar multiplier for the same case split as the Schwartz factor. -/
def localAlpha (q : Prime) : ℤ_[q.val]ˣ →* Oˣ :=
  if q.val = ell then legendreUnit q.val
  else if hq : q.val ∣ N then
    (C.alpha q hq).comp (Units.map (PadicInt.toZModPow _).toMonoidHom)
  else if q.val = 2 then 1
  else if q.val ∣ m then legendreUnit q.val
  else 1

private theorem legendre_two_power (q : Prime) (u : ℤ_[q.val]ˣ) (k : ℕ) :
    legendreUnit (O := O) q.val u ^ (2 ^ (k + 1) : ℕ) = 1 := by
  have hs : legendreUnit (O := O) q.val u * legendreUnit q.val u = 1 := by
    conv_lhs => congr; skip; rw [← legendreUnit_inv]
    exact mul_inv_cancel _
  rw [pow_succ (2 : ℕ), mul_comm, pow_mul, pow_two, hs, one_pow]

/-- The scalar phase of the actual factors. A common power of two kills their
values, including the quadratic factors at the discriminant primes. -/
def schwartzPhase (hne : 2 * m * N * ell ≠ 0) : PhaseData O where
  places := exceptionalPlaces m N ell hne
  alpha := localAlpha (ell := ell) C m
  exponent := C.exponent + 1
  alpha_order q _ u := by
    unfold localAlpha
    split
    · exact legendre_two_power q u _
    · split
      · change C.alpha q _ _ ^ (2 ^ (C.exponent + 1) : ℕ) = 1
        rw [pow_succ (2 : ℕ), pow_mul, C.order, one_pow]
      · split
        · simp
        · split
          · exact legendre_two_power q u _
          · simp

omit [Fact ell.Prime] in
private theorem re_unit_smul_iff (q : Prime) (v : ℤ_[q.val]ˣ)
    (x : Bp q.val (-1) (-(ell : ℚ))) :
    ((v : ℤ_[q.val]) • x).re = 0 ↔ x.re = 0 := by
  change (((v.val : ℚ_[q.val]) • x).re = 0) ↔ _
  rw [QuaternionAlgebra.re_smul, smul_eq_mul, mul_eq_zero]
  exact or_iff_right (fun h => v.ne_zero (PadicInt.coe_eq_zero.mp h))

/-- The transported weight at the division prime. Its trace predicate is the
kernel of the reduced trace, so the definition extends by zero to the ambient
quaternion algebra. -/
def divisionFactor (x : Bp ell (-1) (-(ell : ℚ))) : O :=
  letI : Fact (ell % 4 = 3) := ⟨h⟩
  open Classical in
  if hx : x.re = 0 then
    (LocalDivision.coordinates ell).divisionSchwartz
      ⟨DivisionJoin.ambientEquiv ell x, by
        change LocalDivision.tr (DivisionJoin.ambientEquiv ell x) = 0
        rw [DivisionJoin.ambient_trace, DivisionJoin.reducedTrace, hx, mul_zero]⟩
  else 0

theorem divisionFactor_zero : (divisionFactor h 0 : O) = 0 := by
  let : Fact (ell % 4 = 3) := ⟨h⟩
  classical
  let Z := LocalDivision.coordinates ell
  let x : Z.IntegralZero := ⟨0, by simp⟩
  have hz : Z.zeroInclusion x =
      ⟨DivisionJoin.ambientEquiv ell 0, by simp⟩ := by
    apply Subtype.ext
    change 0 = DivisionJoin.ambientEquiv ell 0
    exact (map_zero _).symm
  unfold divisionFactor
  rw [dite_eq_left (show (0 : Bp ell (-1) (-(ell : ℚ))).re = 0 by rfl), ← hz]
  rw [LocalWeights.DivisionCoordinates.divisionSchwartz,
    (extendWeight_spec _ _ Z.zeroInclusion_openEmbedding.injective).1]
  change Z.residueWeight (Z.red 0) = 0
  rw [map_zero, show (0 : GaloisField ell 2) =
    algebraMap (ZMod ell) (GaloisField ell 2) 0 * Z.beta by simp, Z.residueWeight_eq]
  simp

/-- The split local Schwartz factor, with the level action transported through the
same chart used to construct the completed order. -/
def splitFactor (q : Prime) (hq : q.val ≠ ell) (x : Bp q.val (-1) (-(ell : ℚ))) : O :=
  open Classical in
  if hx : x.re = 0 then
    let X : TraceZero ℚ_[q.val] :=
      ⟨splitChart ell h q hq x, by
        rw [(split_invariants _ _ (splitChart ell h q hq) x).1, hx, mul_zero]⟩
    if hN : q.val ∣ N then levelSchwartz q.val (e := N.factorization q.val) (C.alpha q hN) X
    else if h₂ : q.val = 2 then
      (by
        have he : q = ⟨2, Nat.prime_two⟩ := Subtype.ext h₂
        subst q
        exact dyadicSchwartz X)
    else if q.val ∣ m then nilSchwartz q.val X else goodWeight q.val X
  else 0

/-- The scalar transport in a split chart, including the dyadic affine weight. -/
theorem splitFactor_scale (hN : 0 < N) (q : Prime) (hq : q.val ≠ ell)
    (v : ℤ_[q.val]ˣ) (x : Bp q.val (-1) (-(ell : ℚ))) :
    splitFactor h C m q hq ((v : ℤ_[q.val]) • x) =
      (localAlpha (ell := ell) C m q v : O) * splitFactor h C m q hq x := by
  classical
  have hr := re_unit_smul_iff q v x
  by_cases hx : x.re = 0
  · let E := splitChart ell h q hq
    let y : TraceZero ℚ_[q.val] := ⟨E x, by
      rw [(split_invariants _ _ E x).1, hx, mul_zero]⟩
    let V := Units.map (PadicInt.Coe.ringHom (p := q.val)).toMonoidHom v
    have hs : E ((v : ℤ_[q.val]) • x) = (V.val : ℚ_[q.val]) • E x :=
      map_smul E (v.val : ℚ_[q.val]) x
    simp only [splitFactor, dite_eq_left hx, dite_eq_left (hr.mpr hx), localAlpha, ite_eq_right hq]
    by_cases hqN : q.val ∣ N
    · simp only [dite_eq_left hqN]
      change levelSchwartz q.val (C.alpha q hqN)
        (⟨E ((v : ℤ_[q.val]) • x), by rw [hs, Matrix.trace_smul, y.prop, smul_zero]⟩ : TraceZero ℚ_[q.val]) =
        _ * levelSchwartz q.val (C.alpha q hqN) y
      rw [show (⟨E ((v : ℤ_[q.val]) • x), by rw [hs, Matrix.trace_smul, y.prop, smul_zero]⟩ : TraceZero ℚ_[q.val]) =
        matrixScale V y from Subtype.ext hs]
      exact (levelRule (levelExponent_pos hN q hqN) (C.alpha q hqN)).weight_scale v y
    · simp only [dite_eq_right hqN]
      by_cases hq₂ : q.val = 2
      · have he : q = ⟨2, Nat.prime_two⟩ := Subtype.ext hq₂
        subst q
        simp only [ite_true]
        have hy : (⟨E ((v : ℤ_[2]) • x), by rw [hs, Matrix.trace_smul, y.prop, smul_zero]⟩ : TraceZero ℚ_[2]) =
            matrixScale V y := Subtype.ext hs
        rw [hy]
        exact (dyadicRule (O := O)).weight_scale v y
      · simp only [dite_eq_right hq₂, ite_eq_right hq₂]
        by_cases hqm : q.val ∣ m
        · simp only [ite_eq_left hqm]
          have hy : (⟨E ((v : ℤ_[q.val]) • x), by rw [hs, Matrix.trace_smul, y.prop, smul_zero]⟩ : TraceZero ℚ_[q.val]) =
              matrixScale V y := Subtype.ext hs
          change nilSchwartz q.val _ = _ * nilSchwartz q.val y
          rw [hy]
          exact (nilRule (O := O) (p := q.val)).weight_scale v y
        · simp only [ite_eq_right hqm]
          have hy : (⟨E ((v : ℤ_[q.val]) • x), by rw [hs, Matrix.trace_smul, y.prop, smul_zero]⟩ : TraceZero ℚ_[q.val]) =
              matrixScale V y := Subtype.ext hs
          change goodWeight q.val _ = _ * goodWeight q.val y
          rw [hy]
          exact (goodRule (O := O) (p := q.val)).weight_scale v y
  · simp only [splitFactor, dite_eq_right hx, dite_eq_right (hr.not.mpr hx), mul_zero]

/-- The placewise factor used in the rational product. -/
def localFactor (q : Prime) (x : Bp q.val (-1) (-(ell : ℚ))) : O :=
  if hq : q.val = ell then by
    have he : q = ⟨ell, Fact.out⟩ := Subtype.ext hq
    subst q
    exact divisionFactor h x
  else splitFactor h C m q hq x

/-- Scalar covariance of the actual division factor. -/
theorem divisionFactor_scale (v : ℤ_[ell]ˣ) (x : Bp ell (-1) (-(ell : ℚ))) :
    divisionFactor h ((v : ℤ_[ell]) • x) =
      (legendreUnit (O := O) ell v : O) * divisionFactor h x := by
  classical
  let : Fact (ell % 4 = 3) := ⟨h⟩
  have hr := re_unit_smul_iff (⟨ell, Fact.out⟩ : Prime) v x
  by_cases hx : x.re = 0
  · simp only [divisionFactor, dite_eq_left hx, dite_eq_left (hr.mpr hx)]
    let C := LocalDivision.coordinates ell
    let y : C.RationalZero := ⟨DivisionJoin.ambientEquiv ell x, by
      change LocalDivision.tr (DivisionJoin.ambientEquiv ell x) = 0
      rw [DivisionJoin.ambient_trace, DivisionJoin.reducedTrace, hx, mul_zero]⟩
    let V := Units.map (PadicInt.Coe.ringHom (p := ell)).toMonoidHom v
    have hy : (⟨DivisionJoin.ambientEquiv ell ((v : ℤ_[ell]) • x), by
      change LocalDivision.tr (DivisionJoin.ambientEquiv ell ((v : ℤ_[ell]) • x)) = 0
      rw [DivisionJoin.ambient_trace, DivisionJoin.reducedTrace, hr.mpr hx, mul_zero]⟩ : C.RationalZero) =
        C.scaleZero V y :=
      Subtype.ext (map_smul (DivisionJoin.ambientEquiv ell) (v.val : ℚ_[ell]) x)
    rw [hy]
    exact (C.divisionRule (LocalDivision.localModel ell)).weight_scale v y
  · simp only [divisionFactor, dite_eq_right hx, dite_eq_right (hr.not.mpr hx), mul_zero]

/-- The factor used in the adelic product transforms by its stated scalar character. -/
theorem localFactor_scale (hN : 0 < N) (q : Prime) (v : ℤ_[q.val]ˣ)
    (x : Bp q.val (-1) (-(ell : ℚ))) :
    localFactor h C m q ((v : ℤ_[q.val]) • x) =
      (localAlpha (ell := ell) C m q v : O) * localFactor h C m q x := by
  by_cases hq : q.val = ell
  · have he : q = ⟨ell, Fact.out⟩ := Subtype.ext hq
    subst q
    simpa only [localAlpha, localFactor, Subtype.coe_mk, eq_self, dite_true, ite_true] using divisionFactor_scale h v x
  · simpa only [localFactor, dite_eq_right hq] using splitFactor_scale h C m hN q hq v x

/-- The global integral Schwartz function translated by the chosen class lift. -/
def schwartz (hN : 0 < N) (hne : 2 * m * N * ell ≠ 0) :
    ClassSet (levelOrder ell h N hN) → B (-1) (-(ell : ℚ)) → O :=
  weight (schwartzPhase C m hne) (localFactor h C m)

/-- The actual Schwartz product has finite support on every trace-zero norm sphere. -/
theorem schwartz_finiteSupp (hN : 0 < N) (hne : 2 * m * N * ell ≠ 0)
    (z : ClassSet (levelOrder ell h N hN)) (n : ℚ) :
    {x : B (-1) (-(ell : ℚ)) | x.re = 0 ∧ Visibility.nrd x = n ∧
      schwartz h C m hN hne z x ≠ 0}.Finite :=
  weight_finiteSupp (by norm_num)
    (neg_lt_zero.mpr (Nat.cast_pos.mpr (Fact.out : ell.Prime).pos)) _ _ z n

/-- The coefficient at zero vanishes at the detecting prime. -/
theorem schwartz_zero (hN : 0 < N) (hne : 2 * m * N * ell ≠ 0)
    (z : ClassSet (levelOrder ell h N hN)) :
    coefficientAt (schwartzPhase C m hne) (localFactor h C m) (Adelic.classRepresentative z) 0 = 0 := by
  let q : Prime := ⟨ell, Fact.out⟩
  apply coefficientAt_zero (by norm_num)
    (neg_lt_zero.mpr (Nat.cast_pos.mpr (Fact.out : ell.Prime).pos)) (q := q)
  · exact (mem_exceptionalPlaces m N ell hne q).mpr (dvd_mul_left _ _)
  · simp only [localFactor, q, dite_true]
    exact divisionFactor_zero h

end ZInQ.Manuscript.RC.ThetaJoin
