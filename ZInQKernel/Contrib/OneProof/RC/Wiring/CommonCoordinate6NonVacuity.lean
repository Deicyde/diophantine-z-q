import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate6
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate5NonVacuity

/-!
# Theorem 5.3, Lane RC32 round 2: non-vacuity of the leaf with the actual Frobenius

`CommonCoordinateTrianglesLF` (`CommonCoordinate6.lean`) is inhabited with the actual Frobenius
matrix `frobMat C p` of `ρ_T(Fr_p)` in each relaxation step, given the GLUE `FrobeniusTrace (E_ℓ)`:

* `naturalStep_relaxedCoord`: the relaxation step of round one's construction for **any**
  Frobenius matrix of trace `a_p` and determinant `p` (round one used a companion matrix);
* `trianglesLF_of_eq`: the leaf at one address from (4.7) data with coordinates in `F`, with
  `Fr := frobMat C`;
* `nonempty_trianglesLF_famFive`: at `famFive` (one address bit, the graph prime `5`, unused at the
  address `0`), for the data `constData ℓ`, the datum `TateCoef.rat` (`K = ℚ`, `K_S = ℚ̄`), every
  `ℓ > 0` with `5 ∤ 6ℓ`;
* `commonCoordinateInputsLF_goodData`: the whole leaf `CommonCoordinateInputsLF` for data whose
  support is the set of primes of `6ℓ` (so that every graph prime is good).

Kinds: PROVED, from the GLUE `FrobeniusTrace` (a hypothesis).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix CategoryTheory ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)

/-- **A relaxation step of the construction for any Frobenius matrix with trace `a_p` and
determinant `p`** (PROVED): between the coordinates `relaxedCoord` at `T` and `T ∪ {p}`, with the
step unit `stepUnit` (round one's construction, with the Frobenius matrix a parameter). -/
theorem naturalStep_relaxedCoord {ℓ : ℕ} (Fam : Family) (x : Addr Fam.b) {E uprim : FracLam}
    (hE : LamUnitF E) (Fr : Matrix (Fin 2) (Fin 2) ℤ_[2]) {T : Finset ℕ} {p : ℕ} (hpo : Odd p)
    (hp : p ∈ unusedAt Fam x) (hpT : p ∉ T) (htr : Fr.trace = (apE ℓ p : ℤ_[2]))
    (hdet : Fr.det = (p : ℤ_[2])) :
    NaturalStep (Fr.map zTwoToF) (p : FracLam) (p : FracLam)⁻¹ (apE ℓ p : FracLam)
      (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))
      (relaxedCoord ℓ Fam x E uprim T) (relaxedCoord ℓ Fam x E uprim (insert p T))
      (stepUnit Fam x E T p) LamUnitF LamUnitF := by
  have hp0 : (p : FracLam) ≠ 0 := natCast_ne_zero_F hpo.pos.ne'
  obtain ⟨ha, hd⟩ := trace_det_map_zTwoToF htr hdet
  have hq : (p : FracLam) * (p : FracLam)⁻¹ = 1 := mul_inv_cancel₀ hp0
  have hdetB : (twoPlaceBlock (Fr.map zTwoToF) (p : FracLam) (lamToF (zAt Fam x p : Lambda))
      (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ))).det = (p : FracLam) ^ 4 * lF ℓ Fam x p := by
    rw [det_twoPlaceBlock, quotientDet_eq _ _ hq ha hd, quotientFactor_eq_quotPoly _ _ _ ha hd,
      lF_eq_quotPoly hpo]
  have hl := lF_ne_zero ℓ Fam x hpo
  have hdu : (if insert p T = unusedAt Fam x then E else 1) =
      (if insert p T = unusedAt Fam x ∧ (unusedAt Fam x).Nonempty then E else 1) := by
    by_cases h : insert p T = unusedAt Fam x
    · rw [ite_eq_left h, ite_eq_left ⟨h, ⟨p, hp⟩⟩]
    · rw [ite_eq_right h, ite_eq_right fun h' => h h'.1]
  have hTU : ¬ (T = unusedAt Fam x ∧ (unusedAt Fam x).Nonempty) := by
    rintro ⟨h1, -⟩; rw [← h1] at hp; exact hpT hp
  refine naturalStepF_of ?_ ?_ ?_
  · exact ((lamUnitF_natCast hpo).pow 4).mul (by
      by_cases h : insert p T = unusedAt Fam x
      · rw [ite_eq_left h]; exact hE
      · rw [ite_eq_right h]; exact lamUnitF_one)
  · rw [hdetB]; exact mul_ne_zero (pow_ne_zero 4 hp0) hl
  · rw [hdetB, ← eF_eq_pointFactor, relaxedCoord, relaxedCoord, Finset.prod_insert hpT,
      ite_eq_right hTU, ← hdu]
    field_simp

/-- **The leaf with the actual Frobenius at one address from (4.7) on data with coordinates in
`F`** (PROVED, from the GLUE `FrobeniusTrace`): round one's relaxed coordinates and step units,
with each step `naturalStep_relaxedCoord` at `Fr := frobMat C p`. -/
def trianglesLF_of_eq {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ))
    (hT : FrobeniusTrace (Ecurve ℓ)) (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b)
    (hQ : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2) (hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q)
    (uprim : FracLam) (hprim : IsTExpansion uprim (D.uPrim Fam x))
    (e : Lambdaˣ) (htilde : D.uTilde Fam x = lamIncl (e : Lambda) * D.uPrim Fam x)
    (hone : unusedAt Fam x = ∅ → D.uTilde Fam x = D.uPrim Fam x) :
    CommonCoordinateTrianglesLF C D Fam x :=
  have hodd : ∀ q ∈ Fam.Q, Odd q := fun q hq => (hQ q hq).1.odd_of_ne_two (hQ q hq).2
  { hgood := hgood
    u := relaxedCoord ℓ Fam x (lamToF (e : Lambda)) uprim
    hprim := (trianglesL_of_eq D Fam x hodd uprim hprim e htilde hone).hprim
    eps := stepUnit Fam x (lamToF (e : Lambda))
    hstep := fun _ _ p hp hpT =>
      have hpQ : p ∈ Fam.Q := (mem_unusedAt.mp hp).1
      naturalStep_relaxedCoord Fam x ⟨e, rfl⟩ (frobMat C p) (hodd p hpQ) hp hpT
        (trace_det_frobMat C hT (hQ p hpQ).1 (hQ p hpQ).2 (hgood p hpQ)).1
        (det_frobMat C (hQ p hpQ).1 (hQ p hpQ).2)
    htilde := (trianglesL_of_eq D Fam x hodd uprim hprim e htilde hone).htilde }

/-- `E_ℓ` is elliptic for `ℓ > 0` (PROVED). -/
theorem isElliptic_Ecurve {ℓ : ℕ} (hℓ : 0 < ℓ) : (Ecurve ℓ).IsElliptic :=
  Nonvanishing.curve_isElliptic' (by exact_mod_cast hℓ.ne')

/-- `E_ℓ` has good reduction at every prime `q ∤ 6ℓ` (PROVED, lane RC13's `goodAt_curve`). -/
theorem goodAt_Ecurve {ℓ q : ℕ} (hq : q.Prime) (h : ¬ (q : ℤ) ∣ 6 * ℓ) :
    Nonvanishing.GoodAt (Ecurve ℓ) q := by
  have := Nonvanishing.goodAt_curve (m := (ℓ : ℤ)) hq h
  simpa [Ecurve] using this

/-- **Non-vacuity with the actual Frobenius** (PROVED from the GLUE `FrobeniusTrace`): at the
address `0` of `famFive`, where the graph prime `5` is unused, for `constData ℓ` and the datum
`TateCoef.rat`, with the step at `5` a `NaturalStep` for the actual matrix `frobMat C 5` of
`ρ_T(Fr_5)`. -/
theorem nonempty_trianglesLF_famFive {ℓ : ℕ} (hℓ : 0 < ℓ) (hT : FrobeniusTrace (Ecurve ℓ))
    (h5 : ¬ (5 : ℤ) ∣ 6 * ℓ) :
    Nonempty (@CommonCoordinateTrianglesLF ℓ (isElliptic_Ecurve hℓ)
      (@TateCoef.rat (Ecurve ℓ) (isElliptic_Ecurve hℓ)) (constData ℓ) famFive 0) := by
  have := isElliptic_Ecurve hℓ
  have hmem : ∀ q ∈ famFive.Q, q = 5 := fun q hq => Finset.mem_singleton.mp hq
  refine ⟨trianglesLF_of_eq _ hT _ _ _ (fun q hq => ?_) (fun q hq => ?_) 1 isTExpansion_one 1
    (by simp [constData]) (fun _ => rfl)⟩
  · rw [hmem q hq]; exact ⟨by norm_num, by norm_num⟩
  · rw [hmem q hq]; exact goodAt_Ecurve (by norm_num) (by exact_mod_cast h5)

/-- Data with `u_{prim} = ũ = 1` whose support is the set of primes of `6ℓ`. -/
def goodData (ℓ : ℕ) : RCData ℓ := { constData ℓ with S := (6 * ℓ).primeFactors }

/-- **The whole leaf with the actual Frobenius** (PROVED from the GLUE `FrobeniusTrace`) for
`goodData ℓ`, `ℓ > 0`: every graph prime of a final family lies outside the primes of `6ℓ`, hence
is good. -/
theorem commonCoordinateInputsLF_goodData {ℓ : ℕ} (hℓ : 0 < ℓ) (hT : FrobeniusTrace (Ecurve ℓ)) :
    CommonCoordinateInputsLF (goodData ℓ) := by
  have := isElliptic_Ecurve hℓ
  refine ⟨isElliptic_Ecurve hℓ, TateCoef.rat (Ecurve ℓ), hT, fun Co Ce F hF x => ?_⟩
  have hQ : ∀ q ∈ F.Q, q.Prime ∧ q ≠ 2 := fun q hq => ⟨(hF.1 q hq).1, (hF.1 q hq).2.1⟩
  have hgood : ∀ q ∈ F.Q, Nonvanishing.GoodAt (Ecurve ℓ) q := by
    intro q hq
    obtain ⟨hp, -, hS, -⟩ := hF.1 q hq
    refine goodAt_Ecurve hp fun hdvd => hS ?_
    change q ∈ (6 * ℓ).primeFactors
    rw [Nat.mem_primeFactors]
    exact ⟨hp, by exact_mod_cast hdvd, by positivity⟩
  exact ⟨trianglesLF_of_eq _ hT _ F x hQ hgood 1 isTExpansion_one 1
    (by simp [goodData, constData]) (fun _ => rfl)⟩

end ZInQ.Manuscript.RC.Wiring
