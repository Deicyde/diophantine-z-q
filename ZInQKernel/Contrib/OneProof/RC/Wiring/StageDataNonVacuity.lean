import ZInQKernel.Contrib.OneProof.RC.Wiring.StageData
import ZInQKernel.Contrib.OneProof.RC.Stages.DetectorStages
import ZInQKernel.Contrib.OneProof.RC.Stages.ExactGenus

/-!
The stage examples use an intrinsic unit support disjoint from the chosen companion's prime
support. Later prime exclusions use `withPreparedStagesSeparated`; `stageClauses_fresh_prime` is a
concrete instance with the prime `5` of `k = −5` in the support but not in the intrinsic support. The detector and prime-sequence
statements remain conditional on their stated inputs; this file does not construct the full odd
models.

Round 8, the witness clauses of `OddStagedInstance` (the exact witness `w`, `hQw`, `hσ`, `hev`,
which replace the former open input `WitnessSpecialization`, now PROVED):

* `StageKummer.pinAt`, `pinAt_selected`, `pinAt_of_ne`, `lamOf_pinAt_of_ne`,
  `exists_pinned_stageKummer` (definition, PROVED): for EVERY stage map `ev₀` and every `ev₁` (in
  particular the actual stage map `actualStageMapOn`), the stage map equal to `ev₁` at the selected
  datum and to `ev₀` elsewhere satisfies `hev`'s equation and has the same `λ_θ(D)` as `ev₀` at
  every `D ≠ D_w`; so `hev` adds no condition to the comparison argument at the other parameters;
* `sq_trivial_of_tateRep_eq_conj`, `detector_at_exactWitness` (PROVED from the construction's
  `exists_detector_stages`): at the rational point of an exact witness, when it is nontorsion, the
  detector construction gives `σ` with `σ²` trivial on the Tate module of `E` (`hσ`), the row
  value and actual detecting sequences of the type asked, with `Q` that point (`hQw` by `rfl`).

* `exists_exactWitnessOn`, `exists_exactWitnessOn_Ecurve` (PROVED from the construction's
  `exact_twist_of_genusPoint`, through `EcurveZ_baseChange` and an embedding of the ring class
  field into `ℚ̄`): for a selected datum with `D_w > 0`, `D_w h_*` odd and `h_*` a genus partner,
  the exact witness exists at the multiplier `L₀ · 4B` (`B` the uniform bound at two good primes),
  and its rational point is nontorsion when `L₀ ≠ 0` and the genus point is nontorsion, so that
  `detector_at_exactWitness` applies to it.

Chain for the witness clauses: `exists_exactWitnessOn_Ecurve` gives `w`; `detector_at_exactWitness`
at its point gives `Q` (`hQw` by `rfl`), `σ`, `hσ`, `b`, `hvalue` and the sequences; the stage
clauses follow as for `stageClauses_of_detector`; `exists_pinned_stageKummer` with
`ev₁ = actualStageMapOn …` gives `hev` without changing `λ_θ(D)` at `D ≠ D_w`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open scoped WeierstrassCurve
open TauCeti WeierstrassCurve ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower
  ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages ZInQ.Contrib.CloudB3RC53 Filter
  Topology ZInQ.Manuscript.RC.TateWiring ZInQ.Contrib.CloudB3RC53.OpenImage

/-- **The constructed data satisfy the support clause** (PROVED; the intrinsic support is the
whole support, `preparedSeparated_self`). -/
theorem stageSupport_withPreparedStages {ℓ : ℕ} (W₀ : WData ℓ) {S : Finset ℕ} {hstar : ℤ}
    {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} (q : StageSequence At cw B)
    (hS : ∀ p ∈ S, p.Prime) (hbase : S0 ℓ ⊆ S) (hh : hstar.natAbs.primeFactors ⊆ S)
    (hdisj : Disjoint S W₀.kfin.natAbs.primeFactors) :
    StageSupport (withPreparedStages W₀ S hstar q) :=
  ⟨hS, hbase, hh, S, Finset.Subset.refl _, hbase, hh, hdisj,
    (preparedSeparated_self S).symm⟩

/-- **The constructed data satisfy the stage link, for every stage sequence** (PROVED, `rfl`). -/
theorem stagesFrom_withPreparedStages {ℓ : ℕ} (W₀ : WData ℓ) (S : Finset ℕ) (hstar : ℤ)
    {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} (q : StageSequence At cw B) :
    StagesFrom (withPreparedStages W₀ S hstar q) q :=
  ⟨rfl, rfl, rfl⟩

/-- The support `S₀ ∪ primes(h_*)` consists of primes (PROVED). -/
theorem s0_union_primeFactors_prime (ℓ : ℕ) (hstar : ℤ) :
    ∀ p ∈ S0 ℓ ∪ hstar.natAbs.primeFactors, p.Prime := by
  intro p hp
  rcases Finset.mem_union.mp hp with h | h
  · simp only [S0, Finset.mem_insert, Nat.mem_primeFactors] at h
    rcases h with rfl | rfl | ⟨hp', -⟩
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact hp'
  · exact Nat.prime_of_mem_primeFactors h

/-- **A concrete support** (PROVED): `S₀ ∪ primes(h_*)` satisfies the support clause, for non-stage data satisfying the displayed disjointness condition and every stage sequence. -/
theorem stageSupport_example {ℓ : ℕ} (W₀ : WData ℓ) (hstar : ℤ)
    {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} (q : StageSequence At cw B)
    (hdisj : Disjoint (S0 ℓ ∪ hstar.natAbs.primeFactors) W₀.kfin.natAbs.primeFactors) :
    StageSupport (withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q) :=
  stageSupport_withPreparedStages W₀ q (s0_union_primeFactors_prime ℓ hstar)
    Finset.subset_union_left Finset.subset_union_right hdisj

/-- **The stage clauses from the detector construction** (PROVED from the construction's
`exists_detector_stages`; tex 2468–2493, 8308–8405): given its inputs, for non-stage data satisfying the displayed disjointness condition,
every admissible support and every finite exclusion, the detector value, an actual detecting
sequence of the type asked by `OddStagedInstance`, and the support clause, the stage link and the
data specification for the constructed data. -/
theorem stageClauses_of_detector {ℓ : ℕ} (hℓ : 0 < ℓ) {Dw hstar : ℤ}
    (hDw : 0 < Dw) (hstar₀ : hstar < 0)
    [(Ecurve ℓ).IsElliptic] [(qtwist (Ecurve ℓ) Dw).IsElliptic]
    (P : ((qtwist (Ecurve ℓ) Dw)⁄ℚ).toAffine.Point)
    (hnt : ¬ IsOfFinAddOrder P) (hS : SerreThm3) (hA : HasNoCM (qtwist (Ecurve ℓ) Dw))
    (F₀ : IntermediateField ℚ Qbar) [IsGalois ℚ F₀] [FiniteDimensional ℚ F₀]
    {x y : Qbar} (hxmem : x ∈ F₀) (hymem : y ∈ F₀)
    (hx : x ^ 2 = (Dw : Qbar)) (hy : y ^ 2 = (hstar : Qbar))
    (W₀ : WData ℓ) (S B : Finset ℕ) (hSp : ∀ p ∈ S, p.Prime) (hbase : S0 ℓ ⊆ S)
    (hh : hstar.natAbs.primeFactors ⊆ S)
    (hdisj : Disjoint S W₀.kfin.natAbs.primeFactors) :
    let A := qtwist (Ecurve ℓ) Dw
    let Q := Affine.Point.baseChange (W' := A) ℚ Qbar P
    let d := divisionTower (A := A) Q
    let hQ : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom Q = Q :=
      fun g => Affine.Point.map_baseChange (W' := A) g.toAlgHom P
    ∃ (a : ℕ) (σ : GalQ) (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2])
      (q : StageSequence (ActualAt A (Ecurve ℓ) Q F₀ σ Dw hstar) (a + 1)
        (stageExclusions ℓ Dw hstar B)),
      b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1) ∧
      StageSupport (withPreparedStages W₀ S hstar q) ∧
      StagesFrom (withPreparedStages W₀ S hstar q) q ∧
      (withPreparedStages W₀ S hstar q).hstar = hstar ∧
      PreDataSpec (withPreparedStages W₀ S hstar q) := by
  intro A Q d hQ
  obtain ⟨a, σ, b, -, -, -, hc, hseq⟩ :=
    exists_detector_stages hℓ hDw hstar₀ P hnt hS hA F₀ hxmem hymem hx hy
  obtain ⟨q⟩ := hseq B
  have hsupp := stageSupport_withPreparedStages W₀ q hSp hbase hh hdisj
  have hfrom := stagesFrom_withPreparedStages W₀ S hstar q
  exact ⟨a, σ, b, q, hc, hsupp, hfrom, rfl, (preDataSpec_of_stagesFrom hsupp hfrom).1⟩

/-- **Actual stage sequences exist unconditionally** (PROVED from the construction's
`actualStageSequence`, i.e. Chebotarev by the repository's density theorem; tex 8358–8377,
8399–8405): for actual complex conjugation, the auxiliary field `ℚ(√D_w, √h_*)`, any point `Q`, any
precision offset and any finite exclusion. (The detector value `b c_Q(σ²) = 2^{a+1}` is not claimed
here: for `σ = τ` the square is trivial; it needs the translate of `stageClauses_of_detector`.) -/
theorem exists_conj_stageSequence {ℓ : ℕ} (hℓ : 0 < ℓ) {Dw hstar : ℤ} (hDw : 0 < Dw)
    (hstar₀ : hstar < 0) [(Ecurve ℓ).IsElliptic] [(qtwist (Ecurve ℓ) Dw).IsElliptic]
    (Q : GeomPoint (qtwist (Ecurve ℓ) Dw)) (cw : ℕ) (B : Finset ℕ) :
    ∃ F₀ : IntermediateField ℚ Qbar, Nonempty (StageSequence
      (ActualAt (qtwist (Ecurve ℓ) Dw) (Ecurve ℓ) Q F₀ complexConj Dw hstar) cw
      (stageExclusions ℓ Dw hstar B)) := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((Dw : ℤ) : Qbar) (by norm_num : 0 < 2)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((hstar : ℤ) : Qbar) (by norm_num : 0 < 2)
  let F₀ := IntermediateField.adjoin ℚ ({x, y} : Set Qbar)
  have : FiniteDimensional ℚ F₀ := IntermediateField.finiteDimensional_adjoin
    (fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral)
  refine ⟨F₀, ⟨actualStageSequence (qtwist (Ecurve ℓ) Dw) (Ecurve ℓ) Q F₀ complexConj
    (det_complexConj (Ecurve ℓ)) Dw hstar cw (stageExclusions ℓ Dw hstar B)
    (IntermediateField.subset_adjoin _ _ (by simp)) (IntermediateField.subset_adjoin _ _ (by simp))
    hx hy (complexConj_pos_sqrt hDw hx) (complexConj_neg_sqrt hstar₀ hy)
    (fun p hp hn => stageExclusions_good hℓ.ne' hDw.ne' hstar₀.ne B hp hn)⟩⟩

/-- **The definitional stage clauses with an actual sequence** (PROVED under the displayed disjointness condition): for non-stage data satisfying the displayed disjointness condition `W₀`, the data built at the support `S₀ ∪ primes(h_*)` and an actual sequence of
`exists_conj_stageSequence` satisfy `StageSupport`, `StagesFrom`, `PreDataSpec` and the advancing
precision. -/
theorem stageClauses_conj {ℓ : ℕ} (hℓ : 0 < ℓ) {Dw hstar : ℤ} (hDw : 0 < Dw)
    (hstar₀ : hstar < 0) [(Ecurve ℓ).IsElliptic] [(qtwist (Ecurve ℓ) Dw).IsElliptic]
    (Q : GeomPoint (qtwist (Ecurve ℓ) Dw)) (cw : ℕ) (B : Finset ℕ) (W₀ : WData ℓ)
    (hdisj : Disjoint (S0 ℓ ∪ hstar.natAbs.primeFactors) W₀.kfin.natAbs.primeFactors) :
    ∃ (F₀ : IntermediateField ℚ Qbar) (q : StageSequence
      (ActualAt (qtwist (Ecurve ℓ) Dw) (Ecurve ℓ) Q F₀ complexConj Dw hstar) cw
      (stageExclusions ℓ Dw hstar B)),
      StageSupport (withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q) ∧
      StagesFrom (withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q) q ∧
      PreDataSpec (withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q) ∧
      Tendsto (withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q).Mθ
        ((withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q).stages : Filter ℕ)
        atTop := by
  obtain ⟨F₀, ⟨q⟩⟩ := exists_conj_stageSequence hℓ hDw hstar₀ Q cw B
  have hsupp := stageSupport_example W₀ hstar q hdisj
  have hfrom := stagesFrom_withPreparedStages W₀ (S0 ℓ ∪ hstar.natAbs.primeFactors) hstar q
  exact ⟨F₀, q, hsupp, hfrom, preDataSpec_of_stagesFrom hsupp hfrom⟩

/-- **A concrete instance** (PROVED): `ℓ = 1`, `D_w = 1`, `h_* = −7`, the zero point, offset `0`,
no extra exclusion, non-stage data satisfying the displayed disjointness condition. -/
theorem stageClauses_concrete (W₀ : WData 1)
    (hdisj : Disjoint (S0 1 ∪ (-7 : ℤ).natAbs.primeFactors) W₀.kfin.natAbs.primeFactors) :
    letI := Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1)
    letI : (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)).IsElliptic :=
      Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1))
        (by norm_num)
    ∃ (F₀ : IntermediateField ℚ Qbar) (q : StageSequence
      (ActualAt (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)) (Ecurve 1) 0 F₀ complexConj 1 (-7)) 0
      (stageExclusions 1 1 (-7) ∅)),
      StageSupport (withPreparedStages W₀ (S0 1 ∪ (-7 : ℤ).natAbs.primeFactors) (-7) q) ∧
      StagesFrom (withPreparedStages W₀ (S0 1 ∪ (-7 : ℤ).natAbs.primeFactors) (-7) q) q ∧
      PreDataSpec (withPreparedStages W₀ (S0 1 ∪ (-7 : ℤ).natAbs.primeFactors) (-7) q) := by
  let := Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1)
  let : (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)).IsElliptic :=
    Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1))
      (by norm_num)
  obtain ⟨F₀, q, h1, h2, h3, -⟩ :=
    stageClauses_conj (ℓ := 1) (by norm_num) (Dw := 1) (hstar := -7) (by norm_num) (by norm_num)
      0 0 ∅ W₀ hdisj
  exact ⟨F₀, q, h1, h2, h3⟩

/-- `S₀(1) = {2, 3}` lies in `{2, 3, 7}` (PROVED). -/
theorem s0_one_subset : S0 1 ⊆ ({2, 3, 7} : Finset ℕ) := by
  intro p hp
  simp only [S0, Nat.primeFactors_one, Finset.mem_insert, Finset.notMem_empty, or_false] at hp
  rcases hp with rfl | rfl <;> simp

/-- The primes of `h_* = −7` lie in `{2, 3, 7}` (PROVED). -/
theorem primeFactors_neg_seven_subset : (-7 : ℤ).natAbs.primeFactors ⊆ ({2, 3, 7} : Finset ℕ) := by
  rw [show (-7 : ℤ).natAbs = 7 by rfl, Nat.Prime.primeFactors (by norm_num : Nat.Prime 7)]
  simp

/-- The data `W₀` with the final companion `k = −5` (definition). -/
def withKMinusFive (W₀ : WData 1) : WData 1 := { W₀ with kfin := -5 }

/-- **A concrete instance with a fresh prime of `k` in the support** (PROVED): `ℓ = 1`, `D_w = 1`,
`h_* = −7`, `k = −5`; the support `{5, 2, 3, 7}` contains the prime `5` of `k`, the unit tests are
at the intrinsic support `{2, 3, 7}` (no squareclass condition at `5`), and the data built from an
actual stage sequence satisfy `StageSupport`, `StagesFrom` and `PreDataSpec`. -/
theorem stageClauses_fresh_prime (W₀ : WData 1) :
    letI := Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1)
    letI : (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)).IsElliptic :=
      Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1))
        (by norm_num)
    ∃ (F₀ : IntermediateField ℚ Qbar) (q : StageSequence
      (ActualAt (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)) (Ecurve 1) 0 F₀ complexConj 1 (-7)) 0
      (stageExclusions 1 1 (-7) ∅)),
      StageSupport
        (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q) ∧
      StagesFrom
        (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q) q ∧
      PreDataSpec
        (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q) ∧
      (5 : ℤ) ∣
        (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q).kfin ∧
      5 ∈ (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q).S ∧
      5 ∉ ({2, 3, 7} : Finset ℕ) := by
  let := Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1)
  let : (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)).IsElliptic :=
    Nonvanishing.qtwist_isElliptic (Nonvanishing.curve_nat_isElliptic (by norm_num : 0 < 1))
      (by norm_num)
  obtain ⟨F₀, ⟨q⟩⟩ := exists_conj_stageSequence (ℓ := 1) (by norm_num) (Dw := 1) (hstar := -7)
    (by norm_num) (by norm_num) 0 0 ∅
  have hprime : ∀ p ∈ ({5, 2, 3, 7} : Finset ℕ), p.Prime := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hkf : (withKMinusFive W₀).kfin = -5 := rfl
  have hdisj : Disjoint ({2, 3, 7} : Finset ℕ) (withKMinusFive W₀).kfin.natAbs.primeFactors := by
    rw [hkf, show (-5 : ℤ).natAbs = 5 by rfl, Nat.Prime.primeFactors (by norm_num : Nat.Prime 5)]
    decide
  have hsupp := stageSupport_withPreparedStagesSeparated (withKMinusFive W₀) q hprime
    (by intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢; omega)
    s0_one_subset primeFactors_neg_seven_subset hdisj
  have hfrom : StagesFrom
      (withPreparedStagesSeparated (withKMinusFive W₀) {2, 3, 7} {5, 2, 3, 7} (-7) q) q :=
    ⟨rfl, rfl, rfl⟩
  exact ⟨F₀, q, hsupp, hfrom, (preDataSpec_of_stagesFrom hsupp hfrom).1,
    ⟨-1, by show (-5 : ℤ) = 5 * (-1); norm_num⟩,
    by simp [withPreparedStagesSeparated, withStages], by decide⟩

/-! Round 8: the witness clauses. -/

section Pin

open ZInQ.Contrib.CloudB3RC53.GenusOdd

variable {E : WeierstrassCurve ℚ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ} {Mθ : ℕ → ℕ}

open Classical in
/-- **A stage map pinned at one datum** (definition): `ev₁` at `(D_w, dat)`, `ev₀` at every other
entry. -/
def StageKummer.pinAt (Dw : ℤ) (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
    (ev₁ ev₀ : Visibility.StageKummer E f Lat κ hstar Mθ) :
    Visibility.StageKummer E f Lat κ hstar Mθ :=
  fun i D dat' =>
    if h : D = Dw then
      (by subst h; exact if dat' = dat then ev₁ i D dat' else ev₀ i D dat')
    else ev₀ i D dat'

theorem StageKummer.pinAt_selected (Dw : ℤ) (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
    (ev₁ ev₀ : Visibility.StageKummer E f Lat κ hstar Mθ) (i : ℕ) :
    StageKummer.pinAt Dw dat ev₁ ev₀ i Dw dat = ev₁ i Dw dat := by
  unfold StageKummer.pinAt
  simp

theorem StageKummer.pinAt_of_ne (Dw : ℤ) (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
    (ev₁ ev₀ : Visibility.StageKummer E f Lat κ hstar Mθ) {D : ℤ} (hD : D ≠ Dw) (i : ℕ)
    (dat' : HeegnerDatum E f Lat κ (D * hstar) 1 hstar) :
    StageKummer.pinAt Dw dat ev₁ ev₀ i D dat' = ev₀ i D dat' := by
  unfold StageKummer.pinAt
  simp [hD]

/-- **Pinning does not change `λ_θ(D)` at `D ≠ D_w`** (PROVED). -/
theorem lamOf_pinAt_of_ne (Dw : ℤ) (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
    (ev₁ ev₀ : Visibility.StageKummer E f Lat κ hstar Mθ) (L : ℕ)
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (θ : ℕ) {D : ℤ} (hD : D ≠ Dw) :
    Visibility.lamOf Mθ L selG (StageKummer.pinAt Dw dat ev₁ ev₀) θ D =
      Visibility.lamOf Mθ L selG ev₀ θ D := by
  unfold Visibility.lamOf
  cases selG D with
  | none => rfl
  | some dat' =>
    dsimp only
    rw [StageKummer.pinAt_of_ne Dw dat ev₁ ev₀ hD θ dat']

/-- **`hev` is satisfiable without touching the other parameters** (PROVED): for every `ev₁` (the
actual stage map) and every `ev₀`, some stage map equals `ev₁` at the selected datum and has the
`λ_θ(D)` of `ev₀` at every `D ≠ D_w`. -/
theorem exists_pinned_stageKummer (Dw : ℤ) (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
    (ev₁ ev₀ : Visibility.StageKummer E f Lat κ hstar Mθ) (L : ℕ)
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar)) :
    ∃ ev : Visibility.StageKummer E f Lat κ hstar Mθ, (∀ i, ev i Dw dat = ev₁ i Dw dat) ∧
      ∀ θ D, D ≠ Dw → Visibility.lamOf Mθ L selG ev θ D = Visibility.lamOf Mθ L selG ev₀ θ D :=
  ⟨StageKummer.pinAt Dw dat ev₁ ev₀, StageKummer.pinAt_selected Dw dat ev₁ ev₀,
    fun θ _ hD => lamOf_pinAt_of_ne Dw dat ev₁ ev₀ L selG θ hD⟩

end Pin

/-- **`hσ` from the detector** (PROVED): if `σ` acts on the Tate module of `E` as complex
conjugation, its square acts trivially. -/
theorem sq_trivial_of_tateRep_eq_conj (E : WeierstrassCurve ℚ) {σ : GalQ}
    (h : tateRep E 2 σ = tateRep E 2 complexConj) : tateRep E 2 (σ * σ) = 1 := by
  rw [map_mul, h, ← map_mul, complexConj_sq, map_one]

open ZInQ.Contrib.CloudB3RC53.GenusOdd in
/-- **The detector construction at the exact witness** (PROVED from the construction's
`exists_detector_stages` at the rational point of `w`; tex 2468–2493, 8295–8405): if that point
is nontorsion, then under the detector's inputs there are `σ` with `σ²` trivial on the Tate module
of `E_ℓ`, a row with value `2^{a+1}` at `σ²` and actual detecting sequences, all at the point
`Q = R` over `ℚ̄`. -/
theorem detector_at_exactWitness {ℓ : ℕ} (hℓ : 0 < ℓ) {Dw hstar : ℤ}
    (hDw : 0 < Dw) (hstar₀ : hstar < 0)
    [(Ecurve ℓ).IsElliptic] [(qtwist (Ecurve ℓ) Dw).IsElliptic]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ}
    {dat : HeegnerDatum (Ecurve ℓ) f Lat κ (Dw * hstar) 1 hstar} {L : ℕ}
    (w : ExactWitnessOn (Ecurve ℓ) rfl rfl dat L) (hnt : ¬ IsOfFinAddOrder w.rational)
    (hS : SerreThm3) (hA : HasNoCM (qtwist (Ecurve ℓ) Dw))
    (F₀ : IntermediateField ℚ Qbar) [IsGalois ℚ F₀] [FiniteDimensional ℚ F₀]
    {x y : Qbar} (hxmem : x ∈ F₀) (hymem : y ∈ F₀)
    (hx : x ^ 2 = (Dw : Qbar)) (hy : y ^ 2 = (hstar : Qbar)) :
    let A := qtwist (Ecurve ℓ) Dw
    let Q := WitnessSpec.rationalGeomPoint A w.rational
    let d := divisionTower (A := A) Q
    let hQ : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom Q = Q :=
      WitnessSpec.rationalGeomPoint_fixed A w.rational
    ∃ (a : ℕ) (σ : GalQ) (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2]),
      tateRep (Ecurve ℓ) 2 (σ * σ) = 1 ∧ b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1) ∧
      ∀ B : Finset ℕ, Nonempty (StageSequence (ActualAt A (Ecurve ℓ) Q F₀ σ Dw hstar) (a + 1)
        (stageExclusions ℓ Dw hstar B)) := by
  intro A Q d hQ
  have hnt' : ¬ IsOfFinAddOrder (Affine.Point.equivBaseChangeSelf A.toAffine w.rational) :=
    fun h => hnt (by
      simpa using (Affine.Point.equivBaseChangeSelf A.toAffine).symm.toAddMonoidHom.isOfFinAddOrder h)
  obtain ⟨a, σ, b, hρ, -, -, hc, hseq⟩ :=
    exists_detector_stages hℓ hDw hstar₀ _ hnt' hS hA F₀ hxmem hymem hx hy
  exact ⟨a, σ, b, sq_trivial_of_tateRep_eq_conj _ hρ, hc, hseq⟩

section ExactWitness

open ZInQ.Contrib.CloudB3RC53.GenusOdd ZInQ.Contrib.CloudB3RC53.CST TauCeti.ClassFieldTheory
  ZInQ.Manuscript.RC.Visibility

/-- **The exact witness exists on a curve with an integral model** (PROVED: the construction's
`exact_twist_of_genusPoint`, with an embedding of the ring class field into `ℚ̄`; tex 2462–2466,
8274–8306): at the multiplier `L₀ · 4B`, `B` the uniform bound at two good primes; its rational
point is nontorsion when `L₀ ≠ 0` and the genus point is nontorsion. -/
theorem exists_exactWitnessOn {E : WeierstrassCurve ℚ} (C : WeierstrassCurve ℤ) (hE : C⁄ℚ = E)
    [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0) (P : Prints)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {D hstar : ℤ} (hD : 0 < D) (hodd : Odd (D * hstar))
    (hgp : GenusPartner E hstar) (dat : HeegnerDatum E f Lat κ (D * hstar) 1 hstar)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hp : ¬ (p : ℤ) ∣ C.Δ) (hq : ¬ (q : ℤ) ∣ C.Δ) (L₀ : ℕ) :
    ∃ w : ExactWitnessOn E h₁ h₃ dat
      (L₀ * (4 * (reductionBound (finiteCount C p) * reductionBound (finiteCount C q)))),
      letI := dat.field; letI := dat.nf; letI := dat.nz
      letI := Classical.decEq (ringClassField (conductorOrder dat.K 1))
      L₀ ≠ 0 → ¬ IsOfFinAddOrder (genusPoint dat) → ¬ IsOfFinAddOrder w.rational := by
  subst hE
  obtain ⟨s, hs, hd, R, heq, hnt⟩ :=
    exact_twist_of_genusPoint C h₁ h₃ P hD hodd hgp dat hpq hp hq L₀
  let := dat.field
  let := dat.nf
  let := dat.nz
  exact ⟨⟨IsAlgClosed.lift, s, hs, hd, R, heq⟩, hnt⟩

/-- **The exact witness for `E_ℓ`** (PROVED from `exists_exactWitnessOn` at the integral model
`EcurveZ`). -/
theorem exists_exactWitnessOn_Ecurve {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (P : Prints)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {D hstar : ℤ} (hD : 0 < D) (hodd : Odd (D * hstar))
    (hgp : GenusPartner (Ecurve ℓ) hstar)
    (dat : HeegnerDatum (Ecurve ℓ) f Lat κ (D * hstar) 1 hstar)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (hp : ¬ (p : ℤ) ∣ (EcurveZ ℓ).Δ) (hq : ¬ (q : ℤ) ∣ (EcurveZ ℓ).Δ) (L₀ : ℕ) :
    ∃ w : ExactWitnessOn (Ecurve ℓ) rfl rfl dat
      (L₀ * (4 * (reductionBound (finiteCount (EcurveZ ℓ) p) *
        reductionBound (finiteCount (EcurveZ ℓ) q)))),
      letI := dat.field; letI := dat.nf; letI := dat.nz
      letI := Classical.decEq (ringClassField (conductorOrder dat.K 1))
      L₀ ≠ 0 → ¬ IsOfFinAddOrder (genusPoint dat) → ¬ IsOfFinAddOrder w.rational :=
  exists_exactWitnessOn (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl P hD hodd hgp dat hpq hp hq L₀

end ExactWitness

end ZInQ.Manuscript.RC.Wiring
