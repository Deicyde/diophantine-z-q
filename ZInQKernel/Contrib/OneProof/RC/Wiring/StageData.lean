import ZInQKernel.Contrib.OneProof.RC.Wiring.OddModels
import ZInQKernel.Contrib.OneProof.RC.Wiring.Genus
import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Realization
import ZInQKernel.Contrib.OneProof.RC.Stages.PreparedStages
import ZInQKernel.Contrib.OneProof.RC.Stages.Witness
import ZInQKernel.Contrib.OneProof.RC.Wiring.StageWitness

/-!
**Theorem 5.3, Lane RC0 round 6: the stage data from the Appendix F stage construction.**

Before this file, lane RC0's leaves asked for two things about the stages: `PreDataSpec W`, a
requirement on the freely chosen interface data, and, inside the odd instance, (O.2) at the fixed
witness (`OddInstance.hO2 : WitnessValuation …`, ELLIOT + PRINT). Both are now reduced to the stage
construction of `RC/Stages` (Appendix F, tex 8225–8405; App G 10190–10191):

* `StageSupport W` (definitions): the fixed support consists of primes and contains `S₀` and the
  primes of `h_*` (tex 1974–1975, 2461–2462, 8254–8256), and the prepared filter imposes positive
  unit-squareclass tests at the intrinsic support and only coprimality at its later enlargement
  (`preparedSeparated`, tex 2027–2029, 2460–2462, 8247–8248, 8254–8258, 10594–10596).
  `StageSupport.preparedSpec` (PROVED) gives the old leaf
  `PreparedSpec` (the square class at `2` forces `≡ 1 (mod 8)`).
* `StagesFrom W q` (definitions): the stage fields of `W` are the construction at a stage sequence
  `q`: the hyperfilter, `M_θ = c_w + 1 + θ` and the prepared filter cut by the Legendre test of the
  `θ`-th prime (tex 2489–2493, 2531–2536, 8399–8405, App G 10190–10191). With `StageSupport` it
  gives `PreDataSpec W` and the advancing precision (`preDataSpec_of_stagesFrom`, PROVED from the
  construction's `preDataSpec_preparedStages`).
* `OddStagedInstance W`: the odd models (`OddModels`) together with the fixed witness `D_w`, its
  selected genus datum, the exact witness (a rational point of `A = E^{(D_w)}` whose twist is
  `L P_{D_w}`, tex 2462–2466, 8295–8306), the outputs of the detector construction at that point
  (the point `Q`, a division tower, the auxiliary field, `σ` with `σ²` trivial on the Tate module
  of `E`, the row `b` with `b c_Q(σ²) = 2^{a+1}`, an actual detecting sequence `q`), the stage link
  `StagesFrom W q`, and the stage maps at the selected datum being the actual stage map
  (`actualStageMapOn`, `RC/Wiring/StageWitness.lean`). The specialization identity
  `WitnessSpecialization` (tex 8392–8398), formerly the open input, is PROVED from them
  (`OddStagedInstance.witnessSpecialization`, by the witness specialization of `RC/WitnessSpec`),
  hence (O.2) at the witness (`OddStagedInstance.witnessValuation`, by the construction's
  `witnessValuation_withStages`), so `OddInstance` is PROVED (`OddStagedInstance.toOddInstance`).

Order of choices (tex 2460–2467, 8246–8260). `RCLeaves.data ℓ h` is chosen after the genus
partner `h_*`; the support enlargement by the primes of `h_*`, the witness `D_w`, the multiplier,
the detector and the stage sequence are all made after `h_*`, so they may depend on it, and the
stage fields of `data ℓ h` are the construction at that sequence. The odd models are chosen after
the data, and `OddStagedInstance` asks that its `D_w` and its stage maps be the ones of that same
construction (at the selected datum the stage maps are the actual stage map at the places of the
sequence's Frobenius elements, `hev`).

The witness specialization (round 8). Elliot's good-reduction step at the witness (tex
8392–8398, "Good reduction identifies the reduction of the global division cocycle with this
exact map") is PROVED by the witness specialization of `RC/WitnessSpec` (reduction at the place
of the selected Frobenius, its equivariance on the division point, the prime-to-`p` torsion
specialization, the split twist by the witness root and the quadratic ring class residue). It is
wired here by asking (`hev`) that the stage maps BE that actual map at the selected datum
`(D_w, dat)`; with the exact witness `w`, the point `Q` equal to its rational point (`hQw`, so
`Q` is now the text's point) and `σ²` trivial on the Tate module of `E` (`hσ`, a detector output),
`WitnessSpecialization` follows (`OddStagedInstance.witnessSpecialization`).

Remaining reading. The stage maps `ev` at every other entry `(θ, D, dat')`, `(D, dat') ≠ (D_w, dat)`,
stay interface data, read only by `lamOf` in the comparison argument `hcore` at the admissible
`D ≠ D_w` (the text's `x ↦ b(κ_{M_θ}(x̄))` at the same chosen places, tex 8378–8398, 8439–8456,
9283–9290, which is not constructed there). `hev` constrains no such entry: the construction's
total map is zero off the selected datum, but only its selected entry is asked of `ev`
(`StageDataNonVacuity.lean`: `StageKummer.pinAt`). At `D = D_w` the comparison argument reads the
actual map, as in the text. As before, the comparison argument permits zero stage maps away from
the witness when the coefficients and theta models are replaced by matching witness-supported
data; away from the selected datum nothing identifies the maps with reduction at the constructed
primes.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open scoped WeierstrassCurve
open TauCeti ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC.PrintsArith
  ZInQ.Manuscript.RC.Stages ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
  ZInQ.Contrib.CloudB3RC53.GenusOdd Filter Topology

/-! The fixed support and the prepared filter. -/

/-- Unit tests at the intrinsic support; prime exclusions at the enlarged support. -/
def preparedSeparated (Sunit Sexcl : Finset ℕ) (D : ℤ) : Prop :=
  positivePrepared Sunit D ∧ ∀ p ∈ Sexcl, ¬ (p : ℤ) ∣ D

/-- **The fixed support and the prepared filter** (definitions; owner RC0):
* `support_prime`, `support_base`: the support consists of primes and contains
  `S₀ ℓ = {2, 3} ∪ primes(ℓ)` (tex 1974–1975);
* `support_hstar`: it contains the primes of `h_*`, adjoined before the witness is chosen (tex
  2405–2408, 2461–2462, App F 8254–8256);
* `prepared_eq`: unit-squareclass tests use an intrinsic support containing the base primes and
  the primes of `h_*`, disjoint from the primes of `k`; the enlarged support imposes only prime
  exclusions (tex 2027–2029, 2460–2462, 8247–8248, 8254–8258, 10594–10596). The primes of `k`,
  adjoined to the support afterwards (tex 2600–2603), add no squareclass condition: the stationary
  `k`-tests do not add conditions to the odd symbol. -/
structure StageSupport {ℓ : ℕ} (W : WData ℓ) : Prop where
  support_prime : ∀ p ∈ W.S, p.Prime
  support_base : S0 ℓ ⊆ W.S
  support_hstar : W.hstar.natAbs.primeFactors ⊆ W.S
  prepared_eq : ∃ Sunit : Finset ℕ,
    Sunit ⊆ W.S ∧ S0 ℓ ⊆ Sunit ∧ W.hstar.natAbs.primeFactors ⊆ Sunit ∧
    Disjoint Sunit W.kfin.natAbs.primeFactors ∧
    W.prepared = preparedSeparated Sunit W.S

theorem preparedSeparated_one {Sunit Sexcl : Finset ℕ}
    (hunit : Sunit ⊆ Sexcl) (hS : ∀ p ∈ Sexcl, p.Prime) :
    preparedSeparated Sunit Sexcl 1 := by
  refine ⟨positivePrepared_one (fun p hp => hS p (hunit hp)), fun p hp => ?_⟩
  intro hd
  exact (hS p hp).ne_one (Nat.dvd_one.mp (Int.natCast_dvd.mp hd))

/-- **The old leaf `PreparedSpec` from the support** (PROVED): a prepared parameter is positive,
squarefree and prime to the support, and the square class at `2 ∈ S₀` gives `≡ 1 (mod 8)`. -/
theorem StageSupport.preparedSpec {ℓ : ℕ} {W : WData ℓ} (hS : StageSupport W) :
    PreparedSpec W := by
  obtain ⟨Sunit, hunit, hbase, hh, hdisj, heq⟩ := hS.prepared_eq
  intro d hd
  rw [heq] at hd
  obtain ⟨⟨hpos, hsf, hlocal⟩, havoid⟩ := hd
  have h2 : 2 ∈ Sunit := hbase (by simp [S0])
  obtain ⟨h2d, hsq⟩ := hlocal 2 h2
  have h2d' : ¬ (2 : ℤ) ∣ d := h2d
  have hodd : Odd d := Int.odd_iff.mpr (by omega)
  have h8 := Nonvanishing.modEq_eight_of_isSquareAt_two hodd odd_one (by simpa using hsq)
  have h8' : d % 8 = 1 % 8 := h8
  exact ⟨hpos, hsf, by omega, havoid⟩

/-! The stage fields from a stage sequence. -/

/-- **The stage fields of `W` are the construction at the stage sequence `q`** (definitions; tex
2489–2493, 2531–2536, App F 8399–8405, App G 10190–10191; owner RC0): the hyperfilter on the stages,
the precision `M_θ = c_w + 1 + θ`, and the stage support cut from the prepared filter by the
Legendre test of the `θ`-th prime of `q` (the construction's `withStages`). -/
structure StagesFrom {ℓ : ℕ} (W : WData ℓ) {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ}
    (q : StageSequence At cw B) : Prop where
  stages_eq : W.stages = hyperfilter ℕ
  Mθ_eq : W.Mθ = fun i => cw + 1 + i
  admissible_eq : W.admissible = fun i D => W.prepared D ∧ stageTest q i D

section Link

variable {ℓ : ℕ} {W : WData ℓ} {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ}
  {q : StageSequence At cw B}

/-- **The data are the construction's `withStages`** (PROVED). -/
theorem StagesFrom.withStages_eq (h : StagesFrom W q) : withStages W q W.prepared = W := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold withStages
  rw [← h1, ← h2, ← h3]

/-- **The data specification and the advancing precision from the construction** (PROVED: the
construction's `preDataSpec_withStages` and `stages_advance_withStages`, for the data's own
prepared filter). -/
theorem preDataSpec_of_stagesFrom {ℓ : ℕ} {W : WData ℓ}
    {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} {q : StageSequence At cw B}
    (hS : StageSupport W) (h : StagesFrom W q) :
    PreDataSpec W ∧ Tendsto W.Mθ (W.stages : Filter ℕ) atTop := by
  obtain ⟨Sunit, hunit, hbase, hh, hdisj, heq⟩ := hS.prepared_eq
  have hone : W.prepared 1 := by
    rw [heq]
    exact preparedSeparated_one hunit hS.support_prime
  have h1 := preDataSpec_withStages W q hS.support_prime hS.support_base hone
  have h2 := stages_advance_withStages W q W.prepared
  rw [h.withStages_eq] at h1 h2
  exact ⟨h1, h2⟩

end Link

/-! The odd models with the constructed stages. -/

/-- **The odd side's genuine models with the stage data of the Appendix F construction** (tex
2460–2536, 8225–8405). Fields beyond `OddModels` (kinds and owners):
* `eE`, `eA`: `E_ℓ` and `A = E^{(D_w)}` are elliptic (definitions, instance arguments; PROVED-able
  for `ℓ > 0`, `D_w ≠ 0`; owner RC0);
* `Dw`, `hDw`, `dat`, `hdat`: the fixed witness, in the prepared filter, and its selected
  conductor-one genus datum (definitions; tex 2460–2462, 8254–8258; the selection exists at a
  prepared simple zero by `GenusOddInstance.hselG`);
* `w`: the exact witness, an embedding of the datum's ring class field, a root of `D_w` in it and a
  rational point `R` of `A` whose twist by that root is `L P_{D_w}` (`ExactWitnessOn`; ELLIOT, tex
  2462–2466, 8295–8306; a leaf field; its existence at the multiplier `L₀ · 4B` (a multiple of the
  uniform bound, tex 8295–8297) is PROVED by `exists_exactWitnessOn_Ecurve` (from `Prints`,
  `StageDataNonVacuity`; not used by the deduction); owner: the Appendix F stage construction);
* `Q`, `hQw`, `hQ`, `d`, `F₀`, `σ`, `hσ`, `a`, `b`, `hvalue`, `B`, `q`: the outputs of the detector
  construction at `R`: the point `Q = R` over `ℚ̄` (`hQw`), Galois fixed, a compatible division
  tower, the auxiliary field, the detecting element `σ = hτ` with `σ²` trivial on the Tate module
  of `E` (`hσ`), the fixed row `b` with `b c_Q(σ²) = 2^{a+1}` (`c_w = a + 1`), a finite exclusion
  and an actual detecting sequence at precisions `a + 2 + θ` (ELLIOT, Proposition
  `ex:app-detector`, tex 2468–2493, 8295–8405; leaf fields; their existence for a nontorsion
  rational point of `A`, given Serre's open image (`SerreThm3`, PRINT, not in `Prints`) and the
  absence of CM (with a definitional auxiliary field), is PROVED by `exists_detector_stages`
  (`StageDataNonVacuity`; not used by the deduction); `hσ` from its `tateRep E σ = tateRep E τ`,
  `sq_trivial_of_tateRep_eq_conj`; owner: the Appendix F stage construction);
* `hstages`: the stage fields of `W` are the construction at `q` (definitions, `StagesFrom`);
* `hev`: at the selected datum the stage maps are the actual stage map at the places of the
  selected Frobenius elements (`actualStageMapOn`: reduction into the square-fixed group, the
  finite Kummer map, the inverse torsion specialization through the split twist by the root of `w`,
  and the row `b`; definitions, tex 8378–8398, 8439–8456; owner RC0). It replaces the former open
  input `hred : WitnessSpecialization …`, now PROVED (`witnessSpecialization`). The other entries
  of `ev` are not constrained by it; they are read only by `hcore`. -/
structure OddStagedInstance {ℓ : ℕ} (W : WData ℓ) : Type 1 extends OddModels W where
  /-- `E_ℓ` is elliptic -/
  [eE : (Ecurve ℓ).IsElliptic]
  /-- the fixed witness `D_w` -/
  Dw : ℤ
  /-- it is prepared -/
  hDw : W.prepared Dw
  /-- its selected conductor-one genus datum -/
  dat : HeegnerDatum (Ecurve ℓ) f Lat κ (Dw * W.hstar) 1 W.hstar
  /-- it is the selected one -/
  hdat : selG Dw = some dat
  /-- the exact witness: a rational point of `A` whose twist is `L P_{D_w}` -/
  w : ExactWitnessOn (Ecurve ℓ) rfl rfl dat L
  /-- `A = E^{(D_w)}` is elliptic -/
  [eA : (qtwist (Ecurve ℓ) Dw).IsElliptic]
  /-- the witness point of `A`, over `ℚ̄` -/
  Q : GeomPoint (qtwist (Ecurve ℓ) Dw)
  /-- it is the rational point of the exact witness -/
  hQw : Q = WitnessSpec.rationalGeomPoint (qtwist (Ecurve ℓ) Dw) w.rational
  /-- it is Galois fixed -/
  hQ : ∀ g : GalQ,
    WeierstrassCurve.Affine.Point.map (W' := qtwist (Ecurve ℓ) Dw) g.toAlgHom Q = Q
  /-- a compatible tower of divisions of `Q` -/
  d : DivisionTower (qtwist (Ecurve ℓ) Dw) Q
  /-- the auxiliary field -/
  F₀ : IntermediateField ℚ Qbar
  /-- the detecting element -/
  σ : GalQ
  /-- its square acts trivially on the Tate module of `E_ℓ` -/
  hσ : tateRep (Ecurve ℓ) 2 (σ * σ) = 1
  /-- the exponent, `c_w = a + 1` -/
  a : ℕ
  /-- the fixed integral row -/
  b : TateMod (qtwist (Ecurve ℓ) Dw) 2 →ₗ[ℤ_[2]] ℤ_[2]
  /-- its value at the square of the detecting element -/
  hvalue : b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1)
  /-- the finite prime exclusion -/
  B : Finset ℕ
  /-- the actual detecting sequence -/
  q : StageSequence (ActualAt (qtwist (Ecurve ℓ) Dw) (Ecurve ℓ) Q F₀ σ Dw W.hstar) (a + 1) B
  /-- the stage fields of the data are the construction at `q` -/
  hstages : StagesFrom W q
  /-- at the selected datum the stage maps are the actual stage map -/
  hev : ∀ i, ev i Dw dat = actualStageMapOn (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl dat w hQw
    q hσ b hstages.Mθ_eq i Dw dat

namespace OddStagedInstance

variable {ℓ : ℕ} {W : WData ℓ}

/-- **The specialization identity at the witness** (PROVED; formerly the open input `hred`; tex
8392–8398): the stage maps agree at the selected datum with the actual stage map (`hev`), which
satisfies it (`actualStageMapOn_spec`, from the witness specialization of `RC/WitnessSpec`). -/
theorem witnessSpecialization (I : OddStagedInstance W) :
    letI := I.eE
    letI := I.eA
    WitnessSpecialization (L := I.L) I.dat I.ev I.d I.hQ
      (fun i => (selectedFrobenius I.q i).val) (finiteRow I.b) := by
  have := I.eE
  have := I.eA
  exact witnessSpecialization_of_agree I.hev
    (actualStageMapOn_spec (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl I.dat I.w I.hQw I.d I.hQ
      I.q I.hσ I.b I.hstages.Mθ_eq)

/-- **(O.2) at the fixed witness, read on `λ`** (PROVED: the construction's
`witnessValuation_withStages` with `witnessSpecialization`, transported along
`StagesFrom.withStages_eq`; tex 2490–2493, 2534–2536, 8392–8398): on every stage `D_w` is admissible and `v₂ λ_θ(D_w) = a + 1`. -/
theorem witnessValuation (I : OddStagedInstance W) :
    Visibility.WitnessValuation W (Visibility.lamOf W.Mθ I.L I.selG I.ev) I.Dw (I.a + 1) := by
  have := I.eE
  have := I.eA
  have key : ∀ (V : WData ℓ), withStages W I.q W.prepared = V →
      ∀ ev : Visibility.StageKummer (Ecurve ℓ) I.f I.Lat I.κ W.hstar V.Mθ,
      WitnessSpecialization (L := I.L) I.dat ev I.d I.hQ
        (fun i => (selectedFrobenius I.q i).val) (finiteRow I.b) →
      Visibility.WitnessValuation V (Visibility.lamOf V.Mθ I.L I.selG ev) I.Dw (I.a + 1) := by
    intro V hV
    subst hV
    intro ev hred
    exact witnessValuation_withStages W I.d I.hQ I.q I.hDw I.selG I.dat I.hdat ev I.b I.hvalue hred
  exact key W I.hstages.withStages_eq I.ev I.witnessSpecialization

/-- **The odd instance** (PROVED): the models, the witness `D_w`, `c_w = a + 1` and (O.2) from
`witnessValuation`. -/
def toOddInstance (I : OddStagedInstance W) : OddInstance W where
  toOddModels := I.toOddModels
  Dw := I.Dw
  cw := I.a + 1
  hO2 := I.witnessValuation

/-- **The data specification and the advancing precision** (PROVED from the support and the stage
link, `preDataSpec_of_stagesFrom`). -/
theorem preDataSpec (I : OddStagedInstance W) (hS : StageSupport W) :
    PreDataSpec W ∧ Tendsto W.Mθ (W.stages : Filter ℕ) atTop :=
  preDataSpec_of_stagesFrom hS I.hstages

end OddStagedInstance

def withPreparedStagesSeparated {ℓ : ℕ} (W : WData ℓ) (Sunit Sexcl : Finset ℕ)
    (hstar : ℤ) {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ}
    (q : StageSequence At cw B) : WData ℓ :=
  withStages { W with S := Sexcl, hstar := hstar } q (preparedSeparated Sunit Sexcl)

theorem stageSupport_withPreparedStagesSeparated {ℓ : ℕ} (W : WData ℓ)
    {Sunit Sexcl : Finset ℕ} {hstar : ℤ}
    {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} (q : StageSequence At cw B)
    (hS : ∀ p ∈ Sexcl, p.Prime) (hunit : Sunit ⊆ Sexcl) (hbase : S0 ℓ ⊆ Sunit)
    (hh : hstar.natAbs.primeFactors ⊆ Sunit)
    (hdisj : Disjoint Sunit W.kfin.natAbs.primeFactors) :
    StageSupport (withPreparedStagesSeparated W Sunit Sexcl hstar q) :=
  ⟨hS, hbase.trans hunit, hh.trans hunit, Sunit, hunit, hbase, hh, hdisj, rfl⟩

theorem preparedSeparated_self (S : Finset ℕ) :
    preparedSeparated S S = positivePrepared S := by
  funext D
  apply propext
  exact ⟨fun h => h.1, fun h => ⟨h, fun p hp => (h.2.2 p hp).1⟩⟩

end ZInQ.Manuscript.RC.Wiring
