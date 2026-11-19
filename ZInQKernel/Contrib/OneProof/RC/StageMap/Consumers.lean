import ZInQKernel.Contrib.OneProof.RC.StageMap.Actual

/-! Read the actual evaluations at the types used by the odd comparison and
by the witness valuation. The stage identification is
`Wiring.StagesFrom.withStages_eq` in the existing assembly. -/

noncomputable section

open WeierstrassCurve TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages
  ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped WeierstrassCurve

namespace ZInQ.Manuscript.RC.StageMap

variable {ℓ : ℕ} (W : WData ℓ) [(Ecurve ℓ).IsElliptic]
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (Ecurve ℓ)) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {Dw : ℤ}
  (dat : HeegnerDatum (Ecurve ℓ) f Lat κ (Dw * W.hstar) 1 W.hstar)
  {L : ℕ} (w : ExactWitnessOn (Ecurve ℓ) rfl rfl dat L)
  [(qtwist (Ecurve ℓ) (Dw : ℚ)).IsElliptic] {Q : GeomPoint (qtwist (Ecurve ℓ) (Dw : ℚ))}
  (hQw : Q = WitnessSpec.rationalGeomPoint (qtwist (Ecurve ℓ) (Dw : ℚ)) w.rational)
  {a : ℕ} {S : Finset ℕ} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
  (q : StageSequence (ActualAt (qtwist (Ecurve ℓ) (Dw : ℚ)) (Ecurve ℓ) Q F₀ σ Dw W.hstar) (a + 1) S)
  (hσ : tateRep (Ecurve ℓ) 2 (σ * σ) = 1)
  (emb : DatumEmbeddings (Ecurve ℓ) f Lat κ W.hstar)
  (b : TateMod (qtwist (Ecurve ℓ) (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
  (hstages : withStages W q W.prepared = W)

/-- The corresponding `ev` for the odd models is the `ev` of these evaluations. -/
def actualForStages : Evaluations (Ecurve ℓ) f Lat κ W.hstar W.Mθ (stageTest q) :=
  actualEvaluationsOn (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl dat w hQw q hσ emb b
    (congrArg (fun V : WData ℓ => V.Mθ) hstages.symm)

/-- The witness agreement field for `actualForStages.ev`. -/
theorem actualForStages_at_witness (i : ℕ) :
    (actualForStages W dat w hQw q hσ emb b hstages).ev i Dw dat =
      actualStageMapOn (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl dat w hQw q hσ b
        (congrArg (fun V : WData ℓ => V.Mθ) hstages.symm) i Dw dat :=
  actualEvaluationsOn_at_witness (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl dat w hQw q hσ emb b
    (congrArg (fun V : WData ℓ => V.Mθ) hstages.symm) i

section Admissible

variable {At : ℕ → ℕ → Prop} {cw : ℕ} {B : Finset ℕ} {s : StageSequence At cw B}

omit [(Ecurve ℓ).IsElliptic] in
/-- Every parameter at which the comparison reads `ev` passes the inert-place test. -/
theorem admissible_stageTest (hs : withStages W s W.prepared = W) {i : ℕ} {D : ℤ}
    (hD : W.admissible i D) : stageTest s i D :=
  (show W.prepared D ∧ stageTest s i D from
    (congrArg (fun V : WData ℓ => V.admissible i D) hs).mpr hD).2

end Admissible

variable (selG : (D : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (D * W.hstar) 1 W.hstar))

/-- What `hcore` reads at an admissible parameter: the integer representative of
`b(κ_{M_θ}(reduction(L • P_D)))`, with the same evaluation for each summand
available from `Evaluations.ev_of_support`. This applies in particular at every
nonwitness parameter, without a simple-zero hypothesis. -/
theorem lamOf_admissible {i : ℕ} {D : ℤ}
    (t : HeegnerDatum (Ecurve ℓ) f Lat κ (D * W.hstar) 1 W.hstar)
    (ht : selG D = some t) (hD : W.admissible i D) :
    letI := t.field; letI := t.nf; letI := t.nz
    letI := Classical.decEq (ringClassField (CST.conductorOrder t.K 1))
    let K := actualForStages W dat w hQw q hσ emb b hstages
    lamOf W.Mθ L selG K.ev i D =
      ((K.eval i (K.reduction i D t (admissible_stageTest W hstages hD) (L • genusPoint t))).val : ℤ) :=
  (actualForStages W dat w hQw q hσ emb b hstages).lamOf_eq selG i t
    (admissible_stageTest W hstages hD) ht

/-- Appendix F (O.2) for the same total map used by the comparison. -/
theorem witnessValuation_actualForStages
    (d : DivisionTower (qtwist (Ecurve ℓ) (Dw : ℚ)) Q)
    (hQ : ∀ g : GalQ, Affine.Point.map (W' := qtwist (Ecurve ℓ) (Dw : ℚ)) g.toAlgHom Q = Q)
    (hDw : W.prepared Dw) (hdat : selG Dw = some dat)
    (hvalue : b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1)) :
    WitnessValuation W
      (lamOf W.Mθ L selG (actualForStages W dat w hQw q hσ emb b hstages).ev) Dw (a + 1) := by
  have key : ∀ (V : WData ℓ), withStages W q W.prepared = V →
      ∀ ev : StageKummer (Ecurve ℓ) f Lat κ W.hstar V.Mθ,
      WitnessSpecialization (L := L) dat ev d hQ
        (fun i => (selectedFrobenius q i).val) (finiteRow b) →
      WitnessValuation V (lamOf V.Mθ L selG ev) Dw (a + 1) := by
    intro V hV
    subst hV
    intro ev hred
    exact witnessValuation_withStages W d hQ q hDw selG dat hdat ev b hvalue hred
  exact key W hstages (actualForStages W dat w hQw q hσ emb b hstages).ev
    (actualEvaluationsOn_spec (EcurveZ ℓ) (EcurveZ_baseChange ℓ) rfl rfl dat w hQw q hσ emb b
      (congrArg (fun V : WData ℓ => V.Mθ) hstages.symm) d hQ)

#print axioms actualForStages_at_witness
#print axioms admissible_stageTest
#print axioms lamOf_admissible
#print axioms witnessValuation_actualForStages

end ZInQ.Manuscript.RC.StageMap
