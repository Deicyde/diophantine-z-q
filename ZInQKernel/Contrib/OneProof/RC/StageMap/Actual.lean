import ZInQKernel.Contrib.OneProof.RC.Wiring.StageWitness

/-! The geometric side of the Appendix F stage evaluation (tex 8378–8398, 8439–8456,
9205–9209, 9270–9291). Use one absolute Frobenius place and one finite torsion
identification at each stage. Only the restriction of that place to the datum's
ring class field varies. The dependent packaging and the simultaneous choices
of field embeddings are on-the-spot (c). -/

noncomputable section

open NumberField WeierstrassCurve TauCeti TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages
  ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.WitnessSpec
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped WeierstrassCurve

namespace ZInQ.Manuscript.RC.StageMap

section Interface

variable {E : WeierstrassCurve ℚ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar : ℤ}

/-- Realize each datum's field inside the algebraic closure carrying the stage places.
These choices can also be used by the geometric comparison; they do not depend on the stage. -/
abbrev DatumEmbeddings (E : WeierstrassCurve ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) (hstar : ℤ) :=
  ∀ (D : ℤ) (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar),
    letI := t.field; letI := t.nf; letI := t.nz
    ringClassField (CST.conductorOrder t.K 1) →ₐ[ℚ] Qbar

/-- Field embeddings are choices, not existence hypotheses. -/
def chooseDatumEmbeddings : DatumEmbeddings E f Lat κ hstar := fun _ t =>
  letI := t.field; letI := t.nf; letI := t.nz
  IsAlgClosed.lift

variable {h₁ : E.a₁ = 0} {h₃ : E.a₃ = 0} {Dw : ℤ}
  {dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar} {L : ℕ}

/-- Use the already chosen witness embedding at its one entry. -/
def anchoredEmbeddings (w : ExactWitnessOn E h₁ h₃ dat L)
    (emb : DatumEmbeddings E f Lat κ hstar) : DatumEmbeddings E f Lat κ hstar := by
  intro D t
  by_cases hD : D = Dw
  · subst D
    by_cases ht : t = dat
    · subst t
      exact w.emb
    · exact emb Dw t
  · exact emb D t

@[simp] theorem anchoredEmbeddings_witness (w : ExactWitnessOn E h₁ h₃ dat L)
    (emb : DatumEmbeddings E f Lat κ hstar) :
    anchoredEmbeddings w emb Dw dat = w.emb := by
  simp [anchoredEmbeddings]

/-- The two operations whose composite is read by the comparison, with a common
quadratic fixed group at each stage. The actual construction below instantiates
both fields, including under transport of the integral model and the precision. -/
structure Evaluations (E : WeierstrassCurve ℚ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2)
    (Lat : PeriodPair) (κ : ℂ) (hstar : ℤ) (Mθ : ℕ → ℕ) (support : ℕ → ℤ → Prop) where
  QuadraticPoints : ℕ → Type
  [group : ∀ i, AddCommGroup (QuadraticPoints i)]
  reduction : ∀ i D (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar), support i D →
    letI := t.field; letI := t.nf; letI := t.nz
    letI := Classical.decEq (ringClassField (CST.conductorOrder t.K 1))
    (E⁄(ringClassField (CST.conductorOrder t.K 1))).toAffine.Point →+ QuadraticPoints i
  eval : ∀ i, QuadraticPoints i →+ ZMod (2 ^ Mθ i)

attribute [instance] Evaluations.group

namespace Evaluations

variable {Mθ : ℕ → ℕ} {support : ℕ → ℤ → Prop}
  (K : Evaluations E f Lat κ hstar Mθ support)

/-- Total stage interface. Off the inert support, the comparison does not use
this entry and the extension is zero, without any reduction claim there. -/
def ev : StageKummer E f Lat κ hstar Mθ := by
  classical
  intro i D t
  letI := t.field; letI := t.nf; letI := t.nz
  letI := Classical.decEq (ringClassField (CST.conductorOrder t.K 1))
  exact if h : support i D then (K.eval i).comp (K.reduction i D t h) else 0

theorem ev_of_support (i : ℕ) (D : ℤ) (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar)
    (h : support i D) :
    letI := t.field; letI := t.nf; letI := t.nz
    letI := Classical.decEq (ringClassField (CST.conductorOrder t.K 1))
    K.ev i D t = (K.eval i).comp (K.reduction i D t h) := by
  unfold ev
  exact dite_eq_left h

/-- The integer representative is taken only after reduction, Kummer and the row. -/
theorem lamOf_eq (selG : (D : ℤ) → Option (HeegnerDatum E f Lat κ (D * hstar) 1 hstar))
    (i : ℕ) {D : ℤ} (t : HeegnerDatum E f Lat κ (D * hstar) 1 hstar)
    (h : support i D) (ht : selG D = some t) :
    letI := t.field; letI := t.nf; letI := t.nz
    letI := Classical.decEq (ringClassField (CST.conductorOrder t.K 1))
    lamOf Mθ L selG K.ev i D =
      ((K.eval i (K.reduction i D t h (L • genusPoint t))).val : ℤ) := by
  simp only [lamOf, ht, kummerLift, genusPoint, K.ev_of_support i D t h, AddMonoidHom.comp_apply]

end Evaluations
end Interface

/-- The finite row on the residue torsion is the global row transported through
inverse torsion specialization; the preceding Kummer map uses squared arithmetic
Frobenius and the unchanged convention `F² R − R`. -/
def reducedRead {A : WeierstrassCurve ℚ} {M : ℕ} {g : GalQ} (s : LocalStage A M g)
    (row : TateModuleLevel 2 (GeomPoint A) M →+ ZMod (2 ^ M)) :
    FixedSq s.frob →+ ZMod (2 ^ M) :=
  stageMap (2 ^ M) s.red (Affine.Point.map (W' := A) g.toAlgHom) s.frob s.equivariant
    s.sq_torsion s.torsion_bijective s.div_surjective row (AddMonoidHom.id _)

section Integral

variable (C : WeierstrassCurve ℤ) [(C⁄ℚ).IsElliptic] (h₁ : (C⁄ℚ).a₁ = 0) (h₃ : (C⁄ℚ).a₃ = 0)
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (C⁄ℚ)) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} (dat : HeegnerDatum (C⁄ℚ) f Lat κ (Dw * hstar) 1 hstar)
  {L : ℕ} (w : ExactWitnessOn (C⁄ℚ) h₁ h₃ dat L)
  [(qtwist (C⁄ℚ) (Dw : ℚ)).IsElliptic] {a : ℕ} {S : Finset ℕ}
  {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
  (q : StageSequence (ActualAt (qtwist (C⁄ℚ) (Dw : ℚ)) (C⁄ℚ)
    (rationalGeomPoint (qtwist (C⁄ℚ) (Dw : ℚ)) w.rational) F₀ σ Dw hstar) (a + 1) S)
  (hσ : tateRep (C⁄ℚ) 2 (σ * σ) = 1)

/-- The same absolute place used in `actualLocalStage` and `actualRingClassRed`. -/
abbrev selectedPlace (i : ℕ) : FrobeniusPlace (selectedFrobenius q i).val (q.stage i).p :=
  FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1

/-- Tex 9205–9209: the moving split test on `D` and the fixed nonsplit sign
of `h_*` give the unramified inert case for every datum of `D`. -/
theorem stage_disc_of_test (i : ℕ) {D : ℤ} (t : HeegnerDatum (C⁄ℚ) f Lat κ (D * hstar) 1 hstar)
    (h : stageTest q i D) :
    letI := t.field; letI := t.nf
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    ¬ ((q.stage i).p : ℤ) ∣ discr t.K ∧ legendreSym (q.stage i).p (discr t.K) = -1 := by
  let := t.field; let := t.nf
  let : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  have hplus : legendreSym (q.stage i).p D = 1 := h
  have hsign : legendreSym (q.stage i).p (discr t.K) = -1 := by
    rw [t.disc, legendreSym.mul, hplus, (stage_facts C h₁ h₃ dat w q i).2.2.2.2.2, one_mul]
  refine ⟨fun hd => ?_, hsign⟩
  have hz := (legendreSym.eq_zero_iff (q.stage i).p (discr t.K)).mpr
    ((ZMod.intCast_zmod_eq_zero_iff_dvd (discr t.K) (q.stage i).p).mpr hd)
  rw [hsign] at hz
  exact (by decide : (-1 : ℤ) ≠ 0) hz

variable (emb : DatumEmbeddings (C⁄ℚ) f Lat κ hstar)

/-- Contract the selected place to the ring class field. At conductor one the
inert base prime is principal, so the contracted residue has order `p²`.
`ringClassReduction` uses exactly this residue field inside the absolute one. -/
def ringClassRed (i : ℕ) {D : ℤ} (t : HeegnerDatum (C⁄ℚ) f Lat κ (D * hstar) 1 hstar)
    (h : stageTest q i D) :
    letI := t.field; letI := t.nf; letI := t.nz
    letI := Classical.decEq (ringClassField (CST.conductorOrder t.K 1))
    ((C⁄ℚ)⁄(ringClassField (CST.conductorOrder t.K 1))).toAffine.Point →+
      FixedSq (actualLocalStage C h₁ h₃ dat w q hσ i).frob :=
  letI := t.field; letI := t.nf; letI := t.nz
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  let hd := stage_disc_of_test C h₁ h₃ dat w q i t h
  (selectedPlace C h₁ h₃ dat w q i).ringClassReduction C (anchoredEmbeddings w emb D t)
    t.finrank_two hd.1 hd.2 (stage_facts C h₁ h₃ dat w q i).2.1

/-- A point reduced by `ringClassRed` is the actual geometric reduction of
the embedded point at the chosen absolute place (tex 9270–9277). -/
theorem ringClassRed_agrees (i : ℕ) {D : ℤ}
    (t : HeegnerDatum (C⁄ℚ) f Lat κ (D * hstar) 1 hstar) (h : stageTest q i D)
    (P : letI := t.field; letI := t.nf; letI := t.nz
      ((C⁄ℚ)⁄(ringClassField (CST.conductorOrder t.K 1))).toAffine.Point) :
    letI := t.field; letI := t.nf; letI := t.nz
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    letI := Classical.decEq (ringClassField (CST.conductorOrder t.K 1))
    (ringClassRed C h₁ h₃ dat w q hσ emb i t h P).val =
      (selectedPlace C h₁ h₃ dat w q i).curveReduction C (stage_facts C h₁ h₃ dat w q i).2.1
        (Affine.Point.map (W' := C⁄ℚ) (anchoredEmbeddings w emb D t) P) := by
  let := t.field; let := t.nf; let := t.nz
  let : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  let hd := stage_disc_of_test C h₁ h₃ dat w q i t h
  exact (selectedPlace C h₁ h₃ dat w q i).ringClassReduction_agrees C
    (stage_facts C h₁ h₃ dat w q i).2.1 (anchoredEmbeddings w emb D t) t.finrank_two hd.1 hd.2 P

variable (b : TateMod (qtwist (C⁄ℚ) (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])

/-- The actual `b ∘ κ` at each stage, preceded by reduction at every datum of
every parameter on that stage's inert support. -/
def actualEvaluations :
    Evaluations (C⁄ℚ) f Lat κ hstar (fun i => a + 1 + 1 + i) (stageTest q) where
  QuadraticPoints i := FixedSq (actualLocalStage C h₁ h₃ dat w q hσ i).frob
  group _ := inferInstance
  reduction i _ t h := ringClassRed C h₁ h₃ dat w q hσ emb i t h
  eval i := reducedRead (actualLocalStage C h₁ h₃ dat w q hσ i) (finiteRow b (a + 1 + 1 + i))

/-- Compatibility of the total evaluation with the selected witness entry. -/
theorem actualEvaluations_at_witness (i : ℕ) :
    (actualEvaluations C h₁ h₃ dat w q hσ emb b).ev i Dw dat =
      actualStageMap C h₁ h₃ dat w q hσ b i Dw dat := by
  let := dat.field; let := dat.nf; let := dat.nz
  let := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
  rw [Evaluations.ev_of_support _ i Dw dat (witness_on_stages q i)]
  have he : ringClassRed C h₁ h₃ dat w q hσ emb i dat (witness_on_stages q i) =
      actualRingClassRed C h₁ h₃ dat w q hσ i := by
    let : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    unfold ringClassRed actualRingClassRed
    simp only [anchoredEmbeddings_witness, selectedPlace]
    rfl
  change (reducedRead (actualLocalStage C h₁ h₃ dat w q hσ i) (finiteRow b (a + 1 + 1 + i))).comp
    (ringClassRed C h₁ h₃ dat w q hσ emb i dat (witness_on_stages q i)) = _
  rw [he]
  unfold actualStageMap stageKummer
  rw [witnessReductions_at_witness]
  rfl

end Integral

section Transport

variable {E : WeierstrassCurve ℚ} (C : WeierstrassCurve ℤ) (hE : C⁄ℚ = E)
  [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
  {L : ℕ} (w : ExactWitnessOn E h₁ h₃ dat L) [(qtwist E (Dw : ℚ)).IsElliptic]
  {Q : GeomPoint (qtwist E (Dw : ℚ))}
  (hQw : Q = rationalGeomPoint (qtwist E (Dw : ℚ)) w.rational)
  {a : ℕ} {S : Finset ℕ} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
  (q : StageSequence (ActualAt (qtwist E (Dw : ℚ)) E Q F₀ σ Dw hstar) (a + 1) S)
  (hσ : tateRep E 2 (σ * σ) = 1) (emb : DatumEmbeddings E f Lat κ hstar)
  (b : TateMod (qtwist E (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
  {Mθ : ℕ → ℕ} (hM : Mθ = fun i => a + 1 + 1 + i)

/-- Transport the two operations together so that the comparison can still name
the reduction and finite read separately on `E` and the interface precision. -/
def actualEvaluationsOn : Evaluations E f Lat κ hstar Mθ (stageTest q) := by
  subst hE hQw hM
  exact actualEvaluations C h₁ h₃ dat w q hσ emb b

/-- The `hev` field of `OddStagedInstance` for the actual total map. -/
theorem actualEvaluationsOn_at_witness (i : ℕ) :
    (actualEvaluationsOn C hE h₁ h₃ dat w hQw q hσ emb b hM).ev i Dw dat =
      actualStageMapOn C hE h₁ h₃ dat w hQw q hσ b hM i Dw dat := by
  subst hE hQw hM
  exact actualEvaluations_at_witness C h₁ h₃ dat w q hσ emb b i

/-- Witness specialization for the total stage map, obtained through `hev`. -/
theorem actualEvaluationsOn_spec (d : DivisionTower (qtwist E (Dw : ℚ)) Q)
    (hQ : ∀ g : GalQ, Affine.Point.map (W' := qtwist E (Dw : ℚ)) g.toAlgHom Q = Q) :
    WitnessSpecialization (L := L) dat (actualEvaluationsOn C hE h₁ h₃ dat w hQw q hσ emb b hM).ev
      d hQ (fun i => (selectedFrobenius q i).val) (finiteRow b) :=
  witnessSpecialization_of_agree (actualEvaluationsOn_at_witness C hE h₁ h₃ dat w hQw q hσ emb b hM)
    (actualStageMapOn_spec C hE h₁ h₃ dat w hQw d hQ q hσ b hM)

end Transport

#print axioms anchoredEmbeddings_witness
#print axioms Evaluations.ev_of_support
#print axioms Evaluations.lamOf_eq
#print axioms stage_disc_of_test
#print axioms ringClassRed_agrees
#print axioms actualEvaluations_at_witness
#print axioms actualEvaluationsOn_at_witness
#print axioms actualEvaluationsOn_spec

end ZInQ.Manuscript.RC.StageMap
