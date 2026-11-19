import ZInQKernel.Contrib.OneProof.RC.PM.Stage
import ZInQKernel.Contrib.OneProof.RC.StageMap.Consumers

/-! The detector of Appendix F is the finite row at the selected Frobenius
place, on the reduction of the integral equation (tex 2489–2497, 8432–8459).
The dependent identifications of the two interfaces are on-the-spot (c). -/

noncomputable section

open WeierstrassCurve TauCeti TauCeti.ClassFieldTheory IsLocalRing
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages
  ZInQ.Manuscript.RC.WitnessSpec ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Manuscript.RC.GlueSweep.Tate
open scoped WeierstrassCurve Classical

namespace ZInQ.Manuscript.RC.StageIdent

/-- The prime-field equation at the selected prime. -/
abbrev reducedEquation (C : WeierstrassCurve ℤ) (p : ℕ) :=
  C.map (Int.castRingHom (ZMod p))

theorem reducedEquation_elliptic (C : WeierstrassCurve ℤ) {p : ℕ} [Fact p.Prime]
    (hg : ¬ (p : ℤ) ∣ C.Δ) : (reducedEquation C p).IsElliptic := by
  rw [isElliptic_iff, map_Δ, eq_intCast, isUnit_iff_ne_zero]
  exact fun hz => hg ((ZMod.intCast_zmod_eq_zero_iff_dvd C.Δ p).mp hz)

section Row

variable {A : WeierstrassCurve ℚ} [A.IsElliptic] {M : ℕ} {g σ : GalQ}
variable (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2])

/-- The finite row is invariant under the selected Frobenius because it and the
detecting Galois element agree on the coordinates of the finite torsion. -/
theorem finiteRow_fixed_of_agree (hb : ∀ t, b (tateRep A 2 σ t) = b t)
    (ha : ∀ x ∈ torsField A M, g x = σ x) (t : TateModuleLevel 2 (GeomPoint A) M) :
    finiteRow b M (torsionFrob (Affine.Point.map (W' := A) g.toAlgHom) (2 ^ M) t) =
      finiteRow b M t := by
  obtain ⟨v, rfl⟩ := TateModule.proj_surjective
    (TateModule.tateModuleTransition_surjective_of_natCard (p := 2) (by decide)
      ((A⁄Qbar).natCard_tateModuleLevel (by norm_num : (2 : Qbar) ≠ 0))) M t
  have ht : torsionFrob (Affine.Point.map (W' := A) g.toAlgHom) (2 ^ M)
        (TateModule.proj M v) = TateModule.proj M (tateRep A 2 σ v) := by
    apply Subtype.ext
    exact (map_eq_of_eqOn_torsField A ha _).trans (coe_proj_tateRep A 2 σ v M).symm
  rw [ht, finiteRow_proj, finiteRow_proj, hb]

end Row


section Actual

variable (C : WeierstrassCurve ℤ) [(C⁄ℚ).IsElliptic]
  (h₁ : (C⁄ℚ).a₁ = 0) (h₃ : (C⁄ℚ).a₃ = 0)
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (C⁄ℚ)) :
    Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ}
  (dat : HeegnerDatum (C⁄ℚ) f Lat κ (Dw * hstar) 1 hstar)
  {L : ℕ} (w : ExactWitnessOn (C⁄ℚ) h₁ h₃ dat L)
  [(qtwist (C⁄ℚ) (Dw : ℚ)).IsElliptic] {a : ℕ} {S : Finset ℕ}
  {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
  (q : StageSequence (ActualAt (qtwist (C⁄ℚ) (Dw : ℚ)) (C⁄ℚ)
    (rationalGeomPoint (qtwist (C⁄ℚ) (Dw : ℚ)) w.rational) F₀ σ Dw hstar) (a + 1) S)
  (hσ : tateRep (C⁄ℚ) 2 (σ * σ) = 1)
  (b : TateMod (qtwist (C⁄ℚ) (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
  (hb : ∀ t, b (tateRep (qtwist (C⁄ℚ) (Dw : ℚ)) 2 σ t) = b t)
  (i : ℕ)

include q in
theorem selectedCurve_elliptic :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    (reducedEquation C (q.stage i).p).IsElliptic := by
  let : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  exact reducedEquation_elliptic C (stage_facts C h₁ h₃ dat w q i).2.1

/-- Geometric residue field of the place attached to a Frobenius witness. -/
abbrev residueAt {g : GalQ} {p : ℕ} [Fact p.Prime]
    (hg : ZInQ.Contrib.ChebFD.C10.IsFrobAt g p) :=
  ResidueField (FrobeniusPlace.ofIsFrobAt hg).valuationRing.valuation.valuationSubring

/-- Appendix F's row is obtained by inverse torsion specialization at the chosen
place, with the fixed row from the detecting sequence reduced modulo its precision. -/
def selectedEvaluation :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    PM.Evaluation (residueAt (selectedFrobenius q i).property.1)
      (reducedEquation C (q.stage i).p) (a + 1 + 1 + i) := by
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  let s := actualLocalStage C h₁ h₃ dat w q hσ i
  let n := 2 ^ (a + 1 + 1 + i)
  let g := (selectedFrobenius q i).val
  let r := Affine.Point.map (W' := qtwist (C⁄ℚ) (Dw : ℚ)) g.toAlgHom
  let e := AddEquiv.ofBijective (torsionMap n s.red) s.torsion_bijective
  let row := finiteRow b (a + 1 + 1 + i)
  refine ⟨(stage_facts C h₁ h₃ dat w q i).1,
    frob_sq_on_reduced_torsion n s.red r s.frob s.equivariant s.sq_torsion s.torsion_bijective,
    row.comp e.symm.toAddMonoidHom, ?_⟩
  intro t
  change row (e.symm (torsionFrob s.frob n t)) = row (e.symm t)
  obtain ⟨x, rfl⟩ := e.surjective t
  have he : torsionFrob s.frob n (e x) = e (torsionFrob r n x) :=
    Subtype.ext (s.equivariant x.val).symm
  rw [he, e.symm_apply_apply, e.symm_apply_apply]
  apply finiteRow_fixed_of_agree b hb
  intro z hz
  exact (selectedFrobenius q i).property.2 z
    ((show torsField (qtwist (C⁄ℚ) (Dw : ℚ)) (a + 1 + 1 + i) ≤
      jointField _ _ F₀ (rationalGeomPoint _ w.rational) _ from
      le_sup_right.trans le_sup_left) hz)

variable (emb : StageMap.DatumEmbeddings (C⁄ℚ) f Lat κ hstar)

/-- The App F map and the evaluation component of the actual genus maps are the
same additive map on the quadratic residue points. -/
theorem selectedEvaluation_lam :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    letI := selectedCurve_elliptic C h₁ h₃ dat w q i
    PM.lam (selectedEvaluation C h₁ h₃ dat w q hσ b hb i) =
      (StageMap.actualEvaluations C h₁ h₃ dat w q hσ emb b).eval i := by
  ext P
  rfl

end Actual

section Transport

variable {E : WeierstrassCurve ℚ} (C : WeierstrassCurve ℤ) (hE : C⁄ℚ = E)
  [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) :
    Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
  {L : ℕ} (w : ExactWitnessOn E h₁ h₃ dat L) [(qtwist E (Dw : ℚ)).IsElliptic]
  {Q : GeomPoint (qtwist E (Dw : ℚ))}
  (hQw : Q = rationalGeomPoint (qtwist E (Dw : ℚ)) w.rational)
  {a : ℕ} {S : Finset ℕ} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
  (q : StageSequence (ActualAt (qtwist E (Dw : ℚ)) E Q F₀ σ Dw hstar) (a + 1) S)
  (hσ : tateRep E 2 (σ * σ) = 1)
  (b : TateMod (qtwist E (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
  (hb : ∀ t, b (tateRep (qtwist E (Dw : ℚ)) 2 σ t) = b t)
  {Mθ : ℕ → ℕ} (hM : Mθ = fun i => a + 1 + 1 + i)
  (i : ℕ)

include hE hQw in
theorem selectedCurveOn_elliptic :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    (reducedEquation C (q.stage i).p).IsElliptic := by
  subst hE hQw
  exact selectedCurve_elliptic C h₁ h₃ dat w q i

/-- The detector at the skeleton's precision, over the very same residue field. -/
def selectedEvaluationOn :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    PM.Evaluation (residueAt (selectedFrobenius q i).property.1)
      (reducedEquation C (q.stage i).p) (Mθ i) := by
  subst hE hQw hM
  exact selectedEvaluation C h₁ h₃ dat w q hσ b hb i

variable (emb : StageMap.DatumEmbeddings E f Lat κ hstar)

/-- Identification with the stage-map evaluation after exactly the transports
used by `StageMap.actualForStages`. Eliminating the transports gives equality
of additive maps, not just agreement at a witness point. -/
theorem selectedEvaluationOn_lam :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    letI := selectedCurveOn_elliptic C hE h₁ h₃ dat w hQw q i
    HEq (PM.lam (selectedEvaluationOn C hE h₁ h₃ dat w hQw q hσ b hb hM i))
      ((StageMap.actualEvaluationsOn C hE h₁ h₃ dat w hQw q hσ emb b hM).eval i) := by
  subst hE hQw hM
  exact heq_of_eq (selectedEvaluation_lam C h₁ h₃ dat w q hσ b hb i emb)

end Transport

#print axioms reducedEquation_elliptic
#print axioms finiteRow_fixed_of_agree
#print axioms selectedCurve_elliptic
#print axioms selectedEvaluation
#print axioms selectedEvaluation_lam
#print axioms selectedCurveOn_elliptic
#print axioms selectedEvaluationOn
#print axioms selectedEvaluationOn_lam

end ZInQ.Manuscript.RC.StageIdent
