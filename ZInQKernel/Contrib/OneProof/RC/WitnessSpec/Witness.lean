import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Evaluation

/-! The exact evaluation at the selected conductor-one witness. This assembles
the existing stage-map and valuation interfaces without changing either. -/

noncomputable section

open scoped WeierstrassCurve
open WeierstrassCurve TauCeti ZInQ.Manuscript.RC.PrintsArith
  ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Visibility
  ZInQ.Manuscript.RC.Wiring ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.WitnessSpec

/-- Local geometry needed by the Kummer calculation. The reduction from the twist
includes the split identification on the special fiber. -/
structure LocalStage (A : WeierstrassCurve ℚ) (M : ℕ) (g : GalQ) where
  Points : Type
  group : AddCommGroup Points
  red : GeomPoint A →+ Points
  frob : Points →+ Points
  equivariant : ∀ R, red (Affine.Point.map (W' := A) g.toAlgHom R) = frob (red R)
  sq_torsion : ∀ T : GeomPoint A, (2 ^ M : ℕ) • T = 0 →
    Affine.Point.map (W' := A) g.toAlgHom (Affine.Point.map (W' := A) g.toAlgHom T) = T
  torsion_bijective : Function.Bijective (torsionMap (2 ^ M) red)
  div_surjective : Function.Surjective (fun R : Points => (2 ^ M : ℕ) • R)

attribute [instance] LocalStage.group

section
variable {A E : WeierstrassCurve ℚ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) :
    Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} {L : ℕ} {Mθ : ℕ → ℕ} {g : ℕ → GalQ}
  (s : ∀ i, LocalStage A (Mθ i) (g i))

/-- A specialization for each datum on which quadratic residue descent applies.
The stage interface is total; on data outside the supplied domain it is extended
by zero. -/
abbrev DatumReductions :=
  ∀ (i : ℕ) (D : ℤ) (dat : HeegnerDatum E f Lat κ (D * hstar) 1 hstar),
    letI := dat.field; letI := dat.nf; letI := dat.nz
    letI := Classical.decEq (TauCeti.ClassFieldTheory.ringClassField
      (CST.conductorOrder dat.K 1))
    Option ((E.baseChange (TauCeti.ClassFieldTheory.ringClassField
      (CST.conductorOrder dat.K 1))).toAffine.Point →+ FixedSq (s i).frob)

/-- Compose the supplied datum reductions with the actual finite Kummer map
and the row. No change to `StageKummer` is needed. -/
def stageKummer (r : DatumReductions (E := E) (f := f) (Lat := Lat) (κ := κ) (hstar := hstar) s)
    (row : ∀ M, TateModuleLevel 2 (GeomPoint A) M →+ ZMod (2 ^ M)) :
    StageKummer E f Lat κ hstar Mθ :=
  fun i D dat => by
    letI := dat.field
    letI := dat.nf
    letI := dat.nz
    letI := Classical.decEq (TauCeti.ClassFieldTheory.ringClassField (CST.conductorOrder dat.K 1))
    let H := TauCeti.ClassFieldTheory.ringClassField (CST.conductorOrder dat.K 1)
    change (E⁄H).toAffine.Point →+ ZMod (2 ^ Mθ i)
    exact match r i D dat with
    | none => 0
    | some red =>
      stageMap (G := (E⁄H).toAffine.Point) (2 ^ Mθ i) (s i).red (Affine.Point.map (W' := A) (g i).toAlgHom) (s i).frob
        (s i).equivariant (s i).sq_torsion (s i).torsion_bijective (s i).div_surjective
        (row (Mθ i)) red

/-- For an actual family of local models and a reduction of the selected scaled genus
point agreeing with the rational twist, the identity is exactly `WitnessSpecialization`. -/
theorem witnessSpecialization_of_reductions
    (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
    (r : DatumReductions (E := E) (f := f) (Lat := Lat) (κ := κ) (hstar := hstar) s)
    {Q : GeomPoint A} (d : DivisionTower A Q)
    (hQ : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom Q = Q)
    (row : ∀ M, TateModuleLevel 2 (GeomPoint A) M →+ ZMod (2 ^ M))
    (hmatch : ∀ i, letI := dat.field; letI := dat.nf; letI := dat.nz
      letI := Classical.decEq (TauCeti.ClassFieldTheory.ringClassField
        (CST.conductorOrder dat.K 1))
      ∃ red, r i Dw dat = some red ∧ (red (L • genusPoint dat)).val = (s i).red Q) :
    WitnessSpecialization (L := L) dat (stageKummer s r row) d hQ g row := by
  intro i
  let := dat.field
  let := dat.nf
  let := dat.nz
  let := Classical.decEq (TauCeti.ClassFieldTheory.ringClassField (CST.conductorOrder dat.K 1))
  obtain ⟨red, hred, hP⟩ := hmatch i
  unfold stageKummer
  rw [hred]
  refine stageMap_apply_division (2 ^ Mθ i) (s i).red
    (Affine.Point.map (W' := A) (g i).toAlgHom) (s i).frob (s i).equivariant
    (s i).sq_torsion (s i).torsion_bijective (s i).div_surjective
    (row (Mθ i)) red (L • genusPoint dat) Q (d.point (Mθ i)) (d.divides _) hP.symm _ ?_
  rw [d.coe_proj_cocycle, Affine.Point.map_map]
  rfl

end

/-- The exact valuation at the selected datum, using the unchanged stage sequence
and reading the canonical integer representative only after specialization. -/
theorem witnessValuation_of_reductions {ℓ : ℕ} (W : WData ℓ)
    {A E : WeierstrassCurve ℚ} [A.IsElliptic] [E.IsElliptic]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} {L a : ℕ} {S : Finset ℕ}
    {Q : GeomPoint A} (d : DivisionTower A Q) (hQ)
    {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
    (q : StageSequence (ActualAt A E Q F₀ σ Dw hstar) (a + 1) S)
    {prepared : ℤ → Prop} (hp : prepared Dw)
    (selG : (D : ℤ) → Option (HeegnerDatum E f Lat κ (D * hstar) 1 hstar))
    (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar) (hdat : selG Dw = some dat)
    (s : ∀ i, LocalStage A ((withStages W q prepared).Mθ i) (selectedFrobenius q i).val)
    (r : DatumReductions (E := E) (f := f) (Lat := Lat) (κ := κ) (hstar := hstar) s)
    (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2])
    (hvalue : b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1))
    (hmatch : ∀ i, letI := dat.field; letI := dat.nf; letI := dat.nz
      letI := Classical.decEq (TauCeti.ClassFieldTheory.ringClassField
        (CST.conductorOrder dat.K 1))
      ∃ red, r i Dw dat = some red ∧ (red (L • genusPoint dat)).val = (s i).red Q) :
    WitnessValuation (withStages W q prepared)
      (lamOf (withStages W q prepared).Mθ L selG (stageKummer s r (finiteRow b))) Dw (a + 1) :=
  witnessValuation_withStages W d hQ q hp selG dat hdat (stageKummer s r (finiteRow b)) b hvalue
    (witnessSpecialization_of_reductions s dat r d hQ (finiteRow b) hmatch)

#print axioms LocalStage
#print axioms DatumReductions
#print axioms stageKummer
#print axioms witnessSpecialization_of_reductions
#print axioms witnessValuation_of_reductions

end ZInQ.Manuscript.RC.WitnessSpec
