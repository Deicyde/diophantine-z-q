import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Specialize

/-!
**Theorem 5.3, Lane RC0 round 8: the actual stage map at the selected witness datum.**

The witness specialization of `RC/WitnessSpec` builds, at the selected conductor-one datum of the
fixed witness `D_w`, the stage map of tex 8378–8398 and 8439–8456: at stage `θ`, reduction at the
place of the selected Frobenius (the ring class reduction into the square-fixed group,
`FrobeniusPlace.ringClassReduction`), the finite Kummer map, the inverse torsion specialization
through the split twist by the witness root (`FrobeniusPlace.localStage`) and the fixed integral
row (`stageMap`, `stageKummer`). There it is packaged existentially (`actualWitness`). This file
names it, so that lane RC0's odd instance can ask its own stage maps to BE that map at the selected
datum, and leaves every other entry of the stage maps free:

* `EcurveZ`, `EcurveZ_baseChange` (definition, PROVED): the integral model of `E_ℓ`;
* `ExactWitnessOn` (definition): the exact rational witness of the global twist comparison (tex
  2462–2466, 8295–8306: a rational point `R` of `A = E^{(D_w)}` whose twist is `L P_{D_w}`, with
  the root of `D_w` and an embedding of the ring class field) on a curve over `ℚ`; on `C⁄ℚ` it is
  the construction's `ExactWitness` (`ExactWitnessOn.toExactWitness`);
* `actualLocalStage`, `actualRingClassRed`, `actualStageMap` (definitions): the construction's
  local stage and ring class reduction at the selected Frobenius place of each stage, and the stage
  map they give; it is read only at the selected datum (the construction extends it by zero
  elsewhere, and that extension is never asked to agree with anything);
* `actualRingClassRed_match`, `actualStageMap_spec` (PROVED, the argument of `actualWitness`: the
  two reductions agree on `L P_{D_w}` at the chosen place, and `witnessSpecialization_of_reductions`):
  `WitnessSpecialization` for the actual stage map;
* `actualStageMapOn`, `actualStageMapOn_spec` (definition, PROVED): the same on a curve with an
  integral model, at a witness point equal to the exact witness's rational point and at a
  precision equal to `a + 2 + θ`;
* `witnessSpecialization_of_agree` (PROVED): `WitnessSpecialization` reads a stage map only at the
  selected datum.
-/

noncomputable section

open NumberField WeierstrassCurve TauCeti TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Nonvanishing
  ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.WitnessSpec
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped WeierstrassCurve

namespace ZInQ.Manuscript.RC.Wiring

/-- **The integral model of `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`** (definition; tex 1763). -/
def EcurveZ (ℓ : ℕ) : WeierstrassCurve ℤ := ⟨0, 2 * ℓ, 0, -3 * ℓ ^ 2, 0⟩

/-- Its base change to `ℚ` is `E_ℓ` (PROVED). -/
theorem EcurveZ_baseChange (ℓ : ℕ) : (EcurveZ ℓ)⁄ℚ = Ecurve ℓ := by
  simp only [EcurveZ, Ecurve, ZInQ.Manuscript.curve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, map_zero, map_mul, map_pow, map_neg, map_ofNat, map_natCast]

/-- **The exact witness** (definition; tex 2462–2466, 8295–8306), on a curve `E` over `ℚ` with
`a₁ = a₃ = 0`: an embedding of the conductor-one ring class field of the datum, a root of `D_w`
in it, and a rational point of `E^{(D_w)}` whose twist by that root is `L P_{D_w}` (the output of
the global twist comparison, before any stage choice). The same fields as `ExactWitness`. -/
structure ExactWitnessOn (E : WeierstrassCurve ℚ) (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ}
    {hstar Dw : ℤ} (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar) (L : ℕ) where
  /-- the embedding of the ring class field -/
  emb : letI := dat.field; letI := dat.nf; letI := dat.nz
    (ringClassField (CST.conductorOrder dat.K 1)) →ₐ[ℚ] Qbar
  /-- the root of `D_w` -/
  root : letI := dat.field; letI := dat.nf; letI := dat.nz
    ringClassField (CST.conductorOrder dat.K 1)
  nonzero : letI := dat.field; letI := dat.nf; letI := dat.nz; root ≠ 0
  square : letI := dat.field; letI := dat.nf; letI := dat.nz
    root ^ 2 = algebraMap ℚ (ringClassField (CST.conductorOrder dat.K 1)) (Dw : ℚ)
  /-- the rational point of `A = E^{(D_w)}` -/
  rational : Affine.Point (WeierstrassCurve.toAffine (qtwist E (Dw : ℚ)))
  /-- its twist is `L P_{D_w}` -/
  eq_scaled : letI := dat.field; letI := dat.nf; letI := dat.nz
    letI := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
    twistEmb E (Dw : ℚ) root (twistVC_smul E h₁ h₃ nonzero square) rational = L • genusPoint dat

section Exact

variable {E : WeierstrassCurve ℚ} {h₁ : E.a₁ = 0} {h₃ : E.a₃ = 0}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
  {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} {dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar}
  {L : ℕ} (w : ExactWitnessOn E h₁ h₃ dat L)

/-- The root of `D_w` of the exact witness, in `ℚ̄` (definition). -/
def ExactWitnessOn.qbarRoot : Qbar :=
  letI := dat.field; letI := dat.nf; letI := dat.nz
  w.emb w.root

theorem ExactWitnessOn.qbarRoot_ne_zero : w.qbarRoot ≠ 0 := by
  let := dat.field; let := dat.nf; let := dat.nz
  intro he
  exact w.nonzero (w.emb.injective (he.trans (map_zero w.emb).symm))

theorem ExactWitnessOn.qbarRoot_sq : w.qbarRoot ^ 2 = algebraMap ℚ Qbar (Dw : ℚ) := by
  let := dat.field; let := dat.nf; let := dat.nz
  change (w.emb w.root) ^ 2 = _
  rw [← map_pow, w.square, w.emb.commutes]

end Exact

/-- On `C⁄ℚ`, `ExactWitnessOn` is the construction's `ExactWitness` (definition). -/
def ExactWitnessOn.toExactWitness {C : WeierstrassCurve ℤ} [(C⁄ℚ).IsElliptic]
    {h₁ : (C⁄ℚ).a₁ = 0} {h₃ : (C⁄ℚ).a₃ = 0}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (C⁄ℚ)) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ}
    {dat : HeegnerDatum (C⁄ℚ) f Lat κ (Dw * hstar) 1 hstar} {L : ℕ}
    (w : ExactWitnessOn (C⁄ℚ) h₁ h₃ dat L) : ExactWitness C h₁ h₃ dat L :=
  ⟨w.emb, w.root, w.nonzero, w.square, w.rational, w.eq_scaled⟩

private theorem stage_disc_unit (C : WeierstrassCurve ℤ) {p : ℕ} [Fact p.Prime]
    (h : GoodAt (C⁄ℚ) p) : ¬ (p : ℤ) ∣ C.Δ := by
  obtain ⟨hn, hv⟩ := h.2.2.2.2.2
  have hΔ : (C⁄ℚ).Δ = (C.Δ : ℚ) := by
    rw [baseChange, WeierstrassCurve.map_Δ, eq_intCast]
  rw [hΔ, padicValRat.of_int] at hv
  intro hd
  have hh := (padicValInt_dvd_iff (p := p) 1 C.Δ).mp (by simpa only [pow_one] using hd)
  rcases hh with hzero | hpos
  · exact hn (by rw [hΔ, hzero, Int.cast_zero])
  · omega

private theorem stage_not_dvd {p : ℕ} [Fact p.Prime] {D : ℤ}
    (h : legendreSym p D ≠ 0) : ¬ (p : ℤ) ∣ D := by
  intro hd
  exact h ((legendreSym.eq_zero_iff p D).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hd))

section Actual

variable (C : WeierstrassCurve ℤ) [(C⁄ℚ).IsElliptic] (h₁ : (C⁄ℚ).a₁ = 0) (h₃ : (C⁄ℚ).a₃ = 0)
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (C⁄ℚ)) :
    Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ}
  {hstar Dw : ℤ} (dat : HeegnerDatum (C⁄ℚ) f Lat κ (Dw * hstar) 1 hstar)
  {L : ℕ} (w : ExactWitnessOn (C⁄ℚ) h₁ h₃ dat L)
  [(qtwist (C⁄ℚ) (Dw : ℚ)).IsElliptic] {a : ℕ} {S : Finset ℕ}
  {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
  (q : StageSequence (ActualAt (qtwist (C⁄ℚ) (Dw : ℚ)) (C⁄ℚ)
    (rationalGeomPoint (qtwist (C⁄ℚ) (Dw : ℚ)) w.rational) F₀ σ Dw hstar) (a + 1) S)
  (hσ : tateRep (C⁄ℚ) 2 (σ * σ) = 1)

/-- The arithmetic of stage `i` (PROVED from the stage's `ActualAt`): the prime is odd, of good
reduction for the integral model, prime to `D_w` and `h_*`, with `(D_w/p) = 1`, `(h_*/p) = −1`. -/
theorem stage_facts (i : ℕ) :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    (q.stage i).p ≠ 2 ∧ ¬ ((q.stage i).p : ℤ) ∣ C.Δ ∧ ¬ ((q.stage i).p : ℤ) ∣ Dw ∧
      ¬ ((q.stage i).p : ℤ) ∣ hstar ∧ legendreSym (q.stage i).p Dw = 1 ∧
      legendreSym (q.stage i).p hstar = -1 := by
  let : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  obtain ⟨_, _, hodd, hgood, _, _, _, _, _, _, hplus, hminus⟩ := (q.stage i).arithmetic
  exact ⟨hodd, stage_disc_unit C hgood,
    stage_not_dvd (hplus.symm ▸ (by decide : (1 : ℤ) ≠ 0)),
    stage_not_dvd (hminus.symm ▸ (by decide : (-1 : ℤ) ≠ 0)), hplus, hminus⟩

/-- The selected Frobenius fixes the witness root (PROVED: `(D_w/p) = 1`). -/
theorem stage_root_fixed (i : ℕ) : (selectedFrobenius q i).val w.qbarRoot = w.qbarRoot := by
  let : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  obtain ⟨hodd, -, hDw, -, hplus, -⟩ := stage_facts C h₁ h₃ dat w q i
  have hh := apply_sqrt_of_isFrobAt hodd (selectedFrobenius q i).property.1 hDw
    (show w.qbarRoot ^ 2 = (Dw : Qbar) by simpa only [map_intCast] using w.qbarRoot_sq)
  simpa only [hplus, one_zsmul] using hh

include hσ in
/-- The square of the selected Frobenius fixes the level torsion of the curve (PROVED: the
detecting element's square acts trivially on the Tate module, `actualStage_torsion_sq`). -/
theorem stage_sq_torsion (i : ℕ) (t : GeomPoint (C⁄ℚ))
    (ht : (2 ^ (a + 1 + 1 + i) : ℕ) • t = 0) :
    Affine.Point.map (W' := C⁄ℚ) (selectedFrobenius q i).val.toAlgHom
      (Affine.Point.map (W' := C⁄ℚ) (selectedFrobenius q i).val.toAlgHom t) = t := by
  rw [Affine.Point.map_map]
  exact actualStage_torsion_sq q i hσ ⟨t, AddSubgroup.torsionBy.nsmul_iff.mpr ht⟩

/-- **The actual local stage at stage `i`** (definition; tex 8362–8395): reduction at the place
of the selected Frobenius, composed with the split twist by the witness root. -/
def actualLocalStage (i : ℕ) :
    LocalStage (qtwist (C⁄ℚ) (Dw : ℚ)) (a + 1 + 1 + i) (selectedFrobenius q i).val :=
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  (FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1).localStage C
    (stage_facts C h₁ h₃ dat w q i).2.1 (stage_facts C h₁ h₃ dat w q i).1 (a + 1 + 1 + i) h₁ h₃
    (Dw : ℚ) w.qbarRoot w.qbarRoot_ne_zero w.qbarRoot_sq (stage_root_fixed C h₁ h₃ dat w q i)
    (stage_sq_torsion C h₁ h₃ dat w q hσ i)

/-- The stage prime is prime to the discriminant of the datum's field, where the Legendre symbol is
`−1` (PROVED: `disc K = D_w h_*`). -/
theorem stage_disc (i : ℕ) :
    letI := dat.field; letI := dat.nf; letI := dat.nz
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    ¬ ((q.stage i).p : ℤ) ∣ discr dat.K ∧ legendreSym (q.stage i).p (discr dat.K) = -1 := by
  let := dat.field; let := dat.nf; let := dat.nz
  let : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  obtain ⟨-, -, hDw, hhs, hplus, hminus⟩ := stage_facts C h₁ h₃ dat w q i
  refine ⟨?_, ?_⟩
  · rw [dat.disc]
    exact fun hh =>
      ((Nat.prime_iff_prime_int.mp (Fact.out : (q.stage i).p.Prime)).dvd_or_dvd hh).elim hDw hhs
  · rw [dat.disc, legendreSym.mul, hplus, hminus, one_mul]

/-- **The actual ring class reduction at stage `i`** (definition; tex 8394–8398, 8439–8446): the
reduction of `E(H)` at the place of the selected Frobenius, into the square-fixed group. -/
def actualRingClassRed (i : ℕ) :
    letI := dat.field; letI := dat.nf; letI := dat.nz
    letI := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
    ((C⁄ℚ)⁄(ringClassField (CST.conductorOrder dat.K 1))).toAffine.Point →+
      FixedSq (actualLocalStage C h₁ h₃ dat w q hσ i).frob :=
  letI := dat.field; letI := dat.nf; letI := dat.nz
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  (FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1).ringClassReduction C w.emb
    dat.finrank_two (stage_disc C h₁ h₃ dat w q i).1 (stage_disc C h₁ h₃ dat w q i).2
    (stage_facts C h₁ h₃ dat w q i).2.1

/-- **The two reductions agree on `L P_{D_w}`** (PROVED, the argument of `actualWitness`: the ring
class reduction is the absolute reduction at the same place, and the embedded twist of the exact
witness is its geometric twist with the same root). -/
theorem actualRingClassRed_match (i : ℕ) :
    letI := dat.field; letI := dat.nf; letI := dat.nz
    letI := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
    (actualRingClassRed C h₁ h₃ dat w q hσ i (L • genusPoint dat)).val =
      (actualLocalStage C h₁ h₃ dat w q hσ i).red
        (rationalGeomPoint (qtwist (C⁄ℚ) (Dw : ℚ)) w.rational) := by
  let := dat.field; let := dat.nf; let := dat.nz
  let := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
  let : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  have hgood := (stage_facts C h₁ h₃ dat w q i).2.1
  have hd := stage_disc C h₁ h₃ dat w q i
  change ((FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1).ringClassReduction C
      w.emb dat.finrank_two hd.1 hd.2 hgood (L • genusPoint dat)).val =
    (FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1).curveReduction C hgood
      (geomTwist (C⁄ℚ) h₁ h₃ (Dw : ℚ) w.qbarRoot w.qbarRoot_ne_zero w.qbarRoot_sq
        (rationalGeomPoint (qtwist (C⁄ℚ) (Dw : ℚ)) w.rational))
  refine ((FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1).ringClassReduction_agrees
    C hgood w.emb dat.finrank_two hd.1 hd.2 (L • genusPoint dat)).trans ?_
  exact congrArg ((FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1).curveReduction
      C hgood)
    ((congrArg (Affine.Point.map (W' := C⁄ℚ) w.emb) w.eq_scaled.symm).trans
      (map_twistEmb_eq_geomTwist w.emb (C⁄ℚ) h₁ h₃ (Dw : ℚ) w.nonzero w.square w.rational))

/-- **The actual stage map** (definition; tex 8378–8398, 8439–8456): `b ∘ κ_{M_θ}` of the
reduction at the place of the selected Frobenius, at the selected datum. Its other entries are
the construction's extension by zero and are not read. -/
def actualStageMap (b : TateMod (qtwist (C⁄ℚ) (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2]) :
    StageKummer (C⁄ℚ) f Lat κ hstar (fun i => a + 1 + 1 + i) :=
  stageKummer (actualLocalStage C h₁ h₃ dat w q hσ)
    (witnessReductions (actualLocalStage C h₁ h₃ dat w q hσ) dat
      (actualRingClassRed C h₁ h₃ dat w q hσ)) (finiteRow b)

/-- **`WitnessSpecialization` for the actual stage map** (PROVED: the construction's
`witnessSpecialization_of_reductions` with `actualRingClassRed_match`; tex 8392–8398). -/
theorem actualStageMap_spec
    (d : DivisionTower (qtwist (C⁄ℚ) (Dw : ℚ))
      (rationalGeomPoint (qtwist (C⁄ℚ) (Dw : ℚ)) w.rational))
    (hQ : ∀ g : GalQ, Affine.Point.map (W' := qtwist (C⁄ℚ) (Dw : ℚ)) g.toAlgHom
      (rationalGeomPoint (qtwist (C⁄ℚ) (Dw : ℚ)) w.rational) =
        rationalGeomPoint (qtwist (C⁄ℚ) (Dw : ℚ)) w.rational)
    (b : TateMod (qtwist (C⁄ℚ) (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2]) :
    WitnessSpecialization (L := L) dat (actualStageMap C h₁ h₃ dat w q hσ b) d hQ
      (fun i => (selectedFrobenius q i).val) (finiteRow b) :=
  witnessSpecialization_of_reductions (actualLocalStage C h₁ h₃ dat w q hσ) dat
    (witnessReductions (actualLocalStage C h₁ h₃ dat w q hσ) dat
      (actualRingClassRed C h₁ h₃ dat w q hσ)) d hQ (finiteRow b)
    (fun i => ⟨actualRingClassRed C h₁ h₃ dat w q hσ i,
      witnessReductions_at_witness _ dat _ i, actualRingClassRed_match C h₁ h₃ dat w q hσ i⟩)

end Actual

/-- **The actual stage map on a curve with an integral model** (definition): `actualStageMap`
transported along `C⁄ℚ = E`, the witness point `Q` being the rational point of the exact witness
and the precision being `M_θ = a + 2 + θ`. -/
def actualStageMapOn {E : WeierstrassCurve ℚ} (C : WeierstrassCurve ℤ) (hE : C⁄ℚ = E)
    [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
    {L : ℕ} (w : ExactWitnessOn E h₁ h₃ dat L) [(qtwist E (Dw : ℚ)).IsElliptic]
    {Q : GeomPoint (qtwist E (Dw : ℚ))}
    (hQw : Q = rationalGeomPoint (qtwist E (Dw : ℚ)) w.rational)
    {a : ℕ} {S : Finset ℕ} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
    (q : StageSequence (ActualAt (qtwist E (Dw : ℚ)) E Q F₀ σ Dw hstar) (a + 1) S)
    (hσ : tateRep E 2 (σ * σ) = 1) (b : TateMod (qtwist E (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
    {Mθ : ℕ → ℕ} (hM : Mθ = fun i => a + 1 + 1 + i) : StageKummer E f Lat κ hstar Mθ := by
  subst hE hQw hM
  exact actualStageMap C h₁ h₃ dat w q hσ b

/-- **`WitnessSpecialization` for the transported actual stage map** (PROVED from
`actualStageMap_spec`). -/
theorem actualStageMapOn_spec {E : WeierstrassCurve ℚ} (C : WeierstrassCurve ℤ) (hE : C⁄ℚ = E)
    [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
    {L : ℕ} (w : ExactWitnessOn E h₁ h₃ dat L) [(qtwist E (Dw : ℚ)).IsElliptic]
    {Q : GeomPoint (qtwist E (Dw : ℚ))}
    (hQw : Q = rationalGeomPoint (qtwist E (Dw : ℚ)) w.rational)
    (d : DivisionTower (qtwist E (Dw : ℚ)) Q)
    (hQ : ∀ g : GalQ, Affine.Point.map (W' := qtwist E (Dw : ℚ)) g.toAlgHom Q = Q)
    {a : ℕ} {S : Finset ℕ} {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
    (q : StageSequence (ActualAt (qtwist E (Dw : ℚ)) E Q F₀ σ Dw hstar) (a + 1) S)
    (hσ : tateRep E 2 (σ * σ) = 1) (b : TateMod (qtwist E (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
    {Mθ : ℕ → ℕ} (hM : Mθ = fun i => a + 1 + 1 + i) :
    WitnessSpecialization (L := L) dat (actualStageMapOn C hE h₁ h₃ dat w hQw q hσ b hM) d hQ
      (fun i => (selectedFrobenius q i).val) (finiteRow b) := by
  subst hE hQw hM
  exact actualStageMap_spec C h₁ h₃ dat w q hσ d hQ b

/-- **`WitnessSpecialization` reads the stage map only at the selected datum** (PROVED). -/
theorem witnessSpecialization_of_agree {A E : WeierstrassCurve ℚ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} {L : ℕ} {Mθ : ℕ → ℕ}
    {dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar} {ev ev' : StageKummer E f Lat κ hstar Mθ}
    (hev : ∀ i, ev i Dw dat = ev' i Dw dat) {Q : GeomPoint A} {d : DivisionTower A Q}
    {hQ : ∀ g : GalQ, Affine.Point.map (W' := A) g.toAlgHom Q = Q} {g : ℕ → GalQ}
    {row : ∀ M, TateModuleLevel 2 (GeomPoint A) M →+ ZMod (2 ^ M)}
    (h : WitnessSpecialization (L := L) dat ev' d hQ g row) :
    WitnessSpecialization (L := L) dat ev d hQ g row := by
  intro i
  let := dat.field; let := dat.nf; let := dat.nz
  let := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
  show ev i Dw dat (L • genusPoint dat) = _
  rw [hev i]
  exact h i

end ZInQ.Manuscript.RC.Wiring
