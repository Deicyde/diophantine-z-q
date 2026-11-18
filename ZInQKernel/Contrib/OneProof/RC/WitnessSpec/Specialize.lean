import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.ActualLocal
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.FiniteReduction

/-! The actual evaluation and (O.2) at the fixed multiplied witness.
The extension by zero only fills the unused entries of the total stage interface. -/

noncomputable section

open NumberField WeierstrassCurve TauCeti TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Manuscript.RC.Stages ZInQ.Manuscript.RC.Nonvanishing
  ZInQ.Manuscript.RC.Visibility ZInQ.Manuscript.RC.Wiring
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped WeierstrassCurve Classical

namespace ZInQ.Manuscript.RC.WitnessSpec

section Family

variable {A E : WeierstrassCurve ℚ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) :
    Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ}
  {hstar Dw : ℤ} {Mθ : ℕ → ℕ} {g : ℕ → GalQ}
  (st : ∀ i, LocalStage A (Mθ i) (g i))
  (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)

/-- Fill the sole datum used in the witness specialization. -/
def witnessReductions
    (red : ∀ i, letI := dat.field; letI := dat.nf; letI := dat.nz
      letI := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
      (E⁄(ringClassField (CST.conductorOrder dat.K 1))).toAffine.Point →+
        FixedSq (st i).frob) :
    DatumReductions (E := E) (f := f) (Lat := Lat) (κ := κ) (hstar := hstar) st :=
  fun i D d => by
    by_cases h : D = Dw
    · subst D
      by_cases h' : d = dat
      · subst d
        exact some (red i)
      · exact none
    · exact none

theorem witnessReductions_at_witness
    (red : ∀ i, letI := dat.field; letI := dat.nf; letI := dat.nz
      letI := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
      (E⁄(ringClassField (CST.conductorOrder dat.K 1))).toAffine.Point →+
        FixedSq (st i).frob) (i : ℕ) :
    witnessReductions st dat red i Dw dat = some (red i) := by
  simp [witnessReductions]

#print axioms witnessReductions
#print axioms witnessReductions_at_witness

end Family

private theorem goodAt_disc_unit (C : WeierstrassCurve ℤ) {p : ℕ} [Fact p.Prime]
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

private theorem not_dvd_of_legendre_ne_zero {p : ℕ} [Fact p.Prime] {D : ℤ}
    (h : legendreSym p D ≠ 0) : ¬ (p : ℤ) ∣ D := by
  intro hd
  exact h ((legendreSym.eq_zero_iff p D).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hd))

#print axioms goodAt_disc_unit
#print axioms not_dvd_of_legendre_ne_zero

section Actual

variable (C : WeierstrassCurve ℤ) [(C⁄ℚ).IsElliptic]
  (h₁ : (C⁄ℚ).a₁ = 0) (h₃ : (C⁄ℚ).a₃ = 0)
  {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel (C⁄ℚ)) :
    Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ}
  {hstar Dw : ℤ} (dat : HeegnerDatum (C⁄ℚ) f Lat κ (Dw * hstar) 1 hstar)
  (L : ℕ)

/-- A chosen root in the datum, its embedding, and the exact rational witness
before specializing. The identity here is the output of the global twist
comparison, not an equality assumed after reduction. -/
structure ExactWitness where
  emb : letI := dat.field; letI := dat.nf; letI := dat.nz
    (ringClassField (CST.conductorOrder dat.K 1)) →ₐ[ℚ] Qbar
  root : letI := dat.field; letI := dat.nf; letI := dat.nz
    ringClassField (CST.conductorOrder dat.K 1)
  nonzero : letI := dat.field; letI := dat.nf; letI := dat.nz; root ≠ 0
  square : letI := dat.field; letI := dat.nf; letI := dat.nz
    root ^ 2 = algebraMap ℚ (ringClassField (CST.conductorOrder dat.K 1)) (Dw : ℚ)
  rational : Affine.Point (WeierstrassCurve.toAffine (qtwist (C.baseChange ℚ) (Dw : ℚ)))
  eq_scaled : letI := dat.field; letI := dat.nf; letI := dat.nz
    letI := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
    twistEmb (C.baseChange ℚ) (Dw : ℚ) root (twistVC_smul (C.baseChange ℚ) h₁ h₃ nonzero square)
      rational =
      L • genusPoint dat

variable (w : ExactWitness C h₁ h₃ dat L)

private theorem choose_local_at_witness {g : GalQ} {p M : ℕ} [Fact p.Prime]
    (v : FrobeniusPlace g p) (hp : p ≠ 2)
    (hgood : ¬ (p : ℤ) ∣ C.Δ)
    (hDw : ¬ (p : ℤ) ∣ Dw) (hhs : ¬ (p : ℤ) ∣ hstar)
    (hplus : legendreSym p Dw = 1) (hminus : legendreSym p hstar = -1)
    (hsq : ∀ t : GeomPoint (C.baseChange ℚ), (2 ^ M : ℕ) • t = 0 →
      Affine.Point.map (W' := (C.baseChange ℚ)) g.toAlgHom
        (Affine.Point.map (W' := (C.baseChange ℚ)) g.toAlgHom t) = t) :
    ∃ stage : LocalStage (qtwist (C.baseChange ℚ) (Dw : ℚ)) M g,
      letI := dat.field; letI := dat.nf; letI := dat.nz
      letI := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
      ∃ r : ((C.baseChange ℚ)⁄(ringClassField (CST.conductorOrder dat.K 1))).toAffine.Point →+
        FixedSq stage.frob,
        (r (L • genusPoint dat)).val =
          stage.red (rationalGeomPoint (qtwist (C.baseChange ℚ) (Dw : ℚ)) w.rational) := by
  let := dat.field
  let := dat.nf
  let := dat.nz
  let := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
  let s := w.emb w.root
  have hs : s ≠ 0 := fun he => w.nonzero (w.emb.injective (he.trans (map_zero w.emb).symm))
  have hD : s ^ 2 = algebraMap ℚ Qbar (Dw : ℚ) := by
    change (w.emb w.root) ^ 2 = _
    rw [← map_pow, w.square, w.emb.commutes]
  have hg : g s = s := by
    have hh := apply_sqrt_of_isFrobAt hp ⟨v.prime, v.isPrime, v.under, v.frob⟩ hDw
      (show s ^ 2 = (Dw : Qbar) by simpa only [map_intCast] using hD)
    simpa only [hplus, one_zsmul] using hh
  have hd : ¬ (p : ℤ) ∣ discr dat.K := by
    rw [dat.disc]
    exact fun hh => ((Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_or_dvd hh).elim hDw hhs
  have hsign : legendreSym p (discr dat.K) = -1 := by
    rw [dat.disc, legendreSym.mul, hplus, hminus, one_mul]
  let st := v.localStage C hgood hp M h₁ h₃ (Dw : ℚ) s hs hD hg hsq
  let r := v.ringClassReduction C w.emb dat.finrank_two hd hsign hgood
  refine ⟨st, r, ?_⟩
  change (r (L • genusPoint dat)).val =
    v.curveReduction C hgood (geomTwist (C.baseChange ℚ) h₁ h₃ (Dw : ℚ) s hs hD
      (rationalGeomPoint (qtwist (C.baseChange ℚ) (Dw : ℚ)) w.rational))
  refine (v.ringClassReduction_agrees C hgood w.emb dat.finrank_two hd hsign
    (L • genusPoint dat)).trans ?_
  exact congrArg (v.curveReduction C hgood)
    ((congrArg (Affine.Point.map (W' := (C.baseChange ℚ)) w.emb) w.eq_scaled.symm).trans
      (map_twistEmb_eq_geomTwist w.emb (C.baseChange ℚ) h₁ h₃ (Dw : ℚ) w.nonzero w.square w.rational))

#print axioms ExactWitness
#print axioms choose_local_at_witness

variable [(qtwist (C⁄ℚ) (Dw : ℚ)).IsElliptic]

/-- On the chosen stage sequence, the actual stage maps give the exact finite
cocycle identity and (O.2) for the selected fixed witness. The stage hypotheses
provide good reduction and the two residue signs. -/
theorem actualWitness {ℓ : ℕ} (W : WData ℓ) {a : ℕ} {S : Finset ℕ}
    (d : DivisionTower (qtwist (C.baseChange ℚ) (Dw : ℚ))
      (rationalGeomPoint (qtwist (C.baseChange ℚ) (Dw : ℚ)) w.rational)) (hQ)
    {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
    (q : StageSequence
      (ActualAt (qtwist (C.baseChange ℚ) (Dw : ℚ)) (C.baseChange ℚ)
        (rationalGeomPoint (qtwist (C.baseChange ℚ) (Dw : ℚ)) w.rational) F₀ σ Dw hstar) (a + 1) S)
    (hσ : tateRep (C.baseChange ℚ) 2 (σ * σ) = 1)
    {prepared : ℤ → Prop} (hp : prepared Dw)
    (selG : (D : ℤ) → Option (HeegnerDatum (C.baseChange ℚ) f Lat κ (D * hstar) 1 hstar))
    (hdat : selG Dw = some dat)
    (b : TateMod (qtwist (C.baseChange ℚ) (Dw : ℚ)) 2 →ₗ[ℤ_[2]] ℤ_[2])
    (hvalue : b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1)) :
    ∃ ev : StageKummer (C.baseChange ℚ) f Lat κ hstar (withStages W q prepared).Mθ,
      WitnessSpecialization (L := L) dat ev d hQ (fun i => (selectedFrobenius q i).val)
        (finiteRow b) ∧
      WitnessValuation (withStages W q prepared)
        (lamOf (withStages W q prepared).Mθ L selG ev) Dw (a + 1) := by
  have hex (i : ℕ) :
      ∃ st : LocalStage (qtwist (C.baseChange ℚ) (Dw : ℚ))
          ((withStages W q prepared).Mθ i) (selectedFrobenius q i).val,
        letI := dat.field; letI := dat.nf; letI := dat.nz
        letI := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
        ∃ r : ((C.baseChange ℚ)⁄(ringClassField (CST.conductorOrder dat.K 1))).toAffine.Point →+
          FixedSq st.frob,
          (r (L • genusPoint dat)).val =
            st.red (rationalGeomPoint (qtwist (C.baseChange ℚ) (Dw : ℚ)) w.rational) := by
    let : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    have hs (t : GeomPoint (C.baseChange ℚ)) (ht : (2 ^ ((withStages W q prepared).Mθ i) : ℕ) • t = 0) :=
      actualStage_torsion_sq q i hσ
        ⟨t, AddSubgroup.torsionBy.nsmul_iff.mpr ht⟩
    obtain ⟨_, _, hodd, hgood, _, _, _, _, _, _, hplus, hminus⟩ := (q.stage i).arithmetic
    have hDw := not_dvd_of_legendre_ne_zero (hplus.symm ▸ (by decide : (1 : ℤ) ≠ 0))
    have hhs := not_dvd_of_legendre_ne_zero (hminus.symm ▸ (by decide : (-1 : ℤ) ≠ 0))
    exact choose_local_at_witness C h₁ h₃ dat L w
      (FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1)
      hodd (goodAt_disc_unit C hgood) hDw hhs hplus hminus
      (fun t ht => by rw [Affine.Point.map_map]; exact hs t ht)
  let st i := (hex i).choose
  let red i := (hex i).choose_spec.choose
  let r := witnessReductions st dat red
  have hm (i : ℕ) : letI := dat.field; letI := dat.nf; letI := dat.nz
      letI := Classical.decEq (ringClassField (CST.conductorOrder dat.K 1))
      ∃ ri, r i Dw dat = some ri ∧ (ri (L • genusPoint dat)).val =
        (st i).red (rationalGeomPoint (qtwist (C.baseChange ℚ) (Dw : ℚ)) w.rational) :=
    ⟨red i, witnessReductions_at_witness st dat red i, (hex i).choose_spec.choose_spec⟩
  exact ⟨stageKummer st r (finiteRow b),
    witnessSpecialization_of_reductions st dat r d hQ (finiteRow b) hm,
    witnessValuation_of_reductions W d hQ q hp selG dat hdat st r b hvalue hm⟩

#print axioms actualWitness

end Actual

end ZInQ.Manuscript.RC.WitnessSpec
