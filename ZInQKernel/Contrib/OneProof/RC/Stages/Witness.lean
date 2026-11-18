import ZInQKernel.Contrib.OneProof.RC.Stages.Actual
import ZInQKernel.Contrib.OneProof.RC.Stages.FiniteField
import ZInQKernel.Contrib.OneProof.RC.Visibility.Witness

/-! Appendix F, tex 8392–8398. Isolate the good reduction comparison at the fixed witness. -/

noncomputable section

open scoped WeierstrassCurve
open TauCeti ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Visibility
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Stages

/-- The specialization calculation on one division point: additivity and the chosen
Frobenius action on that division point imply the exact, unscaled finite Kummer identity. -/
theorem kappa_of_specialization {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (red : X →+ Y) (g : X →+ X) (F : Y →+ Y) (n : ℕ)
    (hdiv : Function.Surjective (fun R : Y => n • R))
    (htriv : ∀ t : Y, n • t = 0 → F (F t) = t)
    (Q R : X) (hR : n • R = Q) (P : FixedSq F) (hP : red Q = P.val)
    (hF : red (g (g R)) = F (F (red R))) :
    (kappa F n hdiv htriv P).val = red (g (g R) - R) := by
  rw [kappa_apply F n hdiv htriv P (R := red R) (by rw [← map_nsmul, hR, hP]),
    map_sub, hF]

/-- The remaining reduction comparison after reading the stage map at the selected
genus datum. The right side reads the genuine finite component of the cocycle through
the reduction of the fixed integral row. Equality is in the finite ring, before taking
an integer representative or a valuation. -/
def WitnessSpecialization {A E : WeierstrassCurve ℚ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} {L : ℕ} {Mθ : ℕ → ℕ}
    (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar)
    (ev : StageKummer E f Lat κ hstar Mθ)
    {Q : GeomPoint A} (d : DivisionTower A Q)
    (hQ : ∀ g : GalQ, WeierstrassCurve.Affine.Point.map (W' := A) g.toAlgHom Q = Q)
    (g : ℕ → GalQ)
    (row : ∀ M, TateModuleLevel 2 (GeomPoint A) M →+ ZMod (2 ^ M)) : Prop :=
  ∀ i, letI := dat.field; letI := dat.nf; letI := dat.nz
    letI := Classical.decEq (TauCeti.ClassFieldTheory.ringClassField
      (CST.conductorOrder dat.K 1))
    ev i Dw dat (L • genusPoint dat) =
      row (Mθ i) (TateModule.proj (Mθ i) (d.cocycle hQ (g i * g i)))

/-- A pure power of two below the precision has exactly its original valuation
in the canonical integer representative. -/
theorem val_exact_two_power {c M : ℕ} (h : c < M) {z : ZMod (2 ^ M)}
    (hz : z = (2 ^ c : ℕ)) :
    (2 : ℤ) ^ c ∣ (z.val : ℤ) ∧ ¬ (2 : ℤ) ^ (c + 1) ∣ (z.val : ℤ) := by
  have hv : z.val = 2 ^ c := by
    rw [hz, ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by decide) h)]
  rw [hv, Nat.cast_pow, Nat.cast_ofNat]
  refine ⟨dvd_rfl, ?_⟩
  intro hd
  rw [pow_succ] at hd
  have h' : (2 : ℤ) ∣ 1 :=
    (mul_dvd_mul_iff_left (pow_ne_zero c (by decide : (2 : ℤ) ≠ 0))).mp
      (show (2 : ℤ) ^ c * 2 ∣ (2 : ℤ) ^ c * 1 by simpa using hd)
  norm_num at h'

/-- Appendix F (O.2) at the chosen genus point, on the existing integer lift.
The reduction comparison uses the same Frobenius places as the stage sequence. -/
theorem witnessValuation_withStages {ℓ : ℕ} (W : WData ℓ)
    {A E : WeierstrassCurve ℚ} [A.IsElliptic] [E.IsElliptic]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (CST.newformLevel E) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {hstar Dw : ℤ} {L a : ℕ} {S : Finset ℕ}
    {Q : GeomPoint A} (d : DivisionTower A Q) (hQ) {F₀ : IntermediateField ℚ Qbar} {σ : GalQ}
    (q : StageSequence (ActualAt A E Q F₀ σ Dw hstar) (a + 1) S)
    {prepared : ℤ → Prop} (hp : prepared Dw)
    (selG : (D : ℤ) → Option (HeegnerDatum E f Lat κ (D * hstar) 1 hstar))
    (dat : HeegnerDatum E f Lat κ (Dw * hstar) 1 hstar) (hdat : selG Dw = some dat)
    (ev : StageKummer E f Lat κ hstar (withStages W q prepared).Mθ)
    (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2])
    (hvalue : b (d.cocycle hQ (σ * σ)) = 2 ^ (a + 1))
    (hred : WitnessSpecialization (L := L) dat ev d hQ (fun i => (selectedFrobenius q i).val)
      (finiteRow b)) :
    WitnessValuation (withStages W q prepared)
      (lamOf (withStages W q prepared).Mθ L selG ev) Dw (a + 1) := by
  apply Filter.Eventually.of_forall
  intro i
  refine ⟨⟨hp, witness_on_stages q i⟩, ?_⟩
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  letI := Classical.decEq (TauCeti.ClassFieldTheory.ringClassField (CST.conductorOrder dat.K 1))
  unfold lamOf
  rw [hdat]
  change (2 : ℤ) ^ (a + 1) ∣ ((ev i Dw dat (L • genusPoint dat)).val : ℤ) ∧
    ¬ (2 : ℤ) ^ (a + 1 + 1) ∣ ((ev i Dw dat (L • genusPoint dat)).val : ℤ)
  let m := a + 1 + 1 + i
  have h₁ := hred i
  have h₂ := congrArg (finiteRow b m)
    (DivisionTower.proj_cocycle_sq_eq_of_agree A E d hQ F₀ (selectedFrobenius q i).property.2)
  have h₃ : finiteRow b m (TateModule.proj m (d.cocycle hQ (σ * σ))) =
      ((2 ^ (a + 1) : ℕ) : ZMod (2 ^ m)) := by
    rw [finiteRow_proj, hvalue]
    simp only [map_pow, map_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have hz : ev i Dw dat (L • genusPoint dat) =
      ((2 ^ (a + 1) : ℕ) : ZMod (2 ^ (withStages W q prepared).Mθ i)) :=
    Eq.trans h₁ (Eq.trans h₂ h₃)
  exact val_exact_two_power (show a + 1 < (withStages W q prepared).Mθ i by
    change a + 1 < a + 1 + 1 + i
    omega) hz

#print axioms kappa_of_specialization
#print axioms val_exact_two_power
#print axioms witnessValuation_withStages

end ZInQ.Manuscript.RC.Stages
