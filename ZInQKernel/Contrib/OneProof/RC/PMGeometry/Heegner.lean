import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Geometry
import ZInQKernel.Contrib.OneProof.RC.PMGeometry.Evaluation
import ZInQKernel.Contrib.OneProof.RC.PM.Theta
import ZInQKernel.Contrib.OneProof.RC.Visibility.Models
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.FiniteReduction

/-!
# Heegner reduction at the same place (tex 9265–9291)

The pointwise comparison retains the reference orientation tuple. The theorem
uses it only at the selected datum, where the stage map is the same reduced
detector composed with ring-class reduction.
-/

noncomputable section

open scoped WeierstrassCurve Classical
open WeierstrassCurve NumberField TauCeti.ClassFieldTheory
open ZInQ.Contrib.ChebFD.C10 (GQ Qbar)
open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.PMGeometry

open Eichler Visibility WitnessSpec

/-- The geometric inputs including one Heegner datum. `y c` is the image of the
Heegner conjugate under the generic-fibre parametrization. `reduceCM c` is the
reduction of the corresponding enhanced curve itself, at the chosen place.
`z c` comes from the reference orientation, not the union of the orientations. -/
structure InputsAtDatum {a b : ℚ} {R : Order a b} {ell N : ℕ} [Fact ell.Prime]
    (A : Adelic (ell := ell) (N := N) R)
    {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
    {Ebar : WeierstrassCurve (ZMod ell)} (ap : ℕ → ℤ)
    {Cl Y : Type*} [AddCommGroup Y] (red : Y →+ PM.ReducedPoints (K := K) Ebar)
    (y : Cl → Y) (z : Cl → ClassSet R) where
  model : GeometricInput A K Ebar ap
  reduceCM : Cl → model.Point
  /-- Cornut–Jetchev as used at tex 9265–9279: the chosen CM orbit reduces to
  the reference sign and level orientations. This is the pointwise use of
  the existing Cornut–Jetchev print, including its geometric identification. -/
  cm_class : ∀ c, reduceCM c = (model.classes (z c)).val
  /-- ELLIOT: the extension of the parametrization commutes with reduction
  on these points (tex 8476–8479, 9283–9291). -/
  pi_commutes : ∀ c, model.specialize (reduceCM c) = red (y c)

namespace InputsAtDatum

variable {a b : ℚ} {R : Order a b} {ell N : ℕ} [Fact ell.Prime]
  {A : Adelic (ell := ell) (N := N) R}
  {K : Type*} [Field K] [Algebra (ZMod ell) K] [DecidableEq K]
  {Ebar : WeierstrassCurve (ZMod ell)} {ap : ℕ → ℤ}
  {Cl Y : Type*} [AddCommGroup Y] {red : Y →+ PM.ReducedPoints (K := K) Ebar}
  {y : Cl → Y} {z : Cl → ClassSet R} (I : InputsAtDatum A ap red y z)

/-- The pointwise specialization of the Heegner conjugate's parametrization. -/
theorem point_reduction (c : Cl) : I.model.geometry.pi (z c) = red (y c) := by
  change I.model.specialize (I.model.classes (z c)).val = red (y c)
  rw [← I.cm_class c, I.pi_commutes]

/-- On-the-spot (c): the pointwise lift premise of `Visibility.lamOf_reduction`
for the detector composed with reduction on this datum. -/
theorem lift_at_conjugate [IsSepClosed K] [Ebar.IsElliptic] {M : ℕ}
    (d : PM.Evaluation K Ebar M) (L : ℕ)
    {u : ClassSet R → ℤ} (hu : PM.IsLift I.model.geometry d L u) (c : Cl) :
    (2 : ℤ) ^ M ∣ u (z c) - (((PM.lam d).comp red (L • y c)).val : ℤ) :=
  PM.lift_at_reduction I.model.geometry d L red hu (z c) (y c) (I.point_reduction c)

end InputsAtDatum

section Datum

variable {C : WeierstrassCurve ℤ}
  {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (C⁄ℚ)) :
    Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ} {hstar D : ℤ}
  (dat : HeegnerDatum (C⁄ℚ) f Lat κ (D * hstar) 1 hstar)

abbrev DatumField :=
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  ringClassField (conductorOrder dat.K 1)

abbrev DatumPoints :=
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  ((C⁄ℚ)⁄(DatumField dat)).toAffine.Point

abbrev DatumGalois :=
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  DatumField dat ≃ₐ[dat.K] DatumField dat

/-- The conjugate used in the existing Heegner sum. -/
def conjugate (σ : DatumGalois dat) : DatumPoints dat := by
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  letI := Classical.decEq (DatumField dat)
  exact galPt (C⁄ℚ) σ dat.y

variable {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)

/-- The data for conductor-one reduction at the exact place used by the detector.
The inert hypothesis gives quadratic residue descent by `WitnessSpec`. -/
structure DatumPlace (place : FrobeniusPlace g p) where
  emb : DatumField dat →ₐ[ℚ] Qbar
  inert : letI := dat.field; letI := dat.nf; legendreSym p (discr dat.K) = -1

/-- Use the actual restricted place and its residue map into the detector's
quadratic fixed group. -/
def datumReduction (w : DatumPlace dat v) (hg : ¬ (p : ℤ) ∣ C.Δ) :
    letI := Classical.decEq (DatumField dat)
    DatumPoints dat →+ PM.ReducedPoints (K := ResidueAt v) (ReducedEquation C p) := by
  letI := dat.field
  letI := dat.nf
  letI := dat.nz
  letI := Classical.decEq (DatumField dat)
  have hD : ¬ (p : ℤ) ∣ discr dat.K := by
    intro hd
    have hz := (legendreSym.eq_zero_iff p (discr dat.K)).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd (discr dat.K) p).mpr hd)
    rw [w.inert] at hz
    contradiction
  exact v.ringClassReduction C w.emb dat.finrank_two hD w.inert hg

set_option maxHeartbeats 1000000 in
/-- The selected datum's reduction contribution to `Visibility.ComparisonCore`.
The incoming stage map needs to match the constructed evaluation only at
`(θ, D, dat)`. A map constructed just for the witness gives no such premise
at other data. -/
theorem lamOf_reduction_at {a b : ℚ} {R : Order a b}
    {A : Adelic (ell := p) (N := newformLevel (C⁄ℚ)) R} {ap : ℕ → ℤ}
    [(ReducedEquation C p).IsElliptic]
    (w : DatumPlace dat v) (hg : ¬ (p : ℤ) ∣ C.Δ)
    (Mθ : ℕ → ℕ) (θ L : ℕ) (d : PM.Evaluation (ResidueAt v) (ReducedEquation C p) (Mθ θ))
    (selG : (D' : ℤ) → Option (HeegnerDatum (C⁄ℚ) f Lat κ (D' * hstar) 1 hstar))
    (ev : StageKummer (C⁄ℚ) f Lat κ hstar Mθ)
    (hsel : selG D = some dat)
    (hev : letI := Classical.decEq (DatumField dat)
      ev θ D dat = (PM.lam d).comp (datumReduction dat v w hg))
    {O : Type*} [CommRing O] {Cl : Type} [Fintype Cl]
    (e : Cl ≃ DatumGalois dat) (z : Cl → ClassSet R) (χF : Cl → O)
    (hχF : letI := dat.field; letI := dat.nf; letI := dat.nz
      ∀ c, χF c = ((chiSign dat.χ
        ((ringClassArtinEquiv (conductorOrder dat.K 1)).symm (e c)) : ℤ) : O))
    (I : letI := Classical.decEq (DatumField dat)
      InputsAtDatum A ap (datumReduction dat v w hg) (conjugate dat ∘ e) z)
    {u : ClassSet R → ℤ} (hu : letI := Classical.decEq (DatumField dat)
      PM.IsLift I.model.geometry d L u) :
    (2 : O) ^ Mθ θ ∣ ∑ c, χF c * (u (z c) : O) - (lamOf Mθ L selG ev θ D : O) := by
  let := dat.field
  let := dat.nf
  let := dat.nz
  let := Classical.decEq (DatumField dat)
  refine lamOf_reduction Mθ L selG ev θ dat hsel e χF hχF (u ∘ z) ?_
  intro c
  rw [hev]
  exact I.lift_at_conjugate d L hu c

end Datum

#print axioms InputsAtDatum.point_reduction
#print axioms InputsAtDatum.lift_at_conjugate
#print axioms conjugate
#print axioms datumReduction
#print axioms lamOf_reduction_at

end ZInQ.Manuscript.RC.PMGeometry
