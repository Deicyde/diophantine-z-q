import ZInQKernel.Contrib.OneProof.RC.PM.DetectorRow
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Torsion

/-!
# The detector row at the chosen place (tex 8370–8393, 8452–8459)

Use the same absolute place and arithmetic Frobenius as the witness. The row
is written on the untwisted Tate module, as in the manuscript after the split
twist identification.
-/

noncomputable section

open WeierstrassCurve TauCeti IsLocalRing
open ZInQ.Contrib.ChebFD.C10 (GQ)
open scoped WeierstrassCurve Classical

namespace ZInQ.Manuscript.RC.PMGeometry

open Stages WitnessSpec PrintsArith GlueSweep.Tate

/-- Transport the detector row by a geometric identification from the twist
to the original curve, as in tex 8340–8343. -/
def rowOnOriginal {A E : WeierstrassCurve ℚ} (e : GeomPoint A ≃+ GeomPoint E)
    (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2]) : TateMod E 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  b.comp (TateModule.mapLinearMap e.symm.toAddMonoidHom)

/-- The row remains fixed on the original curve. For the split twist, the
pointwise premise is `Stages.geomTwist_equivariant`. -/
theorem rowOnOriginal_fixed {A E : WeierstrassCurve ℚ} (e : GeomPoint A ≃+ GeomPoint E)
    (σ : GQ) (he : ∀ P, e (Affine.Point.map (W' := A) σ.toAlgHom P) =
      Affine.Point.map (W' := E) σ.toAlgHom (e P))
    (b : TateMod A 2 →ₗ[ℤ_[2]] ℤ_[2]) (hb : ∀ t, b (tateRep A 2 σ t) = b t)
    (t : TateMod E 2) : rowOnOriginal e b (tateRep E 2 σ t) = rowOnOriginal e b t := by
  let f : TateMod E 2 →ₗ[ℤ_[2]] TateMod A 2 := TateModule.mapLinearMap e.symm.toAddMonoidHom
  have hf : f (tateRep E 2 σ t) = tateRep A 2 σ (f t) := by
    apply TateModule.ext
    intro j
    apply Subtype.ext
    simp only [f, TateModule.mapLinearMap_apply, TateModule.proj_map, TateModule.levelMap_apply,
      coe_proj_tateRep, AddEquiv.coe_toAddMonoidHom]
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  change b (f (tateRep E 2 σ t)) = b (f t)
  rw [hf, hb]

/-- The common geometric residue field of the chosen absolute place. -/
abbrev ResidueAt {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p) :=
  ResidueField v.valuationRing.valuation.valuationSubring

/-- The original integral equation reduced over the prime field. -/
abbrev ReducedEquation (C : WeierstrassCurve ℤ) (p : ℕ) :=
  C.map (Int.castRingHom (ZMod p))

/-- The discriminant is a unit in the prime field at the selected good prime. -/
theorem reducedEquation_elliptic (C : WeierstrassCurve ℤ) {p : ℕ} [Fact p.Prime]
    (hg : ¬ (p : ℤ) ∣ C.Δ) : (ReducedEquation C p).IsElliptic := by
  rw [isElliptic_iff, map_Δ]
  exact isUnit_iff_ne_zero.mpr fun h => hg ((ZMod.intCast_zmod_eq_zero_iff_dvd C.Δ p).mp h)

/-- On-the-spot (c), as in the witness specialization: the good-reduction
condition of an actual stage implies that the integral discriminant is a unit. -/
theorem goodIntegralEquation (C : WeierstrassCurve ℤ) {p : ℕ} [Fact p.Prime]
    (h : Nonvanishing.GoodAt (C⁄ℚ) p) : ¬ (p : ℤ) ∣ C.Δ := by
  obtain ⟨hn, hv⟩ := h.2.2.2.2.2
  have hΔ : (C⁄ℚ).Δ = (C.Δ : ℚ) := by
    rw [baseChange, WeierstrassCurve.map_Δ, eq_intCast]
  rw [hΔ, padicValRat.of_int] at hv
  intro hd
  have hh := (padicValInt_dvd_iff (p := p) 1 C.Δ).mp (by simpa only [pow_one] using hd)
  rcases hh with hzero | hpos
  · exact hn (by rw [hΔ, hzero, Int.cast_zero])
  · omega

section Place

variable {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)
  (C : WeierstrassCurve ℤ) [(C⁄ℚ).IsElliptic] (hg : ¬ (p : ℤ) ∣ C.Δ)
  (hodd : p ≠ 2) (M : ℕ)

/-- Actual good reduction restricts to an additive equivalence on geometric
`2^M`-torsion. Both sides use the same Weierstrass equation (tex 8392–8393). -/
def torsionSpecialization : TateModuleLevel 2 (GeomPoint (C⁄ℚ)) M ≃+
    AddSubgroup.torsionBy ((ReducedEquation C p)⁄(ResidueAt v)).toAffine.Point (2 ^ M : ℕ) :=
  AddEquiv.ofBijective (torsionMap (2 ^ M) (v.curveReduction C hg))
    (v.curveReduction_torsion_bijective C hg hodd M)

/-- On torsion, arithmetic Frobenius is the specialization of the selected
absolute Galois action (tex 8453–8456). -/
theorem torsionSpecialization_frob (t : TateModuleLevel 2 (GeomPoint (C⁄ℚ)) M) :
    torsionSpecialization v C hg hodd M
        (torsionFrob (Affine.Point.map (W' := C⁄ℚ) g.toAlgHom) (2 ^ M) t) =
      torsionFrob (curveFrob (K := ResidueAt v) (ReducedEquation C p)) (2 ^ M)
        (torsionSpecialization v C hg hodd M t) := by
  apply Subtype.ext
  exact v.curveReduction_frobenius C hg t.val

variable {σ : GQ} (hagree : ∀ x ∈ torsField (C⁄ℚ) M, g x = σ x)

private theorem proj_onto : Function.Surjective
    (TateModule.proj M : TateMod (C⁄ℚ) 2 →+ TateModuleLevel 2 (GeomPoint (C⁄ℚ)) M) :=
  TateModule.proj_surjective
    (TateModule.tateModuleTransition_surjective_of_natCard (p := 2) (by decide)
      (((C⁄ℚ)⁄Qbar).natCard_tateModuleLevel (by norm_num : (2 : Qbar) ≠ 0))) M

include hagree in
/-- Agreement at level `M` suffices: the Frobenius of the chosen place need
not agree with the detector on the whole Tate module (tex 8370–8377, 8455–8456). -/
theorem finiteRow_fixed (b : TateMod (C⁄ℚ) 2 →ₗ[ℤ_[2]] ℤ_[2])
    (hb : ∀ t, b (tateRep (C⁄ℚ) 2 σ t) = b t)
    (t : TateModuleLevel 2 (GeomPoint (C⁄ℚ)) M) :
    finiteRow b M (torsionFrob (Affine.Point.map (W' := C⁄ℚ) g.toAlgHom) (2 ^ M) t) =
      finiteRow b M t := by
  obtain ⟨u, rfl⟩ := proj_onto C M t
  have ht : torsionFrob (Affine.Point.map (W' := C⁄ℚ) g.toAlgHom) (2 ^ M) (TateModule.proj M u) =
      TateModule.proj M (tateRep (C⁄ℚ) 2 σ u) := by
    apply Subtype.ext
    rw [coe_proj_tateRep]
    exact map_eq_of_eqOn_torsField (C⁄ℚ) hagree (TateModule.proj M u)
  rw [ht, finiteRow_proj, finiteRow_proj, hb]

include hg hodd hagree in
/-- The trivial square action on finite torsion descends at the chosen place
(tex 8376–8377, 8440–8446). -/
theorem square_trivial_at (hσ : tateRep (C⁄ℚ) 2 (σ * σ) = 1) :
    ∀ t : ((ReducedEquation C p)⁄(ResidueAt v)).toAffine.Point, (2 ^ M : ℕ) • t = 0 →
      curveFrob (K := ResidueAt v) (ReducedEquation C p)
        (curveFrob (K := ResidueAt v) (ReducedEquation C p) t) = t := by
  refine frob_sq_on_reduced_torsion _ (v.curveReduction C hg)
    (Affine.Point.map (W' := C⁄ℚ) g.toAlgHom) _
    (v.curveReduction_frobenius C hg) ?_ (v.curveReduction_torsion_bijective C hg hodd M)
  intro t ht
  change Affine.Point.map (W' := C⁄ℚ) g.toAlgHom
    (Affine.Point.map (W' := C⁄ℚ) g.toAlgHom t) = t
  rw [Affine.Point.map_map]
  exact global_frob_sq_on_torsion (C⁄ℚ) hagree (fun s => by
    obtain ⟨u, rfl⟩ := proj_onto C M s
    rw [← coe_proj_tateRep, hσ]
    rfl) ⟨t, AddSubgroup.torsionBy.nsmul_iff.mpr ht⟩

include hagree in
/-- The specialized detector is `ofTateRow` using actual torsion reduction.
It inherits the fixed row and trivial square action, rather than assuming
either on the residue curve. -/
def evaluationAt (b : TateMod (C⁄ℚ) 2 →ₗ[ℤ_[2]] ℤ_[2])
    (hb : ∀ t, b (tateRep (C⁄ℚ) 2 σ t) = b t) (hσ : tateRep (C⁄ℚ) 2 (σ * σ) = 1) :
    PM.Evaluation (ResidueAt v) (ReducedEquation C p) M := by
  refine PM.Evaluation.ofTateRow b hodd (square_trivial_at v C hg hodd M hagree hσ)
    (torsionSpecialization v C hg hodd M) ?_
  intro t
  obtain ⟨u, rfl⟩ := (torsionSpecialization v C hg hodd M).surjective t
  rw [← torsionSpecialization_frob, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact finiteRow_fixed C M hagree b hb u

include hagree in
/-- On-the-spot (c): the existing untwisted local stage map with a supplied
datum reduction is the composite of the constructed detector and that reduction. -/
theorem stageMap_eq_lam_comp [(ReducedEquation C p).IsElliptic]
    (b : TateMod (C⁄ℚ) 2 →ₗ[ℤ_[2]] ℤ_[2])
    (hb : ∀ t, b (tateRep (C⁄ℚ) 2 σ t) = b t) (hσ : tateRep (C⁄ℚ) 2 (σ * σ) = 1)
    (hsq : ∀ t : GeomPoint (C⁄ℚ), (2 ^ M : ℕ) • t = 0 →
      Affine.Point.map (W' := C⁄ℚ) g.toAlgHom (Affine.Point.map (W' := C⁄ℚ) g.toAlgHom t) = t)
    (hdiv : Function.Surjective (fun t : ((ReducedEquation C p)⁄(ResidueAt v)).toAffine.Point =>
      (2 ^ M : ℕ) • t))
    {Y : Type*} [AddCommGroup Y]
    (r : Y →+ PM.ReducedPoints (K := ResidueAt v) (ReducedEquation C p)) :
    stageMap (2 ^ M) (v.curveReduction C hg) (Affine.Point.map (W' := C⁄ℚ) g.toAlgHom)
      (curveFrob (K := ResidueAt v) (ReducedEquation C p)) (v.curveReduction_frobenius C hg)
      hsq (v.curveReduction_torsion_bijective C hg hodd M) hdiv (finiteRow b M) r =
        (PM.lam (evaluationAt v C hg hodd M hagree b hb hσ)).comp r := by
  apply AddMonoidHom.ext
  intro t
  rfl

end Place

section SelectedStage

variable {C : WeierstrassCurve ℤ} [(C⁄ℚ).IsElliptic]
  {A : WeierstrassCurve ℚ} [A.IsElliptic] {Q : GeomPoint A}
  {F₀ : IntermediateField ℚ Qbar} {σ : GQ} {Dw hstar : ℤ} {cw : ℕ} {S : Finset ℕ}
  (q : StageSequence (ActualAt A (C⁄ℚ) Q F₀ σ Dw hstar) cw S) (i : ℕ)

/-- The very place used in `WitnessSpec.actualWitness` for the same stage sequence. -/
abbrev selectedPlace :=
  FrobeniusPlace.ofIsFrobAt (selectedFrobenius q i).property.1

/-- On-the-spot (c) assembly: the stage's joint-field agreement gives exactly
the finite-level premise of the detector, at the selected place. -/
def evaluationOfStage (b : TateMod (C⁄ℚ) 2 →ₗ[ℤ_[2]] ℤ_[2])
    (hb : ∀ t, b (tateRep (C⁄ℚ) 2 σ t) = b t) (hσ : tateRep (C⁄ℚ) 2 (σ * σ) = 1) :
    letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
    PM.Evaluation (ResidueAt (selectedPlace q i)) (ReducedEquation C (q.stage i).p) (cw + 1 + i) := by
  letI : Fact (q.stage i).p.Prime := ⟨(q.stage i).prime⟩
  have h : (q.stage i).p ≠ 2 ∧ Nonvanishing.GoodAt (C⁄ℚ) (q.stage i).p := by
    obtain ⟨_, _, hodd, hgood, _⟩ := (q.stage i).arithmetic
    exact ⟨hodd, hgood⟩
  exact evaluationAt (selectedPlace q i) C (goodIntegralEquation C h.2) h.1 _ (fun x hx =>
    (selectedFrobenius q i).property.2 x (tors_left_le_joint A (C⁄ℚ) F₀ Q _ hx)) b hb hσ

end SelectedStage

#print axioms rowOnOriginal
#print axioms rowOnOriginal_fixed
#print axioms reducedEquation_elliptic
#print axioms goodIntegralEquation
#print axioms torsionSpecialization
#print axioms torsionSpecialization_frob
#print axioms proj_onto
#print axioms finiteRow_fixed
#print axioms square_trivial_at
#print axioms evaluationAt
#print axioms stageMap_eq_lam_comp
#print axioms evaluationOfStage

end ZInQ.Manuscript.RC.PMGeometry
