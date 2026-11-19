import ZInQKernel.Contrib.CloudB3RC53.StageCone.Comparison

/-!
# Integral comparison criteria

The comparison torsion must preserve the integral determinant lattice, not
only its generic fibre. A contractible integral model of the augmented cone
is a sufficient certificate. This file also proves that a nondegenerate
stage always admits a generic comparison; the remaining content is integral.

These are algebraic criteria. No arithmetic model or integral certificate
for a continuous-cochain Selmer complex is assumed to have been constructed.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace ZInQ.Contrib.RC53Assist.StageCone

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.StageCone
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.CloudB3RC53.UniformSwitch
open ZInQ.Manuscript.RC.Central

section BaseChange

variable {A B : Type*} [CommRing A] [CommRing B]
variable {E O : Type*} [Fintype E] [Fintype O] [DecidableEq E] [DecidableEq O]

/-- Entrywise scalar extension of a based complex, retaining all degrees. -/
def basedBaseChange (f : A →+* B) (C : BasedCx A E O) : BasedCx B E O where
  degE := C.degE
  degO := C.degO
  even_degE := C.even_degE
  odd_degO := C.odd_degO
  dOE := C.dOE.map f
  dEO := C.dEO.map f
  dd_E := by
    rw [← Matrix.map_mul, C.dd_E, Matrix.map_zero _ f.map_zero]
  dd_O := by
    rw [← Matrix.map_mul, C.dd_O, Matrix.map_zero _ f.map_zero]
  deg_dOE := by
    intro i j h
    apply C.deg_dOE i j
    intro h0
    exact h (by simp [h0])
  deg_dEO := by
    intro i j h
    apply C.deg_dEO i j
    intro h0
    exact h (by simp [h0])

/-- Scalar extension of an integral contraction. -/
def contractionBaseChange (f : A →+* B) {C : BasedCx A E O}
    (h : Contraction C) : Contraction (basedBaseChange f C) where
  hOE := h.hOE.map f
  hEO := h.hEO.map f
  deg_hOE := by
    intro i j hh
    apply h.deg_hOE i j
    intro h0
    exact hh (by simp [h0])
  deg_hEO := by
    intro i j hh
    apply h.deg_hEO i j
    intro h0
    exact hh (by simp [h0])
  htpy_E := by
    change C.dEO.map f * h.hOE.map f + h.hEO.map f * C.dOE.map f = 1
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ f.map_add,
      h.htpy_E, Matrix.map_one _ f.map_zero f.map_one]
  htpy_O := by
    change C.dOE.map f * h.hEO.map f + h.hOE.map f * C.dEO.map f = 1
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ f.map_add,
      h.htpy_O, Matrix.map_one _ f.map_zero f.map_one]

/-- The determinant of the extended contraction is the extended determinant. -/
theorem tau_baseChange (f : A →+* B) (C : BasedCx A E O)
    (h : Contraction C) (s : E ≃ O) :
    tau (basedBaseChange f C) (contractionBaseChange f h) s = f (tau C h s) := by
  unfold tau
  have he : ((basedBaseChange f C).dOE + (contractionBaseChange f h).hOE).submatrix s id =
      ((C.dOE + h.hOE).submatrix s id).map f := by
    ext i j
    simp [basedBaseChange, contractionBaseChange, map_add]
  rw [he]
  exact (RingHom.map_det f ((C.dOE + h.hOE).submatrix s id)).symm

/-- Torsion commutes with scalar extension when an integral contraction is given. -/
theorem torsion_baseChange [IsDomain A] [IsDomain B] (f : A →+* B)
    (C : BasedCx A E O) (h : Contraction C) (s : E ≃ O) :
    torsion (basedBaseChange f C) s = f (torsion C s) := by
  rw [← tau_eq_torsion _ (contractionBaseChange f h), ← tau_eq_torsion C h s,
    tau_baseChange]

/-- A based integral model of a generic complex, with an actual contraction. -/
structure ContractibleIntegralLift (f : A →+* B) (C : BasedCx B E O) where
  model : BasedCx A E O
  identifies : basedBaseChange f model = C
  contractible : Nonempty (Contraction model)

end BaseChange

section Comparison

variable {A F : Type} [CommRing A] [Field F] {ι : A →+* F}
variable {S : TwoTermStage ι} {M : Matrix (Fin 2) (Fin 2) F} {z₀ l₀ : Fin 2 → F}

/-- The based cone whose torsion is used by the comparison interface. -/
abbrev augmentedComparisonCone (g : StageMap S M z₀ l₀)
    (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0) (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) :=
  BasedCx.cone (g.f.augMap _ _ (stage_hz S) (stage_hw S) z₀ l₀ hz₀ hl₀ g.hz g.hl)

/-- An actual integral contraction of the augmented cone proves the integral-unit condition. -/
theorem integralUnit_of_contractibleLift [IsDomain A] (g : StageMap S M z₀ l₀)
    (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0) (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0)
    (H : ContractibleIntegralLift ι (augmentedComparisonCone g hz₀ hl₀)) :
    g.IntegralUnit hz₀ hl₀ := by
  let s := (σ₀ 2).sumCongr (σ₀ (S.n + 1)).symm
  obtain ⟨h⟩ := H.contractible
  have hu : IsUnit (torsion H.model s) := by
    rw [← tau_eq_torsion H.model h s]
    exact isUnit_tau H.model h s
  obtain ⟨u, hu⟩ := hu
  have ht : g.coneTorsion hz₀ hl₀ = ι (u : A) := by
    change torsion (augmentedComparisonCone g hz₀ hl₀) s = _
    rw [← H.identifies, torsion_baseChange ι H.model h s, ← hu]
  let a : A := (-1) ^ Fintype.card (Fin (S.n + 1) ⊕ (Empty ⊕ Unit))
  have ha : IsUnit a := isUnit_one.neg.pow _
  obtain ⟨aU, haU⟩ := ha
  have hsign : ι a = stageSign S := by simp [a, stageSign]
  refine ⟨aU * u, ?_⟩
  rw [Units.val_mul, map_mul, haU, hsign, ← ht, ← mul_assoc,
    stageSign_mul_self, one_mul]

/-- A generic map obtained by projecting onto the class and the functional.
It is not asserted to preserve any integral lattice. -/
def collapsedStageMap (gHz : (twoTerm M).d1 *ᵥ z₀ = 0)
    (_gHl : l₀ ᵥ* (twoTerm M).d1 = 0) (i : Fin (S.n + 1)) (j : Fin 2)
    (hi : ι (S.z i) ≠ 0) (hj : l₀ j ≠ 0) : StageMap S M z₀ l₀ where
  f :=
    { f0 := 0
      f1 := vecMulVec z₀ (Pi.single i ((ι (S.z i))⁻¹))
      f2 := vecMulVec (Pi.single j ((l₀ j)⁻¹)) (fun t => ι (S.w t))
      f3 := 0
      c0 := by simp [twoTerm]
      c1 := by
        change M * vecMulVec z₀ (Pi.single i ((ι (S.z i))⁻¹)) =
          vecMulVec (Pi.single j ((l₀ j)⁻¹)) (fun t => ι (S.w t)) * S.D.map ι
        have hz : M *ᵥ z₀ = 0 := gHz
        have hw : (fun t => ι (S.w t)) ᵥ* S.D.map ι = 0 := stage_hw S
        rw [mul_vecMulVec, vecMulVec_mul, hz, hw]
        simp [vecMulVec]
      c2 := by simp [twoTerm] }
  hz := by
    ext k
    have hr : (Pi.single i ((ι (S.z i))⁻¹) : Fin (S.n + 1) → F) ⬝ᵥ
        (fun t => ι (S.z t)) = 1 := by simp [hi]
    simp only [mulVec, dotProduct, vecMulVec_apply]
    calc
      (∑ t, z₀ k * (Pi.single i ((ι (S.z i))⁻¹) : Fin (S.n + 1) → F) t * ι (S.z t)) =
          z₀ k * ((Pi.single i ((ι (S.z i))⁻¹) : Fin (S.n + 1) → F) ⬝ᵥ
            (fun t => ι (S.z t))) := by
              simp only [dotProduct, Finset.mul_sum, mul_assoc]
      _ = z₀ k := by rw [hr, mul_one]
  hl := by
    ext k
    have hr : l₀ ⬝ᵥ (Pi.single j ((l₀ j)⁻¹) : Fin 2 → F) = 1 := by simp [hj]
    simp only [vecMul, dotProduct, vecMulVec_apply]
    calc
      (∑ t, l₀ t * ((Pi.single j ((l₀ j)⁻¹) : Fin 2 → F) t * ι (S.w k))) =
          (l₀ ⬝ᵥ (Pi.single j ((l₀ j)⁻¹) : Fin 2 → F)) * ι (S.w k) := by
            simp only [dotProduct, Finset.sum_mul, mul_assoc]
      _ = ι (S.w k) := by rw [hr, one_mul]

/-- Generic comparison existence requires no determinant-lattice hypothesis. -/
theorem exists_stageMap (S : TwoTermStage ι) (M : Matrix (Fin 2) (Fin 2) F)
    (z₀ l₀ : Fin 2 → F) (hz₀ : (twoTerm M).d1 *ᵥ z₀ = 0)
    (hl₀ : l₀ ᵥ* (twoTerm M).d1 = 0) (hS : S.u ≠ 0)
    (hSad : (S.D.map ι).adjugate ≠ 0) (hl : l₀ ≠ 0) :
    Nonempty (StageMap S M z₀ l₀) := by
  obtain ⟨i, _, _, hi, _⟩ := exists_good_entry S.hu hS hSad
  have hj : ∃ j, l₀ j ≠ 0 := by
    by_contra h
    apply hl
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hj
  exact ⟨collapsedStageMap hz₀ hl₀ i j hi hj⟩

/-- In the nondegenerate scope, the comparison interface is exactly the two stage links. -/
theorem stageConeComparison_iff_links (S S' : TwoTermStage ι)
    {ε σ : F} (hε : ε ≠ 0) (hσ : σ ≠ 0) {J : Matrix (Fin 2) (Fin 2) F}
    {v : Fin 2 → F} (hv : v ≠ 0) (hv' : J *ᵥ v ≠ 0)
    (hS : S.u ≠ 0) (hSad : (S.D.map ι).adjugate ≠ 0)
    (hS' : S'.u ≠ 0) (hS'ad : (S'.D.map ι).adjugate ≠ 0) :
    StageConeComparison S S' ε σ J v ↔
      StageModelLink ι S.u (oldMat ε v) v (Pi.single 0 1) ∧
        StageModelLink ι S'.u (newMat ε σ J v) (J *ᵥ v) (Pi.single 1 1) := by
  constructor
  · intro h
    exact ⟨stageModelLink_old hε hv hS hSad h.1,
      stageModelLink_new hε hσ hv' hS' hS'ad h.2⟩
  · rintro ⟨hold, hnew⟩
    obtain ⟨g⟩ := exists_stageMap S _ _ _ (oldMat_hz ε v) (oldMat_hl ε v)
      hS hSad (by intro h; have h0 := congrFun h 0; simp at h0)
    obtain ⟨g'⟩ := exists_stageMap S' _ _ _ (newMat_hz ε σ J v) (newMat_hl ε σ J v)
      hS' hS'ad (by intro h; have h1 := congrFun h 1; simp at h1)
    exact ⟨⟨g, (stageModelLink_iff g _ _ hS hSad (oldMat_coord hε v)
      (neg_ne_zero.mpr (inv_ne_zero hε)) (oldMat_adjugate_ne_zero hε hv)).1 hold⟩,
      ⟨g', (stageModelLink_iff g' _ _ hS' hS'ad (newMat_coord hε hσ J v)
        (inv_ne_zero (mul_ne_zero hσ hε)) (newMat_adjugate_ne_zero hε hσ hv')).1 hnew⟩⟩

/-- Integral cone reduction supplies comparison existence as well as the unit certificates. -/
theorem stageConeComparison_of_identification (S S' : TwoTermStage ι)
    {ε σ : F} (hε : ε ≠ 0) (hσ : σ ≠ 0) {J : Matrix (Fin 2) (Fin 2) F}
    {v : Fin 2 → F} (hv : v ≠ 0) (hv' : J *ᵥ v ≠ 0)
    (hS : S.u ≠ 0) (hSad : (S.D.map ι).adjugate ≠ 0)
    (hS' : S'.u ≠ 0) (hS'ad : (S'.D.map ι).adjugate ≠ 0)
    (H : StageConeIdentification ι S S' ε σ J v) :
    StageConeComparison S S' ε σ J v := by
  apply (stageConeComparison_iff_links S S' hε hσ hv hv' hS hSad hS' hS'ad).2
  exact ⟨stageModelLink_of_coneReduction ι S.D S.z S.w S.u S.hu _ _ _ H.1
      (oldMat_adjugate_ne_zero hε hv),
    stageModelLink_of_coneReduction ι S'.D S'.z S'.w S'.u S'.hu _ _ _ H.2
      (newMat_adjugate_ne_zero hε hσ hv')⟩

end Comparison

set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true

end ZInQ.Contrib.RC53Assist.StageCone
