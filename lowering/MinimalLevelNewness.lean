import lowering.DegeneracyLowering

/-!
# Minimal positive level forces actual newness in a rational translate orbit

A nonzero old degeneracy pairing gives an actual lower-level cusp form by the
proved adjoint trace. The function remains in the original orbit, including the
cases where the negative identity changes membership between the two levels.
Choosing the least positive level with a nonzero orbit cusp therefore makes
every orbit cusp at that level new.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.ReverseHecke

/-- A nonzero actual degeneracy pairing gives a nonzero lower cusp in the original orbit,
with the actual center and integer-weight normalization conditions discharged. -/
theorem exists_lower_cusp_of_pairing (L M d : ℕ) [NeZero L] (hdvd : d * M ∣ L)
    (k : ℤ) (f : ℍ → ℂ) (F : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (hF : ⇑F ∈ functionOrbit k f) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hpair : haveI : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
      CuspForm.peterssonInnerCosets
        (TauCeti.CuspForm.levelRaise d (TauCeti.Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd) g) F ≠ 0) :
    ∃ G : CuspForm ((Gamma1 M).map (mapGL ℝ)) k, G ≠ 0 ∧ ⇑G ∈ functionOrbit k f := by
  classical
  let : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
  let : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
  have hle := TauCeti.Gamma1_map_le_conjAct_scaleGL_of_dvd hdvd
  by_cases hnegM : (-1 : SL(2, ℤ)) ∈ Gamma1 M
  · have hg0 : g ≠ 0 := by
      intro hg
      have hz : TauCeti.CuspForm.levelRaise d hle g = 0 := by
        apply DFunLike.ext
        intro τ
        rw [TauCeti.CuspForm.levelRaise_apply, hg]
        rfl
      exact hpair (by rw [hz, CuspForm.peterssonInnerCosets_zero_left])
    have hk := central_scalar_eq_one (Gamma1 M) k hnegM g hg0
    let gC := centerLift (Gamma1 M) k hk g
    let FC := centerLift (Gamma1 L) k hk F
    have hleC := conjugate_inclusion_withCenter (Gamma1 M) (Gamma1 L) (TauCeti.scaleGL d) hle
    have hVC : TauCeti.CuspForm.levelRaise d hleC gC =
        centerLift (Gamma1 L) k hk (TauCeti.CuspForm.levelRaise d hle g) := by
      apply DFunLike.coe_injective
      simp only [gC, TauCeti.CuspForm.coe_levelRaise, centerLift_coe]
    have hpairC : CuspForm.peterssonInnerCosets (TauCeti.CuspForm.levelRaise d hleC gC) FC ≠ 0 := by
      rw [hVC]
      change CuspForm.peterssonInnerCosets
        (centerLift (Gamma1 L) k hk (TauCeti.CuspForm.levelRaise d hle g))
        (centerLift (Gamma1 L) k hk F) ≠ 0
      rw [petersson_centerLift]
      exact hpair
    have hVnorm : TauCeti.CuspForm.levelRaise d hleC gC =
        (d : ℂ) ^ (1 - k) • CuspForm.restrict hleC (CuspForm.translate gC (TauCeti.scaleGL d)) := by
      apply DFunLike.coe_injective
      rw [TauCeti.CuspForm.coe_levelRaise, FunLike.coe_smul,
        CuspForm.coe_restrict, CuspForm.coe_translate]
    have hrawC : CuspForm.peterssonInnerCosets
        (CuspForm.restrict hleC (CuspForm.translate gC (TauCeti.scaleGL d))) FC ≠ 0 := by
      intro hz
      apply hpairC
      rw [hVnorm, CuspForm.peterssonInnerCosets_smul_left, hz, mul_zero]
    have hleC' : (Gamma1 L).withCenter.map (mapGL ℝ) ≤ ConjAct.toConjAct
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) (TauCeti.scaleGLRat d))⁻¹ •
          (Gamma1 M).withCenter.map (mapGL ℝ) := by
      simpa only [TauCeti.map_ratCast_scaleGLRat] using hleC
    have heqC : CuspForm.restrict hleC'
        (CuspForm.translate gC (GeneralLinearGroup.map (algebraMap ℚ ℝ) (TauCeti.scaleGLRat d))) =
        CuspForm.restrict hleC (CuspForm.translate gC (TauCeti.scaleGL d)) := by
      apply DFunLike.coe_injective
      rw [CuspForm.coe_restrict, CuspForm.coe_restrict, CuspForm.coe_translate,
        CuspForm.coe_translate, TauCeti.map_ratCast_scaleGLRat]
    have hrawC' : CuspForm.peterssonInnerCosets (CuspForm.restrict hleC'
        (CuspForm.translate gC (GeneralLinearGroup.map (algebraMap ℚ ℝ) (TauCeti.scaleGLRat d)))) FC ≠ 0 := by
      rw [heqC]
      exact hrawC
    have hFC : ⇑FC ∈ functionOrbit k f := by
      change ⇑(centerLift (Gamma1 L) k hk F) ∈ functionOrbit k f
      rw [centerLift_coe]
      exact hF
    have hnegC : (-1 : SL(2, ℤ)) ∈ (Gamma1 M).withCenter ↔
        (-1 : SL(2, ℤ)) ∈ (Gamma1 L).withCenter :=
      ⟨fun _ ↦ neg_one_mem_withCenter (Gamma1 L), fun _ ↦ neg_one_mem_withCenter (Gamma1 M)⟩
    obtain ⟨G, hG0, hG⟩ := exists_nonzero_adjoint_trace_in_orbit
      (Gamma1 M).withCenter (Gamma1 L).withCenter (TauCeti.scaleGLRat d)
      (scaleGLRat_hasIntEntries d) (scaleGLRat_det_pos d) hleC' hnegC k f FC hFC gC hrawC'
    refine ⟨CuspForm.restrict (Subgroup.map_mono (Gamma1 M).le_withCenter) G, ?_, ?_⟩
    · intro hz
      exact hG0 ((CuspForm.restrict_eq_zero_iff _).mp hz)
    · rwa [CuspForm.coe_restrict]
  · have hnegL : (-1 : SL(2, ℤ)) ∉ Gamma1 L := fun h ↦
      hnegM (Gamma1_le_Gamma1_of_dvd (dvd_of_mul_left_dvd hdvd) h)
    have hneg : (-1 : SL(2, ℤ)) ∈ Gamma1 M ↔ (-1 : SL(2, ℤ)) ∈ Gamma1 L :=
      ⟨fun h ↦ False.elim (hnegM h), fun h ↦ False.elim (hnegL h)⟩
    exact exists_lower_cusp_of_pairing_same_center L M d hdvd hneg k f F hF g hpair

/-- Positive levels at which an actual nonzero orbit cusp exists. -/
def HasNonzeroOrbitCusp (k : ℤ) (f : ℍ → ℂ) (L : ℕ) : Prop :=
  0 < L ∧ ∃ F : CuspForm ((Gamma1 L).map (mapGL ℝ)) k,
    F ≠ 0 ∧ ⇑F ∈ functionOrbit k f

/-- At a genuinely minimal positive level every actual orbit cusp is new. -/
theorem cuspOrbit_le_new_of_minimal (L : ℕ) [NeZero L] (k : ℤ) (f : ℍ → ℂ)
    (hmin : ∀ M : ℕ, 0 < M → M < L →
      ∀ G : CuspForm ((Gamma1 M).map (mapGL ℝ)) k, G ≠ 0 →
        ⇑G ∈ functionOrbit k f → False) :
    cuspOrbit L k f ≤ TauCeti.cuspFormsNew L k := by
  intro F hF
  rw [TauCeti.mem_cuspFormsNew_iff]
  intro M d hdvd hM g
  let : NeZero d := NeZero.of_dvd (dvd_of_mul_right_dvd hdvd)
  let : NeZero M := NeZero.of_dvd (dvd_of_mul_left_dvd hdvd)
  by_contra hpair
  obtain ⟨G, hG0, hG⟩ := exists_lower_cusp_of_pairing L M d hdvd k f F hF g hpair
  have hML : M < L := (Nat.le_of_dvd (NeZero.pos L) (dvd_of_mul_left_dvd hdvd)).lt_of_ne hM
  exact hmin M (NeZero.pos M) hML G hG0 hG

/-- The original nonzero principal cusp form supplies an actual positive-level orbit witness. -/
theorem principal_square_orbit_witness (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (hf : f ≠ 0) :
    HasNonzeroOrbitCusp k ⇑f (N ^ 2) := by
  obtain ⟨χ, g, hg0, hg⟩ := exists_nonzero_characterOrbit N k f hf
  refine ⟨pow_pos (NeZero.pos N) 2, g.val, fun hz ↦ hg0 (Subtype.ext hz), ?_⟩
  exact hg

/-- The original principal cusp form has a least positive nonzero cusp level in its own orbit,
and every cusp in that orbit at this level is actually new. -/
theorem principal_minimal_new_cusp (N : ℕ) [NeZero N] (k : ℕ) (_hk : 2 ≤ k)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) (k : ℤ)) (hf : f ≠ 0) :
    ∃ L : ℕ, ∃ hL : 0 < L,
      letI : NeZero L := ⟨hL.ne'⟩
      L ≤ N ^ 2 ∧
        cuspOrbit L (k : ℤ) ⇑f ≤ TauCeti.cuspFormsNew L (k : ℤ) ∧
        ∃ F : CuspForm ((Gamma1 L).map (mapGL ℝ)) (k : ℤ),
          F ≠ 0 ∧ ⇑F ∈ functionOrbit (k : ℤ) ⇑f := by
  classical
  have hseed := principal_square_orbit_witness N (k : ℤ) f hf
  have hex : ∃ L : ℕ, HasNonzeroOrbitCusp (k : ℤ) ⇑f L := ⟨N ^ 2, hseed⟩
  let L := Nat.find hex
  have hspec : HasNonzeroOrbitCusp (k : ℤ) ⇑f L := Nat.find_spec hex
  let : NeZero L := ⟨hspec.1.ne'⟩
  have hmin : ∀ M : ℕ, 0 < M → M < L →
      ∀ G : CuspForm ((Gamma1 M).map (mapGL ℝ)) (k : ℤ), G ≠ 0 →
        ⇑G ∈ functionOrbit (k : ℤ) ⇑f → False := by
    intro M hM hML G hG0 hG
    exact Nat.find_min hex hML ⟨hM, G, hG0, hG⟩
  refine ⟨L, hspec.1, Nat.find_min' hex hseed,
    cuspOrbit_le_new_of_minimal L (k : ℤ) ⇑f hmin, ?_⟩
  exact hspec.2

end ZInQ.Contrib.HeckePrimeRationality.ReverseHecke
