import ZInQKernel.Contrib.OneProof.AfTateLambda

/-! The Γ₁(N) transport of the actual `AtTau` predicate. -/

noncomputable section

namespace ShimuraSteps.HeckeJ

open CategoryTheory AlgebraicGeometry LeafModCurves AfTateLam UpperHalfPlane T5Glue
open scoped MatrixGroups Pointwise
open Filter

variable {X : Over SpecQ} [IsIntegral X.left]

/-- The part of the uniformization dictionary that removes a lift of the unit
class `1`. The conditions on the lower row imply membership in Γ₁(N). -/
def TauGammaOne (N : ℕ) (jX tX : X.left.functionField) : Prop :=
  ∀ (g : SL(2, ℤ)), (N : ℤ) ∣ g 1 0 → ((g 1 1 : ℤ) : ZMod N) = 1 →
    ∀ (τ : UpperHalfPlane) (x : CPt X), AtTau N jX tX x (g • τ) ↔ AtTau N jX tX x τ

private theorem scale_lattice (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    IsScale (pp τ) (pp (g • τ)) ((g 1 0 : ℂ) * τ + g 1 1) := by
  let C : ℂ := (g 1 0 : ℂ) * τ + g 1 1
  have hC : C ≠ 0 := by
    simpa [C, ModularGroup.denom_apply] using (denom_ne_zero g τ)
  have hprod : C * ((g • τ : UpperHalfPlane) : ℂ) = (g 0 0 : ℂ) * τ + g 0 1 := by
    have h : ((g • τ : UpperHalfPlane) : ℂ) = ((g 0 0 : ℂ) * τ + g 0 1) / C := by
      rw [coe_specialLinearGroup_apply]
      simp [C]
    rw [h, mul_div_cancel₀ _ hC]
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  refine ⟨hC, ?_⟩
  ext z
  simp only [SetLike.mem_coe, Set.mem_smul_set, smul_eq_mul, PeriodPair.mem_lattice, pp]
  constructor
  · rintro ⟨m, n, rfl⟩
    let a : ℤ := g 0 0 * m - g 0 1 * n
    let b : ℤ := g 1 1 * n - g 1 0 * m
    refine ⟨(a : ℂ) * 1 + (b : ℂ) * ((g • τ : UpperHalfPlane) : ℂ), ⟨a, b, rfl⟩, ?_⟩
    rw [mul_add, mul_left_comm C (b : ℂ), hprod]
    dsimp [C, a, b]
    push_cast
    linear_combination ((m : ℂ) + (n : ℂ) * τ) * hdet
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    refine ⟨g 1 1 * m + g 0 1 * n, g 1 0 * m + g 0 0 * n, ?_⟩
    rw [mul_add, mul_left_comm C (n : ℂ), hprod]
    push_cast
    ring

private theorem evAn_smul (N : ℕ) (g : SL(2, ℤ)) (hg0 : (N : ℤ) ∣ g 1 0)
    (hg1 : ((g 1 1 : ℤ) : ZMod N) = 1)
    (P : Polynomial (Polynomial ℚ)) (τ : UpperHalfPlane) :
    X1Igusa.Weber.evAn N P (g • τ) = X1Igusa.Weber.evAn N P τ := by
  let C : ℂ := (g 1 0 : ℂ) * τ + g 1 1
  have hs : IsScale (pp τ) (pp (g • τ)) C := scale_lattice g τ
  have hw : weber (pp (g • τ)) (1 / (N : ℂ)) = weber (pp τ) (1 / (N : ℂ)) := by
    by_cases hN : N = 0
    · simpa [hN] using (hs.weber 0).symm
    have hd : (N : ℤ) ∣ g 1 1 - 1 := by
      exact dvd_sub_comm.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub (g 1 1) 1 N).mp (by simpa using hg1))
    obtain ⟨c, hc⟩ := hg0
    obtain ⟨d, hd⟩ := hd
    have hcd : C * (1 / (N : ℂ)) = 1 / (N : ℂ) + ((d : ℂ) * 1 + (c : ℂ) * τ) := by
      have hc' : (g 1 0 : ℂ) = (N : ℂ) * (c : ℂ) := by exact_mod_cast hc
      have hd' : (g 1 1 : ℂ) = 1 + (N : ℂ) * (d : ℂ) := by
        exact_mod_cast (show g 1 1 = 1 + (N : ℤ) * d by omega)
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      dsimp [C]
      rw [hc', hd']
      field_simp
      ring
    rw [← hs.weber, hcd]
    exact weber_add_mem _ _ _ (PeriodPair.mem_lattice.mpr ⟨d, c, rfl⟩)
  rw [X1Igusa.Weber.evAn, X1Igusa.Weber.evAn, ← hs.jL, hw]

/-- The two defining coordinates are invariant under a lift of the unit class
`1`, by change of lattice basis and periodicity of the Weber function.
The Möbius homeomorphism transports the punctured limits in `AtTau`. -/
theorem tauGammaOne (N : ℕ) (jX tX : X.left.functionField) : TauGammaOne N jX tX := by
  intro g hg0 hg1 τ x
  let e : UpperHalfPlane ≃ₜ UpperHalfPlane := Homeomorph.smul (Matrix.SpecialLinearGroup.mapGL ℝ g)
  change AtTau N jX tX x (e τ) ↔ AtTau N jX tX x τ
  have hlim (P Q : Polynomial (Polynomial ℤ)) (c : ℂ) :
      let f := fun w => X1Igusa.Weber.evAn N (AfTateOr.toQ P) w /
        X1Igusa.Weber.evAn N (AfTateOr.toQ Q) w
      Tendsto f (nhdsWithin (e τ) {e τ}ᶜ) (nhds c) ↔
        Tendsto f (nhdsWithin τ {τ}ᶜ) (nhds c) := by
    let f := fun w => X1Igusa.Weber.evAn N (AfTateOr.toQ P) w /
        X1Igusa.Weber.evAn N (AfTateOr.toQ Q) w
    change Filter.map f (nhdsWithin (e τ) {e τ}ᶜ) ≤ nhds c ↔ _
    rw [← e.map_punctured_nhds_eq τ, Filter.map_map]
    have hf : f ∘ e = f := by
      funext w
      change _ / _ = _
      dsimp only [f, Function.comp_apply]
      change X1Igusa.Weber.evAn N _ (g • w) / X1Igusa.Weber.evAn N _ (g • w) = _
      rw [evAn_smul N g hg0 hg1, evAn_smul N g hg0 hg1]
    rw [hf]
    rfl
  exact ⟨fun h P Q c hQ hc => h P Q c hQ ((hlim P Q c).2 hc),
    fun h P Q c hQ hc => h P Q c hQ ((hlim P Q c).1 hc)⟩

#print axioms scale_lattice
#print axioms evAn_smul
#print axioms tauGammaOne

end ShimuraSteps.HeckeJ
