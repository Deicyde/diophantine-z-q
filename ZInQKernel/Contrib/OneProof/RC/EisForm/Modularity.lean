import ZInQKernel.Contrib.OneProof.RC.EisForm.Lipschitz
import ZInQKernel.Contrib.OneProof.RC.O12EisConst.Forms

/-! The remaining weight-two modularity check for the series of tex 9647–9654,
9762–9764 and 9862–9864. Packaging of the analytic checks is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisForm

open O12 O12EisConst O12Eisenstein UpperHalfPlane TauCeti
open CongruenceSubgroup Matrix.SpecialLinearGroup
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups Manifold ModularForm

variable {D : Type*} [Field D] {p : ℕ} [Fact p.Prime]

/-- The order in the divisor sum, with the weight factor on the second character. -/
def pairSeries (E : CharacterPair D p) (c : D →+* ℂ) (C : ℂ) : ℍ → ℂ :=
  if E.twistUnramified then series (E.ramified.ringHomComp c) (E.unram.ringHomComp c) C
  else series (E.unram.ringHomComp c) (E.ramified.ringHomComp c) C

theorem pairSeries_eq_lipschitz (E : CharacterPair D p) (c : D →+* ℂ)
    (hu : E.unram.IsPrimitive) (hr : E.ramified.IsPrimitive) (C : ℂ) (z : ℍ) :
    pairSeries E c C z =
      if E.twistUnramified then lipschitzSeries (E.ramified.ringHomComp c) (E.unram.ringHomComp c) C z
      else lipschitzSeries (E.unram.ringHomComp c) (E.ramified.ringHomComp c) C z := by
  by_cases ht : E.twistUnramified = true
  · simpa only [pairSeries, ite_eq_left ht] using
      series_eq_lipschitz (E.ramified.ringHomComp c) _ (primitive_ringHomComp E.unram c hu) C z
  · simpa only [pairSeries, ite_eq_right ht] using
      series_eq_lipschitz (E.unram.ringHomComp c) _ (primitive_ringHomComp E.ramified c hr) C z

theorem pairSeries_positive (E : CharacterPair D p) (c : D →+* ℂ) (C : ℂ) (n : PosIndex) :
    (qExpansion 1 (pairSeries E c C)).coeff n.val = c (E.coeff n.val) := by
  rw [← mapPair_coeff E c]
  unfold pairSeries CharacterPair.coeff
  have hr : (mapPair E c).ramified = E.ramified.ringHomComp c := by
    apply MulChar.ext
    intro u
    simp only [CharacterPair.ramified, MulChar.mul_apply, MulChar.ringHomComp_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, mapPair, quadraticDirichlet,
      map_mul, Int.coe_castRingHom, map_intCast]
  rw [hr]
  cases ht : E.twistUnramified <;>
    simp [mapPair, qExpansion_series, seriesCoeff, n.property]

theorem pairSeries_holo (E : CharacterPair D p) (c : D →+* ℂ) (C : ℂ) :
    MDiff (pairSeries E c C) := by
  unfold pairSeries
  split <;> exact series_holo _ _ _

theorem pairSeries_boundedAtInfty (E : CharacterPair D p) (c : D →+* ℂ) (C : ℂ) :
    IsBoundedAtImInfty (pairSeries E c C) := by
  unfold pairSeries
  split <;> exact series_boundedAtInfty _ _ _

/-- The weight-two transformation law for the already constructed function. -/
def PairSlashLaw (E : CharacterPair D p) (c : D →+* ℂ) (C : ℂ) : Prop :=
  ∀ g : Gamma0 (pairLevel E),
    pairSeries E c C ∣[(2 : ℤ)] mapGL ℝ (g : SL(2, ℤ)) =
      (↑(pairNebentypus E c ((Gamma0Map (pairLevel E)).toHomUnits g)) : ℂ) • pairSeries E c C

/-- The cusp bounds away from infinity for that same function. -/
def PairOtherCusps (E : CharacterPair D p) (c : D →+* ℂ) (C : ℂ) : Prop :=
  ∀ x : OnePoint ℝ, x ≠ OnePoint.infty →
    IsCusp x ((Gamma1 (pairLevel E)).map (mapGL ℝ)) →
    x.IsBoundedAt (pairSeries E c C) 2

/-- The remaining analytic proposition, for the ordered primitive pairs of
even product character. The constant is shared by the two checks. -/
def MissingModularity (E : CharacterPair D p) (c : D →+* ℂ) : Prop :=
  ∃ C : ℂ, PairSlashLaw E c C ∧ PairOtherCusps E c C

/-- The two analytic checks suffice to construct the exact base form in the
constituent interface, with no assumption about its positive expansion. -/
theorem baseForm_of_modularity (E : CharacterPair D p) (c : D →+* ℂ)
    (hu : E.unram.IsPrimitive) (hr : E.ramified.IsPrimitive) (C : ℂ)
    (hslash : PairSlashLaw E c C) (hcusp : PairOtherCusps E c C) :
    Nonempty (BaseForm E c) := by
  let f : ModularForm ((Gamma1 (pairLevel E)).map (mapGL ℝ)) 2 :=
    { toFun := pairSeries E c C
      slash_action_eq' := by
        intro γ hγ
        obtain ⟨g, hg, rfl⟩ := hγ
        let g₀ : Gamma0 (pairLevel E) := ⟨g, Gamma1_in_Gamma0 _ hg⟩
        have h₀ := (mem_Gamma1_iff_toHomUnits_eq_one g₀).mp hg
        simpa only [h₀, map_one, Units.val_one, one_smul] using hslash g₀
      holo' := pairSeries_holo E c C
      bdd_at_cusps' := by
        intro x hx
        by_cases he : x = OnePoint.infty
        · exact he ▸ (OnePoint.isBoundedAt_infty_iff.mpr (pairSeries_boundedAtInfty E c C))
        · exact hcusp x he hx }
  exact ⟨{
    unram_primitive := hu
    ram_primitive := hr
    form := f
    character := (mem_modFormCharSpace_iff_nebentypus 2 _ f).mpr hslash
    positive_expansion := pairSeries_positive E c C }⟩


end ZInQ.Manuscript.RC.EisForm
