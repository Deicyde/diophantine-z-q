import lowering.MinimalLevelNewness
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.CharacterDecomp
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis

/-!
# An actual newform in the original finite rational translate orbit

At the proved minimal positive level, actual diamond projections and the entire
good-Hecke joint family stay inside the original function orbit. Minimality
supplies genuine newness. Only then is the actual first-coefficient nonvanishing
and normalized newform constructor used. No ambient newform span is inverted.
-/

noncomputable section
set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane HeckeRing.GL2
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.ReverseHecke

/-- An actual diamond operator preserves the original rational translate cusp orbit at any positive level. -/
theorem diamondOpCusp_mem_cuspOrbit (L : ℕ) [NeZero L] (k : ℤ) (f : ℍ → ℂ)
    (u : (ZMod L)ˣ) {g : CuspForm ((Gamma1 L).map (mapGL ℝ)) k}
    (hg : g ∈ cuspOrbit L k f) : diamondOpCusp k u g ∈ cuspOrbit L k f := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := L) u
  change ⇑(diamondOpCusp k u g) ∈ functionOrbit k f
  rw [coe_diamondOpCusp k u γ hγ]
  have hpos : 0 < (mapGL ℚ (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℚ).det :=
    _root_.ModularForm.map_mapGL_le_glpos (Gamma0 L) (Subgroup.mem_map_of_mem _ γ.property)
  simpa only [map_mapGL] using slash_mem_functionOrbit k f hg (mapGL ℚ (γ : SL(2, ℤ))) hpos

/-- The actual cusp orbit is stable under every actual diamond group operator. -/
theorem cuspOrbit_diamond_invariant (L : ℕ) [NeZero L] (k : ℤ) (f : ℍ → ℂ) :
    ∀ u : (ZMod L)ˣ, ∀ g ∈ cuspOrbit L k f,
      diamondOpCuspHom k u g ∈ cuspOrbit L k f := by
  intro u g hg
  rw [diamondOpCuspHom_apply]
  exact diamondOpCusp_mem_cuspOrbit L k f u hg

/-- A nonzero actual cusp orbit has a nonzero actual character component in that same orbit. -/
theorem exists_nonzero_character_in_cuspOrbit (L : ℕ) [NeZero L] (k : ℤ) (f : ℍ → ℂ)
    (g : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) (hg0 : g ≠ 0) (hg : g ∈ cuspOrbit L k f) :
    ∃ χ : (ZMod L)ˣ →* ℂˣ, ∃ h : CuspForm ((Gamma1 L).map (mapGL ℝ)) k,
      h ≠ 0 ∧ h ∈ cuspFormCharSpace k χ ∧ h ∈ cuspOrbit L k f := by
  obtain ⟨a, ha, heq⟩ := exists_finsupp_of_diamondOpCusp_invariant k (cuspOrbit L k f)
    (cuspOrbit_diamond_invariant L k f) hg
  by_contra hnone
  have hz : ∀ χ, a χ = 0 := by
    intro χ
    by_contra hχ
    exact hnone ⟨χ, a χ, hχ, (ha χ).2, (ha χ).1⟩
  have hsum : a.sum (fun _ y ↦ y) = 0 := by
    classical
    simp only [Finsupp.sum]
    exact Finset.sum_eq_zero fun χ _ ↦ hz χ
  exact hg0 (heq.symm.trans hsum)

/-- Produce a genuine normalized newform, of some positive level at most N squared,
in a finite complex positive-rational translate combination of the original principal cusp form. -/
theorem principal_newform_rational_translates (N : ℕ) [NeZero N] (k : ℕ) (hk : 2 ≤ k)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) (k : ℤ)) (hf : f ≠ 0) :
    ∃ L : ℕ, ∃ hL : 0 < L,
      letI : NeZero L := ⟨hL.ne'⟩
      ∃ E : Newform L (k : ℤ),
        L ≤ N ^ 2 ∧ E.toCuspForm ≠ 0 ∧
          E.toCuspForm ∈ TauCeti.cuspFormsNew L (k : ℤ) ∧
          (qExpansion 1 E.toCuspForm).coeff 1 = 1 ∧
          ∃ m : ℕ, ∃ c : Fin m → ℂ, ∃ α : Fin m → GL (Fin 2) ℚ,
            (∀ i, 0 < (α i : Matrix (Fin 2) (Fin 2) ℚ).det) ∧
              ⇑E.toCuspForm = ∑ i, c i •
                (⇑f ∣[(k : ℤ)] GeneralLinearGroup.map (algebraMap ℚ ℝ) (α i)) := by
  obtain ⟨L, hL, hdata⟩ := principal_minimal_new_cusp N k hk f hf
  let : NeZero L := ⟨hL.ne'⟩
  obtain ⟨hbound, hnewOrbit, G, hG0, hG⟩ := hdata
  obtain ⟨χ, H, hH0, hHχ, hH⟩ := exists_nonzero_character_in_cuspOrbit L (k : ℤ) ⇑f G hG0 hG
  have hHchar0 : (⟨H, hHχ⟩ : cuspFormCharSpace (k : ℤ) χ) ≠ 0 :=
    fun hz ↦ hH0 (congrArg Subtype.val hz)
  have hHorb : (⟨H, hHχ⟩ : cuspFormCharSpace (k : ℤ) χ) ∈
      characterOrbit L (k : ℤ) χ ⇑f := hH
  obtain ⟨a, h, hh0, hhorbit, heig⟩ := exists_nonzero_good_joint_component
    L (k : ℤ) χ ⇑f ⟨H, hHχ⟩ hHchar0 hHorb
  have hfn0 : h.val ≠ 0 := fun hz ↦ hh0 (Subtype.ext hz)
  have hnew : h.val ∈ TauCeti.cuspFormsNew L (k : ℤ) := hnewOrbit hhorbit
  have hprime : ∀ p : ℕ, p.Prime → p.Coprime L → ∃ b : ℂ,
      heckeRingHomCuspCharSpace (k : ℤ) χ (heckeTGeneratorGamma0 L p)
        ⟨h.val, h.property⟩ = b • ⟨h.val, h.property⟩ := by
    intro p hp hpL
    exact ⟨a ⟨p, hp, hpL⟩, heig ⟨p, hp, hpL⟩⟩
  have hcoeff : (qExpansion 1 h.val).coeff 1 ≠ 0 :=
    TauCeti.qExpansion_coeff_one_ne_zero_of_mem_cuspFormsNew h.property hnew hfn0 hprime
  let E := Newform.ofForallPrime h.property hnew hfn0 hprime
  have hE0 : E.toCuspForm ≠ 0 := by
    change (Newform.ofForallPrime h.property hnew hfn0 hprime).toCuspForm ≠ 0
    rw [Newform.ofForallPrime_toCuspForm]
    exact smul_ne_zero (inv_ne_zero hcoeff) hfn0
  have hEorb : ⇑E.toCuspForm ∈ functionOrbit (k : ℤ) ⇑f := by
    change ⇑(Newform.ofForallPrime h.property hnew hfn0 hprime).toCuspForm ∈ functionOrbit (k : ℤ) ⇑f
    rw [Newform.ofForallPrime_toCuspForm, FunLike.coe_smul]
    exact (functionOrbit (k : ℤ) ⇑f).smul_mem ((qExpansion 1 h.val).coeff 1)⁻¹ hhorbit
  refine ⟨L, hL, E, hbound, hE0, E.isNew, E.isNorm, ?_⟩
  exact functionOrbit_representation (k : ℤ) ⇑f hEorb

end ZInQ.Contrib.HeckePrimeRationality.ReverseHecke
