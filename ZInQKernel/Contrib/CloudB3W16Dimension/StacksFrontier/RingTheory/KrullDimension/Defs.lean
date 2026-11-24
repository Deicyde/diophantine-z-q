module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Height

-- Match upstream elaboration settings; enable current Mathlib defeq compatibility.
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.defeqAttrib.useBackward true




/-!
# Krull dimension and height of a ring
-/

@[expose] public section

-- The former @[stacks 00KE] declaration is now the Mathlib definition.








-- The former @[stacks 00KF] declaration is now the Mathlib theorem.


/-- The Krull dimension of `R` equals the supremum of the heights of its prime ideals. -/

theorem ringKrullDim_eq_iSup_height (R : Type*) [CommRing R] :
    ringKrullDim R = ⨆ (I : PrimeSpectrum R), (I.asIdeal.height : WithBot ℕ∞) := by
  simp_rw [PrimeSpectrum.height_eq_orderHeight]
  exact Order.krullDim_eq_iSup_height

/-- The Krull dimension of `R` equals the supremum of the heights of its maximal ideals. -/

theorem ringKrullDim_eq_iSup_height_maximal (R : Type*) [CommRing R] :
    ringKrullDim R =
      ⨆ (I : {I : PrimeSpectrum R // I.asIdeal.IsMaximal}),
        (I.val.asIdeal.height : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_iSup_height]
  refine le_antisymm (iSup_le fun I ↦ ?_)
    (iSup_le fun ⟨I, _⟩ ↦ le_iSup (fun K : PrimeSpectrum R ↦
      (K.asIdeal.height : WithBot ℕ∞)) I)
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I.asIdeal I.isPrime.ne_top
  exact le_trans (by exact_mod_cast Ideal.height_mono hIm)
    (le_iSup (fun K : {K : PrimeSpectrum R // K.asIdeal.IsMaximal} ↦
      (K.val.asIdeal.height : WithBot ℕ∞)) ⟨⟨m, hm.isPrime⟩, hm⟩)

-- @[stacks 00KH] is already attached to Mathlib's equivalence.

-- The former @[stacks_fixed 0GIE] structure is represented by Mathlib's series.



end
