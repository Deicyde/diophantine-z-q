import ZInQKernel.Contrib.OneProof.Y3ComplexQuotient
import ZInQKernel.Contrib.OneProof.GammaStarArea

/-! The topological period quotient is a sphere. -/

noncomputable section

open HDec HDec.HSyn.G0Split.FibreQM

namespace Y3P1j

/-- The quotient topology from the complex period map is the topology of
the Riemann sphere. -/
theorem period_quotient_homeomorphic_sphere {A : Type*} (F : UpperHalfPlane → A)
    (hF : ∀ τ τ', F τ = F τ' ↔ ∃ g ∈ PkgI1.GammaStar, g • τ = τ')
    (h : PkgI1.QMHauptmodul) :
    Nonempty (Quotient (Setoid.ker F) ≃ₜ OnePoint ℂ) := by
  obtain ⟨f, hf⟩ := qmHauptmodul_iff.mp h
  let R := Setoid.ker F
  have hrel (τ τ' : UpperHalfPlane) : R.r τ τ' ↔ f τ = f τ' :=
    (hF τ τ').trans (hf.2.2.1 τ τ').symm
  let m : Quotient R → OnePoint ℂ := Quotient.lift f (fun τ τ' h => (hrel τ τ').mp h)
  have hm : Continuous m := hf.1.quotient_lift _
  have hb : Function.Bijective m := by
    constructor
    · rintro ⟨τ⟩ ⟨τ'⟩ h
      exact Quotient.sound ((hrel τ τ').mpr h)
    · intro x
      obtain ⟨τ, hτ⟩ := hf.2.2.2.1 x
      exact ⟨Quotient.mk R τ, hτ⟩
  have himage : Quotient.mk R '' GammaStarArea.Tset = Set.univ := by
    refine Set.eq_univ_of_forall ?_
    intro q
    obtain ⟨τ, rfl⟩ := Quotient.exists_rep q
    obtain ⟨g, hg, hs⟩ := GammaStarArea.cover_T τ
    exact ⟨g • τ, hs, (Quotient.sound ((hF τ (g • τ)).mpr ⟨g, hg, rfl⟩)).symm⟩
  have : CompactSpace (Quotient R) := ⟨himage ▸
    GammaStarArea.isCompact_T.image (continuous_quotient_mk' (s := R))⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective m hb) hm⟩

end Y3P1j

#print axioms Y3P1j.period_quotient_homeomorphic_sphere
