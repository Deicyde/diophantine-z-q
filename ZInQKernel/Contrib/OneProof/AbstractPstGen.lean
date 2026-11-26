import ZInQKernel.Contrib.OneProof.AbstractPst

/-! # Fontaine's potential semistability over the abstract `B_st`, for every choice of `ε₀` and `w`

The image ring `BstFOf p h w hw = B_cris[log [p̃]] ⊆ B_dR` is built from a generator `ε₀` of `ℤ_p(1)`
(`t = log [ε₀]` is inverted) and a generator `w` of `ker θ` (in `A_cris`). Neither choice changes the ring:
`acrisOf_eq` for `w`, and `bstFOf_eq_of_gen` for `ε₀` (another generator gives `log [ε₁] = a log [ε₀]` with
`a ∈ ℤ_p ∖ 0`, `tInv_mem_of`). So `IsPstF` at any choices is potential semistability over the abstract
`B_st = B_cris[X]` (`isPstF_iff_abstract`), and likewise on a model (`localIsPstF_iff_abstract`).
-/

noncomputable section

namespace HDec.PkgI4.AbstractPeriods

open BergerBst FontaineSt BmaxOne Module
open _root_.ZInQ.Contrib.G9.BdrKer.Cp (xi)

variable (p : ℕ) [Fact p.Prime]

/-- `B_cris[log [p̃]]` built with `1/log [ε₀]` lies in the one built with `1/log [ε₁]`. -/
theorem bstFOf_le_of_gen {ε₀ ε₁ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (h' : IsGenEps p ε₁)
    (w : PanBergerSplit.Ainf p) (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    BstFOf p h w hw ≤ BstFOf p h' w hw := by
  refine Algebra.adjoin_le ?_
  rintro x ((hx | hx) | hx)
  · exact Algebra.subset_adjoin (Or.inl (Or.inl hx))
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact tInv_mem_of p h' (BstFOf p h' w hw)
      (Algebra.subset_adjoin (Or.inl (Or.inr rfl)))
      ⟨ε₀, h.1, ne_one_of_isGenEps p h, rfl⟩
  · exact Algebra.subset_adjoin (Or.inr hx)

/-- **`B_st^{Fontaine}` does not depend on the generator `ε₀` of `ℤ_p(1)`.** -/
theorem bstFOf_eq_of_gen {ε₀ ε₁ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (h' : IsGenEps p ε₁)
    (w : PanBergerSplit.Ainf p) (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) :
    BstFOf p h w hw = BstFOf p h' w hw :=
  le_antisymm (bstFOf_le_of_gen p h h' w hw) (bstFOf_le_of_gen p h' h w hw)

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- **`IsPstF` at any generators `ε₀` and `w` is potential semistability over the abstract `B_st`.** -/
theorem isPstF_iff_abstract {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) {w : PanBergerSplit.Ainf p}
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w})
    (ρ : GQp p →* GL (Fin n) E) :
    IsPstF p h w hw ρ ↔ IsPstAbstract p ρ := by
  rw [isPstAbstract_iff]
  unfold IsPstF
  rw [bstFOf_eq_xi p h hw hgen, bstFOf_eq_of_gen p h (eps0_spec p)]

/-- A `ℚ̄_p`-valued representation is potentially semistable over the abstract `B_st` on a model `V = E^n`. -/
def LocalIsPstAbstract (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsPstAbstract p ρE

/-- **On a model: `LocalIsPstF` at any generators is `LocalIsPstAbstract`.** -/
theorem localIsPstF_iff_abstract {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀)
    {w : PanBergerSplit.Ainf p} (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0)
    (hgen : RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w}) (n : ℕ)
    (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) :
    LocalIsPstF p h w hw n ρ ↔ LocalIsPstAbstract p n ρ := by
  unfold LocalIsPstF LocalIsPstAbstract
  refine exists_congr fun E => exists_congr fun _ => exists_congr fun ρE => and_congr_right fun _ => ?_
  exact isPstF_iff_abstract p h hw hgen ρE

end HDec.PkgI4.AbstractPeriods
