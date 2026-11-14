
/-! ## g0-assemble: `ModularConstituent` from g0-mod-field's range and `AfterG7`

g0-mod-field proved `G0ModField.ModularConstituentG` (its copy of `ModularConstituent` over the
kernel's `PkgI3.AbVar`, without `LeafAdopt.abVarEquiv`) from `FibreCoverExists`,
`KernelFieldExists`, `UnramifiedSup`, the bundle's T14a, T14b, T15, T30, T31, and `AfterG7`.
Here its file is compiled over `Leaves.lean`'s copies (it needed only the kernel module
`Descent/WP3.lean`, copied above), and the layer caveat of g0-mod-newform is checked:
`LeafAdopt.abVarEquiv` commutes with `baseChange` definitionally (`abVarEquiv_baseChange`,
`abVarEquiv_symm_baseChange`, both `rfl`), so `ModularConstituentG → ModularConstituent` is a
repackaging (`modularConstituent_of_G`). -/

section G0AssembleModSec

namespace HSyn

/-- Layer check: def-faltings' `baseChange` and I3's `baseChange` agree through `abVarEquiv`. -/
theorem abVarEquiv_baseChange (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]
    (A : ZInQ.DefFaltings.AbVar K) :
    LeafAdopt.abVarEquiv L (A.baseChange L) = (LeafAdopt.abVarEquiv K A).baseChange L := rfl

/-- Layer check, the form `ModularConstituent` uses for `J₁(N)_L`. -/
theorem abVarEquiv_symm_baseChange (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]
    (J : PkgI3.AbVar K) :
    LeafAdopt.abVarEquiv L (((LeafAdopt.abVarEquiv K).symm J).baseChange L) = J.baseChange L :=
  rfl

/-- The two textual copies of `CommonConstituent` (g0-mod-field's, g0-split's) agree. -/
theorem commonConstituent_copy {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) :
    G0ModField.CommonConstituent A J ↔ G0Split.CommonConstituent A J := Iff.rfl

/-- **g0-mod-field's `ModularConstituentG` gives g0-split's `ModularConstituent`** (the model
`A : PkgI3.AbVar L` is sent to `(abVarEquiv L).symm A`; every clause is definitionally the same). -/
theorem modularConstituent_of_G (h : G0ModField.ModularConstituentG) :
    G0Split.ModularConstituent := by
  intro Y Φ π h1 h2 u hu y P hy hπ
  obtain ⟨L, emb, A, N, J, hiso, hN, hJ, hNle, hdeg, hCC⟩ := h Y Φ π h1 h2 u hu y P hy hπ
  refine ⟨L, emb, (LeafAdopt.abVarEquiv L.K).symm A, N, J, ?_, hN, hJ, hNle, hdeg, ?_⟩
  · exact hiso
  · rw [abVarEquiv_symm_baseChange, Equiv.apply_symm_apply]
    exact (commonConstituent_copy _ _).1 hCC

/-- **`ModularConstituent` from g0-mod-field's three glue Props, the bundle's T14a, T14b, T15,
T30 (`TextbookLeaves.leafSqrtCrit`, from T16a) and T31, and `AfterG7` (G8-G16).** -/
theorem modularConstituent_of_field (t : TextbookLeaves) (hCover : G0ModField.FibreCoverExists)
    (hKer : G0ModField.KernelFieldExists) (hSup : G0ModField.UnramifiedSup)
    (hRest : G0ModField.AfterG7) : G0Split.ModularConstituent :=
  modularConstituent_of_G (G0ModField.modularConstituent_of_ranges_T14 hCover hKer hSup t.t14a
    t.t14b t.t15 t.leafSqrtCrit t.t31 hRest)

end HSyn

end G0AssembleModSec

#print axioms HSyn.modularConstituent_of_field
