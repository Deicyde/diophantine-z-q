import ZInQKernel.Contrib.OneProof.PanBergerFontaine
import ZInQKernel.Contrib.OneProof.AbstractPstGen

/-! # Berger's and Pan's leaves restated from refereed prints

* `ColmezThm01`: every de Rham representation is potentially semistable, in the printed form of
  Colmez, Astérisque 319 (2008), Théorème 0.1. It gives the field `bergerSurveyF`
  (`bergerSurveyF_of_colmez`), whose current citation, Brinon–Conrad's notes, is unrefereed.
* `PanThm104F`: Pan's Theorem 1.0.4 with "potentially semi-stable in the sense of Fontaine" in Fontaine's
  own definition (Astérisque 223 (1994), Exp. III, 5.6.1 and 1.8.5). Its statement is the field
  `panPrintedF` (`panPrintedF_of_thm104F`); only the source of the definitions changes, from
  Brinon–Conrad's notes to Fontaine's exposés.

Both use Fontaine's `B_st` as a subring of `B_dR`. That `BstFOf` is that subring is proved:
`AcrisImage.acris_image` (the image of `A_cris` is `AcrisOf`), `AbstractPeriods.range_bcrisEmb` and
`AbstractPeriods.range_bstEmb` (the images of `B_cris` and `B_st`).
-/

noncomputable section

namespace HDec.PkgI4.PanBergerRefereed

open BmaxOne BergerBst PanBergerSplit FontaineSt PanDict

/-- **Colmez's theorem: every de Rham representation is potentially semistable** (P. Colmez, *Espaces
vectoriels de dimension finie et représentations de de Rham*, Astérisque 319 (2008), 117–186, Théorème 0.1,
p. 118: "Toute représentation de de Rham de 𝒢_K est potentiellement semi-stable"), at `K = ℚ_p`, for
`V = E^n` (`E/ℚ_p` finite inside `ℚ̄_p`, `ρ_E : G_{ℚ_p} → GL_n(E)` continuous), in the print's own
definitions (§0.2, p. 118):

* de Rham: `dim_{ℚ_p} (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}} = dim_{ℚ_p} V` (`IsDeRhamU`), the condition
  `dim_K D_dR(V) = d` that the print states as equivalent to its definition
  `B_dR^+[1/t] ⊗_{ℚ_p} V ≅ (B_dR^+[1/t])^d`;
* semistable over `L`: `B_st^+[1/t] ⊗_{ℚ_p} V ≅ (B_st^+[1/t])^d` as a module with semilinear `G_L`-action,
  i.e. `B_st^+[1/t] ⊗_{ℚ_p} V` has a basis of `G_L`-invariant vectors (`IsAdmissibleT`); potentially
  semistable: semistable over some finite `L/ℚ_p` inside `ℚ̄_p` (`IsPstFBasis`);
* `B_cris^+ ⊂ B_st^+ ⊂ B_dR^+` are Fontaine's rings (Astérisque 223 (1994), Exp. II), with
  `B_st^+ = B_cris^+[u]` (p. 120), so `B_st^+[1/t] = B_cris[u] ⊆ B_dR` is `BstFOf` (`u = log([p̃]/p)`,
  `log p = 0`).

Stated for every generator `ε₀` of `ℤ_p(1)` and every generator `w` of `ker θ`; the ring does not depend on
them (`acrisOf_eq`, `AbstractPeriods.bstFOf_eq_of_gen`). The statement is `PanDict.BergerSurveyFBasis`. -/
def ColmezThm01 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E),
      Continuous ρE → IsDeRhamU p ρE → IsPstFBasis p h w hw ρE

/-- **The field `bergerSurveyF` from Colmez's theorem**: the basis form of admissibility gives the dimension
form (`PanDict.bergerSurveyF_of_basis`). -/
theorem bergerSurveyF_of_colmez (hC : ColmezThm01) : BergerSurveyF :=
  bergerSurveyF_of_basis hC

/-- **Pan's theorem, with potential semistability in Fontaine's sense** (L. Pan, *The Fontaine–Mazur
conjecture in the residually reducible case*, J. Amer. Math. Soc. 35 (2022), 1031–1169, Theorem 1.0.4 with
Conjecture 1.0.1, read in arXiv:1901.07166v2, pp. 5 and 2, the version the manuscript cites; the journal
numbering is still to be checked), for `p ≥ 5`. The theorem is stated for every odd prime, with an extra
condition only at `p = 3`.

"Potentially semi-stable in the sense of Fontaine" is Fontaine's definition (Astérisque 223 (1994),
Exp. III, 5.6.1, p. 166: potentially `B_st`-admissible). It is used in the equivalent form printed in
Exp. III, 1.8.5, pp. 134–135: `V` becomes `B_st`-admissible over some finite `L`, that is,
`dim_{B_st^{G_L}} (B_st ⊗_{ℚ_p} V)^{G_L} = dim_{ℚ_p} V` (`LocalIsPstF`, on a model `V = E^n`; the model
does not matter, `localIsPstF_iff_forall`). Fontaine identifies `B_st` with its image in `B_dR`
(Exp. II, 4.2.4–4.2.5, p. 86). That image is `BstFOf`, and potential semistability over the abstract
`B_st = B_cris[X]` (Exp. II, 3.1.5–3.1.6, p. 81) is the same condition
(`AbstractPeriods.localIsPstF_iff_abstract`). The statement is `PanDict.PanPrintedF`. -/
def PanThm104F : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    IsIrreducibleP ρ → ρ.FinitelyRamified → LocalIsPstF p h w hw 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTP p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (_ : NeZero N) (k : ℤ) (g : HeckeRing.GL2.EigenformAwayFromLevel N k)
      (ρg : GaloisRep p 2) (ψ : GaloisChar p),
      IsAttachedVia p ιp g ρg ∧ IsTwistOf p ρ ρg ψ

/-- **The field `panPrintedF` is Pan's theorem with Fontaine's definition** (the same statement). -/
theorem panPrintedF_of_thm104F (hP : PanThm104F) : PanPrintedF :=
  hP

end HDec.PkgI4.PanBergerRefereed
