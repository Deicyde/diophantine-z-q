import ZInQKernel.Contrib.OneProof.PanBergerFontaine

/-!
# `bergerSurveyF` as reported in a refereed print: Fontaine, Astérisque 295 (2004), pp. 9–10

The row `bergerSurveyF` (`HDec.PkgI4.PanDict.BergerSurveyF`) is Berger's theorem "every de Rham representation of
`G_{ℚ_p}` is potentially semistable", in Fontaine's dimension form. Its source, Berger, Invent. Math. 148 (2002), has
an unverified journal locator, and no legal open copy of the journal text was found. Fontaine's refereed paper in
Astérisque 295 (2004) states the theorem in its introduction as proved (pp. 9–10), crediting Berger, André, Mebkhout and Kedlaya, and
defines semistability in the dimension form (§5.3); potential semistability is Fontaine's (Astérisque 223 (1994),
Exp. III, 5.6.1, with admissibility in the dimension form, 1.8.5). That is a report of the theorem.

* `FontaineAst295DeRhamPst`: the reported statement, in the row's Lean form.
* `fontaineAst295DeRhamPst_iff`: it is the row (`Iff.rfl`), so nothing changes in strength.
-/

set_option autoImplicit false

noncomputable section

namespace HDec.PkgI4.FontaineAst295

open BmaxOne BergerBst PanBergerSplit FontaineSt PanDict

/-- **Fontaine, *Arithmétique des représentations galoisiennes p-adiques*, Astérisque 295 (2004), 1–115,
pp. 9–10** (Introduction; a report crediting Berger, Invent. Math. 148 (2002), and André, Mebkhout, Kedlaya):

* p. 9: "Deux des conjectures les plus importantes du sujet ont été démontrées […] La seconde (conjecture B) est le
  fait que toute représentation de de Rham est potentiellement semi-stable." The attribution continues on p. 10
  (Berger's reduction to Crew's conjecture, proved by André and Mebkhout, and by Kedlaya).
* Setting (p. 2): K complete for a discrete valuation, of characteristic 0, with perfect residue field of
  characteristic p; representations are finite-dimensional continuous `ℚ_p`-linear."
* p. 83, §5.3 (dimension form): "On dit que la représentation V est semi-stable si dim_{K₀} D_st(V) = dim_{ℚ_p} V".
* Potentially semistable: Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exp. III,
  5.6.1, p. 166: V "est potentiellement semi-stable si elle est potentiellement B_st-admissible", i.e. B_st-admissible
  as a representation of `G_L` for a finite extension L of K; B-admissibility in the dimension form, Exp. III, 1.8.5,
  pp. 134–135.

Lean form (the row `HDec.PkgI4.PanDict.BergerSurveyF`, verbatim): at `K = ℚ_p`, for `V = E^n` (`E/ℚ_p` finite inside
`ℚ̄_p`, `ρ_E : G_{ℚ_p} → GL_n(E)` continuous), de Rham in the dimension form (`IsDeRhamU`) implies potentially
semistable in Fontaine's dimension form over `B_st` embedded in `B_dR` (`IsPstF`, `BstFOf`), for every generator `ε₀`
of `ℤ_p(1)` and every generator `w` of `ker θ` (the ring does not depend on them). Reading steps: an E-linear
representation is read as a `ℚ_p`-representation; "toute représentation" at `K = ℚ_p`. -/
def FontaineAst295DeRhamPst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E),
      Continuous ρE → IsDeRhamU p ρE → IsPstF p h w hw ρE

/-- The reported statement is the row. -/
theorem fontaineAst295DeRhamPst_iff : FontaineAst295DeRhamPst ↔ BergerSurveyF :=
  Iff.rfl

/-- **The row from the report.** -/
theorem bergerSurveyF_of_fontaineAst295 (h : FontaineAst295DeRhamPst) : BergerSurveyF :=
  fontaineAst295DeRhamPst_iff.1 h

end HDec.PkgI4.FontaineAst295
