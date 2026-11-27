import ZInQKernel.Contrib.OneProof.PanBergerFontaine

/-!
# `bergerSurveyF` from its primary source: Berger, Invent. Math. 148 (2002), Théorème 0.7

The row `bergerSurveyF` (`HDec.PkgI4.PanDict.BergerSurveyF`) is Berger's theorem "every de Rham representation of
`G_{ℚ_p}` is potentially semistable", in the dimension form. Berger proves it in his paper (Théorème 0.7 of the
introduction, proved as Corollaire 5.22 in §5.5), from his characterization of potentially semistable
representations by quasi-unipotent differential equations and André's theorem. In §1.2 he defines semistability by
`B_st`-admissibility and states its equivalence with the dimension condition `dim_F D_st(V) = dim_{ℚ_p} V`, noting
that his `B_st = B_max[log[π]]` differs slightly from Fontaine's but gives the same functor `D_st`.

* `BergerInvent2002Thm07`: the theorem, in the row's Lean form.
* `bergerInvent2002Thm07_iff`: it is the row (`Iff.rfl`), so nothing changes in strength.
-/

set_option autoImplicit false

noncomputable section

namespace HDec.PkgI4.BergerInvent2002

open BmaxOne BergerBst PanBergerSplit FontaineSt PanDict

/-- **Berger, *Représentations p-adiques et équations différentielles*, Invent. Math. 148 (2002), 219–284,
Théorème 0.7** (Introduction; proved in §5.5 as Corollaire 5.22). Read in the author's post-referee copy, whose
page numbers are not the journal's:

* Théorème 0.7 (author's copy p. 6): "Si V est une représentation de de Rham, alors V est potentiellement
  semi-stable."
* Corollaire 5.22 (p. 52), with its proof: "C'est une conséquence immédiate du fait que V est potentiellement
  semi-stable si et seulement si N_dR(V) est quasi-unipotent, et du théorème d'André qui assure que c'est toujours
  le cas."
* Setting, §1.1 (p. 8): k perfect of characteristic p, F the fraction field of W(k), K a finite totally ramified
  extension of F (so `K = F = ℚ_p` for `k = 𝔽_p`); a p-adic representation of `G_K`.
* Semistable, §1.2 (p. 11): "On dit qu'une représentation V est semi-stable si elle est B_st-admissible […]; ceci
  équivaut à ce que le F-espace vectoriel D_st(V) = (B_st ⊗_{ℚ_p} V)^{G_K} […] est de dimension d = dim_{ℚ_p}(V).
  La définition de B_st donnée ci-dessus est légèrement différente de celle de Fontaine, mais le foncteur D_st est
  le même."
* De Rham: `B_dR`-admissible (§1.2), equivalently `dim_K (B_dR ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`.

Lean form (the row `HDec.PkgI4.PanDict.BergerSurveyF`, verbatim): at `K = ℚ_p`, for `V = E^n` (`E/ℚ_p` finite inside
`ℚ̄_p`, `ρ_E : G_{ℚ_p} → GL_n(E)` continuous), de Rham in the dimension form (`IsDeRhamU`) implies potentially
semistable in the dimension form: for some finite `L/ℚ_p` inside `ℚ̄_p`, `(B_st ⊗ V)^{G_L}` has full dimension over
`B_st^{G_L}` (`IsPstF`), with Fontaine's `B_st` embedded in `B_dR` (`BstFOf`; Berger: "le foncteur D_st est le
même"), for every generator `ε₀` of `ℤ_p(1)` and every generator `w` of `ker θ` (the ring does not depend on them).
Reading steps: an E-linear representation is read over `ℚ_p`; "potentiellement semi-stable" (not redefined by
Berger) is semistable on `G_L` for a finite `L/K` (Fontaine, Astérisque 223 (1994), Exp. III, 5.6.1, with 1.8.5 for
the dimension form). -/
def BergerInvent2002Thm07 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E),
      Continuous ρE → IsDeRhamU p ρE → IsPstF p h w hw ρE

/-- The theorem is the row. -/
theorem bergerInvent2002Thm07_iff : BergerInvent2002Thm07 ↔ BergerSurveyF :=
  Iff.rfl

/-- **The row from Berger's theorem.** -/
theorem bergerSurveyF_of_berger2002 (h : BergerInvent2002Thm07) : BergerSurveyF :=
  bergerInvent2002Thm07_iff.1 h

end HDec.PkgI4.BergerInvent2002
