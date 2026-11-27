import ZInQKernel.Contrib.OneProof.DeRhamScholzeHT

/-!
# tate-module-prints: two single-print rows on the Tate module

Two rows, each the statement of one printed theorem, on `V_p(A) = ℚ_p ⊗ T_p(A)` (`A.V p`, with
`G_F` acting through `A.galRep p` on the coordinates of the `F̄`-points of `A`), for an abelian
variety `A` over a finite extension `F` of `ℚ_p`:

* `Colmez1992DeRhamAbVar`: Colmez, *Périodes p-adiques des variétés abéliennes*, Math. Ann. 292
  (1992), 629-644, Théorème 5.2 (i)-(ii), p. 639 (the `p`-adic period pairing);
* `Fontaine1982HTAbVar`: Fontaine, *Formes différentielles et modules de Tate des variétés
  abéliennes sur les corps locaux*, Invent. Math. 65 (1982), 379-409, Théorème 2 (Tate, Raynaud),
  p. 388, with the dimension count printed in its proof on the same page.

Together they are meant to replace the added rows `scholzeH1AbVar` and `t10TateDuality` of
`ZInQ.OneProof.frozenTarget`: `TatePrints/Glue.lean` derives
`DeRhamScholze.HTMerge.VpDualDeRhamAbVar` from them in Lean.
-/

namespace DeRhamScholze.TatePrints

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

/-- **Row R1. Colmez, *Périodes p-adiques des variétés abéliennes*, Math. Ann. 292 (1992),
629-644, Théorème 5.2 (i)-(ii), p. 639.**

Standing hypotheses, p. 629: "soit X une variété abélienne définie sur une extension finie K de
Q_p, et 𝒳 un modèle de X sur les entiers de K"; p. 638: "Dans la suite de cette section, X sera
une variété abélienne, 𝒳 un modèle propre de X sur O_K. [...] Par construction, 𝒳(O_{C_p})
s'identifie à X(C_p)"; p. 639: "Soit u=(…,u_n,…), où u_n ∈ 𝒳(O_{C_p}), un élément du module de
Tate T_p(X) de X." No reduction hypothesis. `B_dR` is Fontaine's (§2, p. 632).

Print, p. 639:
"Théorème 5.2. (i) Si F_ω est une des primitives de ω définie à la proposition 4.1, alors la suite
pⁿ(F_ω(a_n) − F_ω(a_n⊕û_n)) tend vers une limite dans B⁺_dR qui ne dépend que de u et de la classe
de ω dans H¹_dR(X).
(ii) L'application périodes p-adique (ω,u) → ∫_u ω de H¹_dR(X) × T_p(X) dans B⁺_dR ainsi définie
est bilinéaire, commute à l'action de Galois [i.e. g(∫_u ω) = ∫_{g(u)} ω si g ∈ Gal(K̄/K)],
respecte les filtrations (i.e. ∫_u ω ∈ Fil¹(B⁺_dR) si ω ∈ H⁰(X, Ω¹_X)) et est non-dégénérée quand
on étend les scalaires à B_dR."
The proof is in the paper, pp. 639-641.

Lean form (direct instance, with weakenings only):
* `H¹_dR(X)` is replaced by an existential type `H`; `P ω` is `u ↦ ∫_u ω`, extended `ℚ_p`-linearly
  from `T_p` to `V_p = ℚ_p ⊗ T_p`;
* kept: values in `B_dR⁺` (5.2(i); `filB p 0`), Galois compatibility (5.2(ii)), and
  non-degeneracy on the `T_p` side after extending scalars to `B_dR` (5.2(ii): an `x` of
  `B_dR ⊗ V_p` killed by every `P ω ⊗ B_dR` is `0`);
* dropped: bilinearity in `ω`, the `Fil¹` clause and (iii).
Base field: a finite `F/ℚ_p`, as in the print. Reading point: the print builds `T_p(X)` from
`X(C_p)`, the row from the `F̄`-points of `A`; since #228 the two are identified in Lean
(`ColmezCp.colmez1992DeRhamAbVar_iff_cp`, `ColmezTorsionIso.vCp_galRep`). Since #239
`𝒳(O_{C_p}) = X(C_p)` is a Lean theorem (`ColmezProperModel.modelPtsEquiv`); the model step reduces
to `ColmezProperModel.ProperModelExists`, proposed for a ruling by Jack or the maintainer. -/
def Colmez1992DeRhamAbVar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (H : Type) (P : H → (A.V p →ₗ[ℚ_[p]] BdR p)),
      (∀ ω u, P ω u ∈ filB p 0) ∧
      (∀ ω (σ : Field.absoluteGaloisGroup F) u,
        P ω (A.galRep p σ u) = bdrAct p (gfToGqp p F σ) (P ω u)) ∧
      (∀ x : BdR p ⊗[ℚ_[p]] A.V p, (∀ ω, (P ω).liftBaseChange (BdR p) x = 0) → x = 0)

/-- **Row R2. Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur
les corps locaux*, Invent. Math. 65 (1982), 379-409, Théorème 2 (Tate, Raynaud), p. 388, with the
dimension count printed in its proof on the same page.**

Standing hypotheses: §1.1, p. 381, "K est un corps local, i.e. un corps complet pour une valuation
discrète, à corps résiduel parfait k de caractéristique p≠0, K_s est une clôture séparable de K,
G = Gal(K_s/K), C le complété de K_s"; §3, p. 387, "on suppose en outre K de caractéristique 0";
0.1, p. 379, `M(i) = M ⊗_{Z_p} T^{⊗i}` with `T = lim μ_{pⁿ}(K̄)`; 3.1, p. 388,
`T_p(X) = Hom_Z(Q_p/Z_p, X(K̄))` (the `K̄`-points, as in the row). No reduction hypothesis.

Print, p. 388: "Théorème 2 (Tate, Raynaud). Soit X une variété abélienne sur K. Il existe des
applications K-linéaires bijectives, canoniques et fonctorielles en X
ρ¹_X : H¹(X, O_X) → Hom_{Z_p[G]}(T_p(X), C),
ρ⁰_X : H⁰(X, Ω_X) → Hom_{Z_p[G]}(T_p(X), C(1))."
The equality "dimension = g" is printed in the proof, p. 388, in the deduction of Théorème 2 from
Théorème 2': "Soit d la dimension de X. [...] Comme la somme de la dimension de
Hom_{Z_p[G]}(T_p(X), C(1)) et de celle de Hom_{Z_p[G]}(T_p(X), C) est inférieure ou égale au rang
du Z_p-module libre T_p(X) ([7], prop. 4), qui est 2d, chacune de ces dimensions est égale à d et
ρ⁰_X est un isomorphisme." Fontaine gives a new proof of the theorem (3.2, p. 388: "une nouvelle
démonstration de ce résultat"; Théorème 2' is proved in 3.3-3.8, pp. 388-394).

Lean form: `Hom_{Z_p[G]}(T_p X, C(i))` is `htF (A.galRep p) i`, the `G_F`-equivariant
`ℚ_p`-linear maps `V_p(A) → ℂ_p(i)` (`σ` acting on `ℂ_p(i)` by `χ(σ)^i σ`), as a vector space over
`F' ⊆ ℚ̄_p`, the image of `F` (the print's `K`), for `i = 1` and `i = 0`; both dimensions are `g`.
Base field: a finite `F/ℚ_p` (complete, discretely valued, perfect residue field, characteristic
`0`). -/
def Fontaine1982HTAbVar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    finrank (fieldF p F) (DeRhamScholze.HT.htF (A.galRep p) 1) = g ∧
      finrank (fieldF p F) (DeRhamScholze.HT.htF (A.galRep p) 0) = g

end DeRhamScholze.TatePrints
