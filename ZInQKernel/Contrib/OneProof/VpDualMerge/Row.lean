import ZInQKernel.Contrib.OneProof.ScholzeH1AbVar

/-!
# vpdual-merge: `VpDualDeRhamAbVar`, the statement on `V_p(A)^∨` behind two added rows

The added bundle of `ZInQ.OneProof.frozenTarget` carries two rows that the live route reads only
together, as the pair of arguments of the three `HTMerge` theorems
`deRhamVpAbVarDirect_of_scholzeH1Milne`, `hodgeTateDecompOr_of_scholzeH1Milne` and
`hodgeTateDecompAbVar_of_scholzeH1`:

* `DeRhamScholze.HTMerge.ScholzeH1AbVar`: `H¹_ét(A_{F̄}, ℚ_p)` (Mathlib's pro-étale cohomology) is
  de Rham, with Hodge jumps in `[0, 1]` and `dim_{ℚ_p} Fil¹ D_dR = [F:ℚ_p] g`;
* `T10Etale.T10_TateDuality`: `H¹(A_{K̄}, ℤ_ℓ) ≅ Hom(T_ℓ A, ℤ_ℓ)`, Galois-equivariantly.

Those theorems use the second row only through `HTMerge.dual_of_H1`, which moves the three clauses
of the first row from `H¹` to `V_p(A)^∨`. This file states the three clauses on `V_p(A)^∨` directly,
as one derived statement (glue, not a row of `frozenTarget`), with `V_p(A) = ℚ_p ⊗ T_p(A)` built
from the `F̄`-points of `A`. It is meant to be fed by single-print rows on `V_p(A)` (in progress),
which are to imply it in Lean:

* `VpDualDeRhamAbVar`: the statement (three clauses, `VpDualIsDeRham`, `VpDualHodgeRange`,
  `VpDualFilOneDim`);
* `vpDual_of_pair`: the current pair of rows implies the statement;
* `deRhamVpAbVarDirect_of_vpDual`, `hodgeTateDecompOr_of_vpDual` (through
  `hodgeTateDecompHom_of_vpDual`) and `hodgeTateDecompAbVar_of_vpDual` (through
  `htDecomp_of_vpDual`): the three outputs of the `HTMerge` theorems from the statement alone. Their
  statements are those of the `HTMerge` theorems; only the hypotheses change.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace DeRhamScholze.HTMerge

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open DeRhamScholze.HT
open scoped TensorProduct

noncomputable section

/-! ## §1. The statement -/

section Clauses

variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- **Clause (i): `V_p(A)^∨` is de Rham.** Here `V_p(A) = ℚ_p ⊗ T_p(A)` with `T_p(A)` the limit of
the `A[p^n](F̄)` (`A.galRep p`, `G_F` acting on coordinates of `F̄`-points), and de Rham means
`dim_{ℚ_p} (B_dR ⊗ W)^{G_F} = [F:ℚ_p] · dim_{ℚ_p} W` (`IsDeRhamFam`).
Source: Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013) e1,
Cor. 1.8, pp. 5-6 (`H^i(X_{k̄,ét}, ℚ_p)` of a proper smooth rigid-analytic variety is de Rham),
at `X = A^an`, with Thm 9.1(ii), p. 74, and Thm 9.3, p. 75 (comparison of the algebraic and the
analytic objects); and Milne, *Abelian Varieties* v2.0 (March 16, 2008), Part I, Thm 12.1(a),
p. 55, with Rem. 12.5, p. 56 (`H¹(A_{k_s}, ℤ_p) ≅ Hom(T_p A, ℤ_p)`, compatibly with
`Gal(k_s/k)`; the edition read on main), which identifies `H¹_ét(A_{F̄}, ℚ_p)` with `V_p(A)^∨`.
The same statement in Milne, *Abelian varieties*, in Cornell-Silverman (eds.), *Arithmetic
Geometry* (Springer, 1986), Thm 15.1(a), p. 129, with Rem. 15.5, p. 131, is not yet read on main
(draft #204). -/
abbrev VpDualIsDeRham (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : Prop :=
  IsDeRhamFam p (fun σ => (A.galRep p).dual σ)

/-- **Clause (ii): the Hodge jumps of `V_p(A)^∨` lie in `[0, 1]`**: `Fil⁰ D_dR = D_dR` and
`Fil² D_dR = 0`, with `Fil^j D_dR = D_dR ∩ (t^j B_dR⁺ ⊗ W)` (`HodgeRange … 1`).
Source: Scholze, Forum Math. Pi 1 (2013) e1, Cor. 1.8, pp. 5-6 (the filtered `D_dR` of
`H^i(X_{k̄,ét}, ℚ_p)` is `H^i_dR(X)` with its Hodge filtration, the Hodge-de Rham spectral sequence
degenerating, so `gr^j H¹_dR = H^{1-j}(X, Ω^j)` vanishes for `j ∉ {0, 1}`), with Thms 9.1(ii)
and 9.3, pp. 74-75; and Milne, *Abelian Varieties* v2.0 (2008), Part I, Thm 12.1(a), p. 55,
with Rem. 12.5, p. 56 (the edition read on main; the 1986 Cornell-Silverman chapter, Thm 15.1(a)
and Rem. 15.5, is not yet read on main, draft #204), for the passage from `H¹_ét(A_{F̄}, ℚ_p)` to
`V_p(A)^∨`. -/
abbrev VpDualHodgeRange (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) : Prop :=
  HodgeRange p (fun σ => (A.galRep p).dual σ) 1

/-- **Clause (iii): `dim_{ℚ_p} Fil¹ D_dR(V_p(A)^∨) = [F:ℚ_p] · g`** for `A` of dimension `g`.
Source: Scholze, Forum Math. Pi 1 (2013) e1, Cor. 1.8, pp. 5-6, with Thm 9.1(ii), p. 74, at
`i = 0` (`Fil¹ H¹_dR(A) = H⁰(A, Ω¹_A)`); Milne, *Abelian Varieties* v2.0 (2008), Part I,
Thm 12.1(a), p. 55, with Rem. 12.5, p. 56 (the edition read on main; the 1986 Cornell-Silverman
chapter, Thm 15.1(a) and Rem. 15.5, is not yet read on main, draft #204), for the passage to
`V_p(A)^∨`. The Hodge number
`h^{1,0}(A) = dim_F H⁰(A, Ω¹_A) = g` is not in Scholze's paper; it is cited from Mumford,
*Abelian varieties*, §4 (`Ω¹_A ≅ 𝒪_A^g`), the source the row `scholzeH1AbVar` names, locator
unverified. -/
abbrev VpDualFilOneDim (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ) : Prop :=
  finrank ℚ_[p] (filD p (fun σ => (A.galRep p).dual σ) 1) = finrank ℚ_[p] F * g

end Clauses

/-- **The statement on `V_p(A)^∨` (derived glue, not a row).** For every prime `p`, every
finite extension `F/ℚ_p` and every abelian variety
`A/F` of dimension `g`, the dual `V_p(A)^∨` of the rational Tate module (built from `F̄`-points) is
de Rham (clause (i), `VpDualIsDeRham`), its Hodge filtration has its jumps in `[0, 1]` (clause (ii),
`VpDualHodgeRange`), and `dim_{ℚ_p} Fil¹ D_dR = [F:ℚ_p] · g` (clause (iii), `VpDualFilOneDim`).
Sources, clause by clause in the docstrings of the three clauses: Scholze, Forum Math. Pi 1 (2013)
e1, Cor. 1.8 with Thms 9.1(ii) and 9.3; Milne, *Abelian Varieties* v2.0 (2008), Part I,
Thm 12.1(a), p. 55, with Rem. 12.5, p. 56 (the edition read on main; the 1986 Cornell-Silverman
chapter, Thm 15.1(a) and Rem. 15.5, is not yet read on main, draft #204); `h^{1,0}(A) = g` from
Mumford, *Abelian varieties*, §4 (locator unverified). These are the sources of the current pair;
the statement is to be derived in Lean from single-print rows. The current pair implies it
(`vpDual_of_pair`). -/
def VpDualDeRhamAbVar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    VpDualIsDeRham p A ∧ VpDualHodgeRange p A ∧ VpDualFilOneDim p A g

/-- The statement with its three clauses unfolded (`Iff.rfl`). -/
theorem vpDualDeRhamAbVar_iff : VpDualDeRhamAbVar ↔
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
      (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
      IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧
        HodgeRange p (fun σ => (A.galRep p).dual σ) 1 ∧
        finrank ℚ_[p] (filD p (fun σ => (A.galRep p).dual σ) 1) = finrank ℚ_[p] F * g :=
  Iff.rfl

/-- **The pair implies the statement.** `HTMerge.dual_of_H1` moves the three
clauses of `ScholzeH1AbVar` along Milne's identification (`T10_TateDuality`), with Mumford's
torsion theorem proved (`mumfordTorsionAlgClosed_proof`). -/
theorem vpDual_of_pair (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality) :
    VpDualDeRhamAbVar :=
  fun p _ F _ _ _ A g hg =>
    dual_of_H1 p hT ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof A _
      (hN p F A g hg)

/-! ## §2. The three outputs of the `HTMerge` theorems, from the statement alone -/

/-- **The Hodge-Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g`** for one abelian variety of
dimension `g`, from the statement (the proof of `HTMerge.htDecomp_of_H1` after its `dual_of_H1`
step). -/
theorem htDecomp_of_vpDual (hV : VpDualDeRhamAbVar) (p : ℕ) [Fact p.Prime] {F : Type} [Field F]
    [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) :
    ∃ e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k))) := by
  have hM := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hp : (p : F) ≠ 0 := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfdV, hdimV⟩ := DeRhamPrint.finrank_V_of_tateModuleFree p
    (DeRhamPrint.tateModuleFree_of_mumford hM) hp A g hg
  obtain ⟨h1, h2, h3⟩ := hV p F A g hg
  obtain ⟨a, b, e, he, hab, hb⟩ :=
    DeRhamScholze.HTAbVar.hodgeTate01_dims (A.galRep p) DeRhamScholze.TT.fontaineTwistT h1 h2 g h3
  rw [hdimV] at hab
  obtain rfl : a = g := by omega
  subst hb
  exact ⟨ZInQ.Contrib.HodgeTateOr.dualEquiv p e,
    ZInQ.Contrib.HodgeTateOr.dualEquiv_map p (A.galRep p) e he⟩

/-- **`deRhamVpAbVarDirect`** from the statement (the conclusion of
`HTMerge.deRhamVpAbVarDirect_of_scholzeH1Milne`). -/
theorem deRhamVpAbVarDirect_of_vpDual (hV : VpDualDeRhamAbVar) :
    DeRhamPrint.Direct.DeRhamVpAbVarDirect := by
  intro p _ F _ _ _ A
  obtain ⟨g, hg⟩ := dim_finite_I4 A
  exact (DeRhamPrint.Direct.isDeRhamTensorOver_iff p (A.galRep p)).mp
    (isDeRhamTensorOver_of_H1 p ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof A
      (hV p F A g hg).1)

/-- **`HodgeTateDecompHom`** from the statement (the conclusion of
`HTMerge.hodgeTateDecompHom_of_scholzeH1`, with `DeRhamHodgeTate01` proved). -/
theorem hodgeTateDecompHom_of_vpDual (hV : VpDualDeRhamAbVar) :
    ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom := by
  intro p _ F _ _ _ A
  obtain ⟨g, hg⟩ := dim_finite_I4 A
  obtain ⟨h1, h2, -⟩ := hV p F A g hg
  exact DeRhamScholze.TT.deRhamHodgeTate01_proof p F (A.V p) (A.galRep p) h1 h2

/-- **`HodgeTateDecompOr`** from the statement (the conclusion of
`HTMerge.hodgeTateDecompOr_of_scholzeH1Milne`). -/
theorem hodgeTateDecompOr_of_vpDual (hV : VpDualDeRhamAbVar) :
    ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr :=
  ZInQ.Contrib.HodgeTateOr.or_of_hom (hodgeTateDecompHom_of_vpDual hV)

/-- **The H field `hodgeTateDecompAbVar`** from the statement (the conclusion of
`HTMerge.hodgeTateDecompAbVar_of_scholzeH1`). -/
theorem hodgeTateDecompAbVar_of_vpDual (hV : VpDualDeRhamAbVar) : HodgeTateDecompAbVar :=
  fun p _ _ _ _ _ A g hg => htDecomp_of_vpDual hV p A g hg

end

end DeRhamScholze.HTMerge
