import ZInQKernel.Contrib.OneProof.HTAbVarScholze

/-!
# ht-merge: one leaf `ScholzeH1AbVar` in place of `ScholzeDeRhamAlg` + `HodgeNumberH1AbVar`

Task ht-merge (2026-11-17; report `docs/research/ht-merge.md`; scratch copy `scratch/ht-merge/ScholzeH1AbVar.lean`).

derham-scholze's leaf `DeRhamScholze.ScholzeDeRhamAlg` (every proper smooth `X`, every degree `i`) is applied in exactly
one place, `DeRhamScholze.dual_deRham_of_scholze` (`hS p F A.X 1`: an abelian variety, degree 1), and ht-abvar's leaf
`DeRhamScholze.HTAbVar.HodgeNumberH1AbVar` is about the same `D_dR(H¹_ét(A_{F̄}, ℚ_p))`. The manuscript states both
facts in one breath for an abelian surface (diophantine_zq.tex `lem:de-rham-descent`: Scholze's comparison,
L10954-10965, and the Hodge numbers `2,2` of `H¹_dR(A/F)`, L10996). Here they are one leaf:

* `ScholzeH1AbVar` (LEAF, consequence): for an abelian variety `A` of dimension `g` over a finite `F/ℚ_p`,
  `H¹_ét(A_{F̄}, ℚ_p)` is de Rham, the Hodge filtration of its `D_dR` has its jumps in `[0, 1]`, and
  `dim_{ℚ_p} Fil¹ D_dR = [F:ℚ_p] · g`. Generalization (on-the-spot) in `g`: the manuscript's lemma is for `g = 2`
  (`ScholzeH1AbSurf` below is that form); the H field `hodgeTateDecompAbVar` (`TailS.lean` L347) and the amended R10 it
  feeds are stated for every `g`.

Proved here, with the statements of the old theorems unchanged (only the leaf hypotheses are replaced):

* `scholzeH1AbVar_of_old`: the old pair implies the new leaf (nothing is lost);
* `deRhamVpAbVarDirect_of_scholzeH1`, `hodgeTateDecompHom_of_scholzeH1`, `hodgeTateDecompOr_of_scholzeH1Milne`,
  `hodgeTateDecompAbVar_of_scholzeH1`: the four theorems that used the old leaves, from `ScholzeH1AbVar` and
  `T10_TateDuality` alone;
* `hodgeTateDecompAbSurf_of_scholzeH1AbSurf`: the manuscript-exact `g = 2` leaf gives the H field for every abelian
  surface (the only instances the end consumer G9 uses, `g9GlueNoT23_of_fieldEmb`, TailC L14121).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace DeRhamScholze.HTMerge

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open DeRhamScholze.HT
open scoped TensorProduct

noncomputable section

/-! ## §1. The leaf -/

/-- **LEAF (consequence; Scholze's comparison for `H¹` of an abelian variety, with its Hodge numbers).**
diophantine_zq.tex `lem:de-rham-descent` (step C3): the abelian variety `A/F` has a smooth proper rigid analytification;
Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013), Cor. 1.8 (with the corrigendum
Forum Math. Pi 4 (2016) e6) and Thms 9.1, 9.3 make `H¹_ét(A_{F̄}, ℚ_p)` de Rham with filtered `D_dR ≅ H¹_dR(A/F)`
(L10954-10965); "The two Hodge numbers of `H¹_dR(A/F)` are `2,2`" (L10996, for the abelian surface; uncited). Under the
filtered comparison: `Fil⁰ = D_dR`, `Fil² = 0` (the Hodge filtration of `H¹_dR` by `H¹(Ω^{≥j})`), and
`dim_F Fil¹ D_dR = dim_F H⁰(A, Ω¹) = g`.

Lean form, over derham-scholze's objects: `H¹_ét(A_{F̄}, ℚ_p) = ℚ_p ⊗_{ℤ_p} H¹(A_{F̄}, ℤ_p)` with Mathlib's pro-étale
`ℓ`-adic cohomology (`HQ`, `rhoH`: `σ` acts by transport along `1 × Spec(σ⁻¹)`, t10-etale's `galH`);
`D_dR = (B_dR ⊗ W)^{G_F}` (`ddrFam`), `Fil^j D_dR = D_dR ∩ (t^j B_dR^+ ⊗ W)` (`filD`), dimensions over `ℚ_p`
(`= [F:ℚ_p] · dim_F`). Not printed form: Mathlib has neither rigid-analytic spaces nor `H_dR` (dictionary steps as in
derham-scholze §3.1). Generalization (on-the-spot) in `g`: the manuscript has `g = 2` (`ScholzeH1AbSurf`); for general `g`
the only change is `h^{1,0}(A) = g` (`Ω¹_A ≅ 𝒪_A^g`; Mumford, *Abelian varieties*, §4, locator UNVERIFIED). -/
def ScholzeH1AbVar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1 ∧
      finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * g

/-- **The manuscript's form (`g = 2`)**: diophantine_zq.tex `lem:de-rham-descent` for an abelian surface `A/F`
(L10939-10941), Scholze's comparison (L10954-10965) and the Hodge numbers `2,2` (L10996): `H¹_ét(A_{F̄}, ℚ_p)` is
de Rham with Hodge jumps in `[0, 1]` and `dim_{ℚ_p} Fil¹ D_dR = 2 [F:ℚ_p]`. Same Lean objects as `ScholzeH1AbVar`. -/
def ScholzeH1AbSurf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), A.dim = (2 : WithBot ℕ∞) →
    IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1 ∧
      finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = 2 * finrank ℚ_[p] F

/-- The general leaf specializes to the manuscript's form. -/
theorem scholzeH1AbSurf_of_abVar (h : ScholzeH1AbVar) : ScholzeH1AbSurf := by
  intro p _ F _ _ _ A hA
  obtain ⟨h1, h2, h3⟩ := h p F A 2 hA
  exact ⟨h1, h2, h3.trans (mul_comm _ _)⟩

/-- **Nothing is lost: the old pair implies the new leaf.** `ScholzeDeRhamAlg` at `X = A`, `i = 1` gives the first two
clauses, `HodgeNumberH1AbVar` the third. -/
theorem scholzeH1AbVar_of_old (hS : ScholzeDeRhamAlg) (hH : DeRhamScholze.HTAbVar.HodgeNumberH1AbVar) :
    ScholzeH1AbVar := by
  intro p _ F _ _ _ A g hg
  have : IsProper A.X.hom := A.proper
  have : Smooth A.X.hom := A.smooth
  obtain ⟨h1, h2⟩ := hS p F A.X 1
  exact ⟨h1, h2, hH p F A g hg⟩

/-- The new leaf implies ht-abvar's leaf (its third clause). -/
theorem hodgeNumberH1AbVar_of_scholzeH1 (h : ScholzeH1AbVar) : DeRhamScholze.HTAbVar.HodgeNumberH1AbVar :=
  fun p _ F _ _ _ A g hg => (h p F A g hg).2.2

/-! ## §2. One abelian variety: transport to `V_p(A)^∨` along Milne's identification -/

section One

variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- For one abelian variety `A`: the three clauses on `H¹_ét(A_{F̄}, ℚ_p)` move to `V_p(A)^∨` (`milneE`,
derham-scholze's transport lemmas). -/
theorem dual_of_H1 (hT : T10Etale.T10_TateDuality) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (n : ℕ)
    (h : IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1 ∧
      finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = n) :
    IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧ HodgeRange p (fun σ => (A.galRep p).dual σ) 1 ∧
      finrank ℚ_[p] (filD p (fun σ => (A.galRep p).dual σ) 1) = n := by
  have hp : (p : F) ≠ 0 := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfree, hfin, -⟩ := DeRhamPrint.tateModuleFree_of_mumford hM F (DeRhamPrint.toKer A) p hp
  obtain ⟨φ, hφ⟩ := hT F (DeRhamPrint.toKer A) p hp
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨isDeRhamFam_of_equiv p (milneE p A φ) (milneE_comm p A φ hφ) h1,
    hodgeRange_of_equiv p (milneE p A φ) (milneE_comm p A φ hφ) 1 h2, ?_⟩
  rw [← map_filD p (milneE p A φ) (milneE_comm p A φ hφ) 1, LinearEquiv.finrank_map_eq]
  exact h3

/-- **`V_p(A)` is de Rham** for one abelian variety, from the first clause (derham-scholze's
`isDeRhamTensorOver_of_scholze`, with the leaf at `A` in place of `ScholzeDeRhamAlg`). -/
theorem isDeRhamTensorOver_of_H1 (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (h1 : IsDeRhamFam p (fun σ => (A.galRep p).dual σ)) :
    IsDeRhamTensorOver p (A.galRep p) := by
  obtain ⟨-, hD⟩ := h1
  obtain ⟨g, hg⟩ := dim_finite_I4 A
  have := (DeRhamPrint.finrank_V_of_tateModuleFree p (DeRhamPrint.tateModuleFree_of_mumford
    hM) (DeRhamPrint.natCast_p_ne_zero p F) A g hg).1
  have hDD : IsDeRhamTensorOver p (A.galRep p).dual.dual :=
    DeRhamPrint.isDeRhamTensorOver_dual p (BdRInv.bdRInvariantsPrinted_proof p F) _ hD
  have hfam : IsDeRhamFam p (fun σ => (A.galRep p).dual.dual σ) := ⟨inferInstance, hDD⟩
  have he : ∀ σ x, (Module.evalEquiv ℚ_[p] (A.V p)).symm ((A.galRep p).dual.dual σ x) =
      A.galRep p σ ((Module.evalEquiv ℚ_[p] (A.V p)).symm x) := by
    intro σ x
    obtain ⟨v, rfl⟩ := (Module.evalEquiv ℚ_[p] (A.V p)).surjective x
    rw [← evalEquiv_comm, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact (isDeRhamFam_of_equiv p (Module.evalEquiv ℚ_[p] (A.V p)).symm he hfam).2

/-- **The Hodge–Tate decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g`** for one abelian variety of dimension `g`, from
the leaf at `A` (ht-abvar's proof of `hodgeTateDecompAbVar_of_scholze`, pointwise). -/
theorem htDecomp_of_H1 (hT : T10Etale.T10_TateDuality) (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞))
    (h : IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1 ∧
      finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * g) :
    ∃ e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k))) := by
  have hM := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hp : (p : F) ≠ 0 := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfdV, hdimV⟩ := DeRhamPrint.finrank_V_of_tateModuleFree p (DeRhamPrint.tateModuleFree_of_mumford hM) hp A g hg
  obtain ⟨h1, h2, h3⟩ := dual_of_H1 p hT hM A _ h
  obtain ⟨a, b, e, he, hab, hb⟩ :=
    DeRhamScholze.HTAbVar.hodgeTate01_dims (A.galRep p) DeRhamScholze.TT.fontaineTwistT h1 h2 g h3
  rw [hdimV] at hab
  obtain rfl : a = g := by omega
  subst hb
  exact ⟨ZInQ.Contrib.HodgeTateOr.dualEquiv p e, ZInQ.Contrib.HodgeTateOr.dualEquiv_map p (A.galRep p) e he⟩

end One

/-! ## §3. The four theorems from the new leaf (statements unchanged, leaf hypotheses replaced) -/

/-- `V_p(A)^∨` de Rham with Hodge jumps in `[0, 1]` (derham-scholze's `dual_deRham_of_scholze`, same conclusion). -/
theorem dual_deRham_of_scholzeH1 (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧ HodgeRange p (fun σ => (A.galRep p).dual σ) 1 := by
  obtain ⟨g, hg⟩ := dim_finite_I4 A
  obtain ⟨h1, h2, -⟩ := dual_of_H1 p hT hM A _ (hN p F A g hg)
  exact ⟨h1, h2⟩

/-- **`deRhamVpAbVarDirect`** (derham-scholze's `deRhamVpAbVarDirect_of_scholze`, conclusion unchanged) from the new
leaf and Milne's identification. -/
theorem deRhamVpAbVarDirect_of_scholzeH1 (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) : DeRhamPrint.Direct.DeRhamVpAbVarDirect :=
  fun p _ F _ _ _ A => (DeRhamPrint.Direct.isDeRhamTensorOver_iff p (A.galRep p)).mp
    (isDeRhamTensorOver_of_H1 p hM A (dual_deRham_of_scholzeH1 hN hT hM p F A).1)

/-- `deRhamVpAbVarDirect` with Mumford's torsion theorem discharged (derham-scholze's `deRhamVpAbVarDirect_of_leaves`). -/
theorem deRhamVpAbVarDirect_of_scholzeH1Milne (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality) :
    DeRhamPrint.Direct.DeRhamVpAbVarDirect :=
  deRhamVpAbVarDirect_of_scholzeH1 hN hT ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof

/-- **`HodgeTateDecompHom`** (derham-scholze's `hodgeTateDecompHom_of_scholze`, conclusion unchanged). -/
theorem hodgeTateDecompHom_of_scholzeH1 (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hW : DeRhamHodgeTate01) : ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom := by
  intro p _ F _ _ _ A
  obtain ⟨h1, h2⟩ := dual_deRham_of_scholzeH1 hN hT hM p F A
  exact hW p F (A.V p) (A.galRep p) h1 h2

/-- **`HodgeTateDecompOr`** (derham-scholze's `TT.hodgeTateDecompOr_of_scholzeMilne`, conclusion unchanged) from the
new leaf and Milne's identification alone. -/
theorem hodgeTateDecompOr_of_scholzeH1Milne (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality) :
    ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr :=
  ZInQ.Contrib.HodgeTateOr.or_of_hom (hodgeTateDecompHom_of_scholzeH1 hN hT
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof DeRhamScholze.TT.deRhamHodgeTate01_proof)

/-- **The H field `hodgeTateDecompAbVar`** (ht-abvar's `hodgeTateDecompAbVar_of_scholze`, conclusion unchanged) from the
new leaf and Milne's identification: the term for consumer (iii)'s swap. -/
theorem hodgeTateDecompAbVar_of_scholzeH1 (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality) :
    HodgeTateDecompAbVar :=
  fun p _ F _ _ _ A g hg => htDecomp_of_H1 p hT A g hg (hN p F A g hg)

/-- Sanity: ht-abvar's theorem is recovered from the old pair through the new leaf. -/
theorem hodgeTateDecompAbVar_of_old (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality)
    (hH : DeRhamScholze.HTAbVar.HodgeNumberH1AbVar) : HodgeTateDecompAbVar :=
  hodgeTateDecompAbVar_of_scholzeH1 (scholzeH1AbVar_of_old hS hH) hT

/-! ## §4. The manuscript-exact `g = 2` leaf suffices for abelian surfaces -/

/-- The H field `HodgeTateDecompAbVar` restricted to abelian surfaces (`g = 2`), verbatim otherwise: the instances the
end consumer G9 uses (`g9GlueNoT23_of_fieldEmb`, TailC L14121, applies R10 at `A'` with `A'.dim = 2`). -/
def HodgeTateDecompAbSurf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), A.dim = ((2 : ℕ) : WithBot ℕ∞) →
    ∃ e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin 2 → ℂ_[p]) × (Fin 2 → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))

/-- `HodgeTateDecompAbSurf` is the `g = 2` instance of the H field. -/
theorem hodgeTateDecompAbSurf_of_abVar (h : HodgeTateDecompAbVar) : HodgeTateDecompAbSurf :=
  fun p _ F _ _ _ A hA => h p F A 2 hA

/-- **The manuscript-exact leaf gives the H field for every abelian surface.** -/
theorem hodgeTateDecompAbSurf_of_scholzeH1AbSurf (hN : ScholzeH1AbSurf) (hT : T10Etale.T10_TateDuality) :
    HodgeTateDecompAbSurf := by
  intro p _ F _ _ _ A hA
  obtain ⟨h1, h2, h3⟩ := hN p F A hA
  exact htDecomp_of_H1 p hT A 2 hA ⟨h1, h2, h3.trans (mul_comm _ _)⟩

end

end DeRhamScholze.HTMerge
