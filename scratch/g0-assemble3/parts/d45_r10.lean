/-! ## g0-assemble3: r10-amend (ZInQKernel/Contrib/R10/Amend.lean and Glue.lean, verbatim minus imports and `#print`
lines), then the closing theorems of Final.lean with g9-abvarbc's `abVarBaseChange` replaced by
`abVarBaseChange_of_mulIsogeny` applied to the `MulIsogeny` of infra-stalks (`G0FibreSimple.MulIsogeny` of part 40 and
g9-abvarbc's namespaced copy `ZInQ.Contrib.AbVarBC.G0FibreSimple.MulIsogeny` have the same text). -/
section G0A3file_Amend
-- (file ZInQKernel/Contrib/R10/Amend.lean, verbatim minus imports and #print lines)

/-!
# R10 amended: the de Rham comparison for abelian varieties with the full Hodge–Tate weights

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task r10-amend, 2026-11-13).

R10's Lean form (`PkgI4.DeRhamComparison`, Leaves.lean `PkgI4Sec`; restated verbatim in
`ZInQKernel/Contrib/G9/I4Layer.lean`) gives the Hodge–Tate multiplicities `g` at the weights `0`
and `−1` of `V_p(A)` for an abelian variety `A` of dimension `g` over a finite `F/ℚ_p`. It does
not say that every other weight has multiplicity `0`. That vanishing is part of the published
theorem (the Hodge–Tate decomposition
`ℂ_p ⊗_{ℚ_p} H¹_et(A_F̄, ℚ_p) ≅ (ℂ_p ⊗_F H¹(A, 𝒪_A)) ⊕ (ℂ_p(−1) ⊗_F H⁰(A, Ω¹_A))`, Faltings,
JAMS 1 (1988), Ch. III Thm 4.1 as cited by the manuscript; Fontaine, Invent. Math. 65 (1982) for
abelian varieties; Tate 1967 §4 for good reduction; together with Tate's
`ℂ_p(j)^{G_F} = 0` for `j ≠ 0`, Tate 1967 §3.3; locators UNVERIFIED, no source on this host; see
`docs/research/r10-amend.md` §2).

`DeRhamComparisonHT` is R10 plus that clause. The clause has no dimension hypothesis: it holds for
every abelian variety. It is exactly g9-derham's bridge `G9Bridge.R10Weights`, so

`deRhamComparisonHT_iff : DeRhamComparisonHT ↔ PkgI4.DeRhamComparison ∧ G9Bridge.R10Weights`.

Sign convention (checked against the definitions): `htMultOver p ρ w` is
`dim_F Hom_{G_F}(V, ℂ_p(−w))`, i.e. `dim_F (ℂ_p(−w) ⊗ V^∨)^{G_F}`, and `ℚ_p(1)` has weight `−1`.
For `V = V_p(A)`, `V^∨ = H¹_et`, so `ℂ_p(i) ⊗ V^∨ ≅ ℂ_p(i)^g ⊕ ℂ_p(i−1)^g`, whose `G_F`-invariants
have `F`-dimension `g·[i = 0] + g·[i = 1]`: multiplicity `g` at `w = 0` and `w = −1`, and `0` at
every other `w`.
-/

namespace ZInQ.Contrib.R10

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4

/-- **R10, amended (I4-L0 with the full weight multiset).** For an abelian variety `A` over a
finite extension `F` of `ℚ_p`: if `dim A = g`, then `V_p(A)` is de Rham as a `G_F`-representation,
with Hodge–Tate weights `0` and `−1` each of multiplicity `g` (this is the old R10,
`PkgI4.DeRhamComparison`); and every weight other than `0` and `−1` has multiplicity `0`.
Faltings 1988 Ch. III Thm 4.1 / Fontaine 1982 (Hodge–Tate decomposition) with Tate 1967 §3.3
(`ℂ_p(j)^{G_F} = 0`, `j ≠ 0`); de Rham part as in R10 (Scholze 2013 Cor. 1.8 with Thms 9.1, 9.3;
Faltings 1989; Tsuji 1999); locators UNVERIFIED. -/
def DeRhamComparisonHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F),
    (∀ g : ℕ, A.dim = (g : WithBot ℕ∞) →
      IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = g ∧
        htMultOver p (A.galRep p) (-1) = g) ∧
    ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0

/-- The amended R10 implies the old R10. -/
theorem deRhamComparison_of_HT (h : DeRhamComparisonHT) : PkgI4.DeRhamComparison :=
  fun p _ F _ _ _ A g hg => (h p F A).1 g hg

/-- The amended R10 implies g9-derham's bridge `R10Weights` (finding F1 of g9-derham). -/
theorem r10Weights_of_HT (h : DeRhamComparisonHT) : G9Bridge.R10Weights :=
  fun p _ F _ _ _ A w hw0 hw1 => (h p F A).2 w hw0 hw1

/-- The amended R10 implies g9-derham run 3c's weight clause `DeRhamComparisonWeights`
(`R10Weights` with a dimension hypothesis). -/
theorem deRhamComparisonWeights_of_HT (h : DeRhamComparisonHT) : DeRhamComparisonWeights :=
  fun p _ F _ _ _ A _ _ w hw0 hw1 => (h p F A).2 w hw0 hw1

/-- The amendment adds exactly the clause `R10Weights` to R10, and nothing else. -/
theorem deRhamComparisonHT_iff :
    DeRhamComparisonHT ↔ PkgI4.DeRhamComparison ∧ G9Bridge.R10Weights :=
  ⟨fun h => ⟨deRhamComparison_of_HT h, r10Weights_of_HT h⟩,
    fun ⟨h1, h2⟩ p _ F _ _ _ A =>
      ⟨fun g hg => h1 p F A g hg, fun w hw0 hw1 => h2 p F A w hw0 hw1⟩⟩

/-- Equivalent multiplicity form: if `dim A = g`, then `htMultOver w = g · #{w ∈ {0, −1}}` for
every `w`. -/
theorem htMultOver_eq_of_HT (h : DeRhamComparisonHT) (p : ℕ) [Fact p.Prime] (F : Type) [Field F]
    [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : PkgI4.I3.AbVar F) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) (w : ℤ) :
    htMultOver p (A.galRep p) w = g * ({0, -1} : Multiset ℤ).count w := by
  obtain ⟨h1, h2⟩ := h p F A
  obtain ⟨_, h0, hm1⟩ := h1 g hg
  by_cases hw0 : w = 0
  · subst hw0; rw [h0]; simp
  by_cases hw1 : w = -1
  · subst hw1; rw [hm1]; simp
  rw [h2 w hw0 hw1]
  simp [hw0, hw1]

end ZInQ.Contrib.R10


end G0A3file_Amend
section G0A3file_Glue
-- (file ZInQKernel/Contrib/R10/Glue.lean, verbatim minus imports and #print lines)

/-!
# G9 from the amended R10 (and base change of abelian varieties)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task r10-amend, 2026-11-13).

g9-derham proved `g9Glue_of_abVarBaseChange : AbVarBaseChange → R10Weights → G9Glue`
(`ZInQKernel/Contrib/G9/LocalModel.lean`). With the amended leaf `DeRhamComparisonHT`
(`Amend.lean`), whose weight clause is `R10Weights`, this gives

* `g9Glue_of_HT : AbVarBaseChange → DeRhamComparisonHT → G9Glue`;
* `G9GlueHT`: g0-mod-galois's `G9Glue` with its R10 hypothesis replaced by the amended leaf and
  the unused T23 hypothesis dropped; `g9GlueHT_of_abVarBaseChange : AbVarBaseChange → G9GlueHT`.
  The proof is g9-derham's `g9Glue_of_fieldEmb` (`Reduction.lean`) with the old R10 and
  `R10Weights` both read off the amended leaf. `G9GlueHT` implies `G9GlueHT'`, the same statement
  with T23 kept, which is `G9Glue` with R10 replaced by its amendment.
-/

namespace ZInQ.Contrib.R10

set_option linter.unusedSectionVars false

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.G9.G0Galois Module
open scoped TensorProduct

noncomputable section

/-- **G9 with the amended R10** (g0-mod-galois's `G9Glue`, R10 replaced by `DeRhamComparisonHT`,
T23 dropped since the proof does not use it). -/
def G9GlueHT : Prop :=
  DeRhamComparisonHT →
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G9Out r

/-- `G9Glue` verbatim, with `PkgI4.DeRhamComparison` replaced by `DeRhamComparisonHT`. -/
def G9GlueHT' : Prop :=
  DeRhamComparisonHT → (∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p) →
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G9Out r

theorem g9GlueHT'_of_g9GlueHT (h : G9GlueHT) : G9GlueHT' :=
  fun hR _ => h hR

/-- `G9Glue` from base change and the amended R10. -/
theorem g9Glue_of_HT (hBC : G9Bridge.AbVarBaseChange) (hR : DeRhamComparisonHT) : G9Glue :=
  g9Glue_of_abVarBaseChange hBC (r10Weights_of_HT hR)

/-- **G9 with the amended R10, from base change of abelian varieties.** g9-derham's proof of
`g9Glue_of_fieldEmb`, with `LocalModel` from `AbVarBaseChange`, `F' ⊆ B_dR` from `fieldEmbBdR`,
and both the old R10 and `R10Weights` from `DeRhamComparisonHT`. -/
theorem g9GlueHT_of_abVarBaseChange (hBC : G9Bridge.AbVarBaseChange) : G9GlueHT := by
  intro hRHT K _ _ A ℓ _ r e hdim hint
  have hLM := localModel_of_abVarBaseChange hBC
  have hR10 := deRhamComparison_of_HT hRHT
  have hW := r10Weights_of_HT hRHT
  obtain ⟨F, _, _, _, _, A', j, c, g, hdim', hc, hg⟩ := hLM K A ℓ hdim
  obtain ⟨hdR, h0, h1⟩ := hR10 ℓ F A' 2 (by rw [hdim']; rfl)
  obtain ⟨ιB, hιB⟩ := fieldEmbBdR ℓ F
  let cb : PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A'.V ℓ ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A.V ℓ :=
    LinearEquiv.baseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ c
  let e' := (cb.trans e).trans (twistPair r g)
  have hcb : ∀ σ x, cb ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      tate A ℓ (j σ) (cb x) := by
    intro σ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      change cb (a ⊗ₜ (A'.galRep ℓ σ v)) = (A.galRep ℓ (j σ)).baseChange (PadicAlgCl ℓ) (cb (a ⊗ₜ v))
      simp only [cb, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, hc]
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have he' : ∀ σ x, e' ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      ((r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec (e' x).1,
        (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec
          (e' x).2) := by
    intro σ x
    have hR : (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) := rfl
    have hconj : r.mat g⁻¹ * r.mat (resQ K (j σ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) * r.mat g⁻¹ := by
      rw [hg σ, galoisRep_mat_mul, galoisRep_mat_mul, ← mul_assoc, ← mul_assoc,
        galoisRep_mat_inv_mul, one_mul]
    simp only [e', LinearEquiv.trans_apply, hcb, twistPair_apply, hint _ (cb x), hR,
      Matrix.mulVec_mulVec, hconj]
  obtain ⟨E, hE, ρE, eE, hmap, he⟩ :=
    coef_descent ℓ F (A'.galRep ℓ) (r.restrictLocal ℓ) e' he'
  have hw : ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver ℓ (A'.galRep ℓ) w = 0 :=
    fun w hw0 hw1 => hW ℓ F A' w hw0 hw1
  exact ⟨⟨E, hE, ρE, hmap, core_dR_F ℓ F ιB hιB (A'.galRep ℓ) ρE eE he hdR⟩,
    ⟨E, hE, ρE, hmap, core_ht ℓ F (A'.galRep ℓ) ρE eE he h0 h1 hw⟩⟩

end

end ZInQ.Contrib.R10


end G0A3file_Glue

namespace ZInQ.Contrib.R10

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.G0Galois

/-- (g0-assemble3) g9-abvarbc's `AbVarBaseChange`, from infra-stalks' `MulIsogeny`. -/
theorem abVarBaseChange_g0a3 : ZInQ.Contrib.G9.G9Bridge.AbVarBaseChange :=
  ZInQ.Contrib.AbVarBC.abVarBaseChange_of_mulIsogeny MulRigidity.mulIsogeny

/-- g0-mod-galois's `G9Glue` (verbatim) from the amended R10 (Final.lean's theorem, with
`abVarBaseChange_g0a3`). -/
theorem g9Glue_of_deRhamComparisonHT (h : DeRhamComparisonHT) : G9Glue :=
  g9Glue_of_HT abVarBaseChange_g0a3 h

end ZInQ.Contrib.R10
