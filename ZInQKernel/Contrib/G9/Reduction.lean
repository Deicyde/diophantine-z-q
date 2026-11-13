import ZInQKernel.Contrib.G9.Statement
import ZInQKernel.Contrib.G9.CoefDescent

/-!
# G9: `G9Glue` from three named bridge statements

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

g0-mod-galois's `G9Glue` (restated verbatim in `Statement.lean`) assumes R10
(`PkgI4.DeRhamComparison`) and T23 (`PkgI4.T23_FontaineClosure`). Its conclusion `G9Out r` needs
three facts that are neither among these hypotheses nor in Mathlib (docs/research/g9-derham.md,
findings F1-F3):

* `G9Bridge.LocalModel` (F2): base change of the abelian surface `A/K` to a finite Galois
  `F/ℚ_ℓ` (a completion of a Galois closure at a place above `ℓ`), as an abelian variety of
  pkg-I4's copy `PkgI4.I3.AbVar`, with `V_ℓ(A_F) ≅ V_ℓ(A)|G_F` (every `ℓⁿ`-torsion point of `A`
  over `F̄` is defined over `K̄`), and the decomposition group compatible with `resQ` up to
  conjugation. STANDARD (Mumford, *Abelian varieties*, §4 Thm/§6 Prop on `[n]`; UNVERIFIED
  locators).
* `G9Bridge.R10Weights` (F1): the Hodge–Tate multiplicities of `V_p(A)` vanish outside
  `{0, −1}`. This is part of the published R10 (Hodge–Tate decomposition
  `ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g`, Tate 1967 / Faltings 1988, with Tate's
  `ℂ_p(j)^{G_F} = 0` for `j ≠ 0`); the Lean R10 records only the weights `0, −1`.
* `G9Bridge.BdRContainsQbar` (F3): `ℚ̄_p ⊆ B_dR` `G_{ℚ_p}`-equivariantly (Fontaine; Hensel's
  lemma in the complete DVR `B_dR^+`, whose residue field is `ℂ_p ⊇ ℚ̄_p`). STANDARD.

`g9Glue_of_bridges : LocalModel → R10Weights → BdRContainsQbar → G9Glue` is proved: the rest of
N5's argument (the finite coefficient field, the counting through `E ⊗ V ≅ r ⊕ r`, the Galois
descent from `F` to `ℚ_ℓ`) is in `CoefDescent.lean` and `LocalCore.lean`. T23 is not used.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open PkgI4 Module G0Galois
open scoped TensorProduct

noncomputable section

namespace G9Bridge

/-- **Bridge F2 (local model).** For an abelian surface `A` over a number field `K` and a prime
`ℓ`, there are a finite Galois extension `F/ℚ_ℓ`, an abelian surface `A'` over `F` (pkg-I4's copy
of pkg-I3's abelian varieties; `A' = A ×_K F` for an embedding `K → F`), a homomorphism
`j : G_F → G_K` (restriction along `K̄ → F̄`), a `ℚ_ℓ`-linear isomorphism `V_ℓ(A') ≅ V_ℓ(A)`
intertwining `G_F` with `G_K` through `j`, and `g ∈ G_ℚ` with
`resQ K (j σ) = g · decomp(σ) · g⁻¹` for `σ ∈ G_F` (the decomposition groups of `G_F` inside
`G_ℚ` through `K` and through `ℚ_ℓ` agree up to the choice of embeddings). -/
def LocalModel : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], A.dim = 2 →
    ∃ (F : Type) (_ : Field F) (_ : Algebra ℚ_[ℓ] F) (_ : FiniteDimensional ℚ_[ℓ] F)
      (_ : IsGalois ℚ_[ℓ] F) (A' : PkgI4.I3.AbVar F)
      (j : Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup K)
      (c : A'.V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ) (g : PkgI4.GQ),
      A'.dim = 2 ∧ (∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (j σ) (c v)) ∧
      ∀ σ, resQ K (j σ) = g * PkgI4.decomp ℓ (PkgI4.gfToGqp ℓ F σ) * g⁻¹

/-- **Bridge F1 (the rest of R10).** For an abelian variety `A` over a finite `F/ℚ_p`, the
Hodge–Tate multiplicities of `V_p(A)` vanish at every weight other than `0` and `−1`. -/
def R10Weights : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (w : ℤ), w ≠ 0 → w ≠ -1 → PkgI4.htMultOver p (A.galRep p) w = 0

/-- **Bridge F3.** `ℚ̄_p` embeds into `B_dR` as a `ℚ_p`-algebra, `G_{ℚ_p}`-equivariantly. -/
def BdRContainsQbar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ ι : PadicAlgCl p →ₐ[ℚ_[p]] PkgI4.BdR p,
    ∀ (σ : PkgI4.GQp p) (x : PadicAlgCl p), PkgI4.bdrAct p σ (ι x) = ι (σ x)

/-- `F' ⊆ B_dR` semilinearly, for every finite Galois `F/ℚ_p` (`F' = fieldF p F ⊆ ℚ̄_p`).
Not a bridge: implied by `BdRContainsQbar` (`fieldEmbBdR_of_bdRContainsQbar`) and proved outright
in `Final.lean` from the second run's `iotaDR` (`G9.lean`). -/
def FieldEmbBdR : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F], ∃ ι' : fieldF p F →ₐ[ℚ_[p]] PkgI4.BdR p,
      ∀ (σ : PkgI4.GQp p) (x : fieldF p F), PkgI4.bdrAct p σ (ι' x) = ι' (gammaF p F σ x)

theorem fieldEmbBdR_of_bdRContainsQbar (h : BdRContainsQbar) : FieldEmbBdR := by
  intro p _ F _ _ _ _
  obtain ⟨ι, hι⟩ := h p
  exact ⟨ι.comp (fieldF p F).val, fun σ x => by
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, hι, gammaF_apply_coe]⟩

end G9Bridge

section Assembly

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem galoisRep_mat_mul (r : GaloisRep ℓ 2) (a b : PkgI4.GQ) :
    r.mat (a * b) = r.mat a * r.mat b := by
  simp [GaloisRep.mat, map_mul, Units.val_mul]

theorem galoisRep_mat_inv_mul (r : GaloisRep ℓ 2) (a : PkgI4.GQ) : r.mat a⁻¹ * r.mat a = 1 := by
  rw [← galoisRep_mat_mul, inv_mul_cancel]
  simp [GaloisRep.mat]

theorem galoisRep_mat_mul_inv (r : GaloisRep ℓ 2) (a : PkgI4.GQ) : r.mat a * r.mat a⁻¹ = 1 := by
  rw [← galoisRep_mat_mul, mul_inv_cancel]
  simp [GaloisRep.mat]

/-- Multiplication by `r(g)⁻¹` on both factors. -/
def twistPair (r : GaloisRep ℓ 2) (g : PkgI4.GQ) :
    ((Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) ≃ₗ[PadicAlgCl ℓ]
      ((Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) :=
  LinearEquiv.ofLinear
    ((Matrix.mulVecLin (r.mat g⁻¹)).prodMap (Matrix.mulVecLin (r.mat g⁻¹)))
    ((Matrix.mulVecLin (r.mat g)).prodMap (Matrix.mulVecLin (r.mat g)))
    (LinearMap.ext fun w => by
      change ((r.mat g⁻¹).mulVec ((r.mat g).mulVec w.1),
        (r.mat g⁻¹).mulVec ((r.mat g).mulVec w.2)) = w
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, galoisRep_mat_inv_mul, Matrix.one_mulVec,
        Matrix.one_mulVec])
    (LinearMap.ext fun w => by
      change ((r.mat g).mulVec ((r.mat g⁻¹).mulVec w.1),
        (r.mat g).mulVec ((r.mat g⁻¹).mulVec w.2)) = w
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, galoisRep_mat_mul_inv, Matrix.one_mulVec,
        Matrix.one_mulVec])

theorem twistPair_apply (r : GaloisRep ℓ 2) (g : PkgI4.GQ)
    (w : (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) :
    twistPair r g w = ((r.mat g⁻¹).mulVec w.1, (r.mat g⁻¹).mulVec w.2) := rfl

end Assembly

/-- **G9 (N5's Lemma `lem:de-rham-descent`), from `LocalModel`, `R10Weights` and an
embedding `F' ⊆ B_dR`.** -/
theorem g9Glue_of_fieldEmb (hLM : G9Bridge.LocalModel) (hW : G9Bridge.R10Weights)
    (hB : G9Bridge.FieldEmbBdR) : G9Glue := by
  intro hR10 _hT23 K _ _ A ℓ _ r e hdim hint
  obtain ⟨F, _, _, _, _, A', j, c, g, hdim', hc, hg⟩ := hLM K A ℓ hdim
  obtain ⟨hdR, h0, h1⟩ := hR10 ℓ F A' 2 (by rw [hdim']; rfl)
  obtain ⟨ιB, hιB⟩ := hB ℓ F
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

/-- **G9 from the three bridges.** -/
theorem g9Glue_of_bridges (hLM : G9Bridge.LocalModel) (hW : G9Bridge.R10Weights)
    (hB : G9Bridge.BdRContainsQbar) : G9Glue :=
  g9Glue_of_fieldEmb hLM hW (G9Bridge.fieldEmbBdR_of_bdRContainsQbar hB)

end

end ZInQ.Contrib.G9

#print axioms ZInQ.Contrib.G9.g9Glue_of_bridges
#print axioms ZInQ.Contrib.G9.g9Glue_of_fieldEmb
#print axioms ZInQ.Contrib.G9.core_ht
#print axioms ZInQ.Contrib.G9.core_dR
#print axioms ZInQ.Contrib.G9.coef_descent
