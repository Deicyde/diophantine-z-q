import ZInQKernel.Contrib.OneProof.FontaineComparison
import ZInQKernel.Contrib.OneProof.LogPTildeFontaine

/-! # Fontaine's formal semistable variable and its image

The proved logarithm argument identifies the formal polynomial ring over the
crystalline coefficients with the actual image in `B_dR`. The comparison
records the action on constants and on the formal variable, in the branch
`log(p) = 0`.
-/

noncomputable section

namespace HDec.PkgI4.FontaineComparison

open BergerBst FontaineSt BmaxOne LogPTransc
open _root_.ZInQ.Contrib.G9.BdrKer.Cp (xi)

/-- The printed crystalline log lemma holds for the concrete period
coefficients. The proof goes through the stronger statement over `B_max`,
proved by the auxiliary-ring argument of Fontaine II §4.3.2. -/
theorem fontaineLog431_proof : FontaineLog431 := by
  intro p _ ε h a b ha hab
  have hle := bcrisOf_le_bmax p h (theta_xi' p)
  refine LogPFontaine.notInFrac_bmax_logPTilde p (Subalgebra.inclusion hle a)
    (Subalgebra.inclusion hle b) ?_ ?_
  · intro he
    apply ha
    apply Subtype.ext
    have h1 := congrArg Subtype.val he
    rw [Subalgebra.coe_inclusion, ZeroMemClass.coe_zero] at h1
    rw [ZeroMemClass.coe_zero]
    exact h1
  · rw [Subalgebra.coe_inclusion, Subalgebra.coe_inclusion]
    exact hab

variable (p : ℕ) [Fact p.Prime]

/-- The crystalline coefficients at the chosen generators. -/
abbrev Crystal := BcrisOf p (eps0_spec p) (xi p) (theta_xi' p)

/-- The image of Fontaine's semistable ring in `B_dR`. -/
abbrev SemistableImage := BstFOf p (eps0_spec p) (xi p) (theta_xi' p)

/-- Fontaine's semistable ring as a formal polynomial ring. -/
abbrev SemistablePoly := Polynomial (Crystal p)

/-- Fontaine II, Théorème 4.2.4 at `K = ℚ_p`, for the image presentation of
the crystalline coefficients. -/
def imageEquiv : SemistablePoly p ≃ₐ[ℚ_[p]] SemistableImage p :=
  semistablePolyEquiv p fontaineLog431_proof (eps0_spec p)

/-- The actual map into the de Rham ring. -/
def polyEval : SemistablePoly p →ₐ[ℚ_[p]] BdR p :=
  (SemistableImage p).val.comp (imageEquiv p).toAlgHom

theorem polyEval_apply (v : SemistablePoly p) :
    polyEval p v = ((imageEquiv p v : SemistableImage p) : BdR p) := rfl

/-- Evaluation at `log [p̃]`. -/
theorem polyEval_eq_aeval (v : SemistablePoly p) :
    polyEval p v = Polynomial.aeval (R := Crystal p) (toBdR p (logPTilde p)) v := rfl

theorem polyEval_injective : Function.Injective (polyEval p) := by
  intro x y hxy
  rw [polyEval_apply, polyEval_apply] at hxy
  exact (imageEquiv p).injective (Subtype.ext hxy)

@[simp] theorem polyEval_X : polyEval p Polynomial.X = toBdR p (logPTilde p) := by
  rw [polyEval_eq_aeval, Polynomial.aeval_X]

@[simp] theorem polyEval_C (a : Crystal p) : polyEval p (Polynomial.C a) = (a : BdR p) := by
  rw [polyEval_eq_aeval, Polynomial.aeval_C]
  rfl

/-- Restrict the actual Galois action to the semistable image. -/
def imageAct (σ : GQp p) : SemistableImage p →ₐ[ℚ_[p]] SemistableImage p :=
  ((bdrAlg p σ).comp (SemistableImage p).val).codRestrict (SemistableImage p)
    (fun z => by
      rw [AlgHom.comp_apply, bdrAlg_apply]
      exact bstF_stable p (eps0_spec p) σ z z.2)

/-- The action transported back to the formal polynomial ring. -/
def polyAct (σ : GQp p) : SemistablePoly p →ₐ[ℚ_[p]] SemistablePoly p :=
  (imageEquiv p).symm.toAlgHom.comp ((imageAct p σ).comp (imageEquiv p).toAlgHom)

theorem polyEval_polyAct (σ : GQp p) (v : SemistablePoly p) :
    polyEval p (polyAct p σ v) = bdrAct p σ (polyEval p v) := by
  show ((imageEquiv p ((imageEquiv p).symm (imageAct p σ (imageEquiv p v))) :
    SemistableImage p) : BdR p) = bdrAct p σ ((imageEquiv p v : SemistableImage p) : BdR p)
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- On constants, the formal action is the action on the crystalline
coefficients. -/
theorem polyAct_C (σ : GQp p) (a : Crystal p) :
    polyAct p σ (Polynomial.C a) =
      Polynomial.C ⟨bdrAct p σ (a : BdR p), bcris_gStable p (eps0_spec p) σ _ a.2⟩ := by
  apply polyEval_injective p
  rw [polyEval_polyAct, polyEval_C, polyEval_C]

/-- On the formal variable, the action is affine: `X ↦ X + c` for some
`c ∈ B_cris` with `c = σ(log [p̃]) − log [p̃]`, the shape of Fontaine's
`g u = u + η(g) t` (Exposé II, 4.3.3, p. 89). The proof takes `c = log [u_σ]`
with `σ(p̃) = p̃ · u_σ`; the statement does not record that formula. No
identification of the semistable ring with a polynomial ring over `B_max` is
used. -/
theorem polyAct_X (σ : GQp p) :
    ∃ c : Crystal p, polyAct p σ Polynomial.X = Polynomial.C c + Polynomial.X ∧
      bdrAct p σ (toBdR p (logPTilde p)) = (c : BdR p) + toBdR p (logPTilde p) := by
  obtain ⟨u, hu, hu1⟩ := exists_uSigma p σ
  have h := bdrAct_logPTilde p σ hu hu1
  refine ⟨⟨toBdR p (logTeich p hu1),
    Algebra.subset_adjoin (Or.inl ⟨_, logTeich_mem_acris p hu1, rfl⟩)⟩, ?_, h⟩
  apply polyEval_injective p
  rw [polyEval_polyAct, map_add, polyEval_C, polyEval_X]
  exact h

end HDec.PkgI4.FontaineComparison
