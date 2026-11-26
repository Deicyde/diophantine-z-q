import ZInQKernel.Contrib.OneProof.ModularHTCoeff
import ZInQKernel.Contrib.OneProof.DeRhamHTMult.Periods
import ZInQKernel.Contrib.OneProof.DeRhamHTMult.DdR

/-! # De Rham representations: graded pieces of `D_dR` give the Hodge–Tate multiplicities

For a finite extension `F/ℚ_p` inside `ℚ̄_p` and a representation `ρ : G_{ℚ_p} → GL_n(F)` on
`V = F^n`, with `D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}}`, `Fil^i B_dR = ξ^i B_dR^+`,
`Fil^i D_dR = D_dR ∩ (Fil^i B_dR ⊗ V)` and `gr^i D_dR = Fil^i D_dR / Fil^{i+1} D_dR` (`DdR`):

* `finrank_grDdR_eq_finrank_htT`: for `V` de Rham,
  `dim_{ℚ_p} gr^i D_dR(V) = dim_{ℚ_p} (ℂ_p(i) ⊗_{ℚ_p} V)^{G_{ℚ_p}}`;
* `printHTMult_eq_finrank_grDdR`: for `V` de Rham,
  `dim_{ℚ_p} gr^i D_dR(V) = [F : ℚ_p] · PrintHTMult p F ρ i`, where
  `PrintHTMult p F ρ i = dim_F (V ⊗_{ℚ_p} ℂ_p(i))^{G_{ℚ_p}}` is the print-side Hodge–Tate
  multiplicity of `ModularHTCoeff.lean` (the cyclotomic character has weight `−1`);
* `printHasHTWeights_of_grDdR`: graded dimensions `[F : ℚ_p] · S.count i` give
  `PrintHasHTWeights p F ρ S`.

Proof: `gr^i B_dR ≅ ℂ_p(i)` through `t^i y ↦ θ(y)` (`t = log [ε]` a uniformizer with
`σ(t) = χ(σ) t`, `Periods`), so `gr^i D_dR` embeds in `(ℂ_p(i) ⊗ V)^G` (flatness of `V`,
`Graded`); the Tate–Sen bound `Σ_i dim (ℂ_p(i) ⊗ V)^G ≤ dim V` (from Tate's two theorems over
`ℚ_p`, proved on main, `TateSenCp`) and `Σ_i dim gr^i D_dR = dim D_dR = dim V` force equality in
every degree.

`KatoDeRhamCoeff` states Kato's de Rham form (Astérisque 295 (2004), 9.4, with 14.10.3 for the
Frobenius polynomial; geometric Frobenius) over a finite coefficient field, and
`modularHTCoeff_of_kato` derives `HTNewAssembly.ModularHTCoeff` from it. This leaf is in Kato's
filtered form and is stronger than the row it implies; no fold is proposed.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace DeRhamHTMult

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-! ## Tate's theorems over `ℚ_p` (proved on main) -/

theorem tate_qp (i : ℤ) (hi : i ≠ 0) (x : ℂ_[p])
    (hx : ∀ σ : GQp p, cycPow p σ i • cpAct p σ x = x) : x = 0 :=
  EigenformHTPrinted.tate p ⊥ i hi x fun σ _ => hx σ

theorem axSen_qp (x : ℂ_[p]) (hx : ∀ σ : GQp p, cpAct p σ x = x) :
    ∃ a : ℚ_[p], x = algebraMap ℚ_[p] ℂ_[p] a := by
  obtain ⟨y, hy⟩ := EigenformHTPrinted.axSen p ⊥ x fun σ _ => hx σ
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp y.2
  refine ⟨a, ?_⟩
  rw [hy, ← ha, PadicComplex.coe_eq, ← IsScalarTower.algebraMap_apply]

/-! ## The main theorem -/

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- **`dim gr^i D_dR(V) = dim (ℂ_p(i) ⊗ V)^{G_{ℚ_p}}`** for `V` de Rham. -/
theorem finrank_grDdR_eq_finrank_htT (ρ : GQp p →* GL (Fin n) E) (hdR : IsDeRhamT p ρ)
    (i : ℤ) : finrank ℚ_[p] (grDdR p ρ i) = finrank ℚ_[p] (htT p ρ i) := by
  obtain ⟨T, hT, hσT⟩ := exists_uniformizer p
  exact finrank_grDdR_eq_finrank_htT_of p (tate_qp p) (axSen_qp p) hT hσT ρ hdR i

/-! ## The print-side multiplicity `PrintHTMult` -/

section PrintSide

variable {F : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] F]

attribute [local instance] HTNewAssembly.smulCommClassE HTNewAssembly.moduleE
  HTNewAssembly.isScalarTowerE

theorem comm_twistAct (ρ : GQp p →* GL (Fin n) F) (i : ℤ) (σ : GQp p)
    (t : (Fin n → F) ⊗[ℚ_[p]] ℂ_[p]) :
    TensorProduct.comm ℚ_[p] (Fin n → F) ℂ_[p] (HTNewAssembly.twistAct p F ρ i σ t) =
      TensorProduct.map (cTwL p i σ) (vActL p ρ σ)
        (TensorProduct.comm ℚ_[p] (Fin n → F) ℂ_[p] t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c =>
    rw [HTNewAssembly.twistAct_tmul, TensorProduct.comm_tmul, TensorProduct.comm_tmul,
      TensorProduct.map_tmul, HTNewAssembly.cTw_apply, cTwL_apply, vActL_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `(V ⊗ ℂ_p(i))^G ≅ (ℂ_p(i) ⊗ V)^G` through `v ⊗ c ↦ c ⊗ v`. -/
theorem map_comm_printHTSpace (ρ : GQp p →* GL (Fin n) F) (i : ℤ) :
    ((HTNewAssembly.PrintHTSpace p F ρ i).restrictScalars ℚ_[p]).map
      (TensorProduct.comm ℚ_[p] (Fin n → F) ℂ_[p]).toLinearMap = htT p ρ i := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩ σ
    have ht' : t ∈ HTNewAssembly.PrintHTSpace p F ρ i := ht
    change TensorProduct.map (cTwL p i σ) (vActL p ρ σ)
      (TensorProduct.comm ℚ_[p] (Fin n → F) ℂ_[p] t) = TensorProduct.comm ℚ_[p] _ _ t
    rw [← comm_twistAct, ht' σ]
  · intro hy
    refine ⟨(TensorProduct.comm ℚ_[p] (Fin n → F) ℂ_[p]).symm y, fun σ => ?_, by simp⟩
    apply (TensorProduct.comm ℚ_[p] (Fin n → F) ℂ_[p]).injective
    rw [comm_twistAct, LinearEquiv.apply_symm_apply]
    exact hy σ

/-- `dim_{ℚ_p} (ℂ_p(i) ⊗ V)^G = [F : ℚ_p] · PrintHTMult p F ρ i`. -/
theorem finrank_htT_eq (ρ : GQp p →* GL (Fin n) F) (i : ℤ) :
    finrank ℚ_[p] (htT p ρ i) = finrank ℚ_[p] F * HTNewAssembly.PrintHTMult p F ρ i := by
  have h1 : finrank ℚ_[p] ((HTNewAssembly.PrintHTSpace p F ρ i).restrictScalars ℚ_[p]) =
      finrank ℚ_[p] (htT p ρ i) := by
    rw [← map_comm_printHTSpace, LinearEquiv.finrank_map_eq]
  have h2 : finrank ℚ_[p] F * finrank F (HTNewAssembly.PrintHTSpace p F ρ i) =
      finrank ℚ_[p] ((HTNewAssembly.PrintHTSpace p F ρ i).restrictScalars ℚ_[p]) := by
    have : Module.Free F (HTNewAssembly.PrintHTSpace p F ρ i) :=
      Module.Free.of_divisionRing F (HTNewAssembly.PrintHTSpace p F ρ i)
    exact Module.finrank_mul_finrank ℚ_[p] F (HTNewAssembly.PrintHTSpace p F ρ i)
  rw [← h1, ← h2]
  rfl

/-- **The identification** (de Rham ⇒ Hodge–Tate on the print's side):
`dim_{ℚ_p} gr^i D_dR(V) = [F : ℚ_p] · dim_F (V ⊗_{ℚ_p} ℂ_p(i))^{G_{ℚ_p}}`. -/
theorem printHTMult_eq_finrank_grDdR (ρ : GQp p →* GL (Fin n) F) (hdR : IsDeRhamT p ρ)
    (i : ℤ) :
    finrank ℚ_[p] (grDdR p ρ i) = finrank ℚ_[p] F * HTNewAssembly.PrintHTMult p F ρ i := by
  rw [finrank_grDdR_eq_finrank_htT p ρ hdR, finrank_htT_eq]

/-- The same, as a quotient: `PrintHTMult p F ρ i = dim_{ℚ_p} gr^i D_dR(V) / [F : ℚ_p]`. -/
theorem printHTMult_eq_div (ρ : GQp p →* GL (Fin n) F) (hdR : IsDeRhamT p ρ) (i : ℤ) :
    HTNewAssembly.PrintHTMult p F ρ i = finrank ℚ_[p] (grDdR p ρ i) / finrank ℚ_[p] F := by
  rw [printHTMult_eq_finrank_grDdR p ρ hdR, Nat.mul_div_cancel_left _ Module.finrank_pos]

/-- **Graded dimensions give the Hodge–Tate weights** (cyclotomic character of weight `−1`). -/
theorem printHasHTWeights_of_grDdR (ρ : GQp p →* GL (Fin n) F) (hdR : IsDeRhamT p ρ)
    (S : Multiset ℤ) (hS : ∀ i, finrank ℚ_[p] (grDdR p ρ i) = finrank ℚ_[p] F * S.count i) :
    HTNewAssembly.PrintHasHTWeights p F ρ S := fun i =>
  Nat.eq_of_mul_eq_mul_left Module.finrank_pos
    ((printHTMult_eq_finrank_grDdR p ρ hdR i).symm.trans (hS i))

end PrintSide

end

/-! ## Kato's de Rham form and `ModularHTCoeff` -/

/-- **Kato's de Rham form of the modular Galois representation** (K. Kato, *p-adic Hodge theory
and values of zeta functions of modular forms*, Astérisque 295 (2004), 117–290; geometric
Frobenius). Locators, all UNVERIFIED for this leaf (no reading of the print recorded): §§9.2–9.4,
(9.2.2), pp. 187–188 for `V_{F_λ}(f)` de Rham at every level (the locators recorded for row R13 in
`docs/research/htnew-assembly.md`); §11.3 for the Hodge filtration jumps `0, k − 1`; 8.3 for
`V_{F_λ}(f)` and 14.10.3 for its Frobenius polynomial. Over a finite coefficient field `E ⊆ ℚ̄_ℓ`:
for a newform `f` of weight `k ≥ 2` there are a finite `E/ℚ_ℓ` inside `ℚ̄_ℓ` and a continuous
`ρ : G_ℚ → GL₂(E)`, unramified at `p ∤ Nℓ`, with geometric Frobenius traces `a_p(f)`, such that
`ρ|_{G_{ℚ_ℓ}}` is de Rham and the graded pieces of its de Rham filtration have `E`-dimension one
in degrees `0` and `k − 1` and zero otherwise (in `ℚ_ℓ`-dimensions,
`[E : ℚ_ℓ] · {0, k − 1}.count i`). -/
def KatoDeRhamCoeff : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (f : HeckeRing.GL2.Newform N k), 2 ≤ k →
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρ : GQ →* GL (Fin 2) E), Continuous ρ ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ v : ValuationSubring Qbar, LiesOver v p →
        ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ∀ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) p →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (((ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) E).trace : E) : PadicAlgCl ℓ) = ιL α) ∧
      IsDeRhamT ℓ (ρ.comp (decomp ℓ)) ∧
      ∀ i : ℤ, finrank ℚ_[ℓ] (grDdR ℓ (ρ.comp (decomp ℓ)) i) =
        finrank ℚ_[ℓ] E * ({0, k - 1} : Multiset ℤ).count i

/-- **`ModularHTCoeff` from Kato's de Rham form**, through `printHasHTWeights_of_grDdR` (the
geometric disjunct). -/
theorem modularHTCoeff_of_kato (h : KatoDeRhamCoeff) : HTNewAssembly.ModularHTCoeff := by
  intro ℓ _ ιC ιL N _ k f hk
  obtain ⟨E, hE, ρ, hc, hun, hfr, hdR, hgr⟩ := h ℓ ιC ιL N k f hk
  exact ⟨E, hE, ρ, hc, hun,
    Or.inr ⟨hfr, printHasHTWeights_of_grDdR ℓ (ρ.comp (decomp ℓ)) hdR _ hgr⟩⟩

end DeRhamHTMult
