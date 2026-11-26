import ZInQKernel.Contrib.OneProof.DeRhamHTMult.BdRFiltration

/-! # The de Rham filtration of `D_dR` and its graded pieces

Over the period ring `B_dR` of `ZInQKernel/Contrib/G9` (the copy with the kernel's `cpAct`,
`cycPow`), for `V = E^n` with `ρ : G_{ℚ_p} → GL_n(E)`:

* `ddrT p ρ = (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}}` and `IsDeRhamT p ρ`: `dim_{ℚ_p} D_dR(V) = dim_{ℚ_p} V`
  (the tensor form of Fontaine's definition; the analogue, over this copy of `B_dR`, of
  `PanBergerSplit.ddrU` / `IsDeRhamU`, which are stated over a separate copy; no Lean bridge
  between the two copies is written yet);
* `filBdR p i = ξ^i B_dR^+` (`ξ` Fontaine's generator of `ker θ`), the de Rham filtration;
* `filDdR p ρ i = D_dR(V) ∩ (Fil^i B_dR ⊗ V)`, `grDdR p ρ i = Fil^i D_dR / Fil^{i+1} D_dR`;
* `htT p ρ i = (ℂ_p(i) ⊗_{ℚ_p} V)^{G_{ℚ_p}}`, `σ` acting on `ℂ_p(i)` by `χ(σ)^i σ`.

`finrank_grDdR_eq_finrank_htT_of`: if `V` is de Rham, `dim gr^i D_dR(V) = dim (ℂ_p(i) ⊗ V)^G`, given
Tate's two theorems over `ℚ_p` and a uniformizer `T` of `B_dR^+` with `σ(T) = χ(σ) T` (both
supplied by the tree in `GradedDdR`).
-/

set_option autoImplicit false

namespace DeRhamHTMult

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] isFractionRingPlus isDVRPlus

/-- `σ` on `B_dR`, `ℚ_p`-linearly. -/
def bdrL (σ : GQp p) : BdR p →ₗ[ℚ_[p]] BdR p where
  toFun := bdrAct p σ
  map_add' := map_add _
  map_smul' c x := bdrAct_smul p σ c x

/-- `σ` on `ℂ_p(i)`: `x ↦ χ(σ)^i σ(x)`. -/
def cTwL (i : ℤ) (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] := cycPow p σ i • cpL p σ

theorem cTwL_apply (i : ℤ) (σ : GQp p) (x : ℂ_[p]) :
    cTwL p i σ x = cycPow p σ i • cpAct p σ x := rfl

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- `ρ(σ)` on `V = E^n`, `ℚ_p`-linearly. -/
def vActL (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E) :=
  (Matrix.mulVecLin (ρ σ : Matrix (Fin n) (Fin n) E)).restrictScalars ℚ_[p]

theorem vActL_apply (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (v : Fin n → E) :
    vActL p ρ σ v = (ρ σ : Matrix (Fin n) (Fin n) E).mulVec v := rfl

/-- **`D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}}`**. -/
def ddrT (ρ : GQp p →* GL (Fin n) E) : Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] (Fin n → E)) :=
  invT (bdrL p) (vActL p ρ)

/-- **`V` is de Rham**: `dim_{ℚ_p} D_dR(V) = dim_{ℚ_p} V`. -/
def IsDeRhamT (ρ : GQp p →* GL (Fin n) E) : Prop :=
  finrank ℚ_[p] (ddrT p ρ) = finrank ℚ_[p] (Fin n → E)

/-- **`(ℂ_p(i) ⊗_{ℚ_p} V)^{G_{ℚ_p}}`**. -/
def htT (ρ : GQp p →* GL (Fin n) E) (i : ℤ) : Submodule ℚ_[p] (ℂ_[p] ⊗[ℚ_[p]] (Fin n → E)) :=
  invT (cTwL p i) (vActL p ρ)

/-! ## The de Rham filtration of `B_dR` -/

/-- Fontaine's generator `ξ` of `ker θ`, in `B_dR^+`. -/
abbrev xiPlus : BDeRhamPlus 𝓞_ℂ_[p] p := BdrKer.ofPlus 𝓞_ℂ_[p] p (BdrKer.Cp.xi' p)

theorem xiPlus_irreducible : Irreducible (xiPlus p) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (BdrKer.Cp.maximalIdeal_BDeRhamPlus p)

theorem toBdR_ne_zero {y : BDeRhamPlus 𝓞_ℂ_[p] p} (hy : y ≠ 0) :
    algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) y ≠ 0 := fun h0 =>
  hy (IsFractionRing.injective (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (h0.trans (map_zero _).symm))

/-- A nonzero element of `B_dR^+` as a unit of the field `B_dR`. -/
def unitOf {y : BDeRhamPlus 𝓞_ℂ_[p] p} (hy : y ≠ 0) : (BdR p)ˣ :=
  Units.mkOfMulEqOne _ _
    (Classical.choose_spec ((BdrKer.Cp.isField_BDeRham p).mul_inv_cancel (toBdR_ne_zero p hy)))

theorem unitOf_val {y : BDeRhamPlus 𝓞_ℂ_[p] p} (hy : y ≠ 0) :
    (unitOf p hy : BdR p) = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) y := rfl

/-- **`Fil^i B_dR = ξ^i B_dR^+`**, `i ∈ ℤ`. -/
def filBdR (i : ℤ) : Submodule ℚ_[p] (BdR p) :=
  filBdRU p (unitOf p (xiPlus_irreducible p).ne_zero) i

/-- Any uniformizer gives the same filtration. -/
theorem filBdR_eq {T : BDeRhamPlus 𝓞_ℂ_[p] p} (hT : Irreducible T) :
    filBdR p = filBdRU p (unitOf p hT.ne_zero) := by
  funext i
  exact filU_eq_of_associated (qpToPlus p) (hkappa p) (unitOf_val p _) (unitOf_val p _)
    (IsDiscreteValuationRing.associated_of_irreducible _ (xiPlus_irreducible p) hT) i

/-! ## The filtration of `D_dR` -/

/-- **`Fil^i D_dR(V) = D_dR(V) ∩ (Fil^i B_dR ⊗_{ℚ_p} V)`**. -/
def filDdR (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] (Fin n → E)) :=
  filD (filBdR p) (bdrL p) (vActL p ρ) i

/-- **`gr^i D_dR(V) = Fil^i D_dR / Fil^{i+1} D_dR`**. -/
abbrev grDdR (ρ : GQp p →* GL (Fin n) E) (i : ℤ) : Type _ :=
  grD (filBdR p) (bdrL p) (vActL p ρ) i

theorem filDdR_le_ddrT (ρ : GQp p →* GL (Fin n) E) (i : ℤ) : filDdR p ρ i ≤ ddrT p ρ :=
  inf_le_left

theorem bdrAct_algebraMap (σ : GQp p) (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    bdrAct p σ (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) y) =
      algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (DR.bdrPlusMap p (oAct p σ) y) := by
  rw [bdrAct, DR.bdrMap, IsLocalization.map_eq]

theorem htT_twisted (ρ : GQp p →* GL (Fin n) E) :
    ∀ i, ∀ y ∈ htT p ρ i, ∀ σ,
      cycPow p σ i • TensorProduct.map (cpL p σ) (vActL p ρ σ) y = y := fun i y hy σ => by
  have h := hy σ
  rwa [cTwL, TensorProduct.map_smul_left, LinearMap.smul_apply] at h

/-- **Graded pieces of `D_dR` have the dimensions of the twisted invariants**: for `V` de Rham,
`dim_{ℚ_p} gr^i D_dR(V) = dim_{ℚ_p} (ℂ_p(i) ⊗_{ℚ_p} V)^{G_{ℚ_p}}`, given Tate's theorems over `ℚ_p`
and a uniformizer `T` of `B_dR^+` with `σ(T) = χ(σ) T`. -/
theorem finrank_grDdR_eq_finrank_htT_of [FiniteDimensional ℚ_[p] E]
    (hT : ∀ i : ℤ, i ≠ 0 → ∀ x : ℂ_[p], (∀ σ, cycPow p σ i • cpAct p σ x = x) → x = 0)
    (hA : ∀ x : ℂ_[p], (∀ σ, cpAct p σ x = x) → ∃ a : ℚ_[p], x = algebraMap ℚ_[p] ℂ_[p] a)
    {T : BDeRhamPlus 𝓞_ℂ_[p] p} (hTirr : Irreducible T)
    (hσT : ∀ σ : GQp p, DR.bdrPlusMap p (oAct p σ) T = qpToPlus p (cycPow p σ 1) * T)
    (ρ : GQp p →* GL (Fin n) E) (hdR : IsDeRhamT p ρ) (i : ℤ) :
    finrank ℚ_[p] (grDdR p ρ i) = finrank ℚ_[p] (htT p ρ i) := by
  have hσu : ∀ σ : GQp p, bdrAct p σ (unitOf p hTirr.ne_zero : BdR p) =
      algebraMap ℚ_[p] (BdR p) (cycPow p σ 1) * (unitOf p hTirr.ne_zero : BdR p) := fun σ => by
    rw [unitOf_val, bdrAct_algebraMap, hσT, map_mul, hkappa]
  have key := finrank_grD_bdR p hTirr (unitOf p hTirr.ne_zero) (unitOf_val p _) hσu
    (bdrL p) (fun _ _ => rfl) (cTwL p) (fun _ _ _ => rfl) (vActL p ρ)
    (finiteDimensional_twisted_cp p (vActL p ρ) (htT p ρ) hT hA (htT_twisted p ρ))
    (sum_finrank_twisted_le p (vActL p ρ) (htT p ρ) hT hA (htT_twisted p ρ)) hdR i
  show finrank ℚ_[p] (grD (filBdR p) (bdrL p) (vActL p ρ) i) = _
  rw [filBdR_eq p hTirr]
  exact key

end

end DeRhamHTMult
