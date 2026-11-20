import ZInQKernel.Contrib.OneProof.DeRhamPrintDirect
import ZInQKernel.Contrib.OneProof.BdRInvariants

/-!
# derham-range: `ι(F') = B_dR^{G_F}`, and the admissibility form of `DeRhamVpAbVarDirect`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task derham-range, 2026-11-17).
Report: `docs/research/derham-range.md`; scratch copy `scratch/derham-range/DeRhamRange.lean`.

The leaf `DeRhamPrint.Direct.DeRhamVpAbVarDirect` (`DeRhamPrintDirect.lean`) states Fontaine's theorem as
`dim_{F'} D_dR(V_p A) = dim_{ℚ_p} V_p A`, with `F'` acting on `B_dR` through `iotaF : F' → B_dR`. A print
defining "de Rham" through Fontaine's admissibility (`V` is `B_dR`-admissible iff `dim_{B_dR^{G_K}} D_dR(V) =
dim_{ℚ_p} V`, with `B_dR^{G_K} = K` stated separately) needs `ι(F') = B_dR^{G_F}`. Here:

* `range_iotaF_eq_bdrFix`: the range of `iotaF` is exactly `B_dR^{G_F}` (`bdrFix`), from `bdrAct_iotaF`, the
  injectivity of `iotaF` (`B_dR` is a field), the proved `BdRInv.bdRInvariantsPrinted_proof`
  (`dim_{ℚ_p} B_dR^{G_F} = [F:ℚ_p]`) and `finrank_fieldF`;
* `bdrFixAlg`, `B_dR^{G_F}` as a `ℚ_p`-subalgebra of `B_dR`, `bdrFixEquiv : F' ≃ₐ[ℚ_p] B_dR^{G_F}` (so
  `B_dR^{G_F}` is a field, `isField_bdrFixAlg`);
* `ddrFix`, `D_dR(W) = (B_dR ⊗ W)^{G_F}` as a `B_dR^{G_F}`-module (no embedding of `F` needed), and
  `finrank_ddrFix`: `dim_{B_dR^{G_F}} D_dR(W) = dim_{F'} D_dR(W)`;
* `DeRhamVpAbVarAdm` (the admissibility form) and `deRhamVpAbVarDirect_iff_adm`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace DeRhamPrint.Range

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module DeRhamPrint.Direct
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-! ## 1. `ι(F') = B_dR^{G_F}` -/

section Range

variable (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

theorem iotaF_injective : Function.Injective (iotaF p F) := by
  have : Nontrivial (BdR p) := (BdrKer.Cp.isField_BDeRham p).nontrivial
  exact (iotaF p F).toRingHom.injective

theorem range_iotaF_le_bdrFix : LinearMap.range (iotaF p F).toLinearMap ≤ bdrFix p F := by
  rintro _ ⟨x, rfl⟩ σ
  exact bdrAct_iotaF p F σ x

/-- **`ι(F') = B_dR^{G_F}`**: the range of `iotaF : F' → B_dR` is exactly the `G_F`-invariants of `B_dR`. -/
theorem range_iotaF_eq_bdrFix : LinearMap.range (iotaF p F).toLinearMap = bdrFix p F := by
  have hB := BdRInv.bdRInvariantsPrinted_proof p F
  have : FiniteDimensional ℚ_[p] (bdrFix p F) :=
    Module.finite_of_finrank_pos (by rw [hB]; exact Module.finrank_pos)
  apply Submodule.eq_of_le_of_finrank_eq (range_iotaF_le_bdrFix p F)
  rw [LinearMap.finrank_range_of_inj (iotaF_injective p F), finrank_fieldF, hB]

/-- Set form of `range_iotaF_eq_bdrFix`. -/
theorem set_range_iotaF : Set.range (iotaF p F) = (bdrFix p F : Set (BdR p)) := by
  rw [← range_iotaF_eq_bdrFix p F, LinearMap.coe_range]
  rfl

theorem mem_bdrFix_iff (x : BdR p) : x ∈ bdrFix p F ↔ ∃ y, iotaF p F y = x := by
  rw [← range_iotaF_eq_bdrFix p F]
  rfl

/-- **`B_dR^{G_F}` as a `ℚ_p`-subalgebra of `B_dR`** (same carrier as `bdrFix`). -/
def bdrFixAlg : Subalgebra ℚ_[p] (BdR p) where
  carrier := {x | ∀ σ : Field.absoluteGaloisGroup F, bdrAct p (gfToGqp p F σ) x = x}
  mul_mem' ha hb σ := by rw [map_mul, ha σ, hb σ]
  one_mem' σ := map_one _
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  zero_mem' σ := map_zero _
  algebraMap_mem' c σ := by
    rw [Algebra.algebraMap_eq_smul_one, bdrAct_smul, map_one]

theorem toSubmodule_bdrFixAlg : Subalgebra.toSubmodule (bdrFixAlg p F) = bdrFix p F :=
  Submodule.ext fun _ => Iff.rfl

theorem iotaF_mem (y : fieldF p F) : iotaF p F y ∈ bdrFixAlg p F := fun σ => bdrAct_iotaF p F σ y

/-- **`F' ≃ₐ[ℚ_p] B_dR^{G_F}`** through `iotaF`. -/
def bdrFixEquiv : fieldF p F ≃ₐ[ℚ_[p]] bdrFixAlg p F :=
  AlgEquiv.ofBijective ((iotaF p F).codRestrict (bdrFixAlg p F) (iotaF_mem p F))
    ⟨fun y z h => iotaF_injective p F (congrArg Subtype.val h), fun x => by
      obtain ⟨y, hy⟩ := (mem_bdrFix_iff p F x.1).mp x.2
      exact ⟨y, Subtype.ext hy⟩⟩

theorem bdrFixEquiv_apply (y : fieldF p F) : ((bdrFixEquiv p F y : bdrFixAlg p F) : BdR p) = iotaF p F y :=
  rfl

/-- `B_dR^{G_F}` is a field. -/
theorem isField_bdrFixAlg : IsField (bdrFixAlg p F) :=
  MulEquiv.isField (Field.toIsField (fieldF p F)) (bdrFixEquiv p F).symm.toMulEquiv

end Range

/-! ## 2. `D_dR` as a `B_dR^{G_F}`-module -/

section Ddr

variable {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]

theorem smul_fix_def (s : bdrFixAlg p F) (x : BdR p ⊗[ℚ_[p]] W) : s • x = (s : BdR p) • x := rfl

theorem map_smulFix (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W)
    (σ : Field.absoluteGaloisGroup F) (s : bdrFixAlg p F) (x : BdR p ⊗[ℚ_[p]] W) :
    TensorProduct.map (drAct p (gfToGqp p F σ)) (ρW σ) (s • x) =
      s • TensorProduct.map (drAct p (gfToGqp p F σ)) (ρW σ) x := by
  rw [smul_fix_def, smul_fix_def]
  induction x using TensorProduct.inductionOn with
  | tmul b w =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', drAct_apply, drAct_apply, smul_eq_mul, smul_eq_mul, map_mul]
    congr 2
    exact s.2 σ
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **`D_dR(W) = (B_dR ⊗_{ℚ_p} W)^{G_F}` as a `B_dR^{G_F}`-module** (Fontaine's admissibility setting: the
coefficient field is the invariant field `B_dR^{G_F}` of the period ring, no embedding of `F` used). Same
carrier as `ddrTensorOver` and `Direct.ddrF`. -/
def ddrFix (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    Submodule (bdrFixAlg p F) (BdR p ⊗[ℚ_[p]] W) where
  carrier := {x | ∀ σ, TensorProduct.map (drAct p (gfToGqp p F σ)) (ρW σ) x = x}
  zero_mem' σ := map_zero _
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  smul_mem' c x hx σ := by rw [map_smulFix, hx σ]

theorem restrictScalars_ddrFix (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    (ddrFix p ρW).restrictScalars ℚ_[p] = ddrTensorOver p ρW :=
  Submodule.ext fun _ => Iff.rfl

attribute [local instance] algF

theorem smul_eq_iotaF_smul (c : fieldF p F) (x : BdR p ⊗[ℚ_[p]] W) :
    c • x = (bdrFixEquiv p F c : bdrFixAlg p F) • x := by
  rw [smul_fix_def]
  induction x using TensorProduct.inductionOn with
  | tmul b w =>
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]
    rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

/-- **The translation**: `dim_{B_dR^{G_F}} D_dR(W) = dim_{F'} D_dR(W)` (through `ι : F' ≃ B_dR^{G_F}`). -/
theorem finrank_ddrFix (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    finrank (bdrFixAlg p F) (ddrFix p ρW) = finrank (fieldF p F) (ddrF p ρW) := by
  let j : ddrF p ρW ≃+ ddrFix p ρW :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have h := rank_eq_of_equiv_equiv (fun c => bdrFixEquiv p F c) j (bdrFixEquiv p F).bijective
    (fun c m => Subtype.ext (smul_eq_iotaF_smul p c m.1))
  simp only [Module.finrank, h]

/-- The admissibility form of "de Rham": `dim_{B_dR^{G_F}} D_dR(W) = dim_{ℚ_p} W`. -/
def IsDeRhamAdm (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) : Prop :=
  finrank (bdrFixAlg p F) (ddrFix p ρW) = finrank ℚ_[p] W

theorem isDeRhamAdm_iff (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    IsDeRhamAdm p ρW ↔ finrank (fieldF p F) (ddrF p ρW) = finrank ℚ_[p] W := by
  rw [IsDeRhamAdm, finrank_ddrFix]

theorem isDeRhamAdm_iff_tensorOver (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    IsDeRhamAdm p ρW ↔ IsDeRhamTensorOver p ρW := by
  rw [isDeRhamAdm_iff, isDeRhamTensorOver_iff]

end Ddr

end

/-! ## 3. The leaf in admissibility form -/

/-- **LEAF (admissibility form; Fontaine: the Tate module of an abelian variety is de Rham).** Same print as
`Direct.DeRhamVpAbVarDirect` (Berger 2004, §II.5.1, p. 19, attributed to Fontaine; locator per the integrator's
reading, UNVERIFIED here), read with Fontaine's admissibility definition: `V` is de Rham iff `D_dR(V) =
(B_dR ⊗_{ℚ_p} V)^{G_K}` has dimension `dim_{ℚ_p} V` over `B_dR^{G_K}`. Lean form: `A` an abelian variety over a
finite extension `F` of `ℚ_p` (pkg-I4's `AbVar`), `G_F` acting through `gfToGqp`, `D_dR = ddrFix` over
`bdrFixAlg = B_dR^{G_F}`. Equivalent to `DeRhamVpAbVarDirect` (`deRhamVpAbVarDirect_iff_adm`) through the proved
`ι(F') = B_dR^{G_F}` (`range_iotaF_eq_bdrFix`). -/
def DeRhamVpAbVarAdm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), IsDeRhamAdm p (A.galRep p)

/-- **The leaf's `dim_{F'}` form is the admissibility form.** -/
theorem deRhamVpAbVarDirect_iff_adm : DeRhamVpAbVarDirect ↔ DeRhamVpAbVarAdm :=
  ⟨fun h p _ F _ _ _ A => (isDeRhamAdm_iff p (A.galRep p)).mpr (h p F A),
    fun h p _ F _ _ _ A => (isDeRhamAdm_iff p (A.galRep p)).mp (h p F A)⟩

/-- **`DeRhamVpAbVarDirect` from the admissibility-form leaf.** -/
theorem deRhamVpAbVarDirect_of_adm (h : DeRhamVpAbVarAdm) : DeRhamVpAbVarDirect :=
  deRhamVpAbVarDirect_iff_adm.mpr h

/-- **The research field `deRhamVpAbVarPrinted` from the admissibility-form leaf.** -/
theorem deRhamVpAbVarPrinted_of_adm (h : DeRhamVpAbVarAdm) : DeRhamVpAbVarPrinted :=
  deRhamVpAbVarPrinted_of_direct (deRhamVpAbVarDirect_of_adm h)

end DeRhamPrint.Range
