import ZInQKernel.Contrib.OneProof.DeRhamPrint

/-!
# derham-direct: `DeRhamVpAbVarPrinted` as a direct instance of its print (Berger II.5.1, p. 19)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task derham-direct, 2026-11-17).
Report: `docs/research/derham-direct.md`; scratch copy `scratch/derham-direct/DeRhamDirect.lean`.

The research field `DeRhamPrint.DeRhamVpAbVarPrinted` (`DeRhamPrint.lean`) states Fontaine's theorem "`V_p(A)` is
de Rham" as `IsDeRhamTensorOver`: `dim_{ℚ_p} (B_dR ⊗ V_p A)^{G_F} = [F:ℚ_p] · dim V_p A`. The print (Berger,
*An introduction to the theory of p-adic representations*, 2004, §II.5.1, p. 19, attributing it to Fontaine) says
`dim_K D_dR(V) = dim_{ℚ_p} V`, with `D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_K}` a `K`-vector space through
`K ⊆ K̄ ⊆ B_dR^+`. Here:

* §1: for any finite `F/ℚ_p` (not necessarily Galois; g9-derham's `iotaDR` needs Galois), `iotaPlusF : F' → B_dR^+`,
  the Hensel lift of `F' ⊆ ℚ̄_p ⊆ ℂ_p` through `θ⁺` (g9-derham's `exists_hensel_lift`), unique
  (`iotaPlusF_unique`), and `bdrAct_iotaF`: `G_F` (through `gfToGqp`, image `G_{F'}`: `range_gfToGqp_eq`) fixes
  `iotaF x ∈ B_dR`;
* §2: `ddrF`, `D_dR` as an `F'`-subspace of `B_dR ⊗ W` (same carrier as `ddrTensorOver`), and the tower law
  `finrank_ddrTensorOver`: `dim_{ℚ_p} D_dR = [F:ℚ_p] · dim_{F'} D_dR`;
* §3: the leaf as printed, `DeRhamVpAbVarDirect` (`dim_{F'} D_dR(V_p A) = dim_{ℚ_p} V_p A`), and
  `deRhamVpAbVarPrinted_of_direct` (with the converse: the two Props are equivalent).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

namespace DeRhamPrint.Direct

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-! ## §1. `F' ⊆ B_dR^+` for any finite `F/ℚ_p`, fixed by `G_F` -/

section Emb

attribute [local instance] algPlus

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

theorem exists_iotaPlusF : ∃ ι₀ : fieldF p F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p,
    ∀ x, thetaAlg p (ι₀ x) = iotaCp p F x :=
  exists_hensel_lift (thetaAlg p) (BdrKer.Cp.thetaPlusCp_surjective p)
    (isUnit_of_thetaAlg_ne_zero p) (iotaCp p F)

/-- **`F' ⊆ B_dR^+`**: the lift of `F' ⊆ ℚ̄_p ⊆ ℂ_p` through `θ⁺ : B_dR^+ → ℂ_p` (Hensel's lemma in the
`ker θ⁺`-adically complete local domain `B_dR^+`). Unique: `iotaPlusF_unique`. -/
def iotaPlusF : fieldF p F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p := (exists_iotaPlusF p F).choose

theorem thetaAlg_iotaPlusF (x : fieldF p F) : thetaAlg p (iotaPlusF p F x) = iotaCp p F x :=
  (exists_iotaPlusF p F).choose_spec x

/-- **The embedding is canonical**: every `ℚ_p`-algebra map `F' → B_dR^+` lifting `F' ⊆ ℂ_p` through `θ⁺`
is `iotaPlusF`. -/
theorem iotaPlusF_unique (ι₀ : fieldF p F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p)
    (h : ∀ x, thetaAlg p (ι₀ x) = iotaCp p F x) : ι₀ = iotaPlusF p F := by
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ_[p] (fieldF p F)
  have hsep : (minpoly ℚ_[p] pb.gen).Separable := Algebra.IsSeparable.isSeparable ℚ_[p] pb.gen
  have hroot : Polynomial.aeval pb.gen (minpoly ℚ_[p] pb.gen) = 0 := minpoly.aeval ℚ_[p] pb.gen
  apply pb.algHom_ext
  refine root_eq_of_theta (thetaAlg p) (minpoly ℚ_[p] pb.gen) ?_ ?_ ?_ ?_
  · rw [Polynomial.aeval_algHom_apply, hroot, map_zero]
  · rw [Polynomial.aeval_algHom_apply, hroot, map_zero]
  · rw [h, thetaAlg_iotaPlusF]
  · rw [thetaAlg_iotaPlusF, Polynomial.aeval_algHom_apply]
    exact (map_ne_zero _).mpr (hsep.aeval_derivative_ne_zero hroot)

/-- `G_F` (through `gfToGqp`) fixes `F' ⊆ ℚ̄_p` pointwise (`range_gfToGqp_eq`). -/
theorem gfToGqp_fix (σ : Field.absoluteGaloisGroup F) (x : fieldF p F) :
    gfToGqp p F σ (x : PadicAlgCl p) = x := by
  have h : gfToGqp p F σ ∈ ((fieldF p F).fixingSubgroup : Set (GQp p)) := by
    rw [← range_gfToGqp_eq p F]
    exact ⟨σ, rfl⟩
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp h x x.2

theorem cpAct_iotaCp_gf (σ : Field.absoluteGaloisGroup F) (x : fieldF p F) :
    cpAct p (gfToGqp p F σ) (iotaCp p F x) = iotaCp p F x := by
  simp only [iotaCp, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  rw [← PadicComplex.coe_eq, cpAct_coe]
  congr 1
  exact gfToGqp_fix p F σ x

theorem bdrPlusMap_iotaPlusF (σ : Field.absoluteGaloisGroup F) (x : fieldF p F) :
    DR.bdrPlusMap p (oAct p (gfToGqp p F σ)) (iotaPlusF p F x) = iotaPlusF p F x :=
  hensel_lift_natural (thetaAlg p) (iotaCp p F) (iotaPlusF p F) (thetaAlg_iotaPlusF p F)
    (sPlus p (gfToGqp p F σ)) (AlgHom.id ℚ_[p] (fieldF p F)) (fun y => by
      change BdrKer.Cp.thetaPlusCp p (DR.bdrPlusMap p (oAct p (gfToGqp p F σ)) (iotaPlusF p F y)) = _
      rw [thetaPlusCp_bdrPlusMap, ← thetaAlg_apply, thetaAlg_iotaPlusF, cpAct_iotaCp_gf]
      rfl) x

/-- **`F' ⊆ B_dR`**, a `ℚ_p`-algebra map for pkg-I4's `ℚ_p ⊆ B_dR` (`B_dR^+ → B_dR` after `iotaPlusF`). -/
def iotaF : fieldF p F →ₐ[ℚ_[p]] BdR p :=
  { (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)).comp (iotaPlusF p F).toRingHom with
    commutes' := fun c => by
      change algebraMap _ (BdR p) (iotaPlusF p F (algebraMap ℚ_[p] _ c)) = qpToBdR p c
      rw [AlgHom.commutes]
      rfl }

theorem iotaF_apply (x : fieldF p F) :
    iotaF p F x = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (iotaPlusF p F x) := rfl

/-- **`F' ⊆ B_dR^{G_F}`**: `G_F` (through `gfToGqp`) fixes `ι(F')`. -/
theorem bdrAct_iotaF (σ : Field.absoluteGaloisGroup F) (x : fieldF p F) :
    bdrAct p (gfToGqp p F σ) (iotaF p F x) = iotaF p F x := by
  rw [iotaF_apply, bdrAct, DR.bdrMap, IsLocalization.map_eq, bdrPlusMap_iotaPlusF]

end Emb

/-! ## §2. `D_dR(V)` as an `F'`-vector space -/

section Ddr

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `B_dR` as an `F'`-algebra through `ι = iotaF` (`F' → ℚ̄_p → B_dR^+ → B_dR`). -/
@[instance_reducible] def algF : Algebra (fieldF p F) (BdR p) := (iotaF p F).toRingHom.toAlgebra

attribute [local instance] algF

theorem algebraMap_algF (x : fieldF p F) : algebraMap (fieldF p F) (BdR p) x = iotaF p F x := rfl

instance towerF : IsScalarTower ℚ_[p] (fieldF p F) (BdR p) :=
  IsScalarTower.of_algebraMap_eq fun c => ((iotaF p F).commutes c).symm

variable {F} {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]

theorem map_smulF (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W)
    (σ : Field.absoluteGaloisGroup F) (c : fieldF p F) (x : BdR p ⊗[ℚ_[p]] W) :
    TensorProduct.map (drAct p (gfToGqp p F σ)) (ρW σ) (c • x) =
      c • TensorProduct.map (drAct p (gfToGqp p F σ)) (ρW σ) x := by
  induction x using TensorProduct.inductionOn with
  | tmul b w =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', drAct_apply, drAct_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
      algebraMap_algF, bdrAct_iotaF]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **`D_dR(W) = (B_dR ⊗_{ℚ_p} W)^{G_F}` as an `F'`-vector space**, `F'` acting on `B_dR` through
`ι : F' → ℚ̄_p → B_dR^+ → B_dR` (Berger's `K`-structure, `K = F'`; `G_F` acts through `gfToGqp`, whose image is
`G_{F'}`). Same carrier as `ddrTensorOver` (`restrictScalars_ddrF`). -/
def ddrF (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    Submodule (fieldF p F) (BdR p ⊗[ℚ_[p]] W) where
  carrier := {x | ∀ σ, TensorProduct.map (drAct p (gfToGqp p F σ)) (ρW σ) x = x}
  zero_mem' σ := map_zero _
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  smul_mem' c x hx σ := by rw [map_smulF, hx σ]

theorem restrictScalars_ddrF (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    (ddrF p ρW).restrictScalars ℚ_[p] = ddrTensorOver p ρW :=
  Submodule.ext fun _ => Iff.rfl

/-- **The translation** `dim_{ℚ_p} D_dR = [F:ℚ_p] · dim_{F'} D_dR` (tower law, `[F':ℚ_p] = [F:ℚ_p]`). -/
theorem finrank_ddrTensorOver (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    finrank ℚ_[p] (ddrTensorOver p ρW) = finrank ℚ_[p] F * finrank (fieldF p F) (ddrF p ρW) := by
  rw [← restrictScalars_ddrF, ← finrank_fieldF p F,
    ((ddrF p ρW).restrictScalarsEquiv ℚ_[p] (fieldF p F)).restrictScalars ℚ_[p] |>.finrank_eq]
  have : Module.Free (fieldF p F) (ddrF p ρW) := by
    exact Module.Free.of_divisionRing (fieldF p F) (ddrF p ρW)
  exact (Module.finrank_mul_finrank ℚ_[p] (fieldF p F) (ddrF p ρW)).symm

/-- `IsDeRhamTensorOver` is the print's `dim_{F'} D_dR(W) = dim_{ℚ_p} W`. -/
theorem isDeRhamTensorOver_iff (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    IsDeRhamTensorOver p ρW ↔ finrank (fieldF p F) (ddrF p ρW) = finrank ℚ_[p] W := by
  rw [IsDeRhamTensorOver, finrank_ddrTensorOver]
  exact ⟨fun h => Nat.eq_of_mul_eq_mul_left Module.finrank_pos h, fun h => by rw [h]⟩

end Ddr

end

/-! ## §3. The leaf as printed, and the field -/

/-- **LEAF (as printed; Fontaine: the Tate module of an abelian variety is de Rham).** Berger, *An introduction to
the theory of p-adic representations*, in *Geometric aspects of Dwork theory* (de Gruyter, 2004), §II.5.1, p. 19
(arXiv math/0210184v1): the Tate modules of abelian varieties are de Rham, attributed to Fontaine. Berger's
definition: `V` is de Rham iff `dim_K D_dR(V) = dim_{ℚ_p} V`, `D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_K}`, a `K`-vector space
through `K ⊆ K̄ ⊆ B_dR^+`. Lean form: `A` an abelian variety over a finite extension `F` of `ℚ_p` (pkg-I4's
`AbVar`), `V = V_p(A) = ℚ_p ⊗ T_p A` with `G_F` acting through `gfToGqp` (image `G_{F'}`, `F' ⊆ ℚ̄_p` the image of
`F`, `range_gfToGqp_eq`: the print's `K` is `F'`); `D_dR = ddrF`, an `F'`-space through `iotaF : F' → ℚ̄_p → B_dR^+
→ B_dR`, the unique lift of `F' ⊆ ℂ_p` through `θ⁺` (`iotaPlusF_unique`), which lands in `B_dR^{G_F}`
(`bdrAct_iotaF`). Period ring: Berger's `B_dR = B_dR^+[1/t]` is the kernel's `B_dR` by `TDict.bdREquivAwayT`. -/
def DeRhamVpAbVarDirect : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
      finrank (fieldF p F) (ddrF p (A.galRep p)) = finrank ℚ_[p] (A.V p)

/-- **The research field `deRhamVpAbVarPrinted` from the printed leaf** (the dimension count). -/
theorem deRhamVpAbVarPrinted_of_direct (h : DeRhamVpAbVarDirect) : DeRhamVpAbVarPrinted :=
  fun p _ F _ _ _ A => (isDeRhamTensorOver_iff p (A.galRep p)).mpr (h p F A)

/-- The converse: the two Props are equivalent (the new leaf is no stronger than the old field). -/
theorem direct_of_deRhamVpAbVarPrinted (h : DeRhamVpAbVarPrinted) : DeRhamVpAbVarDirect :=
  fun p _ F _ _ _ A => (isDeRhamTensorOver_iff p (A.galRep p)).mp (h p F A)

end DeRhamPrint.Direct
