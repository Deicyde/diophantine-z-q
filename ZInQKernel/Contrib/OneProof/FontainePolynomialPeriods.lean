import ZInQKernel.Contrib.OneProof.FontaineAbstract
import ZInQKernel.Contrib.OneProof.PanBergerPst

/-! # Fontaine's periods in the formal polynomial presentation

For Fontaine's action on the formal polynomial ring `B_cris[X]`, the fixed
scalars and the fixed tensors correspond under the comparison to those of the
image in `B_dR`. So the dimension form of potential semistability is the same
in both presentations.
-/

noncomputable section

namespace HDec.PkgI4.FontaineComparison

open BergerBst FontaineSt BmaxOne PanBergerSplit
open _root_.ZInQ.Contrib.G9.BdrKer.Cp (xi)
open Module
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

/-- `B_st^H` in the formal presentation, for Fontaine's action. -/
def polyFixed (H : Subgroup (GQp p)) : Subalgebra ℚ_[p] (SemistablePoly p) where
  carrier := {f | ∀ σ ∈ H, polyAct p σ f = f}
  mul_mem' {a b} ha hb σ hσ := by
    change polyAct p σ (a * b) = a * b
    rw [map_mul, ha σ hσ, hb σ hσ]
  add_mem' {a b} ha hb σ hσ := by
    change polyAct p σ (a + b) = a + b
    rw [map_add, ha σ hσ, hb σ hσ]
  algebraMap_mem' c σ _ := (polyAct p σ).commutes c

theorem mem_polyFixed {H : Subgroup (GQp p)} {f : SemistablePoly p} :
    f ∈ polyFixed p H ↔ ∀ σ ∈ H, polyAct p σ f = f := Iff.rfl

theorem mem_polyFixed_iff_eval {H : Subgroup (GQp p)} {f : SemistablePoly p} :
    f ∈ polyFixed p H ↔ ∀ σ ∈ H, bdrAct p σ (polyEval p f) = polyEval p f := by
  rw [mem_polyFixed]
  refine forall₂_congr fun σ _ => ?_
  rw [← polyEval_polyAct]
  exact (polyEval_injective p).eq_iff.symm

theorem mem_fixedSub_iff {H : Subgroup (GQp p)} {b : SemistableImage p} :
    b ∈ fixedSub p (SemistableImage p) H ↔ ∀ σ ∈ H, bdrAct p σ (b : BdR p) = b := Iff.rfl

/-- The comparison carries the formal fixed scalars onto the fixed scalars of
the image. -/
def fixedEquiv (H : Subgroup (GQp p)) : polyFixed p H ≃+* fixedSub p (SemistableImage p) H where
  toFun f := ⟨imageEquiv p f, (mem_fixedSub_iff p).2 fun σ hσ => by
    rw [← polyEval_apply]
    exact (mem_polyFixed_iff_eval p).1 f.2 σ hσ⟩
  invFun c := ⟨(imageEquiv p).symm c, (mem_polyFixed_iff_eval p).2 fun σ hσ => by
    rw [polyEval_apply, AlgEquiv.apply_symm_apply]
    exact (mem_fixedSub_iff p).1 c.2 σ hσ⟩
  left_inv f := Subtype.ext ((imageEquiv p).symm_apply_apply f)
  right_inv c := Subtype.ext ((imageEquiv p).apply_symm_apply (c : SemistableImage p))
  map_mul' f g := Subtype.ext (map_mul (imageEquiv p) (f : SemistablePoly p) g)
  map_add' f g := Subtype.ext (map_add (imageEquiv p) (f : SemistablePoly p) g)

theorem coe_fixedEquiv (H : Subgroup (GQp p)) (f : polyFixed p H) :
    ((fixedEquiv p H f : fixedSub p (SemistableImage p) H) : SemistableImage p) =
      imageEquiv p f := rfl

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

theorem polyTensor_smul (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (a : SemistablePoly p)
    (x : SemistablePoly p ⊗[ℚ_[p]] (Fin n → E)) :
    TensorProduct.map (polyAct p σ).toLinearMap (vAct p ρ σ) (a • x) =
      polyAct p σ a • TensorProduct.map (polyAct p σ).toLinearMap (vAct p ρ σ) x := by
  induction x using TensorProduct.inductionOn with
  | tmul b z =>
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, AlgHom.toLinearMap_apply,
        AlgHom.toLinearMap_apply, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

set_option synthInstance.maxHeartbeats 400000 in
/-- `(B_st ⊗ V)^H` in the formal presentation, for Fontaine's action. -/
def polyPeriods (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule (polyFixed p H) (SemistablePoly p ⊗[ℚ_[p]] (Fin n → E)) where
  carrier := {x | ∀ σ ∈ H, TensorProduct.map (polyAct p σ).toLinearMap (vAct p ρ σ) x = x}
  zero_mem' σ _ := map_zero _
  add_mem' {x y} hx hy σ hσ := by
    change TensorProduct.map (polyAct p σ).toLinearMap (vAct p ρ σ) (x + y) = x + y
    rw [map_add, hx σ hσ, hy σ hσ]
  smul_mem' c x hx σ hσ := by
    change TensorProduct.map (polyAct p σ).toLinearMap (vAct p ρ σ) (c • x) = c • x
    rw [Subalgebra.smul_def, polyTensor_smul, (mem_polyFixed p).1 c.2 σ hσ, hx σ hσ]

/-- The comparison of tensors. -/
def periodTensor : (SemistablePoly p ⊗[ℚ_[p]] (Fin n → E)) ≃ₗ[ℚ_[p]]
    (SemistableImage p ⊗[ℚ_[p]] (Fin n → E)) :=
  TensorProduct.congr (imageEquiv p).toLinearEquiv (LinearEquiv.refl _ _)

theorem periodTensor_tmul (a : SemistablePoly p) (z : Fin n → E) :
    periodTensor p (a ⊗ₜ[ℚ_[p]] z) = imageEquiv p a ⊗ₜ[ℚ_[p]] z := rfl

theorem inclT_periodTensor_map (ρ : GQp p →* GL (Fin n) E) (σ : GQp p)
    (x : SemistablePoly p ⊗[ℚ_[p]] (Fin n → E)) :
    inclT p (SemistableImage p) (periodTensor p
        (TensorProduct.map (polyAct p σ).toLinearMap (vAct p ρ σ) x)) =
      TensorProduct.map (bdrLin p σ) (vAct p ρ σ)
        (inclT p (SemistableImage p) (periodTensor p x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
      simp only [TensorProduct.map_tmul, periodTensor_tmul, inclT]
      congr 1
      exact polyEval_polyAct p σ a
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_dB_iff_polyPeriods (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E)
    (x : SemistablePoly p ⊗[ℚ_[p]] (Fin n → E)) :
    periodTensor p x ∈ dB p (SemistableImage p) H ρ ↔ x ∈ polyPeriods p H ρ := by
  have hj : Function.Injective (fun y : SemistablePoly p ⊗[ℚ_[p]] (Fin n → E) =>
      inclT p (SemistableImage p) (periodTensor p y)) :=
    (inclT_injective p _).comp (periodTensor p).injective
  change (∀ σ ∈ H, TensorProduct.map (bdrLin p σ) (vAct p ρ σ)
      (inclT p (SemistableImage p) (periodTensor p x)) =
        inclT p (SemistableImage p) (periodTensor p x)) ↔
    ∀ σ ∈ H, TensorProduct.map (polyAct p σ).toLinearMap (vAct p ρ σ) x = x
  refine forall₂_congr fun σ _ => ?_
  rw [← inclT_periodTensor_map]
  exact hj.eq_iff

theorem periodTensor_smul (H : Subgroup (GQp p)) (r : polyFixed p H)
    (x : SemistablePoly p ⊗[ℚ_[p]] (Fin n → E)) :
    periodTensor p (r • x) = fixedEquiv p H r • periodTensor p x := by
  rw [Subalgebra.smul_def, Subalgebra.smul_def, coe_fixedEquiv]
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
      rw [TensorProduct.smul_tmul', periodTensor_tmul, periodTensor_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

set_option synthInstance.maxHeartbeats 400000 in
/-- The fixed tensors of the two presentations, identified additively by the
comparison of tensors. -/
def periodsAddEquiv (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    polyPeriods p H ρ ≃+ dB p (SemistableImage p) H ρ where
  toFun x := ⟨periodTensor p x, (mem_dB_iff_polyPeriods p H ρ x).2 x.2⟩
  invFun y := ⟨(periodTensor p).symm y, (mem_dB_iff_polyPeriods p H ρ _).1 (by
    rw [LinearEquiv.apply_symm_apply]
    exact y.2)⟩
  left_inv x := Subtype.ext
    ((periodTensor p).symm_apply_apply (x : SemistablePoly p ⊗[ℚ_[p]] (Fin n → E)))
  right_inv y := Subtype.ext
    ((periodTensor p).apply_symm_apply (y : SemistableImage p ⊗[ℚ_[p]] (Fin n → E)))
  map_add' x y := Subtype.ext
    ((periodTensor p).map_add (x : SemistablePoly p ⊗[ℚ_[p]] (Fin n → E)) y)

theorem coe_periodsAddEquiv (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E)
    (x : polyPeriods p H ρ) :
    ((periodsAddEquiv p H ρ x : dB p (SemistableImage p) H ρ) :
      SemistableImage p ⊗[ℚ_[p]] (Fin n → E)) = periodTensor p x := rfl

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The fixed tensors of the two presentations have the same dimension over
their (identified) fixed scalars. -/
theorem finrank_polyPeriods (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    finrank (polyFixed p H) (polyPeriods p H ρ) =
      finrank (fixedSub p (SemistableImage p) H) (dB p (SemistableImage p) H ρ) := by
  unfold Module.finrank
  refine congrArg Cardinal.toNat (rank_eq_of_equiv_equiv (fixedEquiv p H) (periodsAddEquiv p H ρ)
    (fixedEquiv p H).bijective fun r m => Subtype.ext ?_)
  simp only [coe_periodsAddEquiv, Submodule.coe_smul]
  exact periodTensor_smul p H r (m : SemistablePoly p ⊗[ℚ_[p]] (Fin n → E))

/-- The dimension form of potential semistability over Fontaine's formal
`B_st = B_cris[X]`, with Fontaine's action. -/
def IsPstPoly (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    finrank (polyFixed p K.fixingSubgroup) (polyPeriods p K.fixingSubgroup ρ) =
      finrank ℚ_[p] (Fin n → E)

/-- Potential semistability over Fontaine's formal `B_st` is exactly the live
predicate over its image in `B_dR`. -/
theorem isPstPoly_iff (ρ : GQp p →* GL (Fin n) E) :
    IsPstPoly p ρ ↔ IsPstF p (eps0_spec p) (xi p) (theta_xi' p) ρ := by
  unfold IsPstPoly IsPstF IsAdmissible
  refine exists_congr fun K => and_congr_right fun _ => ?_
  rw [finrank_polyPeriods]

end HDec.PkgI4.FontaineComparison
