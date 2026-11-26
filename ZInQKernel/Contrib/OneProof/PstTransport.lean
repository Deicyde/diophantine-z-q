import ZInQKernel.Contrib.OneProof.PanBergerFontaine

/-! # Transporting Fontaine's admissibility along an equivariant isomorphism

Let `S` be a `ℚ_p`-algebra with an action of `G_{ℚ_p}` by `ℚ_p`-algebra maps, and let
`e : S ≃ B` be an isomorphism with a subalgebra `B ⊆ B_dR` that intertwines the action with
the action on `B_dR`. Then `e` identifies `S^H` with `B^H` and `(S ⊗_{ℚ_p} V)^H` with
`(B ⊗_{ℚ_p} V)^H`, so the dimension form of admissibility (Brinon–Conrad, CMI notes, §5.2,
pp. 67–68) is the same for `S` and for `B` (`finrank_actPeriods_eq`).
-/

noncomputable section

namespace HDec.PkgI4.AbstractPeriods

open BergerBst BmaxOne Module
open PanBergerSplit (vAct bdrLin)
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]
variable {S : Type*} [CommRing S] [Algebra ℚ_[p] S] (act : GQp p → S →ₐ[ℚ_[p]] S)
variable {E : Type*} [Field E] [Algebra ℚ_[p] E] {n : ℕ}

/-- `S^H`. -/
def actFixed (H : Subgroup (GQp p)) : Subalgebra ℚ_[p] S where
  carrier := {s | ∀ σ ∈ H, act σ s = s}
  mul_mem' {a b} ha hb σ hσ := by
    change act σ (a * b) = a * b
    rw [map_mul, ha σ hσ, hb σ hσ]
  add_mem' {a b} ha hb σ hσ := by
    change act σ (a + b) = a + b
    rw [map_add, ha σ hσ, hb σ hσ]
  algebraMap_mem' c σ _ := (act σ).commutes c

theorem mem_actFixed {H : Subgroup (GQp p)} {s : S} :
    s ∈ actFixed p act H ↔ ∀ σ ∈ H, act σ s = s := Iff.rfl

/-- The action of `σ` on `S ⊗_{ℚ_p} V` is semilinear over its action on `S`. -/
private theorem map_act_smul (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (a : S)
    (x : S ⊗[ℚ_[p]] (Fin n → E)) :
    TensorProduct.map (act σ).toLinearMap (vAct p ρ σ) (a • x) =
      act σ a • TensorProduct.map (act σ).toLinearMap (vAct p ρ σ) x := by
  induction x using TensorProduct.inductionOn with
  | tmul b z =>
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, AlgHom.toLinearMap_apply,
        AlgHom.toLinearMap_apply, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

set_option synthInstance.maxHeartbeats 400000 in
/-- `(S ⊗_{ℚ_p} V)^H`, a module over `S^H`. -/
def actPeriods (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    Submodule (actFixed p act H) (S ⊗[ℚ_[p]] (Fin n → E)) where
  carrier := {x | ∀ σ ∈ H, TensorProduct.map (act σ).toLinearMap (vAct p ρ σ) x = x}
  zero_mem' σ _ := map_zero _
  add_mem' {x y} hx hy σ hσ := by
    change TensorProduct.map (act σ).toLinearMap (vAct p ρ σ) (x + y) = x + y
    rw [map_add, hx σ hσ, hy σ hσ]
  smul_mem' c x hx σ hσ := by
    change TensorProduct.map (act σ).toLinearMap (vAct p ρ σ) (c • x) = c • x
    rw [Subalgebra.smul_def, map_act_smul p act ρ σ, (mem_actFixed p act).1 c.2 σ hσ,
      hx σ hσ]

theorem mem_actPeriods {H : Subgroup (GQp p)} {ρ : GQp p →* GL (Fin n) E}
    {x : S ⊗[ℚ_[p]] (Fin n → E)} :
    x ∈ actPeriods p act H ρ ↔
      ∀ σ ∈ H, TensorProduct.map (act σ).toLinearMap (vAct p ρ σ) x = x := by
  exact Iff.rfl

section Transport

variable (B : Subalgebra ℚ_[p] (BdR p)) (e : S ≃ₐ[ℚ_[p]] B)

private theorem mem_fixedSub_iff_forall {H : Subgroup (GQp p)} {b : B} :
    b ∈ fixedSub p B H ↔ ∀ σ ∈ H, bdrAct p σ (b : BdR p) = b := Iff.rfl

/-- `e` carries the fixed scalars `S^H` onto `B^H`. -/
private def actFixedEquiv (he : ∀ σ s, (e (act σ s) : BdR p) = bdrAct p σ (e s))
    (H : Subgroup (GQp p)) : actFixed p act H ≃+* fixedSub p B H where
  toFun f := ⟨e (f : S), (mem_fixedSub_iff_forall p B).2 fun σ hσ => by
    rw [← he, (mem_actFixed p act).1 f.2 σ hσ]⟩
  invFun c := ⟨e.symm (c : B), (mem_actFixed p act).2 fun σ hσ => e.injective (Subtype.ext (by
    rw [he, AlgEquiv.apply_symm_apply]
    exact (mem_fixedSub_iff_forall p B).1 c.2 σ hσ))⟩
  left_inv f := Subtype.ext (e.symm_apply_apply (f : S))
  right_inv c := Subtype.ext (e.apply_symm_apply (c : B))
  map_mul' f g := Subtype.ext (map_mul e (f : S) g)
  map_add' f g := Subtype.ext (map_add e (f : S) g)

private theorem coe_actFixedEquiv (he : ∀ σ s, (e (act σ s) : BdR p) = bdrAct p σ (e s))
    (H : Subgroup (GQp p)) (f : actFixed p act H) :
    ((actFixedEquiv p act B e he H f : fixedSub p B H) : B) = e f := rfl

/-- The isomorphism of tensors induced by `e`. -/
private def actTensorEquiv :
    (S ⊗[ℚ_[p]] (Fin n → E)) ≃ₗ[ℚ_[p]] (B ⊗[ℚ_[p]] (Fin n → E)) :=
  TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl _ _)

private theorem actTensorEquiv_tmul (a : S) (z : Fin n → E) :
    actTensorEquiv p B e (a ⊗ₜ[ℚ_[p]] z) = e a ⊗ₜ[ℚ_[p]] z := rfl

private theorem inclT_actTensorEquiv_map
    (he : ∀ σ s, (e (act σ s) : BdR p) = bdrAct p σ (e s))
    (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (x : S ⊗[ℚ_[p]] (Fin n → E)) :
    inclT p B (actTensorEquiv p B e
        (TensorProduct.map (act σ).toLinearMap (vAct p ρ σ) x)) =
      TensorProduct.map (bdrLin p σ) (vAct p ρ σ) (inclT p B (actTensorEquiv p B e x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
      simp only [TensorProduct.map_tmul, actTensorEquiv_tmul, inclT]
      congr 1
      exact he σ a
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem mem_dB_iff_mem_actPeriods
    (he : ∀ σ s, (e (act σ s) : BdR p) = bdrAct p σ (e s))
    (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) (x : S ⊗[ℚ_[p]] (Fin n → E)) :
    actTensorEquiv p B e x ∈ dB p B H ρ ↔ x ∈ actPeriods p act H ρ := by
  have hj : Function.Injective (fun y : S ⊗[ℚ_[p]] (Fin n → E) =>
      inclT p B (actTensorEquiv p B e y)) :=
    (inclT_injective p B).comp (actTensorEquiv p B e).injective
  change (∀ σ ∈ H, TensorProduct.map (bdrLin p σ) (vAct p ρ σ)
      (inclT p B (actTensorEquiv p B e x)) = inclT p B (actTensorEquiv p B e x)) ↔
    ∀ σ ∈ H, TensorProduct.map (act σ).toLinearMap (vAct p ρ σ) x = x
  refine forall₂_congr fun σ _ => ?_
  rw [← inclT_actTensorEquiv_map p act B e he]
  exact hj.eq_iff

private theorem actTensorEquiv_smul (he : ∀ σ s, (e (act σ s) : BdR p) = bdrAct p σ (e s))
    (H : Subgroup (GQp p)) (r : actFixed p act H) (x : S ⊗[ℚ_[p]] (Fin n → E)) :
    actTensorEquiv p B e (r • x) = actFixedEquiv p act B e he H r • actTensorEquiv p B e x := by
  rw [Subalgebra.smul_def, Subalgebra.smul_def, coe_actFixedEquiv]
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
      rw [TensorProduct.smul_tmul', actTensorEquiv_tmul, actTensorEquiv_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

set_option synthInstance.maxHeartbeats 400000 in
/-- The fixed tensors of `S` and of `B`, identified additively by `e`. -/
private def actPeriodsAddEquiv (he : ∀ σ s, (e (act σ s) : BdR p) = bdrAct p σ (e s))
    (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    actPeriods p act H ρ ≃+ dB p B H ρ where
  toFun x := ⟨actTensorEquiv p B e (x : S ⊗[ℚ_[p]] (Fin n → E)),
    (mem_dB_iff_mem_actPeriods p act B e he H ρ (x : S ⊗[ℚ_[p]] (Fin n → E))).2 x.2⟩
  invFun y := ⟨(actTensorEquiv p B e).symm (y : B ⊗[ℚ_[p]] (Fin n → E)),
    (mem_dB_iff_mem_actPeriods p act B e he H ρ _).1 (by
      rw [LinearEquiv.apply_symm_apply]
      exact y.2)⟩
  left_inv x := Subtype.ext
    ((actTensorEquiv p B e).symm_apply_apply (x : S ⊗[ℚ_[p]] (Fin n → E)))
  right_inv y := Subtype.ext
    ((actTensorEquiv p B e).apply_symm_apply (y : B ⊗[ℚ_[p]] (Fin n → E)))
  map_add' x y := Subtype.ext
    ((actTensorEquiv p B e).map_add (x : S ⊗[ℚ_[p]] (Fin n → E)) y)

private theorem coe_actPeriodsAddEquiv (he : ∀ σ s, (e (act σ s) : BdR p) = bdrAct p σ (e s))
    (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) (x : actPeriods p act H ρ) :
    ((actPeriodsAddEquiv p act B e he H ρ x : dB p B H ρ) : B ⊗[ℚ_[p]] (Fin n → E)) =
      actTensorEquiv p B e (x : S ⊗[ℚ_[p]] (Fin n → E)) := rfl

end Transport

set_option synthInstance.maxHeartbeats 400000 in
/-- **Transport.** An equivariant isomorphism `e : S ≃ B` with a subalgebra `B ⊆ B_dR` identifies
the fixed scalars and the fixed tensors, so the two dimensions agree. -/
theorem finrank_actPeriods_eq (B : Subalgebra ℚ_[p] (BdR p)) (e : S ≃ₐ[ℚ_[p]] B)
    (he : ∀ σ s, (e (act σ s) : BdR p) = bdrAct p σ (e s))
    (H : Subgroup (GQp p)) (ρ : GQp p →* GL (Fin n) E) :
    finrank (actFixed p act H) (actPeriods p act H ρ) =
      finrank (fixedSub p B H) (dB p B H ρ) := by
  have h := lift_rank_eq_of_equiv_equiv (actFixedEquiv p act B e he H)
    (actPeriodsAddEquiv p act B e he H ρ) (actFixedEquiv p act B e he H).bijective
    fun r m => Subtype.ext (by
      simp only [coe_actPeriodsAddEquiv, Submodule.coe_smul]
      exact actTensorEquiv_smul p act B e he H r (m : S ⊗[ℚ_[p]] (Fin n → E)))
  unfold Module.finrank
  simpa only [Cardinal.toNat_lift] using congrArg Cardinal.toNat h

end HDec.PkgI4.AbstractPeriods
