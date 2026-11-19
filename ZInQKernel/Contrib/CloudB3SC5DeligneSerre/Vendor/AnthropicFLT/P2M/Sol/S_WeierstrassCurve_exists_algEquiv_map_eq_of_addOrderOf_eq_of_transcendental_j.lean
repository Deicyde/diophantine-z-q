/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j (git blob 250e936be4e2d2c5f00c9127d6972b307dde04c3, sha256 bd33ef02d755071f9a3bf6d0f7891afd065c6c565dfd86ff0980265de095641e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j.P2MKcIgusaMonodromy
end P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j.P2MKcIgusaMonodromy

namespace P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace P2MKcIgusaMonodromy

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

universe u v

section Action

variable {k : Type v} {Ω : Type v} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω]
  (E : WeierstrassCurve k) [E.IsElliptic] (M : ℕ) [NeZero M]

variable (Ω) in

abbrev Tor : Submodule ℤ (E.baseChange Ω).toAffine.Point :=
  Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point (M : ℤ)

variable {E M}

theorem mem_Tor_iff (P : (E.baseChange Ω).toAffine.Point) : P ∈ Tor Ω E M ↔ M • P = 0 := by
  rw [Tor, Submodule.mem_torsionBy_iff, natCast_zsmul]

theorem map_id' (P : (E.baseChange Ω).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (AlgHom.id k Ω) P = P := by
  cases P <;> rfl

theorem map_symm_map (σ : Ω ≃ₐ[k] Ω) (P : (E.baseChange Ω).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (σ.symm : Ω →ₐ[k] Ω)
      (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P) = P := by
  rw [Point.map_map, AlgEquiv.symm_comp, map_id']

theorem map_map_symm (σ : Ω ≃ₐ[k] Ω) (P : (E.baseChange Ω).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)
      (WeierstrassCurve.Affine.Point.map (σ.symm : Ω →ₐ[k] Ω) P) = P := by
  rw [Point.map_map, AlgEquiv.comp_symm, map_id']

theorem map_mem_Tor (σ : Ω ≃ₐ[k] Ω) {P : (E.baseChange Ω).toAffine.Point} (hP : P ∈ Tor Ω E M) :
    WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P ∈ Tor Ω E M := by
  rw [mem_Tor_iff] at hP ⊢
  rw [← map_nsmul, hP, map_zero]

variable (E M) in

def actT (σ : Ω ≃ₐ[k] Ω) : Tor Ω E M ≃+ Tor Ω E M where
  toFun P := ⟨WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P.1, map_mem_Tor σ P.2⟩
  invFun P := ⟨WeierstrassCurve.Affine.Point.map (σ.symm : Ω →ₐ[k] Ω) P.1, by
    have := map_mem_Tor (M := M) σ.symm P.2
    exact this⟩
  left_inv P := by
    apply Subtype.ext
    exact map_symm_map σ P.1
  right_inv P := by
    apply Subtype.ext
    exact map_map_symm σ P.1
  map_add' P Q := by
    apply Subtype.ext
    exact map_add _ P.1 Q.1

@[scoped simp] theorem actT_apply_coe (σ : Ω ≃ₐ[k] Ω) (P : Tor Ω E M) :
    ((actT E M σ P : Tor Ω E M) : (E.baseChange Ω).toAffine.Point) =
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P.1 := rfl

theorem coe_mul_eq_comp (σ τ : Ω ≃ₐ[k] Ω) :
    ((σ * τ : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) = (σ : Ω →ₐ[k] Ω).comp (τ : Ω →ₐ[k] Ω) :=
  AlgHom.ext fun _ => rfl

theorem coe_one_eq_id : ((1 : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) = AlgHom.id k Ω :=
  AlgHom.ext fun _ => rfl

variable (E M) in

def rho (e : ZMod M × ZMod M ≃+ Tor Ω E M) : (Ω ≃ₐ[k] Ω) →* AddAut (ZMod M × ZMod M) where
  toFun σ := (e.trans (actT E M σ)).trans e.symm
  map_one' := by
    ext v
    · show (e.symm (actT E M 1 (e v))).1 = v.1
      have : actT E M 1 (e v) = e v := by
        apply Subtype.ext
        show WeierstrassCurve.Affine.Point.map ((1 : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) (e v).1 = (e v).1
        rw [coe_one_eq_id, map_id']
      rw [this, AddEquiv.symm_apply_apply]
    · show (e.symm (actT E M 1 (e v))).2 = v.2
      have : actT E M 1 (e v) = e v := by
        apply Subtype.ext
        show WeierstrassCurve.Affine.Point.map ((1 : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) (e v).1 = (e v).1
        rw [coe_one_eq_id, map_id']
      rw [this, AddEquiv.symm_apply_apply]
  map_mul' σ τ := by
    have key : ∀ v, actT E M (σ * τ) (e v) = actT E M σ (e (e.symm (actT E M τ (e v)))) := by
      intro v
      rw [AddEquiv.apply_symm_apply]
      apply Subtype.ext
      show WeierstrassCurve.Affine.Point.map ((σ * τ : Ω ≃ₐ[k] Ω) : Ω →ₐ[k] Ω) (e v).1 =
        WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)
          (WeierstrassCurve.Affine.Point.map (τ : Ω →ₐ[k] Ω) (e v).1)
      rw [Point.map_map, coe_mul_eq_comp]
    ext v
    · show (e.symm (actT E M (σ * τ) (e v))).1 = (e.symm (actT E M σ (e (e.symm (actT E M τ (e v)))))).1
      rw [key]
    · show (e.symm (actT E M (σ * τ) (e v))).2 = (e.symm (actT E M σ (e (e.symm (actT E M τ (e v)))))).2
      rw [key]

theorem rho_apply (e : ZMod M × ZMod M ≃+ Tor Ω E M) (σ : Ω ≃ₐ[k] Ω) (v : ZMod M × ZMod M) :
    rho E M e σ v = e.symm (actT E M σ (e v)) := rfl

theorem addOrderOf_coe_Tor (P : Tor Ω E M) :
    addOrderOf (P : (E.baseChange Ω).toAffine.Point) = addOrderOf P :=
  addOrderOf_injective (Tor Ω E M).subtype.toAddMonoidHom Subtype.val_injective P

end Action

section Irred

variable (K : Type u) [Field K] {k : Type v} [Field k] [Algebra K k]

theorem exists_algEquiv_ratFunc {x : k} (hx : Transcendental K x)
    (hgen : IntermediateField.adjoin K ({x} : Set k) = ⊤) :
    ∃ φ : RatFunc K ≃ₐ[K] k, φ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = x := by
  have hinj : Function.Injective (Polynomial.aeval (R := K) x) := transcendental_iff_injective.mp hx
  have hφ : nonZeroDivisors (Polynomial K) ≤
      Submonoid.comap (Polynomial.aeval (R := K) x) (nonZeroDivisors k) := by
    intro p hp
    rw [Submonoid.mem_comap]
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    have : p = 0 := hinj (by rw [h0, map_zero])
    exact nonZeroDivisors.ne_zero hp this
  set ψ : RatFunc K →ₐ[K] k := RatFunc.liftAlgHom (Polynomial.aeval x) hφ with hψ
  have hψX : ψ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = x := by
    have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval (R := K) x) hφ Polynomial.X 1
    rw [map_one, div_one, map_one, div_one, Polynomial.aeval_X] at h
    exact h
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy : y ∈ (⊤ : IntermediateField K k) := IntermediateField.mem_top
    rw [← hgen] at hy
    have hle : IntermediateField.adjoin K ({x} : Set k) ≤ ψ.fieldRange := by
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact AlgHom.mem_fieldRange.mpr ⟨_, hψX⟩
    exact AlgHom.mem_fieldRange.mp (hle hy)
  exact ⟨AlgEquiv.ofBijective ψ ⟨ψ.toRingHom.injective, hsurj⟩, hψX⟩

theorem irreducible_fibre {M : ℕ} [NeZero M] (data : ModularCurve.ModularPolynomialData M)
    (hM : (M : K) ≠ 0) {x : k} (hx : Transcendental K x)
    (hgen : IntermediateField.adjoin K ({x} : Set k) = ⊤) :
    Irreducible (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) x)) := by
  obtain ⟨φ, hφX⟩ := exists_algEquiv_ratFunc K hx hgen
  have hirr := data.irreducible_map_ratFunc_of_natCast_ne_zero K M hM
  rw [Polynomial.map_map] at hirr
  rw [← MulEquiv.irreducible_iff (Polynomial.mapEquiv (φ : RatFunc K ≃+* k))] at hirr
  convert hirr using 1
  rw [Polynomial.mapEquiv_apply, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext (fun n => ?_) ?_
  · simp only [eq_intCast, map_intCast]
  · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, Polynomial.coe_mapRingHom, Polynomial.map_X, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv]
    exact hφX.symm

end Irred

section Lines

variable (K : Type u) [Field K] (M : ℕ) [NeZero M] (hMK : (M : K) ≠ 0)
  (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra k Ω]
  [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
  (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)

include hMK hE hgen in

theorem exists_map_mem_zmultiples
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2)
    (P Q : (E.baseChange Ω).toAffine.Point) (hP : addOrderOf P = M) (hQ : addOrderOf Q = M) :
    ∃ (σ : Ω ≃ₐ[k] Ω) (n : ℤ),
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P = n • Q := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData M
  have hMk : (M : k) ≠ 0 := by
    intro h
    apply hMK
    have : algebraMap K k (M : K) = 0 := by rw [map_natCast, h]
    exact (algebraMap K k).injective (by rw [this, map_zero])
  obtain ⟨Θ, hΘ⟩ :=
    WeierstrassCurve.exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
      K M data k Ω hMk E hE hfull

  have hcyc : ∀ R : (E.baseChange Ω).toAffine.Point, addOrderOf R = M →
      IsAddCyclic (AddSubgroup.zmultiples R) ∧ Nat.card (AddSubgroup.zmultiples R) = M := by
    intro R hR
    exact ⟨inferInstance, by rw [Nat.card_zmultiples, hR]⟩
  set HP : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = M} :=
    ⟨AddSubgroup.zmultiples P, hcyc P hP⟩ with hHP
  set HQ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = M} :=
    ⟨AddSubgroup.zmultiples Q, hcyc Q hQ⟩ with hHQ

  set Φk : Polynomial k := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) E.j) with hΦk
  have hΦΩ : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) (algebraMap k Ω E.j)) =
      Φk.map (algebraMap k Ω) := by
    rw [hΦk, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simp
  have hmon : Φk.Monic := data.monic.map _
  have hirr : Irreducible Φk := irreducible_fibre K data hMK hE hgen
  have hmin : ∀ y : Ω, (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω)
      (algebraMap k Ω E.j))).IsRoot y → minpoly k y = Φk := by
    intro y hy
    rw [hΦΩ, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hy
    exact (minpoly.eq_of_irreducible_of_monic hirr hy hmon).symm
  haveI : Normal k Ω := IsAlgClosure.normal k Ω
  have hconj : minpoly k ((Θ HQ).1 : Ω) = minpoly k ((Θ HP).1 : Ω) :=
    (hmin _ (Θ HQ).2).trans (hmin _ (Θ HP).2).symm
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := k) (E := Ω)).mp hconj
  have hσ' : σ ((Θ HP).1 : Ω) = (Θ HQ).1 := hσ

  have hmapcyc : IsAddCyclic ((AddSubgroup.zmultiples P).map
      (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω))) ∧
      Nat.card ((AddSubgroup.zmultiples P).map
        (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω))) = M := by
    rw [AddMonoidHom.map_zmultiples]
    refine hcyc _ ?_
    rw [addOrderOf_injective _ (Point.map_injective (f := (σ : Ω →ₐ[k] Ω))), hP]
  set HP' : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = M} :=
    ⟨(AddSubgroup.zmultiples P).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)), hmapcyc⟩
    with hHP'
  have hnat := hΘ σ HP HP' rfl
  have hEq : Θ HP' = Θ HQ := by
    apply Subtype.ext
    rw [hnat, hσ']
  have hHH : HP' = HQ := Θ.injective hEq
  have hsub : (AddSubgroup.zmultiples P).map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) =
      AddSubgroup.zmultiples Q := congrArg Subtype.val hHH
  have hmem : WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P ∈ AddSubgroup.zmultiples Q := by
    rw [← hsub, AddMonoidHom.map_zmultiples]
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  exact ⟨σ, n, hn.symm⟩

end Lines

section Basis

variable {k : Type v} {Ω : Type v} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω]
  {E : WeierstrassCurve k} [E.IsElliptic] {M : ℕ} [NeZero M]

def basisHom (P₁ P₂ : Tor Ω E M) : ZMod M × ZMod M →+ Tor Ω E M :=
  (ZMod.lift M ⟨zmultiplesHom (Tor Ω E M) P₁, by
      show ((M : ℕ) : ℤ) • P₁ = 0
      apply Subtype.ext
      show (((M : ℕ) : ℤ) • P₁ : Tor Ω E M).1 = 0
      rw [Submodule.coe_smul_of_tower, natCast_zsmul]
      exact (mem_Tor_iff P₁.1).mp P₁.2⟩).coprod
    (ZMod.lift M ⟨zmultiplesHom (Tor Ω E M) P₂, by
      show ((M : ℕ) : ℤ) • P₂ = 0
      apply Subtype.ext
      show (((M : ℕ) : ℤ) • P₂ : Tor Ω E M).1 = 0
      rw [Submodule.coe_smul_of_tower, natCast_zsmul]
      exact (mem_Tor_iff P₂.1).mp P₂.2⟩)

theorem basisHom_apply_intCast (P₁ P₂ : Tor Ω E M) (a b : ℤ) :
    basisHom P₁ P₂ ((a : ZMod M), (b : ZMod M)) = a • P₁ + b • P₂ := by
  rw [basisHom, AddMonoidHom.coprod_apply, ZMod.lift_coe, ZMod.lift_coe]
  rfl

theorem basisHom_apply (P₁ P₂ : Tor Ω E M) (v : ZMod M × ZMod M) :
    basisHom P₁ P₂ v = (v.1.val : ℤ) • P₁ + (v.2.val : ℤ) • P₂ := by
  have h1 : v = (((v.1.val : ℤ) : ZMod M), ((v.2.val : ℤ) : ZMod M)) := by
    ext <;> simp
  conv_lhs => rw [h1]
  exact basisHom_apply_intCast P₁ P₂ _ _

theorem basisHom_injective (P₁ P₂ : Tor Ω E M)
    (hind : ∀ a b : ℤ, a • (P₁ : (E.baseChange Ω).toAffine.Point) + b • (P₂ : _) = 0 →
      (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) :
    Function.Injective (basisHom P₁ P₂) := by
  intro v w hvw
  have h0 : basisHom P₁ P₂ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  rw [basisHom_apply] at h0
  have h0' : ((v - w).1.val : ℤ) • (P₁ : (E.baseChange Ω).toAffine.Point) +
      ((v - w).2.val : ℤ) • (P₂ : _) = 0 := by
    have := congrArg Subtype.val h0
    simpa using this
  obtain ⟨ha, hb⟩ := hind _ _ h0'
  have h1 : (v - w).1 = 0 := by
    rw [← ZMod.natCast_zmod_val (v - w).1, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ha
  have h2 : (v - w).2 = 0 := by
    rw [← ZMod.natCast_zmod_val (v - w).2, ← Int.cast_natCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hb
  have : v - w = 0 := Prod.ext h1 h2
  exact sub_eq_zero.mp this

end Basis

theorem main
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)
    (P P' : (E.baseChange Ω).toAffine.Point) (hP : addOrderOf P = M) (hP' : addOrderOf P' = M) :
    ∃ σ : Ω ≃ₐ[k] Ω, P' = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P := by

  have hMΩ : (M : Ω) ≠ 0 := by
    intro h
    apply hM
    have : algebraMap K Ω (M : K) = 0 := by rw [map_natCast, h]
    exact (algebraMap K Ω).injective (by rw [this, map_zero])
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k

  obtain ⟨e₀⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (K := Ω) E (n := M) hMΩ
  have hcardT : Nat.card (Tor Ω E M) = M ^ 2 := by
    rw [← Nat.card_congr e₀.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  have hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // M • P = 0} = M ^ 2 := by
    rw [← hcardT]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun Q => (mem_Tor_iff Q).symm)

  obtain ⟨P₁, P₂, σ₀, ε, hP₁, hP₂, hind, hε, hσ₁, hσ₂⟩ :=
    WeierstrassCurve.exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j
      K M hM k Ω E hE hgen
  set T₁ : Tor Ω E M := ⟨P₁, (mem_Tor_iff P₁).mpr hP₁⟩ with hT₁
  set T₂ : Tor Ω E M := ⟨P₂, (mem_Tor_iff P₂).mpr hP₂⟩ with hT₂
  have hinj : Function.Injective (basisHom T₁ T₂) := basisHom_injective T₁ T₂ hind
  haveI : Finite (Tor Ω E M) := Nat.finite_of_card_ne_zero (by
    rw [hcardT]; exact pow_ne_zero 2 (NeZero.ne M))
  have hbij : Function.Bijective (basisHom T₁ T₂) := by
    apply hinj.bijective_of_nat_card_le
    rw [hcardT, Nat.card_prod, Nat.card_zmod, sq]
  set e : ZMod M × ZMod M ≃+ Tor Ω E M := AddEquiv.ofBijective (basisHom T₁ T₂) hbij with he_def
  have he_apply : ∀ v, e v = basisHom T₁ T₂ v := fun v => rfl
  have he10 : e (1, 0) = T₁ := by
    rw [he_apply, show ((1, 0) : ZMod M × ZMod M) = (((1 : ℤ) : ZMod M), ((0 : ℤ) : ZMod M)) by simp,
      basisHom_apply_intCast, one_zsmul, zero_zsmul, add_zero]
  have he01 : e (0, 1) = T₂ := by
    rw [he_apply, show ((0, 1) : ZMod M × ZMod M) = (((0 : ℤ) : ZMod M), ((1 : ℤ) : ZMod M)) by simp,
      basisHom_apply_intCast, one_zsmul, zero_zsmul, zero_add]
  have he11 : e (1, 1) = T₁ + T₂ := by
    rw [he_apply, show ((1, 1) : ZMod M × ZMod M) = (((1 : ℤ) : ZMod M), ((1 : ℤ) : ZMod M)) by simp,
      basisHom_apply_intCast, one_zsmul, one_zsmul]

  set H : Subgroup (AddAut (ZMod M × ZMod M)) := (rho E M e).range with hH

  have htrans : ∀ v w : ZMod M × ZMod M, addOrderOf v = M → addOrderOf w = M →
      ∃ h ∈ H, ∃ n : ℤ, h v = n • w := by
    intro v w hv hw
    have hv' : addOrderOf ((e v : Tor Ω E M) : (E.baseChange Ω).toAffine.Point) = M := by
      rw [addOrderOf_coe_Tor, AddEquiv.addOrderOf_eq, hv]
    have hw' : addOrderOf ((e w : Tor Ω E M) : (E.baseChange Ω).toAffine.Point) = M := by
      rw [addOrderOf_coe_Tor, AddEquiv.addOrderOf_eq, hw]
    obtain ⟨σ, n, hn⟩ := exists_map_mem_zmultiples K M hM k Ω E hE hgen hfull _ _ hv' hw'
    refine ⟨rho E M e σ, ⟨σ, rfl⟩, n, ?_⟩
    rw [rho_apply]
    have : actT E M σ (e v) = n • e w := by
      apply Subtype.ext
      rw [actT_apply_coe, hn, Submodule.coe_smul_of_tower]
    rw [this, map_zsmul, AddEquiv.symm_apply_apply]

  have ht : ∃ t ∈ H, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      t (1, 0) = ε • ((1, 0) : ZMod M × ZMod M) ∧ t (0, 1) = ε • ((1, 1) : ZMod M × ZMod M) := by
    refine ⟨rho E M e σ₀, ⟨σ₀, rfl⟩, ε, hε, ?_, ?_⟩
    · rw [rho_apply, he10]
      have : actT E M σ₀ T₁ = ε • T₁ := by
        apply Subtype.ext
        rw [actT_apply_coe, Submodule.coe_smul_of_tower]
        exact hσ₁
      rw [this, map_zsmul, ← he10, AddEquiv.symm_apply_apply]
    · rw [rho_apply, he01]
      have : actT E M σ₀ T₂ = ε • (T₁ + T₂) := by
        apply Subtype.ext
        rw [actT_apply_coe, Submodule.coe_smul_of_tower]
        exact hσ₂
      rw [this, map_zsmul, ← he11, AddEquiv.symm_apply_apply]

  set TP : Tor Ω E M := ⟨P, (mem_Tor_iff P).mpr (by rw [← hP]; exact addOrderOf_nsmul_eq_zero P)⟩
    with hTP
  set TP' : Tor Ω E M := ⟨P', (mem_Tor_iff P').mpr (by rw [← hP']; exact addOrderOf_nsmul_eq_zero P')⟩
    with hTP'
  have hv : addOrderOf (e.symm TP) = M := by
    rw [AddEquiv.addOrderOf_eq, ← addOrderOf_coe_Tor]
    exact hP
  have hw : addOrderOf (e.symm TP') = M := by
    rw [AddEquiv.addOrderOf_eq, ← addOrderOf_coe_Tor]
    exact hP'
  obtain ⟨h, ⟨τ, rfl⟩, hτ⟩ :=
    AddAut.exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem M H htrans ht _ _ hv hw
  rw [rho_apply, AddEquiv.apply_symm_apply] at hτ
  have hτ' : actT E M τ TP = TP' := by
    have := congrArg e hτ
    rwa [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at this
  refine ⟨τ, ?_⟩
  have := congrArg Subtype.val hτ'
  exact this.symm

end P2MKcIgusaMonodromy
open scoped _root_.P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j.P2MKcIgusaMonodromy

end
open scoped _root_.P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j.P2MKcIgusaMonodromy

open WeierstrassCurve WeierstrassCurve.Affine

universe u v in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)
    (P P' : (E.baseChange Ω).toAffine.Point) (hP : addOrderOf P = M) (hP' : addOrderOf P' = M) :
    ∃ σ : Ω ≃ₐ[k] Ω, P' = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P :=
  P2MKcIgusaMonodromy.main K M hM k Ω E hE hgen P P' hP hP'
