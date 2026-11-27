import ZInQKernel.Contrib.OneProof.ColmezTiltIso.Action
import ZInQKernel.Contrib.OneProof.ColmezTiltIso.TpShape

/-!
# Colmez's `B_dR^+` and `B_dR` as `ℤ_p`-algebras

Colmez's rings carry their `ℤ_p = W(F_p)`-structure through `W(F_p) → W(R)`. Here:

* `colmezZpToW : ℤ_p → W(R)`, `(WittVector.map (ZMod.castHom _ _)).comp (WittVector.equiv p).symm`,
  the same recipe as the tree's `zpToW` on `W(O♭)`; `wittEquiv_colmezZpToW`: `wittEquiv` carries one
  to the other.
* `algZpPlus`: the resulting `ℤ_p`-algebra structure on `ColmezBdRPlus 𝓞_ℂ_[p] p` (a scoped instance
  of `ColmezTiltIso.Printed`); its fraction field inherits one.
* `colmezBdRPlusEquiv_algebraMap_zp`: `colmezBdRPlusEquiv` sends `z ∈ ℤ_p` to the tree's
  `ofLoc p (zpToW p z)`; `colmezBdRPlusAlgEquiv`: the same as an isomorphism of `ℤ_p`-algebras, with
  the tree's structure `algZpTree` on `BDeRhamPlus`.
* **`colmezBdRAlgEquiv : FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) ≃ₐ[ℤ_p] BdR p`**:
  `colmezBdREquiv` as an isomorphism of `ℤ_p`-algebras, for the structure `Tp.algZp` (through
  `qpToBdR`) that the `T_p` row uses.
* `colmezThetaPlus_algebraMap_zp`: `θ` on Colmez's `B_dR^+` restricts to `ℤ_p ⊂ ℚ_p ⊂ ℂ_p`.
* `ker_awayEquivCp_comp_colmezThetaInvertP`: reading `θ[1/p]` in `ℂ_p` (through `awayEquivCp`) does
  not change its kernel, so `ColmezBdRPlus` is the printed `lim← W(R)[p^{-1}]/(Ker θ)^n` with
  `θ : W(R)[p^{-1}] → C_p`.
* `ShapeB` and `shapeB_iff`: the shape of the `T_p` row over any `ℤ_p`-algebra, and its transport
  along an isomorphism of `ℤ_p`-algebras compatible with the actions and the "values in `B_dR^+`"
  predicates.
-/

namespace ZInQ.Contrib.ColmezTiltIso

set_option linter.unusedSectionVars false

open Ideal WittVector ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4
open scoped TensorProduct

section ZpExt

/-- Two ring maps out of `ℤ_p` into a `p`-adically separated ring agree. -/
theorem ringHom_ext_padicInt {p : ℕ} [Fact p.Prime] {S : Type*} [CommRing S]
    [IsHausdorff (span {(p : S)}) S] (φ ψ : ℤ_[p] →+* S) : φ = ψ := by
  ext z
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : S)})]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  have hz := PadicInt.appr_spec n z
  rw [Ideal.mem_span_singleton] at hz
  obtain ⟨c, hc⟩ := hz
  have e : φ z - ψ z = φ (z - (z.appr n : ℤ_[p])) - ψ (z - (z.appr n : ℤ_[p])) := by
    simp only [map_sub, map_natCast]
    ring
  rw [e, hc, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, ← mul_sub,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact dvd_mul_right _ _

end ZpExt

variable (p : ℕ) [Fact p.Prime]

instance charP_colmezR : CharP (ColmezR 𝓞_ℂ_[p] p) p :=
  RingHom.charP (colmezEquiv (O := 𝓞_ℂ_[p]) (p := p)).toRingHom
    (colmezEquiv (O := 𝓞_ℂ_[p]) (p := p)).injective p

/-- `ℤ_p = W(F_p) → W(R)`. -/
noncomputable def colmezZpToW : ℤ_[p] →+* WittVector p (ColmezR 𝓞_ℂ_[p] p) :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (ColmezR 𝓞_ℂ_[p] p))).comp
    (WittVector.equiv p).symm.toRingHom

/-- `wittEquiv` carries Colmez's `ℤ_p → W(R)` to the tree's `zpToW : ℤ_p → W(O♭)`. -/
theorem wittEquiv_colmezZpToW (z : ℤ_[p]) : wittEquiv (colmezZpToW p z) = zpToW p z := by
  refine WittVector.ext fun n => ?_
  rw [coeff_wittEquiv]
  simp only [colmezZpToW, zpToW, RingHom.comp_apply, map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod
    ((colmezEquiv (O := 𝓞_ℂ_[p]) (p := p)).toRingHom.comp
      (ZMod.castHom (dvd_refl p) (ColmezR 𝓞_ℂ_[p] p)))
    (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p))) _

/-- `ℤ_p → ColmezBdRPlus`: `ℤ_p → W(R) → W(R)[1/p] → B_dR^+`. -/
noncomputable def colmezZpToPlus : ℤ_[p] →+* ColmezBdRPlus 𝓞_ℂ_[p] p :=
  (algebraMap (Localization.Away (p : WittVector p (ColmezR 𝓞_ℂ_[p] p)))
    (ColmezBdRPlus 𝓞_ℂ_[p] p)).comp
    ((algebraMap _ (Localization.Away (p : WittVector p (ColmezR 𝓞_ℂ_[p] p)))).comp
      (colmezZpToW p))

namespace Printed

/-- Colmez's `B_dR^+` as a `ℤ_p`-algebra, through `ℤ_p = W(F_p) → W(R)`. -/
noncomputable scoped instance algZpPlus : Algebra ℤ_[p] (ColmezBdRPlus 𝓞_ℂ_[p] p) :=
  (colmezZpToPlus p).toAlgebra

end Printed

open scoped Printed

theorem algebraMap_zp_colmezBdRPlus (z : ℤ_[p]) :
    algebraMap ℤ_[p] (ColmezBdRPlus 𝓞_ℂ_[p] p) z =
      AdicCompletion.of _ _ (algebraMap _ _ (colmezZpToW p z)) := by
  change algebraMap (Localization.Away (p : WittVector p (ColmezR 𝓞_ℂ_[p] p)))
    (ColmezBdRPlus 𝓞_ℂ_[p] p) _ = _
  erw [AdicCompletion.algebraMap_apply]

/-- **`colmezBdRPlusEquiv` sends `z ∈ ℤ_p` to the tree's `ofLoc p (zpToW p z)`.** -/
theorem colmezBdRPlusEquiv_algebraMap_zp (z : ℤ_[p]) :
    colmezBdRPlusEquiv (algebraMap ℤ_[p] (ColmezBdRPlus 𝓞_ℂ_[p] p) z) =
      ofLoc p (algebraMap _ _ (zpToW p z)) := by
  rw [algebraMap_zp_colmezBdRPlus, colmezBdRPlusEquiv_of, wittEquiv_colmezZpToW, ofLoc_eq_ofPlus]

/-- The tree's `ℤ_p`-structure on `BDeRhamPlus 𝓞_ℂ_[p] p`: `ℤ_p → W(O♭) → W(O♭)[1/p] → B_dR^+`. -/
@[reducible] noncomputable def algZpTree : Algebra ℤ_[p] (BDeRhamPlus 𝓞_ℂ_[p] p) :=
  ((ofLoc p).comp ((algebraMap _ _).comp (zpToW p))).toAlgebra

/-- **`colmezBdRPlusEquiv` as an isomorphism of `ℤ_p`-algebras** (tree side: `algZpTree`). -/
noncomputable def colmezBdRPlusAlgEquiv :
    letI := algZpTree p
    ColmezBdRPlus 𝓞_ℂ_[p] p ≃ₐ[ℤ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p :=
  letI := algZpTree p
  { colmezBdRPlusEquiv with commutes' := colmezBdRPlusEquiv_algebraMap_zp p }

theorem colmezBdRPlusAlgEquiv_apply (x : ColmezBdRPlus 𝓞_ℂ_[p] p) :
    colmezBdRPlusAlgEquiv p x = colmezBdRPlusEquiv x :=
  rfl

open scoped Tp in
/-- **`colmezBdREquiv` as an isomorphism of `ℤ_p`-algebras**: the fraction field of Colmez's
`B_dR^+` (with the `ℤ_p`-structure from `W(F_p) → W(R)`) and the tree's `B_dR` (with `Tp.algZp`,
through `qpToBdR`). -/
noncomputable def colmezBdRAlgEquiv :
    FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) ≃ₐ[ℤ_[p]] BdR p :=
  { colmezBdREquiv p with
    commutes' := fun z => by
      change colmezBdREquiv p (algebraMap _ _ (algebraMap ℤ_[p] (ColmezBdRPlus 𝓞_ℂ_[p] p) z)) =
        qpToBdR p (algebraMap ℤ_[p] ℚ_[p] z)
      rw [colmezBdREquiv_algebraMap, colmezBdRPlusEquiv_algebraMap_zp, qpToBdR,
        RingHom.comp_apply, RingHom.comp_apply, qpToLoc_algebraMap]
      rfl }

theorem colmezBdRAlgEquiv_apply (y : FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p)) :
    colmezBdRAlgEquiv p y = colmezBdREquiv p y :=
  rfl

/-- `ℤ_p → ℚ_p → ℂ_p` with values in `𝓞_ℂ_p`. -/
noncomputable def zpToO : ℤ_[p] →+* 𝓞_ℂ_[p] :=
  ((algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom).codRestrict 𝓞_ℂ_[p] fun z => by
    rw [Cp.mem_O_iff, RingHom.comp_apply, IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p)
      ℂ_[p], ← PadicComplex.coe_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
    exact z.2

/-- **`θ` on Colmez's `B_dR^+` restricts to `ℤ_p ⊂ ℚ_p ⊂ ℂ_p`.** -/
theorem colmezThetaPlus_algebraMap_zp (z : ℤ_[p]) :
    colmezThetaPlus p (algebraMap ℤ_[p] (ColmezBdRPlus 𝓞_ℂ_[p] p) z) =
      algebraMap ℚ_[p] ℂ_[p] (z : ℚ_[p]) := by
  rw [algebraMap_zp_colmezBdRPlus, colmezThetaPlus_of]
  have h : (colmezTheta 𝓞_ℂ_[p] p).comp (colmezZpToW p) = zpToO p :=
    ringHom_ext_padicInt _ _
  exact congrArg Subtype.val (RingHom.congr_fun h z)

/-- Reading `θ[1/p]` in `ℂ_p` (through `awayEquivCp`) does not change its kernel. -/
theorem ker_awayEquivCp_comp_colmezThetaInvertP :
    RingHom.ker ((BdrKer.Cp.awayEquivCp p).toRingEquiv.toRingHom.comp
      (colmezThetaInvertP 𝓞_ℂ_[p] p)) = RingHom.ker (colmezThetaInvertP 𝓞_ℂ_[p] p) :=
  RingHom.ker_comp_of_injective _ (BdrKer.Cp.awayEquivCp p).injective

/-! ### The shape of the `T_p` row over a `ℤ_p`-algebra, and its transport -/

section Shape

variable {F : Type*} [Field F] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]

variable (F) in
/-- The `T_p` row's conclusion over a `ℤ_p`-algebra `B` with a `G_F`-action `act` and a
"values in `B_dR^+`" predicate `Q`. -/
def ShapeB (B : Type*) [CommRing B] [Algebra ℤ_[p] B] (Q : B → Prop)
    (act : Field.absoluteGaloisGroup F → B → B)
    (τ : Field.absoluteGaloisGroup F → T →ₗ[ℤ_[p]] T) : Prop :=
  ∃ (H : Type) (P : H → (T →ₗ[ℤ_[p]] B)),
    (∀ ω u, Q (P ω u)) ∧
    (∀ ω (σ : Field.absoluteGaloisGroup F) u, P ω (τ σ u) = act σ (P ω u)) ∧
    (∀ x : B ⊗[ℤ_[p]] T, (∀ ω, (P ω).liftBaseChange B x = 0) → x = 0)

theorem shapeB_of {B B' : Type*} [CommRing B] [Algebra ℤ_[p] B] [CommRing B']
    [Algebra ℤ_[p] B'] (e : B ≃ₐ[ℤ_[p]] B') {Q : B → Prop} {Q' : B' → Prop}
    (hQ : ∀ y, Q y → Q' (e y)) {act : Field.absoluteGaloisGroup F → B → B}
    {act' : Field.absoluteGaloisGroup F → B' → B'} (hact : ∀ σ y, e (act σ y) = act' σ (e y))
    (τ : Field.absoluteGaloisGroup F → T →ₗ[ℤ_[p]] T) :
    ShapeB p F B Q act τ → ShapeB p F B' Q' act' τ := by
  rintro ⟨H, P, h0, hgal, hnd⟩
  refine ⟨H, fun ω => e.toLinearMap ∘ₗ P ω, fun ω u => hQ _ (h0 ω u), fun ω σ u => ?_,
    fun x hx => ?_⟩
  · simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
    rw [hgal, hact]
  · set m : B' ⊗[ℤ_[p]] T ≃ₗ[ℤ_[p]] B ⊗[ℤ_[p]] T :=
      TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl ℤ_[p] T)
    have key : ∀ ω (y : B' ⊗[ℤ_[p]] T), (e.toLinearMap ∘ₗ P ω).liftBaseChange B' y =
        e ((P ω).liftBaseChange B (m y)) := by
      intro ω y
      induction y using TensorProduct.inductionOn with
      | tmul b t =>
        simp only [m, TensorProduct.congr_tmul, LinearMap.liftBaseChange_tmul,
          LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, smul_eq_mul, map_mul,
          AlgEquiv.toLinearEquiv_apply, LinearEquiv.refl_apply, AlgEquiv.apply_symm_apply]
      | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add]
    have h1 : m x = 0 := hnd _ fun ω => by
      apply e.injective
      rw [map_zero, ← key]
      exact hx ω
    simpa using congrArg m.symm h1

/-- **Transport of the row's shape** along an isomorphism of `ℤ_p`-algebras compatible with the
actions and the predicates. -/
theorem shapeB_iff {B B' : Type*} [CommRing B] [Algebra ℤ_[p] B] [CommRing B']
    [Algebra ℤ_[p] B'] (e : B ≃ₐ[ℤ_[p]] B') {Q : B → Prop} {Q' : B' → Prop}
    (hQ : ∀ y, Q' (e y) ↔ Q y) {act : Field.absoluteGaloisGroup F → B → B}
    {act' : Field.absoluteGaloisGroup F → B' → B'} (hact : ∀ σ y, e (act σ y) = act' σ (e y))
    (τ : Field.absoluteGaloisGroup F → T →ₗ[ℤ_[p]] T) :
    ShapeB p F B Q act τ ↔ ShapeB p F B' Q' act' τ := by
  constructor
  · exact shapeB_of p e (fun y h => (hQ y).2 h) hact τ
  · refine shapeB_of p e.symm (fun y h => ?_) (fun σ y => ?_) τ
    · rw [← hQ, AlgEquiv.apply_symm_apply]
      exact h
    · apply e.injective
      rw [hact, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

end Shape

end ZInQ.Contrib.ColmezTiltIso
