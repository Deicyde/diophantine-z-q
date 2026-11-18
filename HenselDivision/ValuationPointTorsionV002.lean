import HenselDivision.SmoothCommTorsionV001
import HenselDivision.ValuationStrictHenselV003
import ZInQKernel.HDecomp.Objects

/-!
# Reduction is injective on torsion points with values in a valuation ring over the base

Base `Spec O`, `N` a smooth commutative group scheme over `Spec O`, `φ : O → R` a ring map to a
henselian local ring `R`, and points `a : Spec R → N` over `Spec O`, i.e. morphisms
`Over.mk (Spec φ) ⟶ N` in `Over (Spec O)`. If `n` is invertible in `O`, `a ^ n = 1` and the
restriction of `a` along `Spec κ(R) → Spec R` is trivial, then `a = 1`. Proof: `a` and `1`
factor through the actual torsion scheme `N[n] = N ×_{[n], N, η} Spec O`, which is étale over
`Spec O` because `[n]` is étale (smooth commutative `N`, `n` a unit); after base change along
`Spec φ` the two factorizations are sections of an étale `Spec R`-scheme agreeing at the closed
point, hence equal by Hensel uniqueness. No point equivalence, filtration or bound is used.

The reduction arrow is any `r : Over.mk (Spec (residue ∘ φ)) ⟶ Over.mk (Spec φ)` whose underlying
morphism is `Spec` of the residue map (for instance
`Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) _`). For `w` a valuation subring
of an algebraically closed `Ω` lying over `O` (not necessarily discrete), `R = w` is henselian
(derived), and the statement is instantiated with the ring map `PkgI2.toW O w hw`. An
`n`-independent form compares two torsion points of possibly different orders.

Edition V002: the reduction arrow's domain is the residue object itself (so that its underlying
morphism can be named), and one ambiguous name is qualified. Statements otherwise as in V001.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  IsLocalRing
open scoped MonObj

namespace HenselDivision

section General

variable {O R : Type} [CommRing O] [CommRing R] [HenselianLocalRing R]

/-- **Torsion points over `Spec O` with values in a henselian local ring and trivial reduction
are trivial.** -/
theorem torsion_point_eq_one_of_reduction (φ : O →+* R) (N : Over (Spec (CommRingCat.of O)))
    [GrpObj N] [Smooth N.hom] [IsCommMonObj N] (n : ℕ) (hn : IsUnit (n : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom φ)))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (a : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ N) (ha : a ^ n = 1) (hred : r ≫ a = 1) :
    a = 1 := by
  let P : Over (Spec (CommRingCat.of O)) := Over.mk (Spec.map (CommRingCat.ofHom φ))
  let D : Over (Spec (CommRingCat.of O)) :=
    Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ)))
  have hE : Etale (powHom N n).left := etale_powHom_of_smooth_comm N n hn
  have hK : Etale (torsionKer N n).hom := etale_torsionKer_hom N n hE
  let E := torsionKerHomEquiv N n P
  let â : P ⟶ torsionKer N n := E.symm ⟨a, ha⟩
  let ê : P ⟶ torsionKer N n := E.symm ⟨1, one_pow n⟩
  -- the two factorizations agree after reduction
  have hredK : r ≫ â = r ≫ ê := by
    apply (torsionKerHomEquiv N n D).injective
    apply Subtype.ext
    rw [torsionKerHomEquiv_naturality, torsionKerHomEquiv_naturality]
    change r ≫ (E (E.symm ⟨a, ha⟩)).1 = r ≫ (E (E.symm ⟨1, one_pow n⟩)).1
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change r ≫ a = r ≫ 1
    rw [hred, MonObj.comp_one]
  have hredL : Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ â.left =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ ê.left := by
    have := congrArg (fun f => f.left) hredK
    simp only [Over.comp_left] at this
    rw [hr] at this
    exact this
  -- base change to `Spec R`
  let p : (torsionKer N n).left ⟶ Spec (CommRingCat.of O) := (torsionKer N n).hom
  let b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom φ)
  have : Etale (pullback.snd p b) :=
    MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback p b) hK
  have hwâ : â.left ≫ p = b := Over.w â
  have hwê : ê.left ≫ p = b := Over.w ê
  let s₁ : Spec (CommRingCat.of R) ⟶ pullback p b :=
    pullback.lift â.left (𝟙 _) (by rw [hwâ, Category.id_comp])
  let s₂ : Spec (CommRingCat.of R) ⟶ pullback p b :=
    pullback.lift ê.left (𝟙 _) (by rw [hwê, Category.id_comp])
  have hs₁ : s₁ ≫ pullback.snd p b = 𝟙 _ := pullback.lift_snd _ _ _
  have hs₂ : s₂ ≫ pullback.snd p b = 𝟙 _ := pullback.lift_snd _ _ _
  have hc : closedPt R = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
    rw [closedPt, IsLocalRing.ResidueField.algebraMap_eq]
  have hcl : closedPt R ≫ s₂ = closedPt R ≫ s₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, hc, hredL]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  obtain ⟨s, -, hs⟩ := etale_section_existsUnique (pullback.snd p b) (closedPt R ≫ s₁)
    (by rw [Category.assoc, hs₁, Category.comp_id])
  have e1 := hs s₁ ⟨hs₁, rfl⟩
  have e2 := hs s₂ ⟨hs₂, hcl⟩
  have hleft : â.left = ê.left := by
    have h1 : s₁ ≫ pullback.fst p b = â.left := pullback.lift_fst _ _ _
    have h2 : s₂ ≫ pullback.fst p b = ê.left := pullback.lift_fst _ _ _
    rw [← h1, ← h2, e1, e2]
  have hhat : â = ê := Over.OverMorphism.ext hleft
  have := congrArg (fun g => (E g).1) hhat
  simpa [â, ê] using this

/-- **`n`-independent form**: two torsion points of orders dividing `n` and `m` (both units)
with the same reduction are equal. -/
theorem torsion_point_eq_of_reduction (φ : O →+* R) (N : Over (Spec (CommRingCat.of O)))
    [GrpObj N] [Smooth N.hom] [IsCommMonObj N] (n m : ℕ) (hn : IsUnit (n : O))
    (hm : IsUnit (m : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom φ)))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (a b : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ N) (ha : a ^ n = 1) (hb : b ^ m = 1)
    (hred : r ≫ a = r ≫ b) : a = b := by
  have hnm : IsUnit ((n * m : ℕ) : O) := by rw [Nat.cast_mul]; exact hn.mul hm
  have hc : (a * b⁻¹) ^ (n * m) = 1 := by
    rw [mul_pow, inv_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, inv_one,
      _root_.one_mul]
  have hrc : r ≫ (a * b⁻¹) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hred, mul_inv_cancel]
  have h1 := torsion_point_eq_one_of_reduction φ N (n * m) hnm r hr (a * b⁻¹) hc hrc
  exact mul_inv_eq_one.mp h1

end General

section Valuation

variable {K : Type} [Field K] {O : ValuationSubring K} {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω]

/-- **Instantiation at a valuation ring of an algebraically closed field over `O`.** -/
theorem valuation_point_torsion_eq_one (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (N : Over (Spec (CommRingCat.of O))) [GrpObj N]
    [Smooth N.hom] [IsCommMonObj N] (n : ℕ) (hn : IsUnit (n : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw))))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)))
    (a : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw))) ⟶ N) (ha : a ^ n = 1)
    (hred : r ≫ a = 1) : a = 1 :=
  haveI := henselianLocalRing_of_isAlgClosed w
  torsion_point_eq_one_of_reduction (PkgI2.toW O w hw) N n hn r hr a ha hred

/-- `n`-independent form at a valuation ring of an algebraically closed field over `O`. -/
theorem valuation_point_torsion_eq_of_reduction (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (N : Over (Spec (CommRingCat.of O))) [GrpObj N]
    [Smooth N.hom] [IsCommMonObj N] (n m : ℕ) (hn : IsUnit (n : O)) (hm : IsUnit (m : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw))))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)))
    (a b : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw))) ⟶ N) (ha : a ^ n = 1)
    (hb : b ^ m = 1) (hred : r ≫ a = r ≫ b) : a = b :=
  haveI := henselianLocalRing_of_isAlgClosed w
  torsion_point_eq_of_reduction (PkgI2.toW O w hw) N n m hn hm r hr a b ha hb hred

end Valuation

end HenselDivision

#check @HenselDivision.torsion_point_eq_one_of_reduction
#check @HenselDivision.valuation_point_torsion_eq_one
#print axioms HenselDivision.torsion_point_eq_one_of_reduction
#print axioms HenselDivision.torsion_point_eq_of_reduction
#print axioms HenselDivision.valuation_point_torsion_eq_one
#print axioms HenselDivision.valuation_point_torsion_eq_of_reduction
