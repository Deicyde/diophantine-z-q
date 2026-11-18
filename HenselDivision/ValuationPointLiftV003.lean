import HenselDivision.ValuationPointTorsionV002

/-!
# Existence of integral torsion lifts for points over the base, and the torsion bijection

Base `Spec O`, `N` a smooth commutative group scheme over `Spec O`, `φ : O → R` a ring map to a
henselian local ring `R`, `P = (Spec R → Spec O)` and `D = (Spec κ(R) → Spec R → Spec O)` as objects
over `Spec O`, and `r : D ⟶ P` the reduction arrow (underlying morphism `Spec` of the residue
map). For `m` invertible in `O`:

* **existence** (`torsion_point_lift_exists`): every residual point `x : D ⟶ N` with `x ^ m = 1`
  is `r ≫ a` for some integral point `a : P ⟶ N` with `a ^ m = 1`. The point `x` factors through
  the actual torsion scheme `N[m]`, which is étale over `Spec O` (proved multiplication); after
  base change along `Spec φ` it is a `κ(R)`-point of an étale `Spec R`-scheme over the closed
  point, which `etale_section_existsUnique` lifts to a section; the section gives `a`;
* **bijection** (`torsion_point_restrict_bijective`): with the uniqueness of
  `torsion_point_eq_of_reduction`, restriction along `r` is a bijection
  `{a : P ⟶ N // a ^ m = 1} → {x : D ⟶ N // x ^ m = 1}`, and a group isomorphism of the
  `m`-torsion subgroups (`torsionPointRestrictEquiv`).

Instantiated at `w` a valuation subring of an algebraically closed `Ω` over `O` (not necessarily
discrete) with `φ = PkgI2.toW O w hw`; henselianity of `w` is derived. Only residual torsion is
lifted: nothing is said about generic torsion points that do not extend.

Edition V003: the evaluation lemma of the isomorphism is definitional. Statements as in V001.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
  IsLocalRing
open scoped MonObj

namespace HenselDivision

section General

variable {O R : Type} [CommRing O] [CommRing R] [HenselianLocalRing R]

/-- **Existence of the integral torsion lift.** -/
theorem torsion_point_lift_exists (φ : O →+* R) (N : Over (Spec (CommRingCat.of O)))
    [GrpObj N] [Smooth N.hom] [IsCommMonObj N] (m : ℕ) (hm : IsUnit (m : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom φ)))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (x : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ))) ⟶ N)
    (hx : x ^ m = 1) :
    ∃ a : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ N, a ^ m = 1 ∧ r ≫ a = x := by
  let P : Over (Spec (CommRingCat.of O)) := Over.mk (Spec.map (CommRingCat.ofHom φ))
  let D : Over (Spec (CommRingCat.of O)) :=
    Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ)))
  have hE : Etale (powHom N m).left := etale_powHom_of_smooth_comm N m hm
  have hK : Etale (torsionKer N m).hom := etale_torsionKer_hom N m hE
  -- `x` through the actual torsion scheme
  let xk : D ⟶ torsionKer N m := (torsionKerHomEquiv N m D).symm ⟨x, hx⟩
  let p : (torsionKer N m).left ⟶ Spec (CommRingCat.of O) := (torsionKer N m).hom
  let b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom φ)
  have hc : closedPt R = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) := by
    rw [closedPt, IsLocalRing.ResidueField.algebraMap_eq]
  have hD : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ)) = closedPt R ≫ b := by
    rw [hc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hwx : xk.left ≫ p = closedPt R ≫ b := by
    have h := Over.w xk
    rw [← hD]
    exact h
  -- base change to `Spec R` and Hensel lifting
  have : Etale (pullback.snd p b) :=
    MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback p b) hK
  let x₁ : Spec (CommRingCat.of (ResidueField R)) ⟶ pullback p b :=
    pullback.lift xk.left (closedPt R) hwx
  have hx₁ : x₁ ≫ pullback.snd p b = closedPt R := pullback.lift_snd _ _ _
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := etale_section_existsUnique (pullback.snd p b) x₁ hx₁
  have hsw : (s ≫ pullback.fst p b) ≫ p = b := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs1, Category.id_comp]
  let â : P ⟶ torsionKer N m := Over.homMk (s ≫ pullback.fst p b) hsw
  -- the lift and its reduction
  have hrâ : r ≫ â = xk := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hr, ← hc]
    change closedPt R ≫ s ≫ pullback.fst p b = xk.left
    rw [← Category.assoc, hs2, pullback.lift_fst]
  refine ⟨(torsionKerHomEquiv N m P â).1, (torsionKerHomEquiv N m P â).2, ?_⟩
  rw [← torsionKerHomEquiv_naturality, hrâ, Equiv.apply_symm_apply]

/-- **Restriction to the residue point is a bijection on `m`-torsion points.** -/
theorem torsion_point_restrict_bijective (φ : O →+* R) (N : Over (Spec (CommRingCat.of O)))
    [GrpObj N] [Smooth N.hom] [IsCommMonObj N] (m : ℕ) (hm : IsUnit (m : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom φ)))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    Function.Bijective (fun a : {a : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ N // a ^ m = 1} =>
      (⟨r ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩ :
        {x : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ))) ⟶ N //
          x ^ m = 1})) := by
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    apply Subtype.ext
    exact torsion_point_eq_of_reduction φ N m m hm hm r hr a b ha hb (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, hax⟩ := torsion_point_lift_exists φ N m hm r hr x hx
    exact ⟨⟨a, ha⟩, Subtype.ext hax⟩

/-- Restriction along `r` as a homomorphism of `m`-torsion groups. -/
noncomputable def torsionPointRestrictHom (φ : O →+* R) (N : Over (Spec (CommRingCat.of O)))
    [GrpObj N] [IsCommMonObj N] (m : ℕ)
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom φ))) :
    torsionPts N (Over.mk (Spec.map (CommRingCat.ofHom φ))) m →*
      torsionPts N (Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ)))) m where
  toFun a := ⟨r ≫ a.1, (mem_torsionPts _).2 (by
    rw [← MonObj.comp_pow, (mem_torsionPts _).1 a.2, MonObj.comp_one])⟩
  map_one' := Subtype.ext (MonObj.comp_one _)
  map_mul' a b := Subtype.ext (MonObj.comp_mul _ _ _)

/-- **The torsion group isomorphism** `N(Spec R)[m] ≃* N(Spec κ(R))[m]` for points over `Spec O`. -/
noncomputable def torsionPointRestrictEquiv (φ : O →+* R) (N : Over (Spec (CommRingCat.of O)))
    [GrpObj N] [Smooth N.hom] [IsCommMonObj N] (m : ℕ) (hm : IsUnit (m : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom φ)))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    torsionPts N (Over.mk (Spec.map (CommRingCat.ofHom φ))) m ≃*
      torsionPts N (Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ)))) m :=
  MulEquiv.ofBijective (torsionPointRestrictHom φ N m r) (by
    have hb := torsion_point_restrict_bijective φ N m hm r hr
    constructor
    · intro a b h
      have := hb.1 (a₁ := ⟨a.1, (mem_torsionPts _).1 a.2⟩) (a₂ := ⟨b.1, (mem_torsionPts _).1 b.2⟩)
        (Subtype.ext (congrArg Subtype.val h))
      exact Subtype.ext (congrArg Subtype.val this)
    · intro c
      obtain ⟨a, ha⟩ := hb.2 ⟨c.1, (mem_torsionPts _).1 c.2⟩
      exact ⟨⟨a.1, (mem_torsionPts _).2 a.2⟩, Subtype.ext (congrArg Subtype.val ha)⟩)

lemma torsionPointRestrictEquiv_apply (φ : O →+* R) (N : Over (Spec (CommRingCat.of O)))
    [GrpObj N] [Smooth N.hom] [IsCommMonObj N] (m : ℕ) (hm : IsUnit (m : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue R).comp φ))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom φ)))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (a : torsionPts N (Over.mk (Spec.map (CommRingCat.ofHom φ))) m) :
    (torsionPointRestrictEquiv φ N m hm r hr a).1 = r ≫ a.1 :=
  rfl

end General

section Valuation

variable {K : Type} [Field K] {O : ValuationSubring K} {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω]

/-- **Existence at a valuation ring of an algebraically closed field over `O`.** -/
theorem valuation_point_torsion_lift_exists (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (N : Over (Spec (CommRingCat.of O))) [GrpObj N]
    [Smooth N.hom] [IsCommMonObj N] (m : ℕ) (hm : IsUnit (m : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw))))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)))
    (x : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)))) ⟶
      N)
    (hx : x ^ m = 1) :
    ∃ a : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw))) ⟶ N,
      a ^ m = 1 ∧ r ≫ a = x :=
  haveI := henselianLocalRing_of_isAlgClosed w
  torsion_point_lift_exists (PkgI2.toW O w hw) N m hm r hr x hx

/-- **The literal torsion bijection at `w`.** -/
theorem valuation_point_torsion_restrict_bijective (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (N : Over (Spec (CommRingCat.of O))) [GrpObj N]
    [Smooth N.hom] [IsCommMonObj N] (m : ℕ) (hm : IsUnit (m : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw))))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w))) :
    Function.Bijective
      (fun a : {a : Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw))) ⟶ N // a ^ m = 1} =>
        (⟨r ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩ :
          {x : Over.mk (Spec.map (CommRingCat.ofHom
              ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)))) ⟶ N // x ^ m = 1})) :=
  haveI := henselianLocalRing_of_isAlgClosed w
  torsion_point_restrict_bijective (PkgI2.toW O w hw) N m hm r hr

/-- **The torsion group isomorphism at `w`.** -/
noncomputable def valuationTorsionPointRestrictEquiv (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (N : Over (Spec (CommRingCat.of O))) [GrpObj N]
    [Smooth N.hom] [IsCommMonObj N] (m : ℕ) (hm : IsUnit (m : O))
    (r : Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw))))
    (hr : r.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w))) :
    torsionPts N (Over.mk (Spec.map (CommRingCat.ofHom (PkgI2.toW O w hw)))) m ≃*
      torsionPts N (Over.mk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue w).comp (PkgI2.toW O w hw))))) m :=
  haveI := henselianLocalRing_of_isAlgClosed w
  torsionPointRestrictEquiv (PkgI2.toW O w hw) N m hm r hr

end Valuation

end HenselDivision

#check @HenselDivision.torsion_point_lift_exists
#check @HenselDivision.valuation_point_torsion_lift_exists
#check @HenselDivision.valuation_point_torsion_restrict_bijective
#check @HenselDivision.valuationTorsionPointRestrictEquiv
#print axioms HenselDivision.torsion_point_lift_exists
#print axioms HenselDivision.torsion_point_restrict_bijective
#print axioms HenselDivision.torsionPointRestrictEquiv
#print axioms HenselDivision.torsionPointRestrictEquiv_apply
#print axioms HenselDivision.valuation_point_torsion_lift_exists
#print axioms HenselDivision.valuation_point_torsion_restrict_bijective
#print axioms HenselDivision.valuationTorsionPointRestrictEquiv
