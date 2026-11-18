import ToricBaseChange.TorusFactorsOpenV002

/-!
# A torus split over `k̄`, base changed to an algebraically closed field `Ω ⊇ k̄`

A group scheme `U` over a field `k` with a torus that is split only over `k̄` (an injective natural
homomorphism `e_R : (Rˣ)^r → U(R)` for `k̄`-algebras `R`, the form of a not necessarily split torus
over the residue field) gives, for any field `Ω` with a ring map `ι : k̄ → Ω`, a split torus
`e^Ω : 𝔾_m^r → U_Ω` of the base change `U_Ω = U ×_k Ω` over `Ω`, injective and natural
(`torusTransport`). This is the residue-field / geometric base change step: the special fibre of a
Néron model over the residue field `k` of `O` and that of `N'` over the residue field `k'` of `O'`
are compared over a common algebraically closed field `Ω` receiving `k̄` (an algebraic closure of
`k`, which embeds over `k` into any algebraically closed extension of `k`, e.g. `k̄'`).

The transport `Φ` along `Spec Ω → Spec k` (adjunction `Over.map ⊣ Over.pullback`) is the standard
one, with `R` viewed as a `k`-algebra through `k → Ω → R`.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ToricBaseChange

section Transport

variable {k Ω : Type} [Field k] [Field Ω] (φ : k →+* Ω)

/-- `Spec φ : Spec Ω → Spec k`. -/
abbrev sφ : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom φ)

theorem homEquiv_mul' (X : Over (Spec (CommRingCat.of Ω))) (Y : Over (Spec (CommRingCat.of k)))
    [GrpObj Y] (p q : (Over.map (sφ φ)).obj X ⟶ Y) :
    letI : GrpObj ((Over.pullback (sφ φ)).obj Y) := Functor.grpObjObj
    (Over.mapPullbackAdj (sφ φ)).homEquiv X Y (p * q) =
      (Over.mapPullbackAdj (sφ φ)).homEquiv X Y p * (Over.mapPullbackAdj (sφ φ)).homEquiv X Y q := by
  letI : GrpObj ((Over.pullback (sφ φ)).obj Y) := Functor.grpObjObj
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- An `Ω`-algebra as a `k`-algebra through `φ`. -/
@[reducible] def algK (R : Type) [CommRing R] [Algebra Ω R] : Algebra k R :=
  ((algebraMap Ω R).comp φ).toAlgebra

/-- `Over.map (Spec φ) (Spec R / Ω) ≅ Spec R / k`. -/
def ιR (R : Type) [CommRing R] [Algebra Ω R] :
    letI := algK φ R
    (Over.map (sφ φ)).obj (SpecPt Ω R) ≅ SpecPt k R :=
  letI := algK φ R
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, SpecPt, Over.mk_hom]
    erw [Category.id_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

/-- `(Spec R / Ω ⟶ U_Ω) ≃* (Spec R / k ⟶ U)`. -/
def Φ (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (R : Type) [CommRing R] [Algebra Ω R] :
    letI := algK φ R
    letI : GrpObj ((Over.pullback (sφ φ)).obj U) := Functor.grpObjObj
    (SpecPt Ω R ⟶ (Over.pullback (sφ φ)).obj U) ≃* (SpecPt k R ⟶ U) :=
  letI := algK φ R
  letI : GrpObj ((Over.pullback (sφ φ)).obj U) := Functor.grpObjObj
  { toFun p := (ιR φ R).inv ≫ ((Over.mapPullbackAdj (sφ φ)).homEquiv _ _).symm p
    invFun x := (Over.mapPullbackAdj (sφ φ)).homEquiv _ _ ((ιR φ R).hom ≫ x)
    left_inv p := by
      simp only
      rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
    right_inv x := by
      simp only
      rw [Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
    map_mul' p q := by
      obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sφ φ)).homEquiv _ U).surjective p
      obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sφ φ)).homEquiv _ U).surjective q
      rw [← homEquiv_mul', Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        MonObj.comp_mul] }

theorem Φ_natural (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (R S : Type) [CommRing R]
    [Algebra Ω R] [CommRing S] [Algebra Ω S] (f : R →ₐ[Ω] S)
    (u : SpecPt Ω R ⟶ (Over.pullback (sφ φ)).obj U) :
    letI := algK φ R
    letI := algK φ S
    letI : GrpObj ((Over.pullback (sφ φ)).obj U) := Functor.grpObjObj
    Φ φ U S (SpecPtMap f ≫ u) =
      SpecPtMap (k := k) ({ (f : R →+* S) with commutes' := fun a => f.commutes (φ a) } : R →ₐ[k] S)
        ≫ Φ φ U R u := by
  show (ιR φ S).inv ≫ ((Over.mapPullbackAdj (sφ φ)).homEquiv _ _).symm (SpecPtMap f ≫ u) = _ ≫
    (ιR φ R).inv ≫ ((Over.mapPullbackAdj (sφ φ)).homEquiv _ _).symm u
  rw [Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, ← Category.assoc]
  congr 1

end Transport

/-! ## The torus of `U_Ω` -/

section Torus

variable {k : Type} [Field k] {Ω : Type} [Field Ω] (jb : AlgebraicClosure k →+* Ω)

/-- `k → k̄ → Ω`. -/
abbrev φι : k →+* Ω := jb.comp (algebraMap k (AlgebraicClosure k))

/-- An `Ω`-algebra as a `k̄`-algebra through `ι`. -/
@[reducible] def algBar (R : Type) [CommRing R] [Algebra Ω R] : Algebra (AlgebraicClosure k) R :=
  ((algebraMap Ω R).comp jb).toAlgebra

/-- **Transport of a torus split over `k̄` to the base change `U_Ω`.** `e` is a natural injective
homomorphism `(Rˣ)^r → U(R)` for `k̄`-algebras `R` (viewed as `k`-algebras through `k → k̄`); then
`e^Ω_R := Φ⁻¹ ∘ e_R` (with `R` a `k̄`-algebra through `ι`) is a natural injective homomorphism
`(Rˣ)^r → U_Ω(R)` for `Ω`-algebras `R`. -/
theorem torusTransport (U : Over (Spec (CommRingCat.of k))) [GrpObj U] (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R],
      letI := algK (algebraMap k (AlgebraicClosure k)) R
      (Fin r → Rˣ) →* (SpecPt k R ⟶ U))
    (he_inj : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure k) R], Function.Injective (e R))
    (he_nat : ∀ (R S : Type) [CommRing R] [Algebra (AlgebraicClosure k) R] [CommRing S]
        [Algebra (AlgebraicClosure k) S] (f : R →ₐ[AlgebraicClosure k] S) (t : Fin r → Rˣ),
        letI := algK (algebraMap k (AlgebraicClosure k)) R
        letI := algK (algebraMap k (AlgebraicClosure k)) S
        e S (fun i => Units.map (f : R →* S) (t i)) =
          SpecPtMap (k := k) ({ (f : R →+* S) with
            commutes' := fun a => f.commutes (algebraMap k (AlgebraicClosure k) a) } : R →ₐ[k] S) ≫ e R t) :
    letI : GrpObj ((Over.pullback (sφ (φι jb))).obj U) := Functor.grpObjObj
    ∃ eΩ : ∀ (R : Type) [CommRing R] [Algebra Ω R],
        (Fin r → Rˣ) →* (SpecPt Ω R ⟶ (Over.pullback (sφ (φι jb))).obj U),
      (∀ (R : Type) [CommRing R] [Algebra Ω R], Function.Injective (eΩ R)) ∧
      (∀ (R S : Type) [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S] (f : R →ₐ[Ω] S)
        (t : Fin r → Rˣ), eΩ S (fun i => Units.map (f : R →* S) (t i)) = SpecPtMap f ≫ eΩ R t) ∧
      (∀ (R : Type) [CommRing R] [Algebra Ω R] (t : Fin r → Rˣ),
        letI := algK (φι jb) R
        Φ (φι jb) U R (eΩ R t) = @e R _ (algBar jb R) t) := by
  letI : GrpObj ((Over.pullback (sφ (φι jb))).obj U) := Functor.grpObjObj
  refine ⟨fun R _ _ => (Φ (φι jb) U R).symm.toMonoidHom.comp (@e R _ (algBar jb R)), ?_, ?_, ?_⟩
  · intro R _ _
    exact (Φ (φι jb) U R).symm.injective.comp (@he_inj R _ (algBar jb R))
  · intro R S _ _ _ _ f t
    letI := algK (φι jb) R
    letI := algK (φι jb) S
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    apply (Φ (φι jb) U S).injective
    rw [MulEquiv.apply_symm_apply, Φ_natural, MulEquiv.apply_symm_apply]
    letI := algBar jb R
    letI := algBar jb S
    let f' : R →ₐ[AlgebraicClosure k] S :=
      { (f : R →+* S) with commutes' := fun a => f.commutes (jb a) }
    exact he_nat R S f' t
  · intro R _ _ t
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.apply_symm_apply]

end Torus

end ToricBaseChange
