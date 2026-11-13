import Mathlib
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.SpreadOut.Spread
import ZInQKernel.Contrib.SpreadOut.SmoothLocus

/-!
# Spreading out, IV: abelian varieties over a number field spread out over `𝓞_L[1/f]`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task spread-out, 2026-11-13).

* `ringCoconeIsColimit`: `L = colim_n 𝓞_L[1/n!]` in `CommRingCat` (every `x ∈ L` has an integral
  multiple `y • x`, `0 ≠ y ∈ ℤ`, and `y ∣ |y|!`; the maps `𝓞_L[1/n!] → L` are injective);
* `specConeIsLimit`: hence `Spec L = lim_n Spec 𝓞_L[1/n!]`, a cofiltered limit of affine schemes;
* `abVarSpreadsOut_of_ega`: from the three EGA IV leaves of `Spread.lean`, every abelian variety
  `B` over `L` (the project's `PkgI3.AbVar`) extends to a smooth proper group scheme over
  `𝓞_L[1/n!]` for some `n`, and then over every presentation `R` of `𝓞_L[1/f]`, `f = n!`
  (base change along `Spec R ≅ Spec 𝓞_L[1/f]`).  Its statement is the body of neron-lg's glue
  N1-g1 `AbVarSpreadsOut` (`scratch/neron-lg/NeronLG.lean`), with `HasAbelianSchemeAway` unfolded.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open NumberField

namespace ZInQ.Contrib.SpreadOut.NF

variable (L : Type) [Field L] [NumberField L]

/-- `n!` in `𝓞 L`. -/
noncomputable def sf (n : ℕ) : 𝓞 L := (n.factorial : 𝓞 L)

theorem sf_ne_zero (n : ℕ) : sf L n ≠ 0 := by
  unfold sf
  exact_mod_cast n.factorial_ne_zero

theorem sf_dvd {m n : ℕ} (h : m ≤ n) : sf L m ∣ sf L n := by
  unfold sf
  exact Nat.cast_dvd_cast (Nat.factorial_dvd_factorial h)

/-- The stage `𝓞_L[1/n!]`. -/
abbrev Rg (n : ℕ) : Type := Localization.Away (sf L n)

theorem isUnit_sf_L (n : ℕ) : IsUnit (algebraMap (𝓞 L) L (sf L n)) :=
  isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)).2
    (sf_ne_zero L n))

theorem isUnit_sf_R {m n : ℕ} (h : m ≤ n) : IsUnit (algebraMap (𝓞 L) (Rg L n) (sf L m)) :=
  isUnit_of_dvd_unit (map_dvd _ (sf_dvd L h)) (IsLocalization.Away.algebraMap_isUnit (sf L n))

/-- `𝓞_L[1/n!] → L`. -/
noncomputable def toL (n : ℕ) : Rg L n →+* L := IsLocalization.Away.lift (sf L n) (isUnit_sf_L L n)

/-- `𝓞_L[1/m!] → 𝓞_L[1/n!]` for `m ≤ n`. -/
noncomputable def tr {m n : ℕ} (h : m ≤ n) : Rg L m →+* Rg L n :=
  IsLocalization.Away.lift (sf L m) (isUnit_sf_R L h)

theorem toL_alg (n : ℕ) (x : 𝓞 L) : toL L n (algebraMap (𝓞 L) (Rg L n) x) = algebraMap (𝓞 L) L x :=
  IsLocalization.Away.lift_eq _ _ _

theorem tr_alg {m n : ℕ} (h : m ≤ n) (x : 𝓞 L) :
    tr L h (algebraMap (𝓞 L) (Rg L m) x) = algebraMap (𝓞 L) (Rg L n) x :=
  IsLocalization.Away.lift_eq _ _ _

theorem hom_ext {m : ℕ} {T : Type*} [CommRing T] {f g : Rg L m →+* T}
    (h : ∀ x : 𝓞 L, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers (sf L m)) (RingHom.ext h)

theorem toL_injective (n : ℕ) : Function.Injective (toL L n) := by
  unfold toL IsLocalization.Away.lift
  rw [IsLocalization.lift_injective_iff]
  intro a b
  constructor
  · intro h
    rw [IsLocalization.injective (Rg L n)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (sf_ne_zero L n)) h]
  · intro h
    rw [FaithfulSMul.algebraMap_injective (𝓞 L) L h]

/-- The diagram `n ↦ 𝓞_L[1/n!]`. -/
noncomputable def ringDiag : ℕ ⥤ CommRingCat.{0} where
  obj n := CommRingCat.of (Rg L n)
  map f := CommRingCat.ofHom (tr L (leOfHom f))
  map_id n := by
    apply CommRingCat.hom_ext
    exact hom_ext L (fun x => by simp [tr_alg])
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact hom_ext L (fun x => by simp [tr_alg])

/-- `L` as a cocone over `ringDiag`. -/
noncomputable def ringCocone : Cocone (ringDiag L) where
  pt := CommRingCat.of L
  ι :=
    { app n := CommRingCat.ofHom (toL L n)
      naturality m n f := by
        apply CommRingCat.hom_ext
        exact hom_ext L (fun x => by simp [ringDiag, tr_alg, toL_alg]) }

/-- **`L = colim_n 𝓞_L[1/n!]`.** -/
noncomputable def ringCoconeIsColimit : IsColimit (ringCocone L) := by
  haveI : ReflectsColimit (ringDiag L) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : L)
    haveI := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    haveI := Algebra.IsAlgebraic.trans ℤ ℚ L
    obtain ⟨y, hy0, hy⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ)
      (Algebra.IsAlgebraic.isAlgebraic x)
    let a : 𝓞 L := ⟨y • x, hy⟩
    have ha : algebraMap (𝓞 L) L a = (y : L) * x := by rw [← zsmul_eq_mul]; rfl
    obtain ⟨q, hq⟩ : (y : ℤ) ∣ (y.natAbs.factorial : ℤ) :=
      (Int.dvd_natAbs.2 dvd_rfl).trans (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial
        (Int.natAbs_pos.2 hy0) le_rfl))
    refine ⟨y.natAbs, (algebraMap (𝓞 L) (Rg L y.natAbs) (a * (q : 𝓞 L)) *
      IsLocalization.Away.invSelf (sf L y.natAbs) : Rg L y.natAbs), ?_⟩
    show x = toL L y.natAbs _
    have hinv : toL L y.natAbs (IsLocalization.Away.invSelf (sf L y.natAbs)) *
        algebraMap (𝓞 L) L (sf L y.natAbs) = 1 := by
      rw [← toL_alg, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
    have hinv' := eq_inv_of_mul_eq_one_left hinv
    have hn : algebraMap (𝓞 L) L (sf L y.natAbs) = (y : L) * (q : L) := by
      simp only [sf, map_natCast]
      exact_mod_cast hq
    have hsf : algebraMap (𝓞 L) L (sf L y.natAbs) ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)).2 (sf_ne_zero L _)
    have hy' : (y : L) ≠ 0 := by exact_mod_cast hy0
    have hq' : (q : L) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hn; exact hsf hn
    rw [map_mul, toL_alg, hinv', map_mul, ha, map_intCast, hn]
    field_simp
  · intro n x y h
    have h' : toL L n x = toL L n y := h
    exact ⟨n, 𝟙 n, by rw [toL_injective L n h']⟩

theorem tr_toL {m n : ℕ} (h : m ≤ n) : (toL L n).comp (tr L h) = toL L m :=
  hom_ext L (fun x => by simp [tr_alg, toL_alg])

theorem tr_tr {m n p : ℕ} (h₁ : m ≤ n) (h₂ : n ≤ p) : (tr L h₂).comp (tr L h₁) = tr L (h₁.trans h₂) :=
  hom_ext L (fun x => by simp [tr_alg])

theorem tr_refl (m : ℕ) : tr L (le_refl m) = RingHom.id _ :=
  hom_ext L (fun x => by simp [tr_alg])

/-- The diagram `n ↦ Spec 𝓞_L[1/n!]` (a cofiltered diagram of affine schemes). -/
noncomputable def specDiag : ℕᵒᵖ ⥤ Scheme.{0} where
  obj n := Spec (CommRingCat.of (Rg L n.unop))
  map f := Spec.map (CommRingCat.ofHom (tr L (leOfHom f.unop)))
  map_id n := by
    rw [show leOfHom (𝟙 n).unop = le_refl n.unop from rfl, tr_refl, CommRingCat.ofHom_id,
      Spec.map_id]
  map_comp f g := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, tr_tr]

/-- `Spec L` as a cone over `specDiag`. -/
noncomputable def specCone : Cone (specDiag L) where
  pt := Spec (CommRingCat.of L)
  π :=
    { app n := Spec.map (CommRingCat.ofHom (toL L n.unop))
      naturality m n f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, specDiag]
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, tr_toL] }

theorem specCone_π_app (n : ℕᵒᵖ) :
    (specCone L).π.app n = Spec.map (CommRingCat.ofHom (toL L n.unop)) := rfl

/-- **`Spec L = lim_n Spec 𝓞_L[1/n!]`.** -/
noncomputable def specConeIsLimit : IsLimit (specCone L) := by
  have h := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit L).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro m n f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Iso.refl_hom, Category.id_comp]

instance specDiag_isAffineHom {i j : ℕᵒᵖ} (f : i ⟶ j) : IsAffineHom ((specDiag L).map f) :=
  show IsAffineHom (Spec.map _) from inferInstance

instance specDiag_compactSpace (i : ℕᵒᵖ) : CompactSpace ((specDiag L).obj i) :=
  show CompactSpace (Spec _) from inferInstance

instance specDiag_quasiSeparatedSpace (i : ℕᵒᵖ) : QuasiSeparatedSpace ((specDiag L).obj i) :=
  show QuasiSeparatedSpace (Spec _) from inferInstance

/-- **N1-g1 `AbVarSpreadsOut`, core form (unfolded statement).**  From the leaves 8.8.2 (ii),
8.10.5 (xii) and descent of smoothness for the system `n ↦ Spec 𝓞_L[1/n!]`. -/
theorem abVarSpreadsOut_core (h882 : EGAIV_8_8_2_ii) (hpr : EGAIV_8_10_5_xii)
    (L : Type) [Field L] [NumberField L] (hsm : SmoothDescendsFor (specDiag L) (specCone L))
    (B : PkgI3.AbVar L) :
    ∃ f : 𝓞 L, f ≠ 0 ∧
      ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
        [IsScalarTower (𝓞 L) R L],
        ∃ (G : Over (Spec (CommRingCat.of R))) (_ : GrpObj G) (_ : Smooth G.hom)
          (_ : IsProper G.hom)
          (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
          letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
            Functor.grpObjObj
          IsMonHom gen.hom := by
  have key : ∃ (k : ℕᵒᵖ) (G : Over (Spec (CommRingCat.of (Rg L k.unop)))) (_ : GrpObj G)
      (_ : Smooth G.hom) (_ : IsProper G.hom)
      (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (toL L k.unop)))).obj G ≅ B.X),
      letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (toL L k.unop)))).obj G) :=
        Functor.grpObjObj
      IsMonHom gen.hom := by
    letI : GrpObj (C := Over (specCone L).pt) B.X := B.grp
    exact exists_grpObj_descend' (specDiag L) (specCone L) (specConeIsLimit L) h882 hpr hsm B.X
  obtain ⟨k, G, hG, hGs, hGp, gen, hgen⟩ := key
  refine ⟨sf L k.unop, sf_ne_zero L _, fun R _ _ _ _ _ => ?_⟩
  let φa : Rg L k.unop →ₐ[𝓞 L] R :=
    (IsLocalization.algEquiv (Submonoid.powers (sf L k.unop)) (Rg L k.unop) R).toAlgHom
  let φ : Rg L k.unop →+* R := φa.toRingHom
  have hφ : ∀ x : 𝓞 L, φ (algebraMap _ _ x) = algebraMap _ _ x := φa.commutes
  let ψ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Rg L k.unop)) :=
    Spec.map (CommRingCat.ofHom φ)
  have w : Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ ψ =
      Spec.map (CommRingCat.ofHom (toL L k.unop)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine hom_ext L (fun x => ?_)
    rw [RingHom.coe_comp, Function.comp_apply, hφ, toL_alg]
    exact (IsScalarTower.algebraMap_apply (𝓞 L) R L x).symm
  let θ := pbNat (Spec.map (CommRingCat.ofHom (algebraMap R L))) ψ
    (Spec.map (CommRingCat.ofHom (toL L k.unop))) w
  letI : GrpObj ((Over.pullback ψ).obj G) := Functor.grpObjObj
  refine ⟨(Over.pullback ψ).obj G, Functor.grpObjObj, inferInstance, inferInstance,
    θ.app G ≪≫ gen, ?_⟩
  have hm := compatM_transport (Over.pullback ψ)
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (Over.pullback (Spec.map (CommRingCat.ofHom (toL L k.unop)))) θ gen
    (compatM_of_isMonHom (Over.pullback (Spec.map (CommRingCat.ofHom (toL L k.unop)))) gen hgen)
  have hu := compatU_transport (Over.pullback ψ)
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (Over.pullback (Spec.map (CommRingCat.ofHom (toL L k.unop)))) θ gen
    (compatU_of_isMonHom (Over.pullback (Spec.map (CommRingCat.ofHom (toL L k.unop)))) gen hgen)
  exact isMonHom_of_compat (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (M' := (Over.pullback ψ).obj G) (θ.app G ≪≫ gen) hm hu

/-- **N1-g1 `AbVarSpreadsOut` from the three EGA IV leaves (unfolded statement).**  For an
abelian variety `B` over a number field `L` there is `0 ≠ f ∈ 𝓞_L` (namely `f = n!`) such that for
every presentation `R` of `𝓞_L[1/f]` there is a smooth proper group scheme `G` over `R` whose
generic fibre is identified with `B` as a group scheme. -/
theorem abVarSpreadsOut_of_ega (h882 : EGAIV_8_8_2_ii) (hpr : EGAIV_8_10_5_xii)
    (hsm : EGAIV_17_7_8_ii) (L : Type) [Field L] [NumberField L] (B : PkgI3.AbVar L) :
    ∃ f : 𝓞 L, f ≠ 0 ∧
      ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
        [IsScalarTower (𝓞 L) R L],
        ∃ (G : Over (Spec (CommRingCat.of R))) (_ : GrpObj G) (_ : Smooth G.hom)
          (_ : IsProper G.hom)
          (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
          letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
            Functor.grpObjObj
          IsMonHom gen.hom :=
  abVarSpreadsOut_core h882 hpr L
    (smoothDescendsFor_of_ega (specDiag L) (specCone L) (specConeIsLimit L) hsm) B

/-- `L` is the fraction field of `𝓞_L[1/n!]` (via `toL`). -/
theorem isFractionRing_toL (n : ℕ) :
    letI := (toL L n).toAlgebra
    IsFractionRing (Rg L n) L := by
  letI := (toL L n).toAlgebra
  haveI : IsScalarTower (𝓞 L) (Rg L n) L :=
    IsScalarTower.of_algebraMap_eq (fun x => (toL_alg L n x).symm)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (sf L n))
    (Rg L n) L

/-- **Descent of smoothness for `n ↦ Spec 𝓞_L[1/n!]`, from the pointwise glue
`SmoothAtLocalizationBaseChange`** (Mathlib's smooth locus is open; `L` is a localization of every
`𝓞_L[1/n!]`). -/
theorem smoothDescendsFor_specDiag (hA : SmoothAtLocalizationBaseChange) :
    SmoothDescendsFor (specDiag L) (specCone L) := by
  refine smoothDescendsFor_of_pointwise (specDiag L) (specCone L) (specConeIsLimit L) ?_
  intro i Xi _ y hy
  letI := (toL L i.unop).toAlgebra
  haveI := isFractionRing_toL L i.unop
  exact hA (Rg L i.unop) L (nonZeroDivisors (Rg L i.unop)) Xi.left Xi.hom y hy

/-- **N1-g1 `AbVarSpreadsOut` from the EGA IV leaves 8.8.2 (ii), 8.10.5 (xii) and the pointwise
glue `SmoothAtLocalizationBaseChange` (unfolded statement)**: the smoothness leaf 17.7.8 (ii) is not
needed. -/
theorem abVarSpreadsOut_of_ega_loc (h882 : EGAIV_8_8_2_ii) (hpr : EGAIV_8_10_5_xii)
    (hA : SmoothAtLocalizationBaseChange) (L : Type) [Field L] [NumberField L]
    (B : PkgI3.AbVar L) :
    ∃ f : 𝓞 L, f ≠ 0 ∧
      ∀ (R : Type) [CommRing R] [Algebra (𝓞 L) R] [IsLocalization.Away f R] [Algebra R L]
        [IsScalarTower (𝓞 L) R L],
        ∃ (G : Over (Spec (CommRingCat.of R))) (_ : GrpObj G) (_ : Smooth G.hom)
          (_ : IsProper G.hom)
          (gen : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G ≅ B.X),
          letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj G) :=
            Functor.grpObjObj
          IsMonHom gen.hom :=
  abVarSpreadsOut_core h882 hpr L (smoothDescendsFor_specDiag L hA) B

end ZInQ.Contrib.SpreadOut.NF
