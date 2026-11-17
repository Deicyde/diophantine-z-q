import Mathlib

/-!
# group-law: `Spec R_𝔭` as the limit of the `Spec R[1/s]`, `s ∉ 𝔭`

Verbatim copy (Mathlib only) of gt-blr's section `Diagram` and lemma `map_ej` from
`ZInQKernel/Contrib/OneProof/BLRLocalizes.lean` (namespace `GapBLR`), placed in the namespace
`ZInQ.Contrib.GroupLaw.Loc` so that the group-law modules do not import `BLRLocalizes` (which imports
`OneProof/H/TailZ24`): a fold that uses them from `TailZ23` would otherwise create an import cycle.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.dupNamespace false

open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.GroupLaw.Loc

/-! ## `R_𝔭` as a cofiltered limit of `Spec R[1/s]`, `s ∉ 𝔭` -/

section Diagram

variable {R : Type} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]

/-- The index set: elements `s ∉ 𝔭`, preordered by divisibility. -/
structure Idx where
  /-- the element -/
  s : R
  hs : s ∉ 𝔭

instance : Preorder (Idx 𝔭) where
  le a b := a.s ∣ b.s
  le_refl a := dvd_refl _
  le_trans _ _ _ := dvd_trans

instance : IsDirectedOrder (Idx 𝔭) where
  directed a b := ⟨⟨a.s * b.s, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim a.hs b.hs⟩,
    dvd_mul_right _ _, dvd_mul_left _ _⟩

instance : Nonempty (Idx 𝔭) := ⟨⟨1, fun h => (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 h)⟩⟩

variable {𝔭}

/-- `R[1/s]`. -/
abbrev Loc (a : Idx 𝔭) : Type := Localization.Away a.s

theorem isUnit_le {a b : Idx 𝔭} (h : a ≤ b) : IsUnit (algebraMap R (Loc b) a.s) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit b.s)

/-- The transition map `R[1/s] → R[1/t]` for `s ∣ t`. -/
noncomputable def tr {a b : Idx 𝔭} (h : a ≤ b) : Loc a →+* Loc b :=
  IsLocalization.Away.lift a.s (isUnit_le h)

theorem tr_alg {a b : Idx 𝔭} (h : a ≤ b) (x : R) :
    tr h (algebraMap R (Loc a) x) = algebraMap R (Loc b) x :=
  IsLocalization.Away.lift_eq _ _ _

theorem hom_ext' {a : Idx 𝔭} {T : Type*} [CommRing T] {f g : Loc a →+* T}
    (h : ∀ x : R, f (algebraMap R (Loc a) x) = g (algebraMap R (Loc a) x)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers a.s) (RingHom.ext h)

variable (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭] [IsLocalization.AtPrime R𝔭 𝔭]

theorem isUnit_P (a : Idx 𝔭) : IsUnit (algebraMap R R𝔭 a.s) :=
  IsLocalization.map_units R𝔭 (⟨a.s, a.hs⟩ : 𝔭.primeCompl)

/-- `R[1/s] → R_𝔭`. -/
noncomputable def toP (a : Idx 𝔭) : Loc a →+* R𝔭 :=
  IsLocalization.Away.lift a.s (isUnit_P R𝔭 a)

theorem toP_alg (a : Idx 𝔭) (x : R) : toP R𝔭 a (algebraMap R (Loc a) x) = algebraMap R R𝔭 x :=
  IsLocalization.Away.lift_eq _ _ _

variable (𝔭)

/-- The diagram `s ↦ R[1/s]`. -/
noncomputable def ringDiag : Idx 𝔭 ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Loc a)
  map f := CommRingCat.ofHom (tr (leOfHom f))
  map_id a := by
    apply CommRingCat.hom_ext
    exact hom_ext' (fun x => by simp [tr_alg])
  map_comp f g := by
    apply CommRingCat.hom_ext
    exact hom_ext' (fun x => by simp [tr_alg])

/-- `R_𝔭` as a cocone. -/
noncomputable def ringCocone : Cocone (ringDiag 𝔭) where
  pt := CommRingCat.of R𝔭
  ι :=
    { app a := CommRingCat.ofHom (toP R𝔭 a)
      naturality a b f := by
        apply CommRingCat.hom_ext
        exact hom_ext' (fun x => by simp [ringDiag, tr_alg, toP_alg]) }

/-- **`R_𝔭 = colim_{s ∉ 𝔭} R[1/s]`.** -/
noncomputable def ringCoconeIsColimit : IsColimit (ringCocone 𝔭 R𝔭) := by
  haveI : ReflectsColimit (ringDiag 𝔭) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : R𝔭)
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl x
    let a : Idx 𝔭 := ⟨t.1, t.2⟩
    refine ⟨a, (IsLocalization.mk' (Loc a) r (⟨t.1, Submonoid.mem_powers _⟩ : Submonoid.powers a.s) :
      Loc a), ?_⟩
    show _ = toP R𝔭 a _
    rw [IsLocalization.mk'_eq_iff_eq_mul, ← toP_alg R𝔭 a, ← toP_alg R𝔭 a, ← map_mul]
    congr 1
    exact (IsLocalization.mk'_spec (Loc a) r (⟨t.1, Submonoid.mem_powers _⟩ : Submonoid.powers a.s)).symm
  · intro a x' y' h
    let x : Loc a := x'
    let y : Loc a := y'
    have h' : toP R𝔭 a x = toP R𝔭 a y := h
    obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hz0⟩ := IsLocalization.mk'_surjective (Submonoid.powers a.s) (x - y)
    have hz : IsLocalization.mk' (Loc a) r (⟨_, n, rfl⟩ : Submonoid.powers a.s) = x - y := hz0
    have h0 : toP R𝔭 a (x - y) = 0 := by rw [map_sub, h', sub_self]
    have hr : algebraMap R R𝔭 r = 0 := by
      rw [← toP_alg R𝔭 a, ← IsLocalization.mk'_spec (Loc a) r (⟨_, n, rfl⟩ : Submonoid.powers a.s), map_mul, hz, h0, zero_mul]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl R𝔭 r).1 hr
    let b : Idx 𝔭 := ⟨a.s * m.1, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim a.hs m.2⟩
    have hab : a ≤ b := dvd_mul_right _ _
    refine ⟨b, homOfLE hab, ?_⟩
    show tr hab x = tr hab y
    rw [← sub_eq_zero, ← map_sub, ← hz]
    have hmu : IsUnit (algebraMap R (Loc b) m.1) :=
      isUnit_of_dvd_unit (map_dvd _ (dvd_mul_left m.1 a.s)) (IsLocalization.Away.algebraMap_isUnit b.s)
    have hrb : algebraMap R (Loc b) r = 0 := by
      have : algebraMap R (Loc b) (m.1 * r) = 0 := by rw [hm, map_zero]
      rw [map_mul] at this
      exact (hmu.mul_right_eq_zero).1 this
    have hsu : IsUnit (algebraMap R (Loc b) (a.s ^ n)) := by rw [map_pow]; exact (isUnit_le hab).pow n
    have key := congrArg (tr hab) (IsLocalization.mk'_spec (Loc a) r (⟨_, n, rfl⟩ : Submonoid.powers a.s))
    rw [map_mul, tr_alg, tr_alg, hrb] at key
    exact (hsu.mul_left_eq_zero).1 key

/-- The diagram `s ↦ Spec R[1/s]`. -/
noncomputable def specDiag : (Idx 𝔭)ᵒᵖ ⥤ Scheme.{0} where
  obj a := Spec (CommRingCat.of (Loc a.unop))
  map f := Spec.map (CommRingCat.ofHom (tr (leOfHom f.unop)))
  map_id a := by
    rw [← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    exact hom_ext' (fun x => by simp [tr_alg])
  map_comp f g := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact hom_ext' (fun x => by simp [tr_alg])

/-- `Spec R_𝔭` as a cone. -/
noncomputable def specCone : Cone (specDiag 𝔭) where
  pt := Spec (CommRingCat.of R𝔭)
  π :=
    { app a := Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop))
      naturality a b f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, specDiag]
        rw [← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        exact hom_ext' (fun x => by simp [tr_alg, toP_alg]) }

theorem specCone_π_app (a : (Idx 𝔭)ᵒᵖ) :
    (specCone 𝔭 R𝔭).π.app a = Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop)) := rfl

/-- **`Spec R_𝔭 = lim_{s ∉ 𝔭} Spec R[1/s]`.** -/
noncomputable def specConeIsLimit : IsLimit (specCone 𝔭 R𝔭) := by
  have h := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit 𝔭 R𝔭).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro m n f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Iso.refl_hom, Category.id_comp]

instance specDiag_isAffineHom {i j : (Idx 𝔭)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((specDiag 𝔭).map f) :=
  show IsAffineHom (Spec.map _) from inferInstance

instance specDiag_compactSpace (i : (Idx 𝔭)ᵒᵖ) : CompactSpace ((specDiag 𝔭).obj i) :=
  show CompactSpace (Spec _) from inferInstance

instance specDiag_quasiSeparatedSpace (i : (Idx 𝔭)ᵒᵖ) :
    QuasiSeparatedSpace ((specDiag 𝔭).obj i) :=
  show QuasiSeparatedSpace (Spec _) from inferInstance

variable {𝔭}

/-- `Spec R[1/s] → Spec R`, an open immersion. -/
noncomputable def ej (a : (Idx 𝔭)ᵒᵖ) : (specDiag 𝔭).obj a ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Loc a.unop)))

instance (a : (Idx 𝔭)ᵒᵖ) : IsOpenImmersion (ej a) :=
  IsOpenImmersion.of_isLocalization a.unop.s

theorem π_ej (a : (Idx 𝔭)ᵒᵖ) : (specCone 𝔭 R𝔭).π.app a ≫ ej a =
    Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) := by
  refine (Spec.map_comp (CommRingCat.ofHom (algebraMap R (Loc a.unop)))
    (CommRingCat.ofHom (toP R𝔭 a.unop))).symm.trans ?_
  congr 1
  apply CommRingCat.hom_ext
  ext x
  exact toP_alg R𝔭 a.unop x

theorem toP_ej (a : (Idx 𝔭)ᵒᵖ) : Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop)) ≫ ej a =
    Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) :=
  π_ej R𝔭 a


end Diagram

section MapEj

variable {R : Type} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]

theorem map_ej {a b : (Idx 𝔭)ᵒᵖ} (f : a ⟶ b) : (specDiag 𝔭).map f ≫ ej b = ej a := by
  refine (Spec.map_comp (CommRingCat.ofHom (algebraMap R (Loc b.unop)))
    (CommRingCat.ofHom (tr (leOfHom f.unop)))).symm.trans ?_
  congr 1
  apply CommRingCat.hom_ext
  ext x
  exact tr_alg (leOfHom f.unop) x

end MapEj

end ZInQ.Contrib.GroupLaw.Loc
