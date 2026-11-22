import ZInQKernel.Contrib.OneProof.H.TailZ24

/-!
# gt-blr: BLR §1.2 Prop. 4 (Néron models localize), proved

`CToPrinted.BLR_1_2_4` (field `blr_1_2_4` of the open research bundle, `ZInQKernel/Contrib/OneProof/H/TailZ19.lean`) is
Bosch–Lütkebohmert–Raynaud's Prop. 1.2/4: a smooth separated quasi-compact `R`-model `X` over a Dedekind domain
`R` is a Néron model (`CToPrinted.IsNeronModelOver`) iff `X ⊗_R R_𝔭` is one over `R_𝔭` for every maximal `𝔭`.
This file proves it, `GapBLR.blr_1_2_4 : CToPrinted.BLR_1_2_4`, from Mathlib and the chain alone (both
directions hold for any commutative ring `R` with fraction field `K`). The chain's consumers use only `.mp`;
that half is also stated and proved on its own (`GapBLR.BLR_1_2_4_MP`, `GapBLR.blr_1_2_4_mp`).

* `.mp` (`isNeronModelOver_localization`). Let `Y` be smooth over `R_𝔭`.
  Uniqueness (`uqA`): `Y_K → Y` is scheme-theoretically dominant (flat base change of `Spec K → Spec R_𝔭`,
  Mathlib's `IsSchemeTheoreticallyDominant.of_isPullback`), `Y_K` is reduced (smooth over a field, the chain's
  `LeafQM.AV.R1UnivRigid.isReduced_of_smooth`), so `Y` is reduced and two maps to the separated `X` agreeing on
  `Y_K` agree (`ext_of_isDominant_of_isSeparated`).
  Existence on an affine open `V` (`local_ext`): `Spec R_𝔭 = lim_{s ∉ 𝔭} Spec R[1/s]` (`specConeIsLimit`);
  EGA IV 8.8.2 (ii) and 17.7.8 (ii) (proved in `ZInQKernel/Contrib/CloudW01Spread`) give a smooth `W` over some
  `Spec R[1/s]` with `V = W ×_{R[1/s]} R_𝔭` (`exists_spread`); `W` is smooth over `R` (`Spec R[1/s] → Spec R` is an
  open immersion) with generic fibre `V_K`, so the Néron property of `X` over `R` extends `V_K → X` to `W`, hence
  to `V`. Gluing over the affine cover by uniqueness (`glue_cover`).
* `.mpr` (`isNeronModelOver_of_local`). Uniqueness as above over `R`. Existence near a point `x` of a smooth
  `R`-scheme `Y` (`local_pt`): take an affine open `V ∋ x` and a maximal `𝔭` over the image of `x`; the Néron
  property at `𝔭` extends the map on `V ⊗_R R_𝔭`; since `V ⊗_R R_𝔭 = lim_{s ∉ 𝔭} V ⊗_R R[1/s]`
  (`bcConeIsLimit`) and `X` is locally of finite presentation, the extension comes from some `V ⊗_R R[1/s]`
  (Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`, Stacks 01ZC), i.e. from the open
  `V ∩ y⁻¹D(s) ∋ x`. Glue over these opens by uniqueness.

`neronLocalizesDVR_proved : ReductGlue.NeronLocalizesDVR` follows by c-to-printed's
`CToPrinted.neronLocalizesDVR_of_printed`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry

namespace GapBLR

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

/-! ## Spreading out a smooth affine `R_𝔭`-scheme -/

open ZInQ.Contrib.SpreadOut in
/-- **Spreading out.** A smooth affine scheme `V` over `Spec R_𝔭` is the base change of a smooth scheme
`W` over some `Spec R[1/s]`, `s ∉ 𝔭` (EGA IV 8.8.2 (ii) and 17.7.8 (ii), both proved in
`ZInQKernel/Contrib/CloudW01Spread`). -/
theorem exists_spread (V : Scheme.{0}) [IsAffine V] (v : V ⟶ Spec (CommRingCat.of R𝔭)) [Smooth v] :
    ∃ (a : (Idx 𝔭)ᵒᵖ) (W : Over ((specDiag 𝔭).obj a)) (φ : V ⟶ W.left),
      Smooth W.hom ∧ IsPullback φ v W.hom ((specCone 𝔭 R𝔭).π.app a) := by
  haveI : IsAffineHom v := inferInstance
  haveI : LocallyOfFinitePresentation (Over.mk v).hom := (inferInstance : LocallyOfFinitePresentation v)
  haveI : QuasiCompact (Over.mk v).hom := (inferInstance : QuasiCompact v)
  haveI : QuasiSeparated (Over.mk v).hom := (inferInstance : QuasiSeparated v)
  obtain ⟨i, Xi, hl, hq, hs, ⟨e⟩⟩ := EGAIV_8_8_2_ii_proof (Idx 𝔭) (specDiag 𝔭) (specCone 𝔭 R𝔭)
    (specConeIsLimit 𝔭 R𝔭) (Over.mk v) (inferInstance : LocallyOfFinitePresentation v)
    (inferInstance : QuasiCompact v) (inferInstance : QuasiSeparated v)
  haveI : Smooth (Over.mk v).hom := ‹Smooth v›
  have hsm : Smooth ((Over.pullback ((specCone 𝔭 R𝔭).π.app i)).obj Xi).hom := @smooth_of_iso _ _ (Over.mk v) e ‹Smooth v›
  obtain ⟨j, a, hj⟩ := EGAIV_17_7_8_ii_proof (Idx 𝔭) (specDiag 𝔭) (specCone 𝔭 R𝔭)
    (specConeIsLimit 𝔭 R𝔭) i Xi hl hq hs hsm
  have hw : e.inv.left ≫ pullback.snd Xi.hom ((specCone 𝔭 R𝔭).π.app i) = v := Over.w e.inv
  have hπ : (specCone 𝔭 R𝔭).π.app j ≫ (specDiag 𝔭).map a = (specCone 𝔭 R𝔭).π.app i :=
    (specCone 𝔭 R𝔭).w a
  have hc0 : (e.inv.left ≫ pullback.fst Xi.hom ((specCone 𝔭 R𝔭).π.app i)) ≫ Xi.hom =
      v ≫ (specCone 𝔭 R𝔭).π.app i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
    exact rfl
  have hcomm : (e.inv.left ≫ pullback.fst Xi.hom ((specCone 𝔭 R𝔭).π.app i)) ≫ Xi.hom =
      (v ≫ (specCone 𝔭 R𝔭).π.app j) ≫ (specDiag 𝔭).map a :=
    hc0.trans ((congrArg (fun t => v ≫ t) hπ.symm).trans (Category.assoc _ _ _).symm)
  let φ : V ⟶ pullback Xi.hom ((specDiag 𝔭).map a) := pullback.lift _ _ hcomm
  refine ⟨j, (Over.pullback ((specDiag 𝔭).map a)).obj Xi, φ, hj, ?_⟩
  have houter : IsPullback (e.inv.left ≫ pullback.fst Xi.hom ((specCone 𝔭 R𝔭).π.app i)) v Xi.hom
      ((specCone 𝔭 R𝔭).π.app i) :=
    IsPullback.of_iso_pullback ⟨hc0⟩ ((Over.forget _).mapIso e.symm) rfl hw
  have h1 : φ ≫ pullback.fst _ _ = e.inv.left ≫ pullback.fst Xi.hom ((specCone 𝔭 R𝔭).π.app i) :=
    pullback.lift_fst _ _ _
  refine IsPullback.of_right (h₁₂ := pullback.fst Xi.hom ((specDiag 𝔭).map a))
    (h₂₂ := (specDiag 𝔭).map a) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [h1]; erw [hπ]; exact houter

end Diagram


/-! ## General uniqueness and gluing over a base `Spec A`, `A ⊆ K` -/

section General

variable {K : Type} [Field K]

/-- `Spec K → Spec A` is scheme-theoretically dominant when `A → K` is injective. -/
theorem isSTD_of_injective (A : Type) [CommRing A] [Algebra A K]
    (hinj : Function.Injective (algebraMap A K)) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  haveI : _root_.IsReduced A := isReduced_of_injective (algebraMap A K) hinj
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
    rw [isDominant_iff, Spec.map_base]
    show DenseRange (PrimeSpectrum.comap (algebraMap A K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [hinj (hx.trans (map_zero _).symm)]
    exact zero_mem _
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- **Uniqueness over `Spec A`.** Two maps from a smooth `A`-scheme to a separated `S`-scheme, equal over `S`
and on the generic fibre, are equal. -/
theorem uqA (A : Type) [CommRing A] [Algebra A K] (hinj : Function.Injective (algebraMap A K))
    {S : Scheme.{0}} (X : Over S) [IsSeparated X.hom]
    {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A)) [Smooth w]
    {P : Scheme.{0}} (p : P ⟶ W) (q : P ⟶ Spec (CommRingCat.of K))
    (H : IsPullback p q w (Spec.map (CommRingCat.ofHom (algebraMap A K))))
    (g₁ g₂ : W ⟶ X.left) (h₁₂ : g₁ ≫ X.hom = g₂ ≫ X.hom) (h : p ≫ g₁ = p ≫ g₂) : g₁ = g₂ := by
  haveI := isSTD_of_injective A hinj
  haveI : Smooth q := MorphismProperty.of_isPullback H ‹Smooth w›
  haveI : IsReduced P := LeafQM.AV.R1UnivRigid.isReduced_of_smooth q
  haveI : IsSchemeTheoreticallyDominant p := IsSchemeTheoreticallyDominant.of_isPullback H.flip
  haveI : QuasiCompact p := MorphismProperty.of_isPullback H.flip inferInstance
  haveI : IsReduced W := IsSchemeTheoreticallyDominant.isReduced p
  exact ext_of_isDominant_of_isSeparated X.hom h₁₂ p h

/-- **Gluing over `Spec A`.** Extensions on the pieces of an open cover of a smooth `A`-scheme `Y` that agree
with `b` on the generic fibres glue to an extension of `b`. -/
theorem glue_cover (A : Type) [CommRing A] [Algebra A K] (hinj : Function.Injective (algebraMap A K))
    {S : Scheme.{0}} (X : Over S) [IsSeparated X.hom] (jA : Spec (CommRingCat.of A) ⟶ S)
    {Y : Scheme.{0}} (y : Y ⟶ Spec (CommRingCat.of A)) [Smooth y]
    (b : pullback y (Spec.map (CommRingCat.ofHom (algebraMap A K))) ⟶ X.left)
    (𝒰 : Y.OpenCover) (g : ∀ i, 𝒰.X i ⟶ X.left)
    (hg1 : ∀ i, g i ≫ X.hom = (𝒰.f i ≫ y) ≫ jA)
    (hg2 : ∀ i, pullback.fst (𝒰.f i ≫ y) (Spec.map (CommRingCat.ofHom (algebraMap A K))) ≫ g i =
      pullback.lift (pullback.fst _ _ ≫ 𝒰.f i) (pullback.snd _ _)
        (by rw [Category.assoc]; exact pullback.condition) ≫ b) :
    ∃ f : Y ⟶ X.left, f ≫ X.hom = y ≫ jA ∧
      pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap A K))) ≫ f = b := by
  let kK := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let m : ∀ i, pullback (𝒰.f i ≫ y) kK ⟶ pullback y kK := fun i =>
    pullback.lift (pullback.fst _ _ ≫ 𝒰.f i) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have compat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    intro i j
    let w := pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ y
    have hw' : pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j ≫ y = w := by
      simp only [w, ← Category.assoc, pullback.condition]
    let n : pullback w kK ⟶ pullback (𝒰.f i ≫ y) kK :=
      pullback.lift (pullback.fst w kK ≫ pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd w kK)
        (by rw [Category.assoc]; exact pullback.condition)
    let n' : pullback w kK ⟶ pullback (𝒰.f j ≫ y) kK :=
      pullback.lift (pullback.fst w kK ≫ pullback.snd (𝒰.f i) (𝒰.f j)) (pullback.snd w kK)
        (by rw [Category.assoc, hw']; exact pullback.condition)
    have hnn : n ≫ m i = n' ≫ m j := by
      apply pullback.hom_ext
      · simp only [n, n', m, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [pullback.condition]
      · simp only [n, n', m, Category.assoc, pullback.lift_snd]
    refine uqA A hinj X w (pullback.fst w kK) (pullback.snd w kK)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hg1 i, hg1 j]
      simp only [Category.assoc]
      rw [pullback.condition_assoc]
    · have e1 : pullback.fst w kK ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = n ≫ m i ≫ b := by
        rw [← hg2 i, ← Category.assoc, ← Category.assoc, pullback.lift_fst, Category.assoc]
      have e2 : pullback.fst w kK ≫ pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j = n' ≫ m j ≫ b := by
        rw [← hg2 j, ← Category.assoc, ← Category.assoc, pullback.lift_fst, Category.assoc]
      rw [e1, e2, ← Category.assoc, hnn, Category.assoc]
  refine ⟨𝒰.glueMorphisms g compat, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒰 _ _ (fun i => ?_)
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hg1 i, Category.assoc]
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ (pullback.fst y kK)) _ _ (fun (i : 𝒰.I₀) => ?_)
    let F1 := pullback.fst (pullback.fst y kK) (𝒰.f i)
    let F2 := pullback.snd (pullback.fst y kK) (𝒰.f i)
    have hF : F1 ≫ pullback.fst y kK = F2 ≫ 𝒰.f i := pullback.condition
    let ψ : pullback (pullback.fst y kK) (𝒰.f i) ⟶ pullback (𝒰.f i ≫ y) kK :=
      pullback.lift F2 (F1 ≫ pullback.snd y kK)
        (by rw [← Category.assoc, ← hF, Category.assoc, pullback.condition, Category.assoc])
    have hψ : ψ ≫ m i = F1 := by
      apply pullback.hom_ext
      · simp only [ψ, m, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
        exact hF.symm
      · simp only [ψ, m, Category.assoc, pullback.lift_snd]
    show F1 ≫ pullback.fst y kK ≫ 𝒰.glueMorphisms g compat = F1 ≫ b
    rw [← Category.assoc, hF, Category.assoc, Scheme.Cover.ι_glueMorphisms, ← hψ, Category.assoc,
      ← hg2 i, ← Category.assoc, pullback.lift_fst]

/-- The Néron property of `X` over `R`, against an arbitrary pullback square for the generic fibre. -/
theorem neron_ext {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {X : Over (Spec (CommRingCat.of R))} (hX : CToPrinted.IsNeronModelOver R K X)
    (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom] {P : Scheme.{0}} (p : P ⟶ Y.left)
    (q : P ⟶ Spec (CommRingCat.of K))
    (H : IsPullback p q Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (b : P ⟶ X.left) (hb : b ≫ X.hom = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ f : Y.left ⟶ X.left, f ≫ X.hom = Y.hom ∧ p ≫ f = b := by
  have hb' : (H.isoPullback.inv ≫ b) ≫ X.hom =
      pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [Category.assoc, hb, ← Category.assoc, IsPullback.isoPullback_inv_snd]
  let h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj Y ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X :=
    Over.homMk (pullback.lift _ _ hb') (pullback.lift_snd _ _ _)
  obtain ⟨f, hf⟩ := (hX.2.2.2.2 Y).2 h
  refine ⟨f.left, Over.w f, ?_⟩
  have h1 := congrArg (fun t => t.left ≫ pullback.fst X.hom
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hf
  simp only [Over.pullback_map_left, pullback.lift_fst, h, Over.homMk_left] at h1
  have h2 := congrArg (fun t => H.isoPullback.hom ≫ t) h1
  simp only [IsPullback.isoPullback_hom_fst_assoc, Iso.hom_inv_id_assoc] at h2
  exact h2

end General

/-! ## The Néron property, at `R` and at `R_𝔭` -/

section Main

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {𝔭 : Ideal R} [𝔭.IsPrime] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭] [IsLocalization.AtPrime R𝔭 𝔭]
  [Algebra R𝔭 K] [IsScalarTower R R𝔭 K]

include 𝔭

/-- `R_𝔭 → K` is injective. -/
theorem algebraMap_P_injective : Function.Injective (algebraMap R𝔭 K) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
  have h := IsLocalization.mk'_spec R𝔭 r t
  have h2 := congrArg (algebraMap R𝔭 K) h
  rw [map_mul, hz, zero_mul, ← IsScalarTower.algebraMap_apply] at h2
  have hr : r = 0 := (IsFractionRing.injective R K) (by rw [← h2, map_zero])
  subst hr; exact IsLocalization.mk'_zero _

/-- **Local existence.** For a smooth affine `R_𝔭`-scheme `V`, an `R`-morphism `V_K → X` extends to `V`. -/
theorem local_ext {X : Over (Spec (CommRingCat.of R))} (hX : CToPrinted.IsNeronModelOver R K X)
    (V : Scheme.{0}) [IsAffine V] (v : V ⟶ Spec (CommRingCat.of R𝔭)) [Smooth v]
    (b : pullback v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ⟶ X.left)
    (hb : b ≫ X.hom = pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ g : V ⟶ X.left, g ≫ X.hom = v ≫ Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) ∧
      pullback.fst v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫ g = b := by
  obtain ⟨a, W, φ, hW, Hφ⟩ := exists_spread (𝔭 := 𝔭) R𝔭 V v
  haveI := hW
  have Hφ' : IsPullback φ v W.hom (Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop))) := Hφ
  let V0 : Over (Spec (CommRingCat.of R)) := Over.mk (W.hom ≫ ej a)
  haveI : Smooth V0.hom := show Smooth (W.hom ≫ ej a) from inferInstance
  have hk : Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have H1 := IsPullback.of_hasPullback v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)))
  have H2 := H1.paste_horiz Hφ'
  have H3 : IsPullback (𝟙 W.left) W.hom (W.hom ≫ ej a) (ej a) :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp]⟩
  have H4 := H2.paste_horiz H3
  have H5 : IsPullback (pullback.fst v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫ φ)
      (pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)))) V0.hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    have e1 : (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)) ≫
        Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop))) ≫ ej a =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
      (Category.assoc _ _ _).trans ((congrArg (fun t => Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)) ≫ t)
        (toP_ej R𝔭 a)).trans hk)
    rw [Category.comp_id] at H4
    rw [← e1]
    exact H4
  obtain ⟨f0, hf0, hpf⟩ := neron_ext hX V0 _ _ H5 b hb
  refine ⟨φ ≫ f0, ?_, by rw [← Category.assoc]; exact hpf⟩
  rw [Category.assoc, hf0]
  show φ ≫ W.hom ≫ ej a = _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ej a) Hφ'.w).trans
    ((Category.assoc _ _ _).trans (congrArg (v ≫ ·) (toP_ej R𝔭 a))))

/-- **Existence of extensions** for an arbitrary smooth `R_𝔭`-scheme `Y` (local existence on the affine cover,
glued by `glue_cover`). -/
theorem glue_ext {X : Over (Spec (CommRingCat.of R))} [IsSeparated X.hom]
    (hX : CToPrinted.IsNeronModelOver R K X)
    (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of R𝔭)) [Smooth y]
    (b : pullback y (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ⟶ X.left)
    (hb : b ≫ X.hom = pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ g : Y ⟶ X.left, g ≫ X.hom = y ≫ Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) ∧
      pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫ g = b := by
  let 𝒰 := Y.affineCover
  have hm : ∀ i, (pullback.lift (pullback.fst (𝒰.f i ≫ y) (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫
      𝒰.f i) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition) ≫ b) ≫ X.hom =
      pullback.snd (𝒰.f i ≫ y) (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := fun i => by
    rw [Category.assoc, hb, ← Category.assoc, pullback.lift_snd]
  choose g hg1 hg2 using fun i => local_ext (𝔭 := 𝔭) R𝔭 hX (𝒰.X i) (𝒰.f i ≫ y) _ (hm i)
  exact glue_cover R𝔭 (algebraMap_P_injective (R := R) (𝔭 := 𝔭) (K := K) R𝔭) X _ y b 𝒰 g hg1 hg2

/-- **A Néron model over `R` stays a Néron model over `R_𝔭`** (any ring `R` with fraction field `K`, any prime
`𝔭`). -/
theorem isNeronModelOver_localization {X : Over (Spec (CommRingCat.of R))} (hX : CToPrinted.IsNeronModelOver R K X) :
    CToPrinted.IsNeronModelOver R𝔭 K ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X) := by
  have hX' := hX
  obtain ⟨hsm, hsep, hlft, hqc, -⟩ := hX'
  let jR := Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))
  let kK := Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))
  have hk : kK ≫ jR = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  refine ⟨show Smooth (pullback.snd X.hom jR) from inferInstance,
    show IsSeparated (pullback.snd X.hom jR) from inferInstance,
    show LocallyOfFiniteType (pullback.snd X.hom jR) from inferInstance,
    show QuasiCompact (pullback.snd X.hom jR) from inferInstance, fun Y _ => ⟨?_, ?_⟩⟩
  · intro f₁ f₂ h
    have w₁ : f₁.left ≫ pullback.snd X.hom jR = Y.hom := Over.w f₁
    have w₂ : f₂.left ≫ pullback.snd X.hom jR = Y.hom := Over.w f₂
    have key : f₁.left ≫ pullback.fst X.hom jR = f₂.left ≫ pullback.fst X.hom jR := by
      refine uqA R𝔭 (algebraMap_P_injective (R := R) (𝔭 := 𝔭) (K := K) R𝔭) X Y.hom
        (pullback.fst Y.hom kK) (pullback.snd Y.hom kK) (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
      · rw [Category.assoc, pullback.condition, ← Category.assoc, w₁, Category.assoc, pullback.condition,
          ← Category.assoc, w₂]
      · have h1 := congrArg (fun t => t.left ≫ pullback.fst _ _ ≫ pullback.fst _ _) h
        simpa only [Over.pullback_map_left, pullback.lift_fst_assoc, Category.assoc] using h1
    apply Over.OverMorphism.ext
    exact pullback.hom_ext key (w₁.trans w₂.symm)
  · intro h
    have hw : h.left ≫ pullback.snd (pullback.snd X.hom jR) kK = pullback.snd Y.hom kK := Over.w h
    let a := h.left ≫ pullback.fst (pullback.snd X.hom jR) kK ≫ pullback.fst X.hom jR
    have ha : a ≫ X.hom = pullback.snd Y.hom kK ≫ Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      simp only [a, Category.assoc]
      rw [pullback.condition, pullback.condition_assoc, ← Category.assoc, hw, hk]
    obtain ⟨g, hg1, hg2⟩ := glue_ext (𝔭 := 𝔭) R𝔭 hX Y.left Y.hom a ha
    refine ⟨Over.homMk (pullback.lift g Y.hom hg1) (pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Over.pullback_map_left, Over.homMk_left, Category.assoc, pullback.lift_fst]
        exact hg2
      · simp only [Over.pullback_map_left, Over.homMk_left, Category.assoc, pullback.lift_fst,
          pullback.lift_snd]
        exact pullback.condition.trans ((congrArg (· ≫ kK) hw).symm.trans ((Category.assoc _ _ _).trans
          (congrArg (h.left ≫ ·) pullback.condition.symm)))
    · simp only [Over.pullback_map_left, Over.homMk_left, pullback.lift_snd]
      exact hw.symm

end Main

/-! ## The limit `Spec R_𝔭 = lim Spec R[1/s]` in `Over (Spec R)`, and its base change -/

section OverLim

variable {R : Type} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
  [IsLocalization.AtPrime R𝔭 𝔭]

theorem map_ej {a b : (Idx 𝔭)ᵒᵖ} (f : a ⟶ b) : (specDiag 𝔭).map f ≫ ej b = ej a := by
  refine (Spec.map_comp (CommRingCat.ofHom (algebraMap R (Loc b.unop)))
    (CommRingCat.ofHom (tr (leOfHom f.unop)))).symm.trans ?_
  congr 1
  apply CommRingCat.hom_ext
  ext x
  exact tr_alg (leOfHom f.unop) x

/-- `s ↦ (Spec R[1/s] → Spec R)` in `Over (Spec R)`. -/
noncomputable def overDiag : (Idx 𝔭)ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) where
  obj a := Over.mk (ej a)
  map f := Over.homMk ((specDiag 𝔭).map f) (map_ej 𝔭 f)
  map_id a := by ext1; exact (specDiag 𝔭).map_id a
  map_comp f g := by ext1; exact (specDiag 𝔭).map_comp f g

/-- `Spec R_𝔭 → Spec R` as a cone over `overDiag`. -/
noncomputable def overCone : Cone (overDiag 𝔭) where
  pt := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))
  π := { app a := Over.homMk ((specCone 𝔭 R𝔭).π.app a) (π_ej R𝔭 a)
         naturality a b f := by ext1; exact (specCone 𝔭 R𝔭).π.naturality f }

/-- `Spec R_𝔭 = lim Spec R[1/s]` in `Over (Spec R)`. -/
noncomputable def overConeIsLimit : IsLimit (overCone 𝔭 R𝔭) := by
  haveI : IsConnected (Idx 𝔭)ᵒᵖ := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget _)
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) (specConeIsLimit 𝔭 R𝔭)
  · intro m n f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro n
    simp only [Iso.refl_hom, Category.id_comp]

variable {V : Scheme.{0}} (v : V ⟶ Spec (CommRingCat.of R))

/-- `s ↦ R[1/s] ×_R V`. -/
noncomputable abbrev bcDiag : (Idx 𝔭)ᵒᵖ ⥤ Scheme.{0} :=
  (overDiag 𝔭 ⋙ Over.pullback v) ⋙ Over.forget V

/-- `R_𝔭 ×_R V` as a cone over `bcDiag`. -/
noncomputable abbrev bcCone : Cone (bcDiag 𝔭 v) :=
  (Over.forget V).mapCone ((Over.pullback v).mapCone (overCone 𝔭 R𝔭))

/-- `R_𝔭 ×_R V = lim R[1/s] ×_R V`. -/
noncomputable def bcConeIsLimit : IsLimit (bcCone 𝔭 R𝔭 v) := by
  haveI : IsConnected (Idx 𝔭)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.forget V) (isLimitOfPreserves (Over.pullback v) (overConeIsLimit 𝔭 R𝔭))

/-- The structure maps `R[1/s] ×_R V → Spec R`. -/
noncomputable def bcT : bcDiag 𝔭 v ⟶ (Functor.const _).obj (Spec (CommRingCat.of R)) where
  app a := pullback.snd (ej a) v ≫ v
  naturality a b f := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    exact pullback.lift_snd_assoc _ _ _ _

end OverLim

/-! ## The converse: local Néron models at every maximal ideal give a Néron model -/

section Converse

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- The Néron property of `X ⊗_R R_𝔭` over `R_𝔭`, as an extension property for `R`-morphisms into `X`. -/
theorem neron_ext_loc (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K]
    {X : Over (Spec (CommRingCat.of R))}
    (hX : CToPrinted.IsNeronModelOver R𝔭 K
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X))
    (Y : Over (Spec (CommRingCat.of R𝔭))) [Smooth Y.hom] {P : Scheme.{0}} (p : P ⟶ Y.left)
    (q : P ⟶ Spec (CommRingCat.of K))
    (H : IsPullback p q Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))))
    (b : P ⟶ X.left) (hb : b ≫ X.hom = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ f : Y.left ⟶ X.left, f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) ∧
      p ≫ f = b := by
  have hk : Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)) = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let b' : P ⟶ pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))) :=
    pullback.lift b (q ≫ Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K)))
      (by rw [hb, Category.assoc, hk])
  obtain ⟨f', hf'1, hf'2⟩ := neron_ext hX Y p q H b' (pullback.lift_snd _ _ _)
  have hf'1' : f' ≫ pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))) = Y.hom := hf'1
  refine ⟨f' ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hf'1']
  · rw [← Category.assoc, hf'2, pullback.lift_fst]

end Converse

section BC

variable {R : Type} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
  [IsLocalization.AtPrime R𝔭 𝔭] {V : Scheme.{0}} (v : V ⟶ Spec (CommRingCat.of R))

/-- The cone maps `R_𝔭 ×_R V → R[1/s] ×_R V`, written with explicit pullbacks. -/
noncomputable def bcπ (a : (Idx 𝔭)ᵒᵖ) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))) v ⟶ pullback (ej a) v :=
  pullback.lift (pullback.fst _ v ≫ Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop))) (pullback.snd _ v)
    (((Category.assoc _ _ _).trans (congrArg (pullback.fst _ v ≫ ·) (toP_ej R𝔭 a))).trans
      pullback.condition)

theorem bcCone_π (a : (Idx 𝔭)ᵒᵖ) : (bcCone 𝔭 R𝔭 v).π.app a = bcπ 𝔭 R𝔭 v a := rfl

theorem bcπ_fst (a : (Idx 𝔭)ᵒᵖ) : (bcCone 𝔭 R𝔭 v).π.app a ≫ pullback.fst (ej a) v =
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))) v ≫
      Spec.map (CommRingCat.ofHom (toP R𝔭 a.unop)) :=
  pullback.lift_fst _ _ _

theorem bcπ_snd (a : (Idx 𝔭)ᵒᵖ) : (bcCone 𝔭 R𝔭 v).π.app a ≫ pullback.snd (ej a) v =
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))) v :=
  pullback.lift_snd _ _ _

end BC

section Local

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Local existence at a point** for the converse: around every point of a smooth `R`-scheme `Y`, an
`R`-morphism `Y_K → X` extends, given the Néron property of `X ⊗_R R_𝔭` at every maximal `𝔭`. -/
theorem local_pt {X : Over (Spec (CommRingCat.of R))} [Smooth X.hom]
    (hloc : ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
      [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
      CToPrinted.IsNeronModelOver R𝔭 K
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X))
    {Y : Scheme.{0}} (y : Y ⟶ Spec (CommRingCat.of R)) [Smooth y]
    (a : pullback y (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ X.left)
    (ha : a ≫ X.hom = pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))) (x : Y) :
    ∃ U : Y.Opens, x ∈ U ∧ ∃ g : U.toScheme ⟶ X.left, g ≫ X.hom = U.ι ≫ y ∧
      pullback.fst (U.ι ≫ y) (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ g =
        pullback.lift (pullback.fst _ _ ≫ U.ι) (pullback.snd _ _)
          (by rw [Category.assoc]; exact pullback.condition) ≫ a := by
  let ιK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  -- an affine open around `x`
  obtain ⟨_, ⟨V0, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : Y.Opens := V0
  haveI : IsAffine V := hV
  let v := V.ι ≫ y
  -- a maximal ideal over the image of `x`
  let q : PrimeSpectrum R := y.base x
  obtain ⟨𝔭, h𝔭, hq𝔭⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  haveI := h𝔭
  let R𝔭 := Localization.AtPrime 𝔭
  have hunit : ∀ t : 𝔭.primeCompl, IsUnit (algebraMap R K t) := fun t =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2
      (fun h => t.2 (h ▸ 𝔭.zero_mem)))
  letI : Algebra R𝔭 K := (IsLocalization.lift (M := 𝔭.primeCompl) (S := R𝔭) hunit).toAlgebra
  haveI : IsScalarTower R R𝔭 K :=
    IsScalarTower.of_algebraMap_eq (fun z => (IsLocalization.lift_eq hunit z).symm)
  let jR := Spec.map (CommRingCat.ofHom (algebraMap R R𝔭))
  let kK := Spec.map (CommRingCat.ofHom (algebraMap R𝔭 K))
  have hk : kK ≫ jR = ιK := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hN := hloc 𝔭 R𝔭
  -- the extension over `V ⊗_R R_𝔭`
  let Y' : Over (Spec (CommRingCat.of R𝔭)) := Over.mk (pullback.fst jR v)
  haveI : Smooth Y'.hom := show Smooth (pullback.fst jR v) from inferInstance
  have eqb : (pullback.fst (pullback.fst jR v) kK ≫ pullback.snd jR v ≫ V.ι) ≫ y =
      pullback.snd (pullback.fst jR v) kK ≫ ιK := by
    show pullback.fst (pullback.fst jR v) kK ≫ pullback.snd jR v ≫ v = _
    rw [← pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hk]
  let ε : pullback (pullback.fst jR v) kK ⟶ pullback y ιK :=
    pullback.lift (pullback.fst _ _ ≫ pullback.snd jR v ≫ V.ι) (pullback.snd _ _) eqb
  have hb : (ε ≫ a) ≫ X.hom = pullback.snd (pullback.fst jR v) kK ≫ ιK := by
    rw [Category.assoc, ha, ← Category.assoc, pullback.lift_snd]
  obtain ⟨f𝔭, hf1, hf2⟩ := neron_ext_loc R𝔭 hN Y' (pullback.fst _ _) (pullback.snd _ _)
    (IsPullback.of_hasPullback _ _) (ε ≫ a) hb
  have hf1' : f𝔭 ≫ X.hom = pullback.fst jR v ≫ jR := hf1
  have hf2' : pullback.fst (pullback.fst jR v) kK ≫ f𝔭 = ε ≫ a := hf2
  -- spread `f𝔭` to some `R[1/s] ×_R V`
  haveI hA : ∀ (i : (Idx 𝔭)ᵒᵖ), IsAffine ((bcDiag 𝔭 v).obj i) := fun i => by
    haveI : IsAffine ((specDiag 𝔭).obj i) := show IsAffine (Spec _) from inferInstance
    exact show IsAffine (pullback (ej i) v) from inferInstance
  haveI : ∀ {i j : (Idx 𝔭)ᵒᵖ} (f : i ⟶ j), IsAffineHom ((bcDiag 𝔭 v).map f) := fun f => inferInstance
  haveI : ∀ i : (Idx 𝔭)ᵒᵖ, CompactSpace ((bcDiag 𝔭 v).obj i) := fun i => inferInstance
  haveI : ∀ i : (Idx 𝔭)ᵒᵖ, QuasiSeparatedSpace ((bcDiag 𝔭 v).obj i) := fun i => inferInstance
  have ha' : (bcCone 𝔭 R𝔭 v).π ≫ bcT 𝔭 v = (Functor.const _).map (f𝔭 ≫ X.hom) := by
    ext i
    show bcπ 𝔭 R𝔭 v i ≫ pullback.snd (ej i) v ≫ v = f𝔭 ≫ X.hom
    exact (pullback.lift_snd_assoc _ _ _ _).trans (pullback.condition.symm.trans hf1'.symm)
  obtain ⟨s, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (bcDiag 𝔭 v) (bcT 𝔭 v) X.hom (bcCone 𝔭 R𝔭 v) (bcConeIsLimit 𝔭 R𝔭 v) f𝔭 ha'
  let g' : pullback (ej s) v ⟶ X.left := g
  have hg2' : g' ≫ X.hom = pullback.snd (ej s) v ≫ v := hg2
  have hg1' : bcπ 𝔭 R𝔭 v s ≫ g' = f𝔭 := hg1
  -- the open `U = V ∩ y⁻¹ D(s)` around `x`
  let U : Y.Opens := V ⊓ y ⁻¹ᵁ (ej s).opensRange
  have hxU : x ∈ U := by
    refine ⟨hxV, ?_⟩
    have hrange := Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of R) s.unop.s
    have hmem : y.base x ∈ PrimeSpectrum.basicOpen (R := R) s.unop.s :=
      (PrimeSpectrum.mem_basicOpen _ _).2 (fun h => s.unop.hs (hq𝔭 h))
    exact (congrArg (y.base x ∈ ·) hrange).mpr hmem
  have hle : U ≤ V := inf_le_left
  have hr : Set.range (U.ι ≫ y).base ⊆ Set.range (ej s).base := by
    rintro _ ⟨z, rfl⟩
    exact z.2.2
  let n : U.toScheme ⟶ pullback (ej s) v :=
    pullback.lift (IsOpenImmersion.lift (ej s) (U.ι ≫ y) hr) (Y.homOfLE hle)
      (by rw [IsOpenImmersion.lift_fac]; show _ = Y.homOfLE hle ≫ V.ι ≫ y
          rw [← Category.assoc, Scheme.homOfLE_ι])
  refine ⟨U, hxU, n ≫ g', ?_, ?_⟩
  · rw [Category.assoc, hg2']
    show n ≫ pullback.snd (ej s) v ≫ V.ι ≫ y = U.ι ≫ y
    rw [← Category.assoc, pullback.lift_snd, ← Category.assoc, Scheme.homOfLE_ι]
  · let F := pullback.fst (U.ι ≫ y) ιK
    let G := pullback.snd (U.ι ≫ y) ιK
    have hFG : F ≫ U.ι ≫ y = G ≫ ιK := pullback.condition
    let ρ : pullback (U.ι ≫ y) ιK ⟶ pullback jR v :=
      pullback.lift (G ≫ kK) (F ≫ Y.homOfLE hle) (by
        show (G ≫ kK) ≫ jR = (F ≫ Y.homOfLE hle) ≫ V.ι ≫ y
        rw [Category.assoc, hk, Category.assoc, ← Category.assoc (Y.homOfLE hle), Scheme.homOfLE_ι, hFG])
    have l0 : bcπ 𝔭 R𝔭 v s ≫ pullback.fst (ej s) v ≫ ej s = pullback.fst jR v ≫ jR :=
      (pullback.lift_fst_assoc _ _ _ _).trans ((Category.assoc _ _ _).trans
        (congrArg (pullback.fst jR v ≫ ·) (toP_ej R𝔭 s)))
    have l3 : bcπ 𝔭 R𝔭 v s ≫ pullback.snd (ej s) v = pullback.snd jR v := pullback.lift_snd _ _ _
    have l1 : ρ ≫ bcπ 𝔭 R𝔭 v s ≫ pullback.fst (ej s) v ≫ ej s = G ≫ ιK := by
      rw [l0, pullback.lift_fst_assoc, Category.assoc, hk]
    have l2 : F ≫ n ≫ pullback.fst (ej s) v ≫ ej s = G ≫ ιK := by
      rw [pullback.lift_fst_assoc, IsOpenImmersion.lift_fac, hFG]
    have c1 : ρ ≫ bcπ 𝔭 R𝔭 v s = F ≫ n := by
      apply pullback.hom_ext
      · rw [← cancel_mono (ej s)]
        simp only [Category.assoc]
        rw [l1, l2]
      · simp only [Category.assoc]
        rw [l3, pullback.lift_snd, pullback.lift_snd]
    let ρ' : pullback (U.ι ≫ y) ιK ⟶ pullback (pullback.fst jR v) kK :=
      pullback.lift ρ G (pullback.lift_fst _ _ _)
    have c2 : ρ' ≫ ε = pullback.lift (F ≫ U.ι) G (by rw [Category.assoc]; exact hFG) := by
      apply pullback.hom_ext
      · simp only [ε, ρ', ρ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
        rw [Scheme.homOfLE_ι]
      · simp only [ε, ρ', Category.assoc, pullback.lift_snd]
    have hρ : ρ = ρ' ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have key : F ≫ n ≫ g' = pullback.lift (F ≫ U.ι) G (by rw [Category.assoc]; exact hFG) ≫ a := by
      rw [← Category.assoc, ← c1, Category.assoc, hg1', hρ, Category.assoc, hf2', ← Category.assoc, c2]
    exact key

/-- **The converse of BLR 1.2/4's `.mp`**: if `X ⊗_R R_𝔭` is a Néron model over `R_𝔭` for every maximal `𝔭`,
then `X` is a Néron model over `R`. -/
theorem isNeronModelOver_of_local {X : Over (Spec (CommRingCat.of R))} [Smooth X.hom] [IsSeparated X.hom]
    [QuasiCompact X.hom]
    (hloc : ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
      [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
      CToPrinted.IsNeronModelOver R𝔭 K
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X)) :
    CToPrinted.IsNeronModelOver R K X := by
  let ιK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, fun Y _ => ⟨?_, ?_⟩⟩
  · intro f₁ f₂ h
    have key : f₁.left = f₂.left := by
      refine uqA R (IsFractionRing.injective R K) X Y.hom (pullback.fst Y.hom ιK) (pullback.snd Y.hom ιK)
        (IsPullback.of_hasPullback _ _) _ _ ((Over.w f₁).trans (Over.w f₂).symm) ?_
      have h1 := congrArg (fun t => t.left ≫ pullback.fst _ _) h
      simpa only [Over.pullback_map_left, pullback.lift_fst] using h1
    exact Over.OverMorphism.ext key
  · intro h
    have hw : h.left ≫ pullback.snd X.hom ιK = pullback.snd Y.hom ιK := Over.w h
    let a := h.left ≫ pullback.fst X.hom ιK
    have ha : a ≫ X.hom = pullback.snd Y.hom ιK ≫ ιK := by
      simp only [a, Category.assoc]
      rw [pullback.condition, ← Category.assoc, hw]
    choose U hxU g hg1 hg2 using local_pt hloc Y.hom a ha
    let 𝒰 : Y.left.OpenCover := {
      I₀ := Y.left, X i := (U i), f i := (U i).ι,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ⟨x, by simpa using hxU x⟩, inferInstance⟩ }
    obtain ⟨f, hf1, hf2⟩ := glue_cover R (IsFractionRing.injective R K) X (𝟙 _) Y.hom a 𝒰 g
      (fun i => by rw [Category.comp_id]; exact hg1 i) hg2
    rw [Category.comp_id] at hf1
    refine ⟨Over.homMk f hf1, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, Over.homMk_left, pullback.lift_fst]
      exact hf2
    · simp only [Over.pullback_map_left, Over.homMk_left, pullback.lift_snd]
      exact hw.symm

end Local

/-! ## BLR 1.2/4 and its `.mp` half -/

/-- **BLR §1.2 Prop. 4, proved**: exactly `CToPrinted.BLR_1_2_4` (both directions), for every Dedekind domain
(indeed every ring with a fraction field). -/
theorem blr_1_2_4 : CToPrinted.BLR_1_2_4 := by
  intro R K _ _ _ _ _ X _ _ _
  exact ⟨fun hX 𝔭 _ R𝔭 _ _ _ _ _ => isNeronModelOver_localization (𝔭 := 𝔭) R𝔭 hX,
    fun h => isNeronModelOver_of_local h⟩

/-- **The `.mp` half of `CToPrinted.BLR_1_2_4`** (BLR, *Néron models*, §1.2 Prop. 4, "only if"), with the
same binders: the only direction the chain's consumers use. -/
def BLR_1_2_4_MP : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom],
    CToPrinted.IsNeronModelOver R K X →
      ∀ (𝔭 : Ideal R) [𝔭.IsMaximal] (R𝔭 : Type) [CommRing R𝔭] [Algebra R R𝔭]
        [IsLocalization.AtPrime R𝔭 𝔭] [Algebra R𝔭 K] [IsScalarTower R R𝔭 K],
        CToPrinted.IsNeronModelOver R𝔭 K
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R𝔭)))).obj X)

/-- **`BLR_1_2_4_MP`, proved** directly (`isNeronModelOver_localization`). -/
theorem blr_1_2_4_mp : BLR_1_2_4_MP := by
  intro R K _ _ _ _ _ X _ _ _ hX 𝔭 _ R𝔭 _ _ _ _ _
  exact isNeronModelOver_localization (𝔭 := 𝔭) R𝔭 hX

/-- The printed statement implies its `.mp` half (so `BLR_1_2_4_MP` is never stronger than the leaf). -/
theorem blr_1_2_4_mp_of_printed (h : CToPrinted.BLR_1_2_4) : BLR_1_2_4_MP := by
  intro R K _ _ _ _ _ X _ _ _ hX 𝔭 _ R𝔭 _ _ _ _ _
  exact (h R K X).mp hX 𝔭 R𝔭

/-- **`ReductGlue.NeronLocalizesDVR`, proved** (no hypotheses): c-to-printed's
`CToPrinted.neronLocalizesDVR_of_printed` applied to `blr_1_2_4`. -/
theorem neronLocalizesDVR_proved : ReductGlue.NeronLocalizesDVR :=
  CToPrinted.neronLocalizesDVR_of_printed blr_1_2_4

end GapBLR
