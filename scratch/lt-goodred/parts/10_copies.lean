/-! ## lt-goodred §1: verbatim copies of the definitions that `GoodRedTorsion` and `QMEndRank` use

Above this point: lines 1-14993 of `scratch/linked-tate/Leaves.lean` (a byte-identical copy of the
pin-applied `scratch/h-decomposition/Leaves.lean`; it contains `PkgI2`, `PkgI3`, `PkgI4`,
`ObjBridge`, `LeafQM` up to `LeafQM.AV.Qbar`), closed by `end AV`, `end LeafQM`, `end`,
`end LeafQMSec`. Below, copied verbatim from linked-tate's parts (each block names its source):
* `G0Galois.resQ`, `G0Galois.qEmbRing`, `G0Galois.resQ_spec` (parts/70_galois.lean L37-57);
* `G0ModField.IF`, `G0ModField.incAlg`, `G0ModField.numberField_of_fd` (parts/75_modfield.lean
  L43, L54-55, L786);
* unram-tate's `bcPt`, `trPt` and their Galois naturality (parts/96_unramtate.lean L612-722);
* neron-lg's classification of valuation subrings of number fields (scratch/neron-lg/NeronLG.lean
  L209-215, L227-236, L1410-1472: `dvrAt`, `ringOfIntegers_mem`, `toO`, `toO_coe`, `center'`,
  `dvrAt_center'`, `isDiscreteValuationRing_of_ne_top`), namespace renamed to `LTGoodRed.NLG`. -/

section LTGoodRedCopies

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- The embedding `ℚ̄ → K̄` that `Field.absoluteGaloisGroup.map` chooses (`IsAlgClosed.lift`). -/
def qEmbRing (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →+* AlgebraicClosure K :=
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom

/-- `qEmb K ∘ resQ K τ = τ ∘ qEmb K` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
lemma resQ_spec (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure ℚ) :
    qEmbRing K (resQ K τ x) = τ (qEmbRing K x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

end G0Galois

namespace G0ModField

open LeafQM.AV

/-- Intermediate fields of `ℚ̄/ℚ`. -/
abbrev IF : Type := IntermediateField ℚ Qbar

/-- The algebra `L → L'` for `L ≤ L'`. -/
@[instance_reducible] noncomputable def incAlg {L L' : IF} (h : L ≤ L') : Algebra L L' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- A finite-dimensional `L ⊆ ℚ̄` is a number field. -/
theorem numberField_of_fd (L : IF) [FiniteDimensional ℚ L] : NumberField L := ⟨⟩

end G0ModField

namespace UnramTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

/-- `Spec L → Spec K`. -/
noncomputable abbrev sK (K L : Type) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

theorem specMap_comp_sK :
    Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ sK K L =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K L Ω]

/-- `Over.map (Spec L → Spec K) (Spec Ω / L) ≅ Spec Ω / K`. -/
noncomputable def ptMapIso :
    (Over.map (sK K L)).obj (PkgI3.AbVar.ptObj (K := L) Ω) ≅ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, PkgI3.AbVar.ptObj, Over.mk_hom]
    erw [Category.id_comp]
    exact (specMap_comp_sK (K := K) (L := L) Ω).symm)

/-- The adjunction bijection is multiplicative. -/
theorem homEquiv_mul (X : Over (Spec (CommRingCat.of L)))
    (p q : (Over.map (sK K L)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (sK K L)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (sK K L)).homEquiv X A.X p *
        (Over.mapPullbackAdj (sK K L)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- **Points of a base change**: `A_L(Ω) ≃* A(Ω)`. -/
noncomputable def bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω where
  toFun p := (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  invFun x := (Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)
  left_inv p := Equiv.apply_symm_apply ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X) p
  right_inv x := by
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)) = x
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  map_mul' p q := by
    obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective p
    obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective q
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
        ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X p' *
          (Over.mapPullbackAdj (sK K L)).homEquiv _ A.X q') = _
    rw [← homEquiv_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      MonObj.comp_mul]

/-- `bcPt` is natural for `L`-automorphisms of `Ω`. -/
theorem bcPt_galAct (σ : Ω ≃ₐ[L] Ω) (p : (A.baseChange L).Pt Ω) :
    bcPt A Ω ((A.baseChange L).galAct σ p) = A.galAct (σ.restrictScalars K) (bcPt A Ω p) := by
  show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      (PkgI3.AbVar.galHom σ ≫ p) =
    PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv ≫
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  have hnat := Adjunction.homEquiv_naturality_left_symm (Over.mapPullbackAdj (sK K L))
    (PkgI3.AbVar.galHom σ) (p : PkgI3.AbVar.ptObj Ω ⟶ (Over.pullback (sK K L)).obj A.X)
  have hsq : (ptMapIso Ω).inv ≫ (Over.map (sK K L)).map (PkgI3.AbVar.galHom σ) =
      PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv := by
    apply Over.OverMorphism.ext
    simp [ptMapIso, PkgI3.AbVar.galHom]
    rfl
  erw [hnat]
  rw [← Category.assoc, hsq, Category.assoc]

end BC

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-isomorphism `φ : Ω ≃ Ω₂`. -/
noncomputable def trHom (φ : Ω ≃ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem trHom_left (φ : Ω ≃ₐ[K] Ω₂) :
    (trHom φ).left = Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) := rfl

theorem trHom_symm_comp (φ : Ω ≃ₐ[K] Ω₂) : trHom φ.symm ≫ trHom φ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (φ.symm : Ω₂ →+* Ω)) ≫
    Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) = 𝟙 (Spec (CommRingCat.of Ω))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (φ.symm : Ω₂ →+* Ω).comp (φ : Ω →+* Ω₂) = RingHom.id Ω by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

theorem trHom_comp_symm (φ : Ω ≃ₐ[K] Ω₂) : trHom φ ≫ trHom φ.symm = 𝟙 _ := by
  simpa using trHom_symm_comp φ.symm

/-- **Transport of points** along `φ : Ω ≃ₐ[K] Ω₂`. -/
noncomputable def trPt (φ : Ω ≃ₐ[K] Ω₂) : A.Pt Ω ≃* A.Pt Ω₂ where
  toFun p := trHom φ ≫ p
  invFun x := trHom φ.symm ≫ x
  left_inv p := by simp [← Category.assoc, trHom_symm_comp]
  right_inv x := by simp [← Category.assoc, trHom_comp_symm]
  map_mul' p q := MonObj.comp_mul _ _ _

/-- `trPt φ` carries the action of `σ` to that of `φσφ⁻¹`. -/
theorem trPt_galAct (φ : Ω ≃ₐ[K] Ω₂) (σ : Ω ≃ₐ[K] Ω) (σ₂ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, σ₂ (φ x) = φ (σ x)) (p : A.Pt Ω) :
    trPt A φ (A.galAct σ p) = A.galAct σ₂ (trPt A φ p) := by
  show trHom φ ≫ PkgI3.AbVar.galHom σ ≫ p = PkgI3.AbVar.galHom σ₂ ≫ trHom φ ≫ p
  have hsq : trHom φ ≫ PkgI3.AbVar.galHom σ = PkgI3.AbVar.galHom σ₂ ≫ trHom φ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ₂ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, ← Category.assoc, hsq]

end Tr

end UnramTate

namespace LTGoodRed.NLG

open NumberField

/-- The discrete valuation ring `𝓞_{L,v}` of a nonzero prime `v` of `𝓞_L`, as a valuation subring
of `L` (the ring of the `v`-adic valuation). -/
noncomputable def dvrAt {L : Type} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ValuationSubring L :=
  (v.valuation L).valuationSubring

instance {L : Type} [Field L] [NumberField L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    IsDiscreteValuationRing (dvrAt v) := by
  unfold dvrAt; infer_instance

section Restrict

variable {K : Type} [Field K] [NumberField K]

/-- Every valuation subring of a number field contains `𝓞_K` (it is integrally closed). -/
theorem ringOfIntegers_mem (O : ValuationSubring K) (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem O)

theorem toO_coe (O : ValuationSubring K) (x : 𝓞 K) : ((toO O x : O) : K) = algebraMap (𝓞 K) K x :=
  rfl

/-- The center of a valuation subring `O ≠ ⊤` of a number field on `𝓞_K`: a nonzero prime. -/
def center' (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := (IsLocalRing.maximalIdeal O).comap (toO O)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy⟩ : ∃ y : K, y ∉ O := by
      by_contra h
      push_neg at h
      exact hO (eq_top_iff.2 fun y _ => h y)
    have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hyi : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    let x : O := ⟨y⁻¹, hyi⟩
    have hx : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu'⟩ := hu
      apply hy
      have : ((u⁻¹ : Oˣ) : O) * x = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Oˣ) : O) : K)) * y⁻¹ = 1 := congrArg Subtype.val this
      have h3 : y = (((u⁻¹ : Oˣ) : O) : K) := by
        field_simp at h2
        exact h2.symm
      rw [h3]; exact (((u⁻¹ : Oˣ) : O)).2
    have hx0 : x ≠ 0 := fun h => inv_ne_zero hy0 (congrArg Subtype.val h)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have ha : toO O a = x * toO O b := by
      apply Subtype.ext
      rw [toO_coe, Subring.coe_mul, toO_coe, ← hab, div_mul_cancel₀ _ hb0]
    intro hbot
    have hmem : a ∈ (IsLocalRing.maximalIdeal O).comap (toO O) := by
      rw [Ideal.mem_comap, ha]; exact Ideal.mul_mem_right _ _ hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    apply Subtype.ext
    rw [← hab, hmem, map_zero, zero_div]; rfl

/-- **Every valuation subring `O ≠ ⊤` of a number field is `𝓞_{K,v}` (proved).** -/
theorem dvrAt_center' (O : ValuationSubring K) (hO : O ≠ ⊤) : dvrAt (center' O hO) = O := by
  apply ValuationSubring.eq_of_le_of_ne_top _ _ hO
  intro x hx
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (center' O hO) x hx
  have hd : IsUnit (toO O d) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hvd : O.valuation (algebraMap (𝓞 K) K d) = 1 := (O.valuation_eq_one_iff _).1 hd
  apply O.mem_of_valuation_le_one
  have h2 := congrArg O.valuation hnd
  rw [map_mul, hvd, _root_.mul_one] at h2
  rw [h2]
  exact O.valuation_le_one (toO O n)

/-- Every valuation subring `O ≠ ⊤` of a number field is a DVR. -/
theorem isDiscreteValuationRing_of_ne_top (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by
  rw [← dvrAt_center' O hO]
  infer_instance

end Restrict

end LTGoodRed.NLG

end

end LTGoodRedCopies
