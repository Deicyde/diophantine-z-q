import ZInQKernel.Contrib.CloudB3RC53.Duality.LocalKummerChar0
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer

/-!
# Lane RC29, round 2 (comparison, part 1): separable closure, algebraic closure, Weil pairing

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer` (tex 3413–3468), proof,
tex 3442–3445:

> The local finite dualities [Milne, I.2.3, I.3.2–I.3.5] make the Kummer map adjoint to
> `H¹(F, B[2^a]) → H¹(F, B)[2^a]`. The latter has Kummer image as kernel, so the Kummer image is
> its exact annihilator.

The other group states the local duality of this sentence as a PRINT
(`MilneLocalTateDualityKummerCharZero`) in the cohomology of `Gal(Fˢ/F)` with coefficients in the
points over the separable closure `Fˢ` (`WeierstrassCurve.PointCoeff`, `TorsionCoeff`) and the
roots of unity `KummerCoeff F m = μ_m(Fˢ)`. Lanes RC26, RC28 and RC29 use `G_F = Gal(F̄/F)`
(`Field.absoluteGaloisGroup F`) and the points over the algebraic closure `F̄` (lane RC28's
`PtAlg`, `TorsAlg`). This file builds the comparison data over a field `F` of characteristic zero.

* `compSepVal`, `compSepEquiv`: the inclusion `Fˢ → F̄`, an `F`-algebra isomorphism `e` in
  characteristic zero (`compSep_eq_top`: every algebraic extension of `F` is separable).
* `compGal : G_F ≃ₜ* Gal(Fˢ/F)`, the restriction isomorphism of the other group
  (`absoluteGaloisGroupRestrictEquiv`); its inverse is conjugation `τ ↦ e τ e⁻¹`
  (`compGal_symm_eq_autCongr`), and `e (compGal σ x) = σ (e x)` (`compSepVal_compGal`).
* `compSepPt : B(Fˢ) ≃+ B(F̄)` and `compSepTors : B(Fˢ)[m] ≃+ B(F̄)[m]`, the point maps along `e`;
  equivariant along `compGal` (`compSepPt_smul`, `compSepTors_smul`);
  `compSepPtHom_basePointCoeff`: they respect the inclusions of `B(F)`.
* `MuAlg F m = μ_m(F̄)`, written additively, a discrete `G_F`-module (Galois action
  `σ • ζ = σ(ζ)`, `coe_smul_muAlg`; `MuAlg.instContinuousSMul`), and `compMu : μ_m(Fˢ) ≃+ μ_m(F̄)`,
  equivariant (`compMu_smul`).
* `compWeil : B(F̄)[m] →ₗ[ℤ] B(F̄)[m] →ₗ[ℤ] μ_m(F̄)`, the vendored Weil pairing `e_m` of
  `B ×_F F̄` (Silverman, *The Arithmetic of Elliptic Curves*, III.8.1) as a `ℤ`-bilinear map;
  `compWeil_smul`: Galois equivariance (the other group's `weilPairing_torsionGaloisAction`);
  `compWeil_compTors`: **it corresponds to the other group's Weil pairing over `Fˢ`**
  (`torsionCoeffWeilPairing`) under `compSepTors` and `compMu` (the other group's
  `weilPairing_torsionMapAlong` and `weilPairing_torsionByCongr_cast`).

Kinds: all declarations are definitions or PROVED. No hypothesis beyond `CharZero F` (and `B`
elliptic, `m ≠ 0` for the Weil pairing) is used.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open TauCeti TauCeti.ContCohomology WeierstrassCurve ZInQ.Manuscript.RC.CoefModules

/-! ### The separable closure and the algebraic closure -/

section Closures

variable (F : Type) [Field F]

/-- Definition. The inclusion `Fˢ → F̄` of the separable closure into the algebraic closure, as an
`F`-algebra map. -/
def compSepVal : SeparableClosure F →ₐ[F] AlgebraicClosure F :=
  (separableClosure F (AlgebraicClosure F)).val

/-- PROVED. The inclusion `Fˢ → F̄` is the coercion. -/
@[simp]
theorem compSepVal_apply (x : SeparableClosure F) : compSepVal F x = (x : AlgebraicClosure F) :=
  rfl

/-- PROVED. The inclusion `Fˢ → F̄` is injective. -/
theorem compSepVal_injective : Function.Injective (compSepVal F) :=
  Subtype.val_injective

/-- PROVED. In characteristic zero the separable closure of `F` in `F̄` is all of `F̄`: `F` is
perfect, so the algebraic extension `F̄/F` is separable. -/
theorem compSep_eq_top [CharZero F] : separableClosure F (AlgebraicClosure F) = ⊤ :=
  (separableClosure.eq_top_iff F (AlgebraicClosure F)).2 inferInstance

/-- PROVED. In characteristic zero the inclusion `Fˢ → F̄` is surjective. -/
theorem compSepVal_surjective [CharZero F] : Function.Surjective (compSepVal F) := fun y =>
  ⟨⟨y, by rw [compSep_eq_top F]; exact IntermediateField.mem_top⟩, rfl⟩

/-- Definition. **The `F`-algebra isomorphism `e : Fˢ ≃ F̄`** of a field of characteristic zero
(the inclusion of the separable closure into the algebraic closure). -/
def compSepEquiv [CharZero F] : SeparableClosure F ≃ₐ[F] AlgebraicClosure F :=
  AlgEquiv.ofBijective (compSepVal F) ⟨compSepVal_injective F, compSepVal_surjective F⟩

/-- PROVED. `e` is the inclusion. -/
@[simp]
theorem compSepEquiv_apply [CharZero F] (x : SeparableClosure F) :
    compSepEquiv F x = compSepVal F x :=
  rfl

/-- Definition. **The continuous group isomorphism `G_F = Gal(F̄/F) ≃ Gal(Fˢ/F)`**: restriction
to the separable closure (the other group's `absoluteGaloisGroupRestrictEquiv`, defined for every
field). Its inverse is conjugation by `e` (`compGal_symm_eq_autCongr`). -/
def compGal : Field.absoluteGaloisGroup F ≃ₜ* AbsoluteGaloisGroup F :=
  absoluteGaloisGroupRestrictEquiv F

/-- PROVED. `e (compGal σ x) = σ (e x)` for `σ ∈ G_F`, `x ∈ Fˢ`. -/
theorem compSepVal_compGal (σ : Field.absoluteGaloisGroup F) (x : SeparableClosure F) :
    compSepVal F (compGal F σ x) = σ.toAlgHom (compSepVal F x) :=
  coe_absoluteGaloisGroupRestrictEquiv_apply F σ x

/-- PROVED. **The inverse of `compGal` is `τ ↦ e τ e⁻¹`**: for `τ ∈ Gal(Fˢ/F)`, the automorphism
`compGal⁻¹ τ` of `F̄` is `e ∘ τ ∘ e⁻¹` (Mathlib's `AlgEquiv.autCongr e τ`). -/
theorem compGal_symm_eq_autCongr [CharZero F] (τ : AbsoluteGaloisGroup F) :
    @Eq (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ((compGal F).symm τ)
      (AlgEquiv.autCongr (compSepEquiv F) τ) := by
  rw [AlgEquiv.autCongr_apply]
  refine AlgEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (compSepEquiv F).surjective y
  rw [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.trans_apply, compSepEquiv_apply,
    compSepEquiv_apply]
  have h := compSepVal_compGal F ((compGal F).symm τ) x
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  exact h.symm

end Closures

/-! ### Points over the two closures -/

section Points

variable (F : Type) [Field F] (B : WeierstrassCurve F)

open scoped Classical in
/-- Definition. **The point map `B(Fˢ) → B(F̄)`** along the inclusion `Fˢ → F̄`, from the other
group's coefficient module `B.PointCoeff` to lane RC28's `PtAlg F B`. -/
def compSepPtHom : B.PointCoeff →+ PtAlg F B :=
  (ptEquiv F B).toAddMonoidHom.comp
    ((Affine.Point.map (W' := B) (compSepVal F)).comp B.pointCoeffEquiv.symm.toAddMonoidHom)

open scoped Classical in
/-- PROVED. `compSepPtHom` on a point of `B ×_F Fˢ` is the point map along `Fˢ → F̄`. -/
theorem compSepPtHom_pointCoeffEquiv (P : (B.baseChange (SeparableClosure F)).toAffine.Point) :
    compSepPtHom F B (B.pointCoeffEquiv P) =
      ptEquiv F B (Affine.Point.map (W' := B) (compSepVal F) P) := by
  simp only [compSepPtHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply]

open scoped Classical in
/-- PROVED. **Equivariance**: `e_*(compGal σ • P) = σ • e_* P` for `σ ∈ G_F`. -/
theorem compSepPtHom_smul (σ : Field.absoluteGaloisGroup F) (P : B.PointCoeff) :
    compSepPtHom F B (compGal F σ • P) = σ • compSepPtHom F B P := by
  obtain ⟨P, rfl⟩ := B.pointCoeffEquiv.surjective P
  have hcomp : (compSepVal F).comp (compGal F σ).toAlgHom = σ.toAlgHom.comp (compSepVal F) :=
    AlgHom.ext fun x => compSepVal_compGal F σ x
  rw [smul_pointCoeffEquiv, compSepPtHom_pointCoeffEquiv, compSepPtHom_pointCoeffEquiv,
    smul_ptEquiv, Affine.Point.map_map, Affine.Point.map_map, hcomp]

open scoped Classical in
/-- PROVED. The point map along the identity of an extension `L/F` is the identity. -/
theorem compPoint_map_id {L : Type} [Field L] [Algebra F L]
    (P : (B.baseChange L).toAffine.Point) : Affine.Point.map (W' := B) (AlgHom.id F L) P = P := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

open scoped Classical in
/-- PROVED. In characteristic zero the point map `B(Fˢ) → B(F̄)` is bijective. -/
theorem compSepPtHom_bijective [CharZero F] : Function.Bijective (compSepPtHom F B) := by
  refine ⟨fun P Q h => ?_, fun Q => ?_⟩
  · obtain ⟨P, rfl⟩ := B.pointCoeffEquiv.surjective P
    obtain ⟨Q, rfl⟩ := B.pointCoeffEquiv.surjective Q
    rw [compSepPtHom_pointCoeffEquiv, compSepPtHom_pointCoeffEquiv] at h
    exact congrArg _ (Affine.Point.map_injective _ ((ptEquiv F B).injective h))
  · obtain ⟨Q, rfl⟩ := (ptEquiv F B).surjective Q
    refine ⟨B.pointCoeffEquiv (Affine.Point.map (W' := B) (compSepEquiv F).symm.toAlgHom Q), ?_⟩
    have hid : (compSepVal F).comp (compSepEquiv F).symm.toAlgHom =
        AlgHom.id F (AlgebraicClosure F) :=
      AlgHom.ext fun y => (compSepEquiv F).apply_symm_apply y
    rw [compSepPtHom_pointCoeffEquiv, Affine.Point.map_map, hid, compPoint_map_id]

/-- Definition. **`B(Fˢ) ≃+ B(F̄)`** for `F` of characteristic zero. -/
def compSepPt [CharZero F] : B.PointCoeff ≃+ PtAlg F B :=
  AddEquiv.ofBijective (compSepPtHom F B) (compSepPtHom_bijective F B)

/-- PROVED. `compSepPt` is the point map. -/
@[simp]
theorem compSepPt_apply [CharZero F] (P : B.PointCoeff) : compSepPt F B P = compSepPtHom F B P :=
  rfl

/-- PROVED. **`compSepPt` is equivariant along `compGal`.** -/
theorem compSepPt_smul [CharZero F] (σ : Field.absoluteGaloisGroup F) (P : B.PointCoeff) :
    compSepPt F B (compGal F σ • P) = σ • compSepPt F B P :=
  compSepPtHom_smul F B σ P

open scoped Classical in
/-- PROVED. The point map `B(Fˢ) → B(F̄)` respects the inclusions of `B(F)`: it sends the other
group's `basePointCoeff P` to lane RC28's `basePt P`. -/
theorem compSepPtHom_basePointCoeff [DecidableEq F] (P : B.toAffine.Point) :
    compSepPtHom F B (B.basePointCoeff P) = basePt F B P := by
  rw [basePointCoeff, basePt, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, compSepPtHom_pointCoeffEquiv, Affine.Point.map_map,
    Subsingleton.elim ((compSepVal F).comp (Algebra.ofId F (SeparableClosure F)))
      (Algebra.ofId F (AlgebraicClosure F))]
  rfl

section Tors

variable [CharZero F] (m : ℕ)

/-- Definition. **`B(Fˢ)[m] ≃+ B(F̄)[m]`**, the restriction of `compSepPt` to the `m`-torsion. -/
def compSepTors : B.TorsionCoeff m ≃+ TorsAlg F B m :=
  AddEquiv.torsionByCongr (compSepPt F B) m

/-- PROVED. `compSepTors` on underlying points. -/
@[simp]
theorem coe_compSepTors (P : B.TorsionCoeff m) :
    (compSepTors F B m P : PtAlg F B) = compSepPt F B (P : B.PointCoeff) :=
  AddEquiv.torsionByCongr_apply_coe _ _ _

/-- PROVED. **`compSepTors` is equivariant along `compGal`.** -/
theorem compSepTors_smul (σ : Field.absoluteGaloisGroup F) (P : B.TorsionCoeff m) :
    compSepTors F B m (compGal F σ • P) = σ • compSepTors F B m P :=
  Subtype.ext (by
    rw [coe_compSepTors, coe_smul_torsAlg, coe_smul_torsionCoeff, compSepPt_smul, coe_compSepTors])

/-- PROVED. The inverse of `compSepTors` is equivariant along `compGal`. -/
theorem compSepTors_symm_smul (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m) :
    (compSepTors F B m).symm (σ • t) = compGal F σ • (compSepTors F B m).symm t := by
  apply (compSepTors F B m).injective
  rw [compSepTors_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- PROVED. The inverse of `compSepTors`, along `compGal⁻¹`: the compatibility condition of the
other group's pullbacks (`cocyclesMap1`, `explicitMap1`) for the pair
`(compGal⁻¹, compSepTors⁻¹)`. -/
theorem compSepTors_symm_smul_symm (τ : AbsoluteGaloisGroup F) (t : TorsAlg F B m) :
    (compSepTors F B m).symm ((compGal F).symm τ • t) = τ • (compSepTors F B m).symm t := by
  rw [compSepTors_symm_smul, ContinuousMulEquiv.apply_symm_apply]

end Tors

end Points

/-! ### The roots of unity of `F̄` -/

section Mu

variable (F : Type) [Field F] (m : ℕ)

/-- Definition. **`μ_m(F̄)`**: the `m`-th roots of unity of the algebraic closure, written
additively (the counterpart over `F̄` of the other group's `KummerCoeff F m = μ_m(Fˢ)`). -/
abbrev MuAlg : Type := Additive (rootsOfUnity m (AlgebraicClosure F))

/-- Definition. `μ_m(F̄)` carries the discrete topology. -/
instance MuAlg.instTopologicalSpace : TopologicalSpace (MuAlg F m) := ⊥

/-- PROVED. The topology of `μ_m(F̄)` is discrete. -/
instance MuAlg.instDiscreteTopology : DiscreteTopology (MuAlg F m) := ⟨rfl⟩

/-- Definition. The Galois action on `μ_m(F̄)`, `σ • ζ = σ(ζ)` (Mathlib's
`restrictRootsOfUnity` along `σ`). -/
def muAlgSMul (σ : Field.absoluteGaloisGroup F) (ζ : MuAlg F m) : MuAlg F m :=
  Additive.ofMul (restrictRootsOfUnity σ.toAlgHom m ζ.toMul)

/-- Definition. The value in `F̄` of an element of `μ_m(F̄)`. -/
abbrev muAlgVal (ζ : MuAlg F m) : AlgebraicClosure F :=
  (((Additive.toMul ζ : rootsOfUnity m (AlgebraicClosure F)) : (AlgebraicClosure F)ˣ) :
    AlgebraicClosure F)

/-- PROVED. Elements of `μ_m(F̄)` are determined by their values in `F̄`. -/
theorem muAlg_ext {ζ ξ : MuAlg F m} (h : muAlgVal F m ζ = muAlgVal F m ξ) : ζ = ξ :=
  Additive.toMul.injective (Subtype.ext (Units.ext h))

/-- PROVED. The value of `σ • ζ` is `σ` applied to the value of `ζ`. -/
theorem muAlgVal_muAlgSMul (σ : Field.absoluteGaloisGroup F) (ζ : MuAlg F m) :
    muAlgVal F m (muAlgSMul F m σ ζ) = σ.toAlgHom (muAlgVal F m ζ) :=
  restrictRootsOfUnity_coe_apply _ _

/-- PROVED. The value of `0 ∈ μ_m(F̄)` is `1`. -/
theorem muAlgVal_zero : muAlgVal F m 0 = 1 := by
  simp [muAlgVal]

/-- Definition, PROVED. **`μ_m(F̄)` is a `G_F`-module.** -/
instance MuAlg.instDistribMulAction :
    DistribMulAction (Field.absoluteGaloisGroup F) (MuAlg F m) where
  smul := muAlgSMul F m
  one_smul ζ := muAlg_ext F m ((muAlgVal_muAlgSMul F m 1 ζ).trans rfl)
  mul_smul σ τ ζ := muAlg_ext F m (by
    change muAlgVal F m (muAlgSMul F m (σ * τ) ζ) =
      muAlgVal F m (muAlgSMul F m σ (muAlgSMul F m τ ζ))
    rw [muAlgVal_muAlgSMul, muAlgVal_muAlgSMul, muAlgVal_muAlgSMul]
    rfl)
  smul_zero σ := muAlg_ext F m (by
    change muAlgVal F m (muAlgSMul F m σ 0) = muAlgVal F m 0
    rw [muAlgVal_muAlgSMul, muAlgVal_zero]
    exact map_one σ.toAlgHom)
  smul_add σ ζ ξ := muAlg_ext F m (by
    change muAlgVal F m (muAlgSMul F m σ (ζ + ξ)) =
      muAlgVal F m (muAlgSMul F m σ ζ + muAlgSMul F m σ ξ)
    rw [muAlgVal_muAlgSMul]
    simp only [muAlgVal, toMul_add, Subgroup.coe_mul, Units.val_mul, map_mul]
    rw [← muAlgVal, ← muAlgVal, ← muAlgVal, ← muAlgVal, muAlgVal_muAlgSMul,
      muAlgVal_muAlgSMul])

/-- PROVED. **The Galois action on `μ_m(F̄)` is `σ • ζ = σ(ζ)`** on values. -/
theorem coe_smul_muAlg (σ : Field.absoluteGaloisGroup F) (ζ : MuAlg F m) :
    muAlgVal F m (σ • ζ) = σ.toAlgHom (muAlgVal F m ζ) :=
  muAlgVal_muAlgSMul F m σ ζ

/-- PROVED. **`μ_m(F̄)` is a discrete `G_F`-module**: the stabilizer of `ζ` contains the open
stabilizer of its value in `F̄` (lane RC28's `isOpen_fix`). -/
instance MuAlg.instContinuousSMul : ContinuousSMul (Field.absoluteGaloisGroup F) (MuAlg F m) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun ζ => ?_
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  refine Filter.mem_of_superset ((isOpen_fix (muAlgVal F m ζ)).mem_nhds rfl) ?_
  intro σ hσ
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  exact muAlg_ext F m ((coe_smul_muAlg F m σ ζ).trans hσ)

/-- PROVED. The value of `g • x` for `g ∈ Gal(Fˢ/F)` and `x ∈ μ_m(Fˢ)` (the other group's
`KummerCoeff`) is `g` applied to the value of `x`. -/
theorem coe_smul_kummerCoeff (g : AbsoluteGaloisGroup F) (x : KummerCoeff F m) :
    (((Additive.toMul (g • x) : rootsOfUnity m (SeparableClosure F)) : (SeparableClosure F)ˣ) :
        SeparableClosure F) =
      g (((Additive.toMul x : rootsOfUnity m (SeparableClosure F)) : (SeparableClosure F)ˣ) :
        SeparableClosure F) := by
  simp [AlgEquiv.smul_units_def]

variable [CharZero F]

/-- Definition. **`μ_m(Fˢ) ≃+ μ_m(F̄)`**, induced by `e : Fˢ ≃ F̄`. -/
def compMu : KummerCoeff F m ≃+ MuAlg F m :=
  MulEquiv.toAdditive ((compSepEquiv F).toRingEquiv.toMulEquiv.restrictRootsOfUnity m)

/-- PROVED. `compMu` on values. -/
theorem muAlgVal_compMu (x : KummerCoeff F m) :
    muAlgVal F m (compMu F m x) =
      compSepVal F (((Additive.toMul x : rootsOfUnity m (SeparableClosure F)) :
        (SeparableClosure F)ˣ) : SeparableClosure F) :=
  MulEquiv.restrictRootsOfUnity_coe_apply _ _

/-- PROVED. **`compMu` is equivariant along `compGal`.** -/
theorem compMu_smul (σ : Field.absoluteGaloisGroup F) (x : KummerCoeff F m) :
    compMu F m (compGal F σ • x) = σ • compMu F m x := by
  apply muAlg_ext F m
  rw [muAlgVal_compMu, coe_smul_muAlg, muAlgVal_compMu, coe_smul_kummerCoeff]
  exact compSepVal_compGal F σ _

end Mu

/-! ### The Weil pairing over `F̄` -/

section Weil

variable (F : Type) [Field F] (B : WeierstrassCurve F) (m : ℕ)

/-- PROVED. `m ≠ 0` in `F̄` (characteristic zero). -/
theorem compNatCast_ne_zero [CharZero F] [NeZero m] : (m : AlgebraicClosure F) ≠ 0 := by
  rw [← map_natCast (algebraMap F (AlgebraicClosure F)), map_ne_zero]
  exact Nat.cast_ne_zero.2 (NeZero.ne m)

open scoped Classical in
/-- Definition. `B(F̄)[m]` read as the `m`-torsion of the points of `B ×_F F̄` (the domain of the
vendored Weil pairing). -/
def compSepTorsPt : TorsAlg F B m ≃+
    AddSubgroup.torsionBy (B.baseChange (AlgebraicClosure F)).toAffine.Point (m : ℤ) :=
  AddEquiv.torsionByCongr (ptEquiv F B).symm m

open scoped Classical in
/-- PROVED. The Galois action on `B(F̄)[m]`, read in the domain of the Weil pairing, is the other
group's `torsionGaloisAction` (lane RC28's `torsionGaloisAction_eq_smul`). -/
theorem compSepTorsPt_smul (σ : Field.absoluteGaloisGroup F) (P : TorsAlg F B m) :
    compSepTorsPt F B m (σ • P) =
      Multiplicative.toAdd (B.torsionGaloisAction (m : ℤ) σ) (compSepTorsPt F B m P) := by
  apply Subtype.ext
  apply (ptEquiv F B).injective
  rw [torsionGaloisAction_eq_smul]
  simp only [compSepTorsPt, AddEquiv.torsionByCongr_apply_coe, AddEquiv.apply_symm_apply,
    coe_smul_torsAlg]

open scoped Classical in
/-- PROVED. The point map along `Fˢ → F̄` is the other group's transport `mapAlong`, followed by
the identification `(B ×_F Fˢ) ×_{Fˢ} F̄ = B ×_F F̄`. -/
theorem compPoint_map_eq_cast
    (h : (B.baseChange (SeparableClosure F)).map
        (compSepVal F : SeparableClosure F →+* AlgebraicClosure F) =
      B.baseChange (AlgebraicClosure F))
    (P : (B.baseChange (SeparableClosure F)).toAffine.Point) :
    Affine.Point.map (W' := B) (compSepVal F) P =
      AddEquiv.cast (M := fun V : WeierstrassCurve (AlgebraicClosure F) => V.toAffine.Point) h
        (P.mapAlong (compSepVal F : SeparableClosure F →+* AlgebraicClosure F)
          (compSepVal F : SeparableClosure F →+* AlgebraicClosure F).injective) := by
  rcases P with _ | ⟨x, y, hP⟩
  · rw [← Affine.Point.zero_def, map_zero, Affine.Point.mapAlong_zero, map_zero]
  · rw [Affine.Point.map_some, Affine.Point.mapAlong_some, AddEquiv.cast_apply,
      Affine.Point.cast_some h]
    rfl

open scoped Classical in
/-- PROVED. `compSepTors`, read in the domain of the Weil pairing over `F̄`, is the other group's
`torsionMapAlong` along `Fˢ → F̄` (followed by the identification of the base changes). -/
theorem compSepTorsPt_compTors [CharZero F] (P : B.TorsionCoeff m) :
    compSepTorsPt F B m (compSepTors F B m P) =
      AddEquiv.torsionByCongr
        (AddEquiv.cast (M := fun V : WeierstrassCurve (AlgebraicClosure F) => V.toAffine.Point)
          (map_baseChange B (compSepVal F))) m
        ((B.baseChange (SeparableClosure F)).torsionMapAlong
          (compSepVal F : SeparableClosure F →+* AlgebraicClosure F) m
          ((AddEquiv.torsionByCongr B.pointCoeffEquiv m).symm P)) := by
  apply Subtype.ext
  obtain ⟨P, hP⟩ := P
  obtain ⟨P, rfl⟩ := B.pointCoeffEquiv.surjective P
  rw [compSepTorsPt, AddEquiv.torsionByCongr_apply_coe, AddEquiv.torsionByCongr_apply_coe,
    coe_torsionMapAlong_apply, AddEquiv.torsionByCongr_symm_apply_coe, coe_compSepTors,
    compSepPt_apply, compSepPtHom_pointCoeffEquiv, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]
  exact compPoint_map_eq_cast F B _ P

variable [CharZero F] [B.IsElliptic] [NeZero m]

open scoped Classical in
/-- Definition. The Weil pairing `e_m` of `B ×_F F̄` on `B(F̄)[m]`, additive in each variable
(the other group's `Isogeny.weilPairing`, Silverman III.8.1). -/
def compWeilHom : TorsAlg F B m →+ TorsAlg F B m →+ MuAlg F m :=
  ((Isogeny.weilPairing (B.baseChange (AlgebraicClosure F)) m (compNatCast_ne_zero F m)).compl₂
    (compSepTorsPt F B m).toAddMonoidHom).comp (compSepTorsPt F B m).toAddMonoidHom

/-- Definition. **The Weil pairing `e_m : B(F̄)[m] × B(F̄)[m] → μ_m(F̄)` as a `ℤ`-bilinear map**
(the coefficient pairing of the local cup product of lanes RC26 and RC29). -/
def compWeil : TorsAlg F B m →ₗ[ℤ] TorsAlg F B m →ₗ[ℤ] MuAlg F m :=
  LinearMap.mk₂ ℤ (fun P Q => compWeilHom F B m P Q)
    (fun P P' Q => by rw [map_add, AddMonoidHom.add_apply])
    (fun c P Q => by
      change compWeilHom F B m (c • P) Q = c • compWeilHom F B m P Q
      rw [map_zsmul, AddMonoidHom.zsmul_apply])
    (fun P Q Q' => map_add _ Q Q')
    (fun c P Q => map_zsmul _ c Q)

/-- PROVED. `compWeil` is `compWeilHom`. -/
theorem compWeil_apply (P Q : TorsAlg F B m) : compWeil F B m P Q = compWeilHom F B m P Q :=
  rfl

/-- PROVED. `compWeil` is jointly continuous (the modules are discrete). -/
theorem compWeil_continuous :
    Continuous fun x : TorsAlg F B m × TorsAlg F B m => compWeil F B m x.1 x.2 :=
  continuous_of_discreteTopology

open scoped Classical in
/-- PROVED. **The Weil pairing over `F̄` is Galois equivariant**: `e_m(σP, σQ) = σ(e_m(P, Q))`
(the other group's `weilPairing_torsionGaloisAction`, Silverman III.8.1(e)). This is lane RC26's
equivariance hypothesis `hβ` for `compWeil`. -/
theorem compWeil_smul (σ : Field.absoluteGaloisGroup F) (P Q : TorsAlg F B m) :
    compWeil F B m (σ • P) (σ • Q) = σ • compWeil F B m P Q := by
  rw [compWeil_apply, compWeil_apply]
  change Isogeny.weilPairing (B.baseChange (AlgebraicClosure F)) m (compNatCast_ne_zero F m)
      (compSepTorsPt F B m (σ • P)) (compSepTorsPt F B m (σ • Q)) =
    muAlgSMul F m σ (Isogeny.weilPairing (B.baseChange (AlgebraicClosure F)) m
      (compNatCast_ne_zero F m) (compSepTorsPt F B m P) (compSepTorsPt F B m Q))
  rw [compSepTorsPt_smul, compSepTorsPt_smul,
    weilPairing_torsionGaloisAction (K := AlgebraicClosure F) B m (compNatCast_ne_zero F m) σ
      (compSepTorsPt F B m P) (compSepTorsPt F B m Q)]
  apply muAlg_ext F m
  rw [muAlgVal_muAlgSMul]
  exact restrictRootsOfUnity_coe_apply _ _

open scoped Classical in
/-- PROVED. **The Weil pairing over `F̄` corresponds to the other group's Weil pairing over `Fˢ`**:
`e_m(e P, e Q) = e(e_m(P, Q))` for `P, Q ∈ B(Fˢ)[m]`, i.e. `compWeil` and the other group's
`torsionCoeffWeilPairing` agree under `compSepTors` and `compMu` (the other group's
`weilPairing_torsionMapAlong`, `weilPairing_torsionByCongr_cast`; Silverman III.8.1). -/
theorem compWeil_compTors (hm : IsUnit (m : F)) (P Q : B.TorsionCoeff m) :
    compWeil F B m (compSepTors F B m P) (compSepTors F B m Q) =
      compMu F m (B.torsionCoeffWeilPairing m hm P Q) := by
  have hm' : (m : SeparableClosure F) ≠ 0 := hm.natCast_ne_zero_of_algebra
  rw [compWeil_apply, torsionCoeffWeilPairing_apply B m hm hm']
  change Isogeny.weilPairing (B.baseChange (AlgebraicClosure F)) m (compNatCast_ne_zero F m)
      (compSepTorsPt F B m (compSepTors F B m P)) (compSepTorsPt F B m (compSepTors F B m Q)) = _
  rw [compSepTorsPt_compTors, compSepTorsPt_compTors,
    weilPairing_torsionByCongr_cast _ _ (compNatCast_ne_zero F m),
    weilPairing_torsionMapAlong _ _ _ hm']
  apply muAlg_ext F m
  rw [muAlgVal_compMu]
  exact restrictRootsOfUnity_coe_apply _ _

end Weil

end ZInQ.Manuscript.RC.KummerMaps
