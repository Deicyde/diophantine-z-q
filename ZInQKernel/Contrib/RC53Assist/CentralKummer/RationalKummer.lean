import ZInQKernel.Contrib.OneProof.RC.KummerMaps.LocalGlobal
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.TateBasis
import ZInQKernel.Contrib.OneProof.RC.Wiring.BaseZeroText
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchLeaf
import ZInQKernel.Contrib.RC53Assist.CentralSelmer.Comparison
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Flat

/-!
# Input (1) of the central comparison, pinned to the genuine rational Kummer complex

Input (1) of `centralSelmerComparisonOfSpecializedModel` asks for a complex `K` of `ℚ₂`-vector
spaces, a cochain map `i : K ⟶ CU ⊗_A ℚ₂` into the specialized base model with `[QuasiIsoAt i 1]`,
and `CU.d 0 1 = 0`. As free data this is satisfied by `K := CU ⊗_A ℚ₂`, `i := 𝟙`. This file pins
both ends to genuine objects and determines exactly what input (1) then asserts.

## The genuine objects

* **`K₀`** (manuscript lines 3952--3962 and 4007--4018): `rationalKummerComplex S W hFull`, the
  ordinary compact Kummer complex `C_K = compactKummerComplex S W hFull` tensored with `ℚ₂`.
  `C_K` is the Selmer complex (4.3) of the genuine Galois Selmer data `galoisSelData` over `ℤ₂`,
  with coefficients the `2`-adic Tate module `T₂E = lim E(K_S)[2^n]` (inverse-limit topology,
  continuous Galois action) and, at every place `v ∈ S`, the **`2`-adic Kummer condition**
  `U⁰ = C⁰_cont(G_{K_v}, T₂E)`, `U¹ = Z_v ⊔ B¹_cont`, `Uⁿ = 0` otherwise, where `Z_v` is the
  `ℤ₂`-span of the `2`-adic Kummer cocycles `σ ↦ (σ R n − R n)_n` of the points of `E(K_v)`, for
  compatible towers `R` of `2`-power division points, read in `E(K_S)[2^n]` through the inverse of
  the decomposition comparison `compTorsEquiv` at every level. The only hypothesis is the full
  `2`-power torsion of `E` over `K_S` (`hFull`, Néron--Ogg--Shafarevich for `S` containing the places
  above `2` and of bad reduction), already used by the finite-level Kummer maps.
  Proved properties: the cocycle identity and continuity (`tateKummerCocycleOf_isCocycle`);
  independence of the towers up to continuous coboundaries (`tateKummerCocycleOf_sub_mem`,
  `tateKummerCocycleOf_mem_sup`); additivity up to coboundaries (`tateKummerCocycle_add_sub_mem`);
  `H⁰` of the condition is local `H⁰` and `H¹` injects into local `H¹`
  (`tateKummerCondition_isIso_homologyMap_zero`, `tateKummerCondition_mono_homologyMap_one`);
  reduction modulo `2^n` gives the finite-level Kummer cocycle of the division point, which lies in
  the finite-level Kummer condition (`tateKummer_reduction`); the data are genuine Galois Selmer data
  for finite `S` (`isGaloisSelData_tateKummerSelData`); `Hⁿ(K₀) ≅ Hⁿ(C_K) ⊗_{ℤ₂} ℚ₂`
  (`rationalKummerHomologyIso`, flat base change). For a base-zero leaf model `M` the complex is
  `leafKummerComplex M S hFull`, for `E_ℓ` over the leaf's field `K = ℚ(√k)`.
  The finite-level Kummer complexes themselves cannot serve as `K₀`: their rationalization is
  zero (the companion development on finite levels, `finiteLevel_kummer_input_one_refuted`).
* **`CU`** (lines 4341--4364): the base model is the two-term complex `[A^{m+1} --Dm--> A^{m+1}]`
  in degrees one and two (`twoTermModel Dm`), with canonical coordinates and `hd`
  (`twoTermModel_hd`), and `CU.d 0 1 = 0` because its degree-zero term is zero
  (`twoTermModel_d_zero_one`). The comparison type `CentralSelmerComparison … Dm` depends on the
  model only through `Dm`, so this model can be used for every leaf; for the leaf's own `CU` the
  conclusion `CU.d 0 1 = 0` follows from a zero degree-zero term (`d_zero_one_of_isZero`).

## What input (1) asserts for these objects

* Over a field every linear isomorphism `H¹(K) ≃ H¹(C)` is induced by an explicit cochain map
  concentrated in degree one (`comparisonMap`, `homologyMap_comparisonMap`), a quasi-isomorphism in
  degree one; so degree-one quasi-isomorphisms exist exactly when the degree-one cohomologies are
  isomorphic (`nonempty_quasiIsoAt_one_iff`).
* Hence input (1) for the genuine `K₀` and the base model holds **exactly** when
  `H¹(K₀) ≃ ker ρ(Dm)` (`genuine_input_one_iff`, `curve_input_one_iff`, `leaf_input_one_iff`),
  equivalently, for finite-dimensional `H¹(K₀)`, when `dim H¹(K₀) = dim ker ρ(Dm)`
  (`genuine_input_one_iff_finrank`). The map `i` is constructed from such an identification
  (`genuineKummerModelMap`, `KummerInputOne.map`, with their quasi-isomorphism instances).
  `KummerInputOne ℓ K hE Dm` packages pinned input (1) for `E_ℓ` over `K` and a model matrix `Dm`
  (independently of a leaf, so that it can replace the field `central`); `KummerInputOne.central`
  and `leafCentral` produce the comparison from it and inputs (2), (3).
* With the universal-coefficient and descent data and under full Selmer corank one, input (1) is
  equivalent to the base-zero field `hcentral : rank ρ(Dm) = m` (`input_one_iff_hcentral`,
  `nonempty_kummerInputOne_iff`), and every existing leaf model yields pinned input (1)
  (`nonempty_leafKummerInputOne`).
* The replacement of the field `central` by pinned input (1) is lossless at the level of data:
  the comparison rebuilt from pinned input (1) is `x ↦ e (φ⁻¹ x)` with `e` the
  universal-coefficient and descent comparison (`KummerInputOne.central_cmp_apply`), and a given
  comparison `C` is recovered exactly from `KummerInputOne.ofCentral C`
  (`KummerInputOne.central_ofCentral`).

## What remains open

The identification `φ : H¹(K₀) ≃ ker ρ(Dm)` itself. In the manuscript it comes from the
comparison `i : K₀ → R₀ = C_U(M)₀` with the central fibre of the actual primitive complex (lines
3952--3962) and from the identification of the base model with that complex after cancelling unit
disks (lines 4353--4360). The leaf's matrix `Dm` is a free field: no primitive complex over
`Λ_(t)` and no identification of `Dm` with it is constructed in the project, so `φ` cannot be
derived here. No printed statement is assumed in this file.
-/

noncomputable section

namespace ZInQ.Manuscript.RC53Assist.CentralKummer

open CategoryTheory

section FieldComparison

variable {k : Type} [Field k] (K C : CochainComplex (ModuleCat.{0} k) ℤ)

/-- The inclusion of cycles is injective. -/
theorem iCycles_ker_eq_bot (n : ℤ) : LinearMap.ker (K.iCycles n).hom = ⊥ :=
  LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- The projection from cycles onto cohomology is surjective. -/
theorem homologyπ_surjective (n : ℤ) : Function.Surjective (K.homologyπ n).hom :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- Over a field the cohomology is a projective module. -/
theorem projective_homology (n : ℤ) : Module.Projective k (C.homology n) :=
  haveI : Module.Free k (C.homology n) := Module.Free.of_divisionRing k _
  Module.Projective.of_free

/-- A linear retraction of the inclusion of cycles (it exists over a field). -/
def cyclesRetraction (n : ℤ) : K.X n →ₗ[k] K.cycles n :=
  Classical.choose (LinearMap.exists_leftInverse_of_injective (K.iCycles n).hom
    (iCycles_ker_eq_bot K n))

/-- The retraction is a left inverse of the inclusion of cycles. -/
theorem cyclesRetraction_iCycles (n : ℤ) (z : K.cycles n) :
    cyclesRetraction K n ((K.iCycles n).hom z) = z :=
  LinearMap.congr_fun (Classical.choose_spec (LinearMap.exists_leftInverse_of_injective
    (K.iCycles n).hom (iCycles_ker_eq_bot K n))) z

/-- A linear section of the projection from cycles onto cohomology (it exists over a field). -/
def homologySection (n : ℤ) : C.homology n →ₗ[k] C.cycles n :=
  haveI := projective_homology C n
  Classical.choose (LinearMap.exists_rightInverse_of_surjective (C.homologyπ n).hom
    (LinearMap.range_eq_top.mpr (homologyπ_surjective C n)))

/-- The section is a right inverse of the projection onto cohomology. -/
theorem homologyπ_homologySection (n : ℤ) (x : C.homology n) :
    (C.homologyπ n).hom (homologySection C n x) = x :=
  haveI := projective_homology C n
  LinearMap.congr_fun (Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective
    (C.homologyπ n).hom (LinearMap.range_eq_top.mpr (homologyπ_surjective C n)))) x

variable {K C}

/-- The degree-one component of the comparison, with values in `H¹(C)`:
`x ↦ φ [r x]`, for the retraction `r` onto the cycles. -/
def toH1 (φ : K.homology 1 ≃ₗ[k] C.homology 1) : K.X 1 ⟶ ModuleCat.of k (C.homology 1) :=
  ModuleCat.ofHom (φ.toLinearMap ∘ₗ (K.homologyπ 1).hom ∘ₗ cyclesRetraction K 1)

/-- The cycle representative `H¹(C) → C¹` given by the chosen section. -/
def fromH1 : ModuleCat.of k (C.homology 1) ⟶ C.X 1 :=
  ModuleCat.ofHom ((C.iCycles 1).hom ∘ₗ homologySection C 1)

/-- The degree-one component kills the incoming differential (it factors through cycles
modulo boundaries). -/
theorem d_toH1 (φ : K.homology 1 ≃ₗ[k] C.homology 1) (i : ℤ)
    (_hi : (ComplexShape.up ℤ).Rel i 1) : K.d i 1 ≫ toH1 φ = 0 := by
  rw [← K.toCycles_i i 1]
  ext x
  change φ ((K.homologyπ 1).hom (cyclesRetraction K 1 ((K.iCycles 1).hom
    ((K.toCycles i 1).hom x)))) = 0
  rw [cyclesRetraction_iCycles]
  have h := congrArg (fun f => f.hom x) (K.toCycles_comp_homologyπ i 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  rw [h, map_zero]

/-- The cycle representative is killed by the outgoing differential. -/
theorem fromH1_d (k' : ℤ) (_hk : (ComplexShape.up ℤ).Rel 1 k') :
    fromH1 (C := C) ≫ C.d 1 k' = 0 := by
  change ModuleCat.ofHom (homologySection C 1) ≫ C.iCycles 1 ≫ C.d 1 k' = 0
  rw [C.iCycles_d, Limits.comp_zero]

/-- **The cochain map inducing a prescribed isomorphism in degree one.** For complexes over a
field and a linear isomorphism `φ : H¹(K) ≃ H¹(C)`, the composite
`K ⟶ H¹(C)[−1] ⟶ C` of `toH1 φ` and the cycle representative `fromH1`. It is zero outside
degree one. -/
def comparisonMap (φ : K.homology 1 ≃ₗ[k] C.homology 1) : K ⟶ C :=
  HomologicalComplex.mkHomToSingle (toH1 φ) (d_toH1 φ) ≫
    HomologicalComplex.mkHomFromSingle (fromH1 (C := C)) fromH1_d

/-- The degree-one component of the comparison map. -/
theorem comparisonMap_f_one (φ : K.homology 1 ≃ₗ[k] C.homology 1) :
    (comparisonMap φ).f 1 = toH1 φ ≫ fromH1 (C := C) := by
  rw [comparisonMap, HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
    HomologicalComplex.mkHomFromSingle_f, Category.assoc, Iso.inv_hom_id_assoc]

/-- On cycles, the comparison map is `z ↦ s (φ [z])`. -/
theorem cyclesMap_comparisonMap (φ : K.homology 1 ≃ₗ[k] C.homology 1) (z : K.cycles 1) :
    (HomologicalComplex.cyclesMap (comparisonMap φ) 1).hom z =
      homologySection C 1 (φ ((K.homologyπ 1).hom z)) := by
  apply (ModuleCat.mono_iff_injective (C.iCycles 1)).mp inferInstance
  have h := congrArg (fun f => f.hom z) (HomologicalComplex.cyclesMap_i (comparisonMap φ) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, comparisonMap_f_one]
  change (C.iCycles 1).hom (homologySection C 1 (φ ((K.homologyπ 1).hom
    (cyclesRetraction K 1 ((K.iCycles 1).hom z))))) = _
  rw [cyclesRetraction_iCycles]

/-- **The comparison map induces `φ` on degree-one cohomology.** -/
theorem homologyMap_comparisonMap (φ : K.homology 1 ≃ₗ[k] C.homology 1) (x : K.homology 1) :
    (HomologicalComplex.homologyMap (comparisonMap φ) 1).hom x = φ x := by
  obtain ⟨z, rfl⟩ := homologyπ_surjective K 1 x
  have h := congrArg (fun f => f.hom z)
    (HomologicalComplex.homologyπ_naturality (comparisonMap φ) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, cyclesMap_comparisonMap, homologyπ_homologySection]

/-- The comparison map is a quasi-isomorphism in degree one. -/
instance quasiIsoAt_comparisonMap (φ : K.homology 1 ≃ₗ[k] C.homology 1) :
    QuasiIsoAt (comparisonMap φ) 1 := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : HomologicalComplex.homologyMap (comparisonMap φ) 1 = φ.toModuleIso.hom := by
    ext x
    exact homologyMap_comparisonMap φ x
  rw [this]
  infer_instance

variable (K C) in
/-- **Degree-one quasi-isomorphisms over a field are exactly degree-one cohomology
isomorphisms.** -/
theorem nonempty_quasiIsoAt_one_iff :
    (∃ i : K ⟶ C, QuasiIsoAt i 1) ↔ Nonempty (K.homology 1 ≃ₗ[k] C.homology 1) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨(asIso (HomologicalComplex.homologyMap i 1)).toLinearEquiv⟩
  · rintro ⟨φ⟩
    exact ⟨comparisonMap φ, inferInstance⟩

end FieldComparison

section TwoTermModel

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC53Assist.CentralSelmer Matrix

/-- `1 → 2` is a step of the cohomological shape. -/
theorem rel_one_two : (ComplexShape.up ℤ).Rel 1 2 := rfl

variable {m : ℕ} (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)

/-- The differential `Dm : A^{m+1} → A^{m+1}` as a morphism of modules. -/
def modelHom : ModuleCat.of Rings.LambdaT (Fin (m + 1) → Rings.LambdaT) ⟶
    ModuleCat.of Rings.LambdaT (Fin (m + 1) → Rings.LambdaT) :=
  ModuleCat.ofHom Dm.mulVecLin

/-- **The two-term base model** `[A^{m+1} --Dm--> A^{m+1}]`, in degrees one and two, over
`A = Λ_(t)` (Lemma `ex:arith-base-zero`, manuscript lines 4341--4364). -/
def twoTermModel : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ :=
  HomologicalComplex.double (modelHom Dm) rel_one_two

/-- The degree-one coordinates of the two-term model. -/
def twoTermModelE1 :
    (twoTermModel Dm).X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT) :=
  (HomologicalComplex.doubleXIso₀ _ rel_one_two).toLinearEquiv

/-- The degree-two coordinates of the two-term model. -/
def twoTermModelE2 :
    (twoTermModel Dm).X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT) :=
  (HomologicalComplex.doubleXIso₁ _ rel_one_two (by decide)).toLinearEquiv

/-- The two-term model vanishes outside degrees one and two. -/
theorem twoTermModel_isZero (n : ℤ) (h₁ : n ≠ 1) (h₂ : n ≠ 2) :
    Limits.IsZero ((twoTermModel Dm).X n) :=
  HomologicalComplex.isZero_double_X _ rel_one_two n h₁ h₂

/-- **`CU.d 0 1 = 0` for the two-term model**: its degree-zero term is zero. -/
theorem twoTermModel_d_zero_one : (twoTermModel Dm).d 0 1 = 0 :=
  (twoTermModel_isZero Dm 0 (by decide) (by decide)).eq_of_src _ _

/-- **In the canonical coordinates the differential of the two-term model is `Dm`.** -/
theorem twoTermModel_hd (x : (twoTermModel Dm).X 1) :
    twoTermModelE2 Dm (((twoTermModel Dm).d 1 2).hom x) = Dm *ᵥ twoTermModelE1 Dm x := by
  have h : (HomologicalComplex.double (modelHom Dm) rel_one_two).d 1 2 ≫
      (HomologicalComplex.doubleXIso₁ (modelHom Dm) rel_one_two (by decide)).hom =
      (HomologicalComplex.doubleXIso₀ (modelHom Dm) rel_one_two).hom ≫ modelHom Dm := by
    rw [HomologicalComplex.double_d (modelHom Dm) rel_one_two (by decide)]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hx := congrArg (fun g => g.hom x) h
  simp only [ModuleCat.hom_comp, modelHom, ModuleCat.hom_ofHom] at hx
  exact hx

/-- For any model complex, a zero degree-zero term gives `CU.d 0 1 = 0`. -/
theorem d_zero_one_of_isZero {R : Type} [CommRing R] (CU : CochainComplex (ModuleCat.{0} R) ℤ)
    (h : Limits.IsZero (CU.X 0)) : CU.d 0 1 = 0 :=
  h.eq_of_src _ _

/-- **The central degree-one cohomology of the two-term model is the central kernel**
`ker ρ(Dm)` (coefficient extension of the actual complex, `specializedModelHomologyOneEquiv`). -/
def twoTermCentralH1 :
    (scalarChangedComplex Rings.rhoT (twoTermModel Dm)).homology 1 ≃ₗ[ℚ_[2]]
      LinearMap.ker (Dm.map Rings.rhoT).mulVecLin :=
  specializedModelHomologyOneEquiv Rings.rhoT (twoTermModel Dm) Dm (twoTermModelE1 Dm)
    (twoTermModelE2 Dm) (twoTermModel_d_zero_one Dm) (twoTermModel_hd Dm)

variable {Dm}

/-- **Input (1) for the two-term base model, from a degree-one identification.** For a complex
`K` of `ℚ₂`-vector spaces and a linear isomorphism `φ : H¹(K) ≃ ker ρ(Dm)`, the cochain map
`K ⟶ (twoTermModel Dm) ⊗_A ℚ₂` concentrated in degree one inducing `φ`. -/
def kummerModelMap (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ)
    (φ : K.homology 1 ≃ₗ[ℚ_[2]] LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) :
    K ⟶ scalarChangedComplex Rings.rhoT (twoTermModel Dm) :=
  comparisonMap (φ.trans (twoTermCentralH1 Dm).symm)

/-- The comparison into the two-term model is a quasi-isomorphism in degree one. -/
instance quasiIsoAt_kummerModelMap (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ)
    (φ : K.homology 1 ≃ₗ[ℚ_[2]] LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) :
    QuasiIsoAt (kummerModelMap K φ) 1 :=
  quasiIsoAt_comparisonMap _

/-- The map of `kummerModelMap` on degree-one cohomology, read in the central kernel, is `φ`. -/
theorem twoTermCentralH1_homologyMap_kummerModelMap (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ)
    (φ : K.homology 1 ≃ₗ[ℚ_[2]] LinearMap.ker (Dm.map Rings.rhoT).mulVecLin)
    (x : K.homology 1) :
    twoTermCentralH1 Dm
        ((HomologicalComplex.homologyMap (kummerModelMap K φ) 1).hom x) = φ x := by
  rw [kummerModelMap, homologyMap_comparisonMap, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]

/-- **Input (1) holds exactly when degree-one cohomology is the central kernel.** For any model
`CU` with coordinates `e1`, `e2` for `Dm` and `CU.d 0 1 = 0`, and any complex `K` of
`ℚ₂`-vector spaces, a degree-one quasi-isomorphism `K ⟶ CU ⊗_A ℚ₂` exists if and only if
`H¹(K) ≃ ker ρ(Dm)`. -/
theorem nonempty_input_one_iff (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ) :
    (∃ i : K ⟶ scalarChangedComplex Rings.rhoT CU, QuasiIsoAt i 1) ↔
      Nonempty (K.homology 1 ≃ₗ[ℚ_[2]] LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) := by
  rw [nonempty_quasiIsoAt_one_iff]
  let e := specializedModelHomologyOneEquiv Rings.rhoT CU Dm e1 e2 hzero hd
  exact ⟨fun ⟨φ⟩ => ⟨φ.trans e⟩, fun ⟨φ⟩ => ⟨φ.trans e.symm⟩⟩

/-- **The finite-dimensional form**: input (1) holds exactly when `dim H¹(K) = dim ker ρ(Dm)`. -/
theorem nonempty_input_one_iff_finrank (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ) [FiniteDimensional ℚ_[2] (K.homology 1)] :
    (∃ i : K ⟶ scalarChangedComplex Rings.rhoT CU, QuasiIsoAt i 1) ↔
      Module.finrank ℚ_[2] (K.homology 1) =
        Module.finrank ℚ_[2] (LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) := by
  rw [nonempty_input_one_iff CU e1 e2 hzero hd K]
  exact ⟨fun ⟨φ⟩ => φ.finrank_eq, fun h => ⟨LinearEquiv.ofFinrankEq _ _ h⟩⟩

end TwoTermModel

section Constructor

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC53Assist.CentralSelmer ZInQ.Manuscript.SelmerTwoPower
  ZInQ.Manuscript.RC.BaseZeroLimit ZInQ.Contrib.CloudB3RC53

/-- **The central comparison from the degree-one Kummer identification.** Input (1) of
`centralSelmerComparisonOfSpecializedModel` is supplied by the two-term base model
(`twoTermModel Dm`, with `CU.d 0 1 = 0` and its coordinates proved) and the explicit cochain map
`kummerModelMap K φ` with its degree-one quasi-isomorphism instance. The remaining inputs are the
degree-one identification `φ`, the universal-coefficient data `eK`, `j`, `hj` and the quadratic
descent data `f`, `hf`. -/
def centralSelmerComparisonOfKummerIdentification {ℓ : ℕ} {k : ℤ} {m r : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ)
    (φ : K.homology 1 ≃ₗ[ℚ_[2]] LinearMap.ker (Dm.map Rings.rhoT).mulVecLin)
    (eK : K.homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {S : Type} [AddCommGroup S] (j : (Fin r → Q2Z2) →+ S) (hj : BoundedDefects j)
    (f : S →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f) :
    CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm :=
  centralSelmerComparisonOfSpecializedModel Dm (twoTermModel Dm) (twoTermModelE1 Dm)
    (twoTermModelE2 Dm) (twoTermModel_d_zero_one Dm) (twoTermModel_hd Dm) K
    (kummerModelMap K φ) eK j hj f hf

end Constructor

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
  ZInQ.Manuscript.RC.LambdaCoef ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

attribute [local instance] levTop

section Topology

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}

/-- Scalar multiplication by `a ∈ ℤ₂` on `T₂E` is continuous (at level `n` it is multiplication by
`a mod 2^n` on the discrete group `E(K_S)[2^n]`). -/
instance continuousConstSMul_tateS : ContinuousConstSMul ℤ_[2] (TateS K S W) := by
  refine ⟨fun a => continuous_induced_rng.mpr (continuous_pi fun n => ?_)⟩
  change Continuous (fun P : TateS K S W => resN n a • projLev n P)
  exact (continuous_of_discreteTopology (f := fun x : Lev K S W n => resN n a • x)).comp
    (continuous_projLev n)

end Topology

section Tower

variable (F : Type) [Field F] [DecidableEq F] (B : WeierstrassCurve F)

/-- **A compatible tower of `2`-power division points** of `P ∈ B(F)` in `B(F̄)`:
`R 0 = P` and `2 R (n + 1) = R n`. -/
def IsDivTower (P : B.toAffine.Point) (R : ℕ → PtAlg F B) : Prop :=
  R 0 = basePt F B P ∧ ∀ n, 2 • R (n + 1) = R n

/-- The chosen tower: `R 0 = P`, and `R (n + 1)` a chosen half of `R n` (`B(F̄)` is divisible). -/
def divTower [CharZero F] [B.IsElliptic] (P : B.toAffine.Point) : ℕ → PtAlg F B
  | 0 => basePt F B P
  | n + 1 => Classical.choose (exists_nsmul_eq (F := F) (B := B) 2 (divTower P n))

/-- `2 R (n + 1) = R n` for the chosen tower. -/
theorem two_smul_divTower [CharZero F] [B.IsElliptic] (P : B.toAffine.Point) (n : ℕ) :
    2 • divTower F B P (n + 1) = divTower F B P n :=
  Classical.choose_spec (exists_nsmul_eq (F := F) (B := B) 2 (divTower F B P n))

/-- The chosen tower is a compatible tower. -/
theorem isDivTower_divTower [CharZero F] [B.IsElliptic] (P : B.toAffine.Point) :
    IsDivTower F B P (divTower F B P) :=
  ⟨rfl, two_smul_divTower F B P⟩

variable {F B}

/-- `2^n R n = P`. -/
theorem IsDivTower.two_pow_smul {P : B.toAffine.Point} {R : ℕ → PtAlg F B}
    (h : IsDivTower F B P R) (n : ℕ) : (2 ^ n : ℕ) • R n = basePt F B P := by
  induction n with
  | zero => simpa using h.1
  | succ n ih => rw [pow_succ, mul_comm, mul_nsmul, h.2 n, ih]

/-- The sum of compatible towers of `P` and `P'` is a compatible tower of `P + P'`. -/
theorem IsDivTower.add {P P' : B.toAffine.Point} {R R' : ℕ → PtAlg F B}
    (h : IsDivTower F B P R) (h' : IsDivTower F B P' R') : IsDivTower F B (P + P') (R + R') :=
  ⟨by rw [Pi.add_apply, h.1, h'.1, map_add], fun n => by rw [Pi.add_apply, Pi.add_apply,
    nsmul_add, h.2 n, h'.2 n]⟩

/-- **The level-`n` Kummer function of a tower**: `σ ↦ σ R n − R n ∈ B(F̄)[2^n]`; this is the
finite-level Kummer function `kummerFunOf` of the division point `R n`. -/
def towerKummerOf {P : B.toAffine.Point} {R : ℕ → PtAlg F B} (h : IsDivTower F B P R) (n : ℕ)
    (σ : Field.absoluteGaloisGroup F) : TorsAlg F B (2 ^ n) :=
  kummerFunOf F B (2 ^ n) (h.two_pow_smul n) σ

/-- The value of the level-`n` Kummer function of a tower. -/
theorem coe_towerKummerOf {P : B.toAffine.Point} {R : ℕ → PtAlg F B} (h : IsDivTower F B P R)
    (n : ℕ) (σ : Field.absoluteGaloisGroup F) :
    (towerKummerOf h n σ : PtAlg F B) = σ • R n - R n :=
  rfl

/-- The level-`n` Kummer function of a tower is continuous (locally constant). -/
theorem continuous_towerKummerOf {P : B.toAffine.Point} {R : ℕ → PtAlg F B}
    (h : IsDivTower F B P R) (n : ℕ) : Continuous (towerKummerOf h n) :=
  Continuous.subtype_mk ((continuous_id.smul continuous_const).sub continuous_const) _

/-- The cocycle identity `κ(στ) = σ κ(τ) + κ(σ)` at level `n`. -/
theorem towerKummerOf_mul {P : B.toAffine.Point} {R : ℕ → PtAlg F B} (h : IsDivTower F B P R)
    (n : ℕ) (σ τ : Field.absoluteGaloisGroup F) :
    towerKummerOf h n (σ * τ) = σ • towerKummerOf h n τ + towerKummerOf h n σ := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, coe_smul_torsAlg, coe_towerKummerOf, mul_smul, smul_sub]
  abel

/-- Compatibility of the levels: `2 κ_{n+1}(σ) = κ_n(σ)`. -/
theorem two_smul_towerKummerOf {P : B.toAffine.Point} {R : ℕ → PtAlg F B}
    (h : IsDivTower F B P R) (n : ℕ) (σ : Field.absoluteGaloisGroup F) :
    2 • (towerKummerOf h (n + 1) σ : PtAlg F B) = towerKummerOf h n σ := by
  rw [coe_towerKummerOf, coe_towerKummerOf, nsmul_sub, smul_comm, h.2 n]

/-- The level-`n` Kummer function of a sum of towers is the sum of the Kummer functions. -/
theorem towerKummerOf_add {P P' : B.toAffine.Point} {R R' : ℕ → PtAlg F B}
    (h : IsDivTower F B P R) (h' : IsDivTower F B P' R') (n : ℕ)
    (σ : Field.absoluteGaloisGroup F) :
    towerKummerOf (h.add h') n σ = towerKummerOf h n σ + towerKummerOf h' n σ := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, coe_towerKummerOf, Pi.add_apply, smul_add]
  abel

/-- The difference of two towers of the same point, at level `n`: an element of `B(F̄)[2^n]`. -/
def towerDiff {P : B.toAffine.Point} {R R' : ℕ → PtAlg F B} (h : IsDivTower F B P R)
    (h' : IsDivTower F B P R') (n : ℕ) : TorsAlg F B (2 ^ n) :=
  ⟨R n - R' n, by
    rw [AddSubgroup.torsionBy.nsmul_iff, nsmul_sub, h.two_pow_smul n, h'.two_pow_smul n,
      sub_self]⟩

/-- Compatibility of the levels of the difference of two towers. -/
theorem two_smul_towerDiff {P : B.toAffine.Point} {R R' : ℕ → PtAlg F B}
    (h : IsDivTower F B P R) (h' : IsDivTower F B P R') (n : ℕ) :
    2 • (towerDiff h h' (n + 1) : PtAlg F B) = towerDiff h h' n := by
  change 2 • (R (n + 1) - R' (n + 1)) = R n - R' n
  rw [nsmul_sub, h.2 n, h'.2 n]

/-- Two towers of the same point give level-`n` Kummer functions differing by the coboundary of
their difference. -/
theorem towerKummerOf_sub {P : B.toAffine.Point} {R R' : ℕ → PtAlg F B}
    (h : IsDivTower F B P R) (h' : IsDivTower F B P R') (n : ℕ)
    (σ : Field.absoluteGaloisGroup F) :
    towerKummerOf h n σ - towerKummerOf h' n σ = σ • towerDiff h h' n - towerDiff h h' n := by
  apply Subtype.ext
  change (σ • R n - R n) - (σ • R' n - R' n) = σ • (R n - R' n) - (R n - R' n)
  rw [smul_sub]
  abel

end Tower

section TwoAdic

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (v.adicCompletion K)]

/-- A compatible system of elements `t n ∈ E(K̄_v)[2^n]` (`2 t (n + 1) = t n`), read through the
inverse identifications `E(K_S)[2^n] ≃ E(K̄_v)[2^n]`, is an element of `T₂E`. -/
def tateOfLocal
    (t : ∀ n : ℕ, TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ n))
    (ht : ∀ n, 2 • (t (n + 1) : PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))) =
      t n) : TateS K S W :=
  ⟨fun n => (compTorsEquiv W (2 ^ n) (hFull n) v).symm (t n), fun n => by
    apply compTors_injective W (2 ^ n) v
    apply Subtype.ext
    rw [coe_compTors, coe_transLev, map_nsmul, ← coe_compTors,
      ← compTorsEquiv_apply W _ (hFull _), ← compTorsEquiv_apply W _ (hFull _),
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ht n]⟩

omit [DecidableEq (v.adicCompletion K)] in
/-- The level-`n` coordinate of `tateOfLocal t`, read in `E(K̄_v)[2^n]`, is `t n`. -/
theorem compTors_tateOfLocal
    (t : ∀ n : ℕ, TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ n))
    (ht : ∀ n, 2 • (t (n + 1) : PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))) =
      t n) (n : ℕ) :
    compTors W (2 ^ n) v (projLev n (tateOfLocal W hFull v t ht)) = t n := by
  rw [← compTorsEquiv_apply W (2 ^ n) (hFull n)]
  exact AddEquiv.apply_symm_apply _ _

/-- **The `2`-adic Kummer function of a tower** `σ ↦ (σ R n − R n)_n ∈ T₂E`, with values in the
Tate module of `E(K_S)` through the inverse identifications at every level. -/
def tateKummerFunOf {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) (σ : Gloc K v) : TateS K S W :=
  tateOfLocal W hFull v (fun n => towerKummerOf h n σ) (fun n => two_smul_towerKummerOf h n σ)

/-- **The levels of the `2`-adic Kummer function** are the finite-level Kummer functions of the
division points of the tower, read in `E(K̄_v)[2^n]`. -/
theorem compTors_tateKummerFunOf {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) (σ : Gloc K v) (n : ℕ) :
    compTors W (2 ^ n) v (projLev n (tateKummerFunOf W hFull v h σ)) = towerKummerOf h n σ :=
  compTors_tateOfLocal W hFull v _ _ n

/-- The cocycle identity for the `2`-adic Kummer function, with `G_{K_v}` acting on `T₂E` through
the localization `G_{K_v} → G_{K,S}`. -/
theorem tateKummerFunOf_mul {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) (σ τ : Gloc K v) :
    tateKummerFunOf W hFull v h (σ * τ) =
      locMap K S v σ • tateKummerFunOf W hFull v h τ + tateKummerFunOf W hFull v h σ := by
  apply Subtype.ext
  funext n
  change (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf h n (σ * τ)) =
    locMap K S v σ • (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf h n τ) +
      (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf h n σ)
  rw [towerKummerOf_mul, map_add, compTorsEquiv_symm_smul]

/-- The `2`-adic Kummer function of a sum of towers is the sum of the Kummer functions. -/
theorem tateKummerFunOf_add {P P' : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R R' : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) (h' : IsDivTower _ _ P' R') (σ : Gloc K v) :
    tateKummerFunOf W hFull v (h.add h') σ =
      tateKummerFunOf W hFull v h σ + tateKummerFunOf W hFull v h' σ := by
  apply Subtype.ext
  funext n
  change (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf (h.add h') n σ) =
    (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf h n σ) +
      (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf h' n σ)
  rw [towerKummerOf_add, map_add]

/-- The element of `T₂E` given by the difference of two towers of the same point. -/
def tateTowerDiff {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R R' : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) (h' : IsDivTower _ _ P R') : TateS K S W :=
  tateOfLocal W hFull v (fun n => towerDiff h h' n) (fun n => two_smul_towerDiff h h' n)

/-- Two towers of the same point give `2`-adic Kummer functions differing by the coboundary of the
element `tateTowerDiff` of `T₂E`. -/
theorem tateKummerFunOf_sub {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R R' : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) (h' : IsDivTower _ _ P R') (σ : Gloc K v) :
    tateKummerFunOf W hFull v h σ - tateKummerFunOf W hFull v h' σ =
      locMap K S v σ • tateTowerDiff W hFull v h h' - tateTowerDiff W hFull v h h' := by
  apply Subtype.ext
  funext n
  change (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf h n σ) -
      (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf h' n σ) =
    locMap K S v σ • (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerDiff h h' n) -
      (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerDiff h h' n)
  rw [← map_sub, towerKummerOf_sub, map_sub, compTorsEquiv_symm_smul]

/-- The `2`-adic Kummer function is continuous for the inverse-limit topology of `T₂E`. -/
theorem continuous_tateKummerFunOf {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) : Continuous (tateKummerFunOf W hFull v h) := by
  refine continuous_induced_rng.mpr (continuous_pi fun n => ?_)
  change Continuous (fun σ => (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf h n σ))
  exact continuous_of_discreteTopology.comp (continuous_towerKummerOf h n)

/-- **The `2`-adic Kummer cocycle of a tower**, a continuous inhomogeneous `1`-cochain of
`G_{K_v}` with values in `T₂E` (with `G_{K_v}` acting through the localization). -/
def tateKummerCocycleOf {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) :
    contCochain ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 1 :=
  ⟨(fun g => (tateKummerFunOf W hFull v h (g 0) : ResMod (locMap K S v) (TateS K S W)) :
      (Fin 1 → Gloc K v) → ResMod (locMap K S v) (TateS K S W)),
    (continuous_tateKummerFunOf W hFull v h).comp (continuous_apply 0)⟩

/-- The `2`-adic Kummer cochain is a cocycle. -/
theorem tateKummerCocycleOf_isCocycle {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) :
    contD ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 1
      (tateKummerCocycleOf W hFull v h) = 0 := by
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := ℤ_[2]) (G := Gloc K v)
    (M := ResMod (locMap K S v) (TateS K S W)) 1 (tateKummerCocycleOf W hFull v h) g
  refine h1.trans ?_
  rw [Fin.sum_univ_two]
  change locMap K S v (g 0) • tateKummerFunOf W hFull v h (g 1) +
    ((-1 : ℤ_[2]) ^ ((0 : ℕ) + 1) • tateKummerFunOf W hFull v h (g 0 * g 1) +
    (-1 : ℤ_[2]) ^ ((1 : ℕ) + 1) • tateKummerFunOf W hFull v h (g 0)) = 0
  rw [tateKummerFunOf_mul]
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_smul]
  abel

/-- **Two towers of the same point give `2`-adic Kummer cocycles differing by a continuous
coboundary**: the condition does not depend on the chosen division points. -/
theorem tateKummerCocycleOf_sub_mem {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R R' : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) (h' : IsDivTower _ _ P R') :
    tateKummerCocycleOf W hFull v h - tateKummerCocycleOf W hFull v h' ∈
      contB1 ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) := by
  refine (mem_contB1_iff _).2 ⟨constCochain
    (show ResMod (locMap K S v) (TateS K S W) from tateTowerDiff W hFull v h h'), ?_⟩
  apply Subtype.ext
  funext g
  refine (cfun_contD_constCochain (k := ℤ_[2]) (G := Gloc K v)
    (M := ResMod (locMap K S v) (TateS K S W)) _ g).trans ?_
  exact (tateKummerFunOf_sub W hFull v h h' (g 0)).symm

/-- **The `2`-adic Kummer cocycle of a sum of towers is the sum of the cocycles.** -/
theorem tateKummerCocycleOf_add {P P' : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R R' : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) (h' : IsDivTower _ _ P' R') :
    tateKummerCocycleOf W hFull v (h.add h') =
      tateKummerCocycleOf W hFull v h + tateKummerCocycleOf W hFull v h' := by
  apply Subtype.ext
  funext g
  exact tateKummerFunOf_add W hFull v h h' (g 0)

/-- The `2`-adic Kummer cocycle of `P ∈ E(K_v)` for the chosen tower. -/
abbrev tateKummerCocycle (P : (W.baseChange (v.adicCompletion K)).toAffine.Point) :
    contCochain ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 1 :=
  tateKummerCocycleOf W hFull v (isDivTower_divTower _ _ P)

/-- **The `2`-adic Kummer submodule** `Z_v ⊆ C¹_cont(G_{K_v}, T₂E)`: the `ℤ₂`-span of the
`2`-adic Kummer cocycles of the points of `E(K_v)`. -/
abbrev tateKummerZ :
    Submodule ℤ_[2] (contCochain ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 1) :=
  cochainSpan (Set.range (tateKummerCocycle W hFull v))

/-- The `2`-adic Kummer submodule consists of cocycles. -/
theorem tateKummerZ_cocycle :
    ∀ z ∈ tateKummerZ W hFull v,
      contD ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) 1 z = 0 :=
  cochainSpan_cocycle _ (by
    rintro _ ⟨P, rfl⟩
    exact tateKummerCocycleOf_isCocycle W hFull v _)

/-- **Every tower gives a cocycle in `Z_v ⊔ B¹`**: the Kummer condition below does not depend on
the chosen division points. -/
theorem tateKummerCocycleOf_mem_sup {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) :
    tateKummerCocycleOf W hFull v h ∈
      tateKummerZ W hFull v ⊔ contB1 ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) := by
  have hmem := Submodule.add_mem_sup
    (Submodule.subset_span ⟨P, rfl⟩ : tateKummerCocycle W hFull v P ∈ tateKummerZ W hFull v)
    (tateKummerCocycleOf_sub_mem W hFull v h (isDivTower_divTower _ _ P))
  rwa [add_sub_cancel] at hmem

/-- **The `2`-adic Kummer map is additive up to continuous coboundaries.** -/
theorem tateKummerCocycle_add_sub_mem
    (P P' : (W.baseChange (v.adicCompletion K)).toAffine.Point) :
    tateKummerCocycle W hFull v (P + P') - tateKummerCocycle W hFull v P -
        tateKummerCocycle W hFull v P' ∈
      contB1 ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)) := by
  have h := tateKummerCocycleOf_sub_mem W hFull v (isDivTower_divTower _ _ (P + P'))
    ((isDivTower_divTower _ _ P).add (isDivTower_divTower _ _ P'))
  rw [tateKummerCocycleOf_add, ← sub_sub] at h
  exact h

/-- **The `2`-adic Kummer condition at `v`**:
`U⁰ = C⁰_cont(G_{K_v}, T₂E)`, `U¹ = Z_v ⊔ B¹_cont`, `Uⁿ = 0` otherwise. -/
abbrev tateKummerCondition : GCx ℤ_[2] :=
  cocycleCondition (tateKummerZ W hFull v) (tateKummerZ_cocycle W hFull v)

/-- The inclusion of the `2`-adic Kummer condition into the local cochains. -/
abbrev tateKummerConditionι :
    GHom (tateKummerCondition W hFull v)
      (natCx (contCochains ℤ_[2] (Gloc K v) (ResMod (locMap K S v) (TateS K S W)))) :=
  cocycleConditionι (tateKummerZ W hFull v) (tateKummerZ_cocycle W hFull v)

/-- The `2`-adic Kummer condition has the degree-zero cohomology of the local complex. -/
theorem tateKummerCondition_isIso_homologyMap_zero :
    IsIso (HomologicalComplex.homologyMap (GHom.toCC (tateKummerConditionι W hFull v)) 0) :=
  cocycleCondition_isIso_homologyMap_zero _ _

/-- The degree-one cohomology of the `2`-adic Kummer condition injects into local cohomology. -/
theorem tateKummerCondition_mono_homologyMap_one :
    Mono (HomologicalComplex.homologyMap (GHom.toCC (tateKummerConditionι W hFull v)) 1) :=
  cocycleCondition_mono_homologyMap_one _ _

end TwoAdic

section Complex

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))

open scoped Classical in
/-- **The `2`-adic Kummer local conditions** at all places of `S`, in the format of the genuine
Galois Selmer data (`GaloisLocalConditions`). -/
def tateKummerLocalConditions : GaloisLocalConditions K S ℤ_[2] (TateS K S W) :=
  ⟨fun v => tateKummerCondition W hFull v.1, fun v => tateKummerConditionι W hFull v.1⟩

/-- The `2`-adic Kummer conditions are subcomplexes of the local cochains. -/
theorem tateKummerLocalConditions_injective (v : Places K S) (n : ℤ) :
    Function.Injective (((tateKummerLocalConditions S W hFull).i v).f n n rfl) := by
  classical
  exact cocycleConditionι_injective _ _ n

/-- **The genuine Selmer data of the ordinary compact Kummer complex**: continuous cochains of
`G_{K,S}` and of the decomposition groups with values in `T₂E`, with the `2`-adic Kummer conditions
at every place of `S` (`galoisSelData`). -/
def tateKummerSelData : SelData ℤ_[2] :=
  galoisSelData K S ℤ_[2] (TateS K S W) (tateKummerLocalConditions S W hFull)

/-- **The data are genuine Galois Selmer data** in the sense of `IsGaloisSelData`, for finite `S`. -/
theorem isGaloisSelData_tateKummerSelData (hS : S.Finite) :
    ZInQ.Manuscript.RC.Wiring.IsGaloisSelData (tateKummerSelData S W hFull) :=
  ⟨K, inferInstance, inferInstance, S, TateS K S W, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    tateKummerLocalConditions S W hFull, hS, tateKummerLocalConditions_injective S W hFull, rfl⟩

/-- **The ordinary compact Kummer complex `C_K`** (manuscript lines 4007--4018), a cochain complex of
`ℤ₂`-modules. -/
def compactKummerComplex : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ :=
  (selCx (tateKummerSelData S W hFull)).toCC

/-- **The ordinary rational Kummer complex `K₀ = C_K ⊗_{ℤ₂} ℚ₂`** (manuscript lines 3952--3962),
a cochain complex of `ℚ₂`-vector spaces. -/
def rationalKummerComplex : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ :=
  ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex PadicInt.Coe.ringHom
    (compactKummerComplex S W hFull)

end Complex

section FlatBaseChange

/-- `ℚ₂` is flat over `ℤ₂` (a localization). -/
theorem flat_padicIntCoe : (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]).Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat ℚ_[2] (nonZeroDivisors ℤ_[2]))

/-- **Rationalization commutes with cohomology**: for a complex `C` of `ℤ₂`-modules,
`Hⁿ(C ⊗_{ℤ₂} ℚ₂) ≅ Hⁿ(C) ⊗_{ℤ₂} ℚ₂` (flat base change; extension of scalars along a flat map
preserves finite limits, and as a left adjoint it preserves colimits). -/
def rationalizationHomologyIso (C : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ) (n : ℤ) :
    (ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex PadicInt.Coe.ringHom C).homology
        n ≅ (ModuleCat.extendScalars PadicInt.Coe.ringHom).obj (C.homology n) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat flat_padicIntCoe
  have : Limits.PreservesFiniteColimits
      (ModuleCat.extendScalars.{0, 0, 0} (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])) := by
    have := (ModuleCat.extendRestrictScalarsAdj.{0, 0, 0}
      (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])).leftAdjoint_preservesColimits
    infer_instance
  exact ShortComplex.mapHomologyIso (C.sc n) (ModuleCat.extendScalars PadicInt.Coe.ringHom)

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))

/-- **`Hⁿ(K₀) = Hⁿ(C_K) ⊗_{ℤ₂} ℚ₂`** for the ordinary compact and rational Kummer complexes. -/
def rationalKummerHomologyIso (n : ℤ) :
    (rationalKummerComplex S W hFull).homology n ≅
      (ModuleCat.extendScalars PadicInt.Coe.ringHom).obj
        ((compactKummerComplex S W hFull).homology n) :=
  rationalizationHomologyIso (compactKummerComplex S W hFull) n

end FlatBaseChange

section Reduction

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (v.adicCompletion K)]

/-- **Reduction modulo `2^n`.** The level-`n` coordinate of the `2`-adic Kummer cocycle of a tower,
read in `E(K̄_v)[2^n]`, is the finite-level Kummer cocycle of the division point `R n`, and that
cocycle lies in the finite-level Kummer condition `kummerZ ⊔ B¹` at level `2^n`. -/
theorem tateKummer_reduction {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) (n : ℕ) :
    (∀ σ : Gloc K v, compTors W (2 ^ n) v (projLev n (tateKummerFunOf W hFull v h σ)) =
      kummerFunOf (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ n)
        (h.two_pow_smul n) σ) ∧
    kummerCocycleOf (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ n)
        (h.two_pow_smul n) ∈
      kummerZ (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ n) ⊔
        contB1 ℤ (Gloc K v)
          (TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ n)) :=
  ⟨fun σ => compTors_tateKummerFunOf W hFull v h σ n, kummerCocycleOf_mem_sup _ _ (2 ^ n) _⟩

end Reduction

section Genuine

open ZInQ.Manuscript.RC ZInQ.Manuscript.RC53Assist.CentralSelmer

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))
  {m : ℕ} (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)

/-- **Input (1) for the genuine objects, from a degree-one identification**: the cochain map from
the ordinary rational Kummer complex into the specialized two-term base model inducing `φ`. -/
def genuineKummerModelMap
    (φ : (rationalKummerComplex S W hFull).homology 1 ≃ₗ[ℚ_[2]]
      LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) :
    rationalKummerComplex S W hFull ⟶ scalarChangedComplex Rings.rhoT (twoTermModel Dm) :=
  kummerModelMap (rationalKummerComplex S W hFull) φ

/-- The cochain map `genuineKummerModelMap` is a quasi-isomorphism in degree one. -/
instance quasiIsoAt_genuineKummerModelMap
    (φ : (rationalKummerComplex S W hFull).homology 1 ≃ₗ[ℚ_[2]]
      LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) :
    QuasiIsoAt (genuineKummerModelMap S W hFull Dm φ) 1 :=
  quasiIsoAt_kummerModelMap _ φ

/-- **Input (1) for the genuine objects is exactly a degree-one identification** `H¹(K₀) ≃ ker ρ(Dm)`. -/
theorem genuine_input_one_iff :
    (∃ i : rationalKummerComplex S W hFull ⟶ scalarChangedComplex Rings.rhoT (twoTermModel Dm),
        QuasiIsoAt i 1) ↔
      Nonempty ((rationalKummerComplex S W hFull).homology 1 ≃ₗ[ℚ_[2]]
        LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) :=
  nonempty_input_one_iff (twoTermModel Dm) (twoTermModelE1 Dm) (twoTermModelE2 Dm)
    (twoTermModel_d_zero_one Dm) (twoTermModel_hd Dm) _

/-- **The finite-dimensional form**: input (1) for the genuine objects holds exactly when
`dim H¹(K₀) = dim ker ρ(Dm)`. -/
theorem genuine_input_one_iff_finrank
    [FiniteDimensional ℚ_[2] ((rationalKummerComplex S W hFull).homology 1)] :
    (∃ i : rationalKummerComplex S W hFull ⟶ scalarChangedComplex Rings.rhoT (twoTermModel Dm),
        QuasiIsoAt i 1) ↔
      Module.finrank ℚ_[2] ((rationalKummerComplex S W hFull).homology 1) =
        Module.finrank ℚ_[2] (LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) :=
  nonempty_input_one_iff_finrank (twoTermModel Dm) (twoTermModelE1 Dm) (twoTermModelE2 Dm)
    (twoTermModel_d_zero_one Dm) (twoTermModel_hd Dm) _

end Genuine

section Transparency

open Matrix
open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC
  ZInQ.Manuscript.RC.BaseZeroLimit ZInQ.Manuscript.RC53Assist.CentralSelmer

/-- **What input (1) amounts to.** In the presence of the universal-coefficient data `eK`, `j` and
the quadratic descent data `f` with bounded defects, and under full Selmer corank one, a degree-one
quasi-isomorphism `K ⟶ CU ⊗ ℚ₂` exists if and only if `rank ρ(Dm) = m` (the base-zero field
`hcentral`). -/
theorem input_one_iff_hcentral {ℓ : ℕ} {k : ℤ} {m r : ℕ}
    (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT)
    (CU : CochainComplex (ModuleCat.{0} Rings.LambdaT) ℤ)
    (e1 : CU.X 1 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (e2 : CU.X 2 ≃ₗ[Rings.LambdaT] (Fin (m + 1) → Rings.LambdaT))
    (hzero : CU.d 0 1 = 0) (hd : ∀ x, e2 ((CU.d 1 2).hom x) = Dm *ᵥ e1 x)
    (K : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ)
    (eK : K.homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {Sg : Type} [AddCommGroup Sg] (j : (Fin r → Q2Z2) →+ Sg) (hj : BoundedDefects j)
    (f : Sg →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f)
    (hSel : SelmerCorankOneOverK ℓ k) :
    (∃ i : K ⟶ scalarChangedComplex Rings.rhoT CU, QuasiIsoAt i 1) ↔
      (Dm.map Rings.rhoT).rank = m := by
  constructor
  · rintro ⟨i, hi⟩
    exact hcentral_of_specializedModel Dm CU e1 e2 hzero hd K i eK j hj f hf hSel
  · intro hrank
    let e : K.homology 1 ≃ₗ[ℚ_[2]]
        RatTate (selmerTwoPower (Ecurve ℓ)) × RatTate (selmerTwoPower (Etw ℓ k)) :=
      (universalCoefficientsRatTateEquiv eK j hj).trans
        ((ratTateEquivOfBoundedDefects f hf).trans (fullSelmerProductRatTateEquiv _ _))
    have := finiteDimensional_ratTate_prod_of_Z2Corank hSel.1 hSel.2
    have : FiniteDimensional ℚ_[2] (K.homology 1) := LinearEquiv.finiteDimensional e.symm
    rw [nonempty_input_one_iff_finrank CU e1 e2 hzero hd K, e.finrank_eq,
      finrank_ratTate_prod_of_Z2Corank hSel.1 hSel.2, finrank_ker_of_rank_eq _ hrank]

end Transparency

section Curve

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC
  ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.BaseZeroLimit ZInQ.Manuscript.RC53Assist.CentralSelmer

/-- **The ordinary rational Kummer complex of `E_ℓ` over a number field `K`** (in the application
`K = ℚ(√k)`), for a set `S` of finite places over which the full `2`-power torsion is defined. -/
def curveKummerComplex (ℓ : ℕ) (K : Type) [Field K] [NumberField K]
    (hE : (Ecurve ℓ).IsElliptic) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hFull : ∀ n : ℕ, FullTorsion K S ((Ecurve ℓ).baseChange K) (2 ^ n)) :
    CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ :=
  haveI := hE
  rationalKummerComplex S ((Ecurve ℓ).baseChange K) hFull

/-- **Input (1) pinned to the genuine objects**, for `E_ℓ` over a number field `K` and a base-model
matrix `Dm`: a finite set `S` of finite places over which the full `2`-power torsion of `E_ℓ` is
defined, and a linear identification of `H¹` of the genuine rational Kummer complex with the
central kernel `ker ρ(Dm)`. -/
structure KummerInputOne (ℓ : ℕ) (K : Type) [Field K] [NumberField K]
    (hE : (Ecurve ℓ).IsElliptic) {m : ℕ} (Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT) :
    Type where
  /-- the finite set of finite places of the Selmer data -/
  S : Set (HeightOneSpectrum (𝓞 K))
  /-- it is finite -/
  hS : S.Finite
  /-- the full `2`-power torsion of `E_ℓ` is defined over `K_S` (Néron--Ogg--Shafarevich for `S`
  containing the places above `2` and of bad reduction) -/
  hFull : ∀ n : ℕ, FullTorsion K S ((Ecurve ℓ).baseChange K) (2 ^ n)
  /-- the degree-one identification of the rational Kummer cohomology with the central kernel -/
  φ : (curveKummerComplex ℓ K hE S hFull).homology 1 ≃ₗ[ℚ_[2]]
    LinearMap.ker (Dm.map Rings.rhoT).mulVecLin

variable {ℓ : ℕ} {K : Type} [Field K] [NumberField K] {hE : (Ecurve ℓ).IsElliptic} {m : ℕ}
  {Dm : Matrix (Fin (m + 1)) (Fin (m + 1)) Rings.LambdaT}

/-- The cochain map of input (1), from the genuine rational Kummer complex into the specialized
two-term base model. -/
def KummerInputOne.map (I : KummerInputOne ℓ K hE Dm) :
    curveKummerComplex ℓ K hE I.S I.hFull ⟶ scalarChangedComplex Rings.rhoT (twoTermModel Dm) :=
  kummerModelMap (curveKummerComplex ℓ K hE I.S I.hFull) I.φ

/-- It is a quasi-isomorphism in degree one. -/
instance KummerInputOne.quasiIsoAt_map (I : KummerInputOne ℓ K hE Dm) : QuasiIsoAt I.map 1 :=
  quasiIsoAt_kummerModelMap _ I.φ

/-- The base model has `CU.d 0 1 = 0`. -/
theorem KummerInputOne.hzero (_I : KummerInputOne ℓ K hE Dm) : (twoTermModel Dm).d 0 1 = 0 :=
  twoTermModel_d_zero_one Dm

/-- The map induces `φ` on degree-one cohomology, read in the central kernel. -/
theorem KummerInputOne.homologyMap_map (I : KummerInputOne ℓ K hE Dm)
    (x : (curveKummerComplex ℓ K hE I.S I.hFull).homology 1) :
    twoTermCentralH1 Dm ((HomologicalComplex.homologyMap I.map 1).hom x) = I.φ x :=
  twoTermCentralH1_homologyMap_kummerModelMap _ I.φ x

/-- The Kummer complex of input (1) comes from genuine Galois Selmer data. -/
theorem KummerInputOne.isGaloisSelData (I : KummerInputOne ℓ K hE Dm) :
    haveI := hE
    IsGaloisSelData (tateKummerSelData I.S ((Ecurve ℓ).baseChange K) I.hFull) :=
  haveI := hE
  isGaloisSelData_tateKummerSelData I.S ((Ecurve ℓ).baseChange K) I.hFull I.hS

/-- **The `central` comparison from pinned input (1)**, through
`centralSelmerComparisonOfSpecializedModel` with the two-term base model, given the
universal-coefficient data `eK`, `j` and the quadratic descent data `f`. -/
def KummerInputOne.central (I : KummerInputOne ℓ K hE Dm) (k : ℤ) {r : ℕ}
    (eK : (curveKummerComplex ℓ K hE I.S I.hFull).homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {Sg : Type} [AddCommGroup Sg] (j : (Fin r → Q2Z2) →+ Sg) (hj : BoundedDefects j)
    (f : Sg →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f) :
    CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm :=
  centralSelmerComparisonOfSpecializedModel Dm (twoTermModel Dm) (twoTermModelE1 Dm)
    (twoTermModelE2 Dm) (twoTermModel_d_zero_one Dm) (twoTermModel_hd Dm)
    (curveKummerComplex ℓ K hE I.S I.hFull) I.map eK j hj f hf

omit [Field K] [NumberField K] in
/-- Linear algebra of the rebuilt comparison: if `t ∘ h = φ` then `(h⁻¹ ∘ t⁻¹)` followed by `e`
is `e ∘ φ⁻¹`. -/
theorem chain_apply_of_comp {R : Type} [CommRing R] {A B H D : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup H] [Module R H] [AddCommGroup D] [Module R D]
    (t : B ≃ₗ[R] A) (h : H ≃ₗ[R] B) (φ : H ≃ₗ[R] A) (e : H ≃ₗ[R] D)
    (hφ : ∀ y, t (h y) = φ y) (x : A) :
    (t.symm.trans (h.symm.trans e)) x = e (φ.symm x) := by
  have hx : h.symm (t.symm x) = φ.symm x := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq, hφ, LinearEquiv.apply_symm_apply]
  simp only [LinearEquiv.trans_apply, hx]

omit [Field K] [NumberField K] in
/-- Linear algebra of the round trip: `e ((e.trans c⁻¹)⁻¹ x) = c x`. -/
theorem apply_trans_symm_symm {R : Type} [CommRing R] {A H D : Type} [AddCommGroup A]
    [Module R A] [AddCommGroup H] [Module R H] [AddCommGroup D] [Module R D]
    (e : H ≃ₗ[R] D) (c : A ≃ₗ[R] D) (x : A) : e ((e.trans c.symm).symm x) = c x := by
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

/-- The universal-coefficient and descent comparison `H¹(K₀) ≃ V₂ Sel(E/ℚ) × V₂ Sel(E^{(k)}/ℚ)`
determined by inputs (2) and (3). -/
def selmerSideEquiv {Kc : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ} (k : ℤ) {r : ℕ}
    (eK : Kc.homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {Sg : Type} [AddCommGroup Sg] (j : (Fin r → Q2Z2) →+ Sg) (hj : BoundedDefects j)
    (f : Sg →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f) :
    Kc.homology 1 ≃ₗ[ℚ_[2]]
      RatTate (selmerTwoPower (Ecurve ℓ)) × RatTate (selmerTwoPower (Etw ℓ k)) :=
  (universalCoefficientsRatTateEquiv eK j hj).trans
    ((ratTateEquivOfBoundedDefects f hf).trans (fullSelmerProductRatTateEquiv _ _))

/-- **The comparison produced from pinned input (1)** is `x ↦ e (φ⁻¹ x)`, with `e` the
universal-coefficient and descent comparison. -/
theorem KummerInputOne.central_cmp_apply (I : KummerInputOne ℓ K hE Dm) (k : ℤ) {r : ℕ}
    (eK : (curveKummerComplex ℓ K hE I.S I.hFull).homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {Sg : Type} [AddCommGroup Sg] (j : (Fin r → Q2Z2) →+ Sg) (hj : BoundedDefects j)
    (f : Sg →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f)
    (x : LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) :
    (I.central k eK j hj f hf).cmp x = selmerSideEquiv k eK j hj f hf (I.φ.symm x) := by
  have hc : (I.central k eK j hj f hf).cmp = (twoTermCentralH1 Dm).symm.trans
      ((asIso (HomologicalComplex.homologyMap I.map 1)).toLinearEquiv.symm.trans
        (selmerSideEquiv k eK j hj f hf)) := rfl
  exact (LinearEquiv.congr_fun hc x).trans (chain_apply_of_comp _ _ I.φ _
    (fun y => I.homologyMap_map y) x)

/-- **Pinned input (1) from a central comparison**: given the universal-coefficient and descent
data, a comparison `C` for `Dm` determines the identification `φ = C⁻¹ ∘ e`. -/
def KummerInputOne.ofCentral (k : ℤ) (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (hFull : ∀ n : ℕ, FullTorsion K S ((Ecurve ℓ).baseChange K) (2 ^ n)) {r : ℕ}
    (eK : (curveKummerComplex ℓ K hE S hFull).homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {Sg : Type} [AddCommGroup Sg] (j : (Fin r → Q2Z2) →+ Sg) (hj : BoundedDefects j)
    (f : Sg →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f)
    (C : CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm) :
    KummerInputOne ℓ K hE Dm :=
  ⟨S, hS, hFull, (selmerSideEquiv k eK j hj f hf).trans C.cmp.symm⟩

/-- **The replacement is lossless**: the comparison rebuilt from `KummerInputOne.ofCentral C` and
the same universal-coefficient and descent data is `C` itself. -/
theorem KummerInputOne.central_ofCentral (k : ℤ) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) (hFull : ∀ n : ℕ, FullTorsion K S ((Ecurve ℓ).baseChange K) (2 ^ n)) {r : ℕ}
    (eK : (curveKummerComplex ℓ K hE S hFull).homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {Sg : Type} [AddCommGroup Sg] (j : (Fin r → Q2Z2) →+ Sg) (hj : BoundedDefects j)
    (f : Sg →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f)
    (C : CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ k)) Dm) :
    ((KummerInputOne.ofCentral k S hS hFull eK j hj f hf C).central k eK j hj f hf).cmp =
      C.cmp := by
  refine LinearEquiv.ext fun x => ?_
  exact (KummerInputOne.central_cmp_apply (KummerInputOne.ofCentral k S hS hFull eK j hj f hf C)
    k eK j hj f hf x).trans (apply_trans_symm_symm _ C.cmp x)

/-- **Input (1) for the genuine objects is exactly a degree-one identification**: for `E_ℓ` over
`K`, a degree-one quasi-isomorphism from the genuine rational Kummer complex into the specialized
two-term base model exists if and only if `H¹(K₀) ≃ ker ρ(Dm)`. -/
theorem curve_input_one_iff (S : Set (HeightOneSpectrum (𝓞 K)))
    (hFull : ∀ n : ℕ, FullTorsion K S ((Ecurve ℓ).baseChange K) (2 ^ n)) :
    (∃ i : curveKummerComplex ℓ K hE S hFull ⟶
        scalarChangedComplex Rings.rhoT (twoTermModel Dm), QuasiIsoAt i 1) ↔
      Nonempty ((curveKummerComplex ℓ K hE S hFull).homology 1 ≃ₗ[ℚ_[2]]
        LinearMap.ker (Dm.map Rings.rhoT).mulVecLin) :=
  nonempty_input_one_iff (twoTermModel Dm) (twoTermModelE1 Dm) (twoTermModelE2 Dm)
    (twoTermModel_d_zero_one Dm) (twoTermModel_hd Dm) _

/-- **Pinned input (1) is equivalent to `hcentral`** given the universal-coefficient and descent
data for the genuine Kummer complex and full Selmer corank one. -/
theorem nonempty_kummerInputOne_iff (k : ℤ) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) (hFull : ∀ n : ℕ, FullTorsion K S ((Ecurve ℓ).baseChange K) (2 ^ n))
    {r : ℕ} (eK : (curveKummerComplex ℓ K hE S hFull).homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {Sg : Type} [AddCommGroup Sg] (j : (Fin r → Q2Z2) →+ Sg) (hj : BoundedDefects j)
    (f : Sg →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ k)) (hf : BoundedDefects f)
    (hSel : SelmerCorankOneOverK ℓ k) :
    (∃ I : KummerInputOne ℓ K hE Dm, I.S = S) ↔ (Dm.map Rings.rhoT).rank = m := by
  rw [← input_one_iff_hcentral Dm (twoTermModel Dm) (twoTermModelE1 Dm) (twoTermModelE2 Dm)
    (twoTermModel_d_zero_one Dm) (twoTermModel_hd Dm) (curveKummerComplex ℓ K hE S hFull) eK j hj
    f hf hSel, curve_input_one_iff S hFull]
  constructor
  · rintro ⟨I, rfl⟩
    exact ⟨I.φ⟩
  · rintro ⟨φ⟩
    exact ⟨⟨S, hS, hFull, φ⟩, rfl⟩

end Curve

section Leaf

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC
  ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.BaseZeroLimit ZInQ.Manuscript.RC53Assist.CentralSelmer

variable {ℓ : ℕ} {D : RCData ℓ} {Fam : Family} (M : BaseZeroLeafModelText D Fam)
  (S : Set (HeightOneSpectrum (𝓞 M.K)))
  (hFull : ∀ n : ℕ, FullTorsion M.K S ((Ecurve ℓ).baseChange M.K) (2 ^ n))

/-- **The ordinary rational Kummer complex of `E_ℓ` over the field `K = ℚ(√k)` of a base-zero leaf
model.** -/
abbrev leafKummerComplex : CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ :=
  curveKummerComplex ℓ M.K M.hE S hFull

/-- **Input (1) for a base-zero leaf model**, with `K₀` the genuine rational Kummer complex of `E_ℓ`
over the leaf's field and `CU` the two-term model of the leaf's matrix, holds exactly when
`H¹(K₀) ≃ ker ρ(Dm)`. -/
theorem leaf_input_one_iff :
    (∃ i : leafKummerComplex M S hFull ⟶
        scalarChangedComplex Rings.rhoT (twoTermModel M.core.Dm), QuasiIsoAt i 1) ↔
      Nonempty ((leafKummerComplex M S hFull).homology 1 ≃ₗ[ℚ_[2]]
        LinearMap.ker (M.core.Dm.map Rings.rhoT).mulVecLin) :=
  curve_input_one_iff S hFull

/-- The same with the leaf's own model complex `CU`, when its degree-zero term vanishes. -/
theorem leaf_input_one_iff_ownModel (hX0 : Limits.IsZero (M.core.CU.X 0)) :
    (∃ i : leafKummerComplex M S hFull ⟶ scalarChangedComplex Rings.rhoT M.core.CU,
        QuasiIsoAt i 1) ↔
      Nonempty ((leafKummerComplex M S hFull).homology 1 ≃ₗ[ℚ_[2]]
        LinearMap.ker (M.core.Dm.map Rings.rhoT).mulVecLin) :=
  nonempty_input_one_iff M.core.CU M.core.e1 M.core.e2 (d_zero_one_of_isZero M.core.CU hX0)
    M.core.hd _

/-- **Pinned input (1) for a leaf model** (the type of `KummerInputOne` at the leaf's field, curve
and matrix). -/
abbrev LeafKummerInputOne : Type := KummerInputOne ℓ M.K M.hE M.core.Dm

/-- **The leaf's `central` field from pinned input (1)** and the universal-coefficient and descent
data (exact type of the field `central` of the leaf's core). -/
def leafCentral (I : LeafKummerInputOne M) {r : ℕ}
    (eK : (leafKummerComplex M I.S I.hFull).homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {Sg : Type} [AddCommGroup Sg] (j : (Fin r → Q2Z2) →+ Sg) (hj : BoundedDefects j)
    (f : Sg →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ D.kfin)) (hf : BoundedDefects f) :
    CentralSelmerComparison (selmerTwoPower (Ecurve ℓ)) (selmerTwoPower (Etw ℓ D.kfin))
      M.core.Dm :=
  I.central D.kfin eK j hj f hf

/-- **Pinned input (1) follows from the existing leaf.** For a leaf model (whose `central` field
gives `hcentral`) under full Selmer corank one, the universal-coefficient and descent data for the
genuine Kummer complex produce pinned input (1) with the given `S`. -/
theorem nonempty_leafKummerInputOne (hS : S.Finite) {r : ℕ}
    (eK : (leafKummerComplex M S hFull).homology 1 ≃ₗ[ℚ_[2]] (Fin r → ℚ_[2]))
    {Sg : Type} [AddCommGroup Sg] (j : (Fin r → Q2Z2) →+ Sg) (hj : BoundedDefects j)
    (f : Sg →+ fullSelmerProduct (Ecurve ℓ) (Etw ℓ D.kfin)) (hf : BoundedDefects f)
    (hSel : SelmerCorankOneOverK ℓ D.kfin) : ∃ I : LeafKummerInputOne M, I.S = S :=
  (nonempty_kummerInputOne_iff D.kfin S hS hFull eK j hj f hf hSel).mpr
    (hcentral_of_selmer hSel M.core.central)

end Leaf

section NonVacuity

example (K : Type) [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic] :
    CochainComplex (ModuleCat.{0} ℚ_[2]) ℤ :=
  rationalKummerComplex Set.univ W (hasFullTwoTorsion_univ (K := K) (W := W)).full

end NonVacuity

end ZInQ.Manuscript.RC53Assist.CentralKummer
