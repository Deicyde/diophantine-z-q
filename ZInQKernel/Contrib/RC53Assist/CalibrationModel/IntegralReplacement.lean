import ZInQKernel.Contrib.RC53Assist.Calibration.KummerIntegral
import ZInQKernel.Contrib.RC53Assist.CentralKummer.RationalKummer
import ZInQKernel.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel
import Mathlib

/-!
# Finite free resolutions of the compact integral Kummer complex

Over a principal ideal domain, finite presentations of the cohomology groups
produce a degreewise finite free complex and an actual quasi-isomorphism to the
original complex. Bounded cohomology gives a bounded replacement. This argument
uses projective lifts of generators and relations, not nilpotence of the maximal
ideal and not a splitting of arbitrary flat modules.

Coefficient extension preserves homotopy equivalences without any flatness
assumption on the coefficient ring. The comparison with the genuine finite
Selmer complexes is a separate comparison, not a consequence of this fact alone.
-/

noncomputable section

set_option maxHeartbeats 600000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.CalibrationModel

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Manuscript.RC53Assist.CentralSelmer
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral

section Presentations

variable {R : Type} [CommRing R]

/-- A finite free resolution of a module, in homological degrees one and zero. -/
structure FreeResolution (H : Type) [AddCommGroup H] [Module R H] where
  generators : ℕ
  relations : ℕ
  differential : (Fin relations → R) →ₗ[R] (Fin generators → R)
  injective : Function.Injective differential
  projection : (Fin generators → R) →ₗ[R] H
  surjective : Function.Surjective projection
  exact : ∀ x, projection x = 0 ↔ ∃ y, differential y = x

variable {H : Type} [AddCommGroup H] [Module R H]

/-- Every relation projects to zero. -/
theorem FreeResolution.projection_differential (T : FreeResolution (R := R) H)
    (y : Fin T.relations → R) : T.projection (T.differential y) = 0 :=
  (T.exact _).2 ⟨y, rfl⟩

/-- The zero resolution for a zero module. -/
def zeroFreeResolution (hH : Subsingleton H) : FreeResolution (R := R) H where
  generators := 0
  relations := 0
  differential := 0
  injective := fun _ _ _ => Subsingleton.elim _ _
  projection := 0
  surjective := fun _ => ⟨0, hH.elim _ _⟩
  exact := fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => rfl⟩

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Finite generation over a principal ideal domain gives a finite free resolution. -/
def finiteFreeResolution (hH : Module.Finite R H) : FreeResolution (R := R) H := by
  let := hH
  let a := Classical.choose (Module.Finite.exists_fin' R H)
  let q := Classical.choose (Classical.choose_spec (Module.Finite.exists_fin' R H))
  have hq := Classical.choose_spec (Classical.choose_spec (Module.Finite.exists_fin' R H))
  let B := (LinearMap.ker q).basisOfPid (Pi.basisFun R (Fin a))
  let d : (Fin B.1 → R) →ₗ[R] (Fin a → R) :=
    (LinearMap.ker q).subtype.comp B.2.equivFun.symm.toLinearMap
  refine ⟨a, B.1, d, ?_, q, hq, ?_⟩
  · exact Subtype.val_injective.comp B.2.equivFun.symm.injective
  · intro x
    constructor
    · intro hx
      refine ⟨B.2.equivFun ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (B.2.equivFun.symm_apply_apply ⟨x, hx⟩)
    · rintro ⟨y, rfl⟩
      exact (B.2.equivFun.symm y).2

/-- Choose a resolution that is identically zero when the module is zero. -/
def chosenFreeResolution (hH : Module.Finite R H) : FreeResolution (R := R) H := by
  classical
  exact if h0 : Subsingleton H then zeroFreeResolution h0 else finiteFreeResolution hH

/-- The chosen presentation has no generators or relations for a zero module. -/
theorem chosenFreeResolution_zero (hH : Module.Finite R H) (h0 : Subsingleton H) :
    (chosenFreeResolution hH).generators = 0 ∧
      (chosenFreeResolution hH).relations = 0 := by
  simp [chosenFreeResolution, h0, zeroFreeResolution]

end Presentations

section ResolutionComplex

variable {R : Type} [CommRing R] (C : CochainComplex (ModuleCat.{0} R) ℤ)
  (T : ∀ n : ℤ, FreeResolution (R := R) (C.homology n))

/-- Projection from cycles to cohomology is surjective. -/
theorem homologyProjection_surjective (n : ℤ) :
    Function.Surjective (C.homologyπ n).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- Boundaries, with their values restricted to the kernel of the class map. -/
def boundarySurjection (n : ℤ) :
    C.X n →ₗ[R] LinearMap.ker (C.homologyπ (n + 1)).hom :=
  (C.toCycles n (n + 1)).hom.codRestrict _ (fun x => by
    apply LinearMap.mem_ker.2
    have h := congrArg (fun f => f.hom x) (C.toCycles_comp_homologyπ n (n + 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h)

/-- Every cycle of class zero is a boundary. -/
theorem boundarySurjection_surjective (n : ℤ) :
    Function.Surjective (boundarySurjection C n) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, hx⟩ := (C.moduleCat_homologyπ_eq_zero_iff
    (n := n + 1) (m := n) (by simp) z).1 hz
  exact ⟨x, Subtype.ext hx⟩

/-- Lift the chosen cohomology generators to cycles. -/
def generatorLift (n : ℤ) : (Fin (T n).generators → R) →ₗ[R] C.cycles n :=
  Classical.choose (Module.projective_lifting_property (C.homologyπ n).hom
    (T n).projection (homologyProjection_surjective C n))

/-- The lifted cycles represent the prescribed generators. -/
theorem generatorLift_projection (n : ℤ) :
    (C.homologyπ n).hom.comp (generatorLift C T n) = (T n).projection :=
  Classical.choose_spec (Module.projective_lifting_property (C.homologyπ n).hom
    (T n).projection (homologyProjection_surjective C n))

/-- The lifted relations are cycles of class zero. -/
def relationCycle (n : ℤ) :
    (Fin (T (n + 1)).relations → R) →ₗ[R]
      LinearMap.ker (C.homologyπ (n + 1)).hom :=
  ((generatorLift C T (n + 1)).comp (T (n + 1)).differential).codRestrict _ (fun x => by
    change (C.homologyπ (n + 1)).hom
      (generatorLift C T (n + 1) ((T (n + 1)).differential x)) = 0
    rw [← LinearMap.comp_apply, generatorLift_projection]
    exact (T (n + 1)).projection_differential x)

/-- Lift the relations one degree earlier as actual bounding cochains. -/
def relationLift (n : ℤ) : (Fin (T (n + 1)).relations → R) →ₗ[R] C.X n :=
  Classical.choose (Module.projective_lifting_property (boundarySurjection C n)
    (relationCycle C T n) (boundarySurjection_surjective C n))

/-- The differential of a bounding cochain is the lifted relation. -/
theorem relationLift_differential (n : ℤ) (x : Fin (T (n + 1)).relations → R) :
    (C.d n (n + 1)).hom (relationLift C T n x) =
      (C.iCycles (n + 1)).hom (generatorLift C T (n + 1) ((T (n + 1)).differential x)) := by
  have h := LinearMap.congr_fun (Classical.choose_spec
    (Module.projective_lifting_property (boundarySurjection C n)
      (relationCycle C T n) (boundarySurjection_surjective C n))) x
  have h' := congrArg Subtype.val h
  change (C.toCycles n (n + 1)).hom (relationLift C T n x) =
    generatorLift C T (n + 1) ((T (n + 1)).differential x) at h'
  have hd := congrArg (fun f => f.hom (relationLift C T n x)) (C.toCycles_i n (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hd
  rw [← hd, h']

/-- The term in degree n contains generators of Hⁿ and relations of Hⁿ⁺¹. -/
def resolutionTerm (n : ℤ) : ModuleCat.{0} R :=
  ModuleCat.of R ((Fin (T n).generators → R) × (Fin (T (n + 1)).relations → R))

/-- The direct sum of the two-term free resolutions of all cohomology groups. -/
def resolutionGCx : GCx R where
  X := resolutionTerm C T
  d i j hij := by
    subst j
    exact ((T (i + 1)).differential.comp (LinearMap.snd R _ _)).prod 0
  d_d i j k hij hjk x := by
    subst j
    subst k
    change ((T (i + 1 + 1)).differential 0, 0) = 0
    simp

/-- The cochain-complex form of the resolution model. -/
def resolutionComplex : CochainComplex (ModuleCat.{0} R) ℤ := (resolutionGCx C T).toCC

/-- The only nonzero differential block is the relation inclusion. -/
theorem resolutionComplex_differential (n : ℤ) (x : (resolutionComplex C T).X n) :
    ((resolutionComplex C T).d n (n + 1)).hom x = ((T (n + 1)).differential x.2, 0) :=
  GCx.toCC_d_hom (resolutionGCx C T) n (n + 1) rfl x

/-- The actual comparison sends generators to their cycles and relations to bounding cochains. -/
def resolutionComparison : resolutionComplex C T ⟶ C where
  f n := ModuleCat.ofHom
    (((C.iCycles n).hom.comp (generatorLift C T n)).comp (LinearMap.fst R _ _) +
      (relationLift C T n).comp (LinearMap.snd R _ _))
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (C.d i (i + 1)).hom
      ((C.iCycles i).hom (generatorLift C T i x.1) + relationLift C T i x.2) =
        (C.iCycles (i + 1)).hom
          (generatorLift C T (i + 1) (((resolutionComplex C T).d i (i + 1)).hom x).1) +
        relationLift C T (i + 1) (((resolutionComplex C T).d i (i + 1)).hom x).2
    rw [resolutionComplex_differential, map_add, relationLift_differential]
    have hz := congrArg (fun f => f.hom (generatorLift C T i x.1)) (C.iCycles_d i (i + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at hz
    simp only [hz, zero_add, map_zero, add_zero]

/-- A cycle in the model has zero relation-source coordinate. -/
theorem resolutionCycle_second_zero (n : ℤ) (z : (resolutionComplex C T).cycles n) :
    (((resolutionComplex C T).iCycles n).hom z).2 = 0 := by
  let P := resolutionComplex C T
  have h := congrArg (fun f => f.hom z) (P.iCycles_d n (n + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  rw [resolutionComplex_differential] at h
  apply (T (n + 1)).injective
  exact (congrArg Prod.fst h).trans (map_zero _).symm

/-- Inclusion of the generator summand into the cycles. -/
def generatorCycleMap (n : ℤ) :
    ModuleCat.of R (Fin (T n).generators → R) ⟶ (resolutionComplex C T).cycles n :=
  (resolutionComplex C T).liftCycles
    (ModuleCat.ofHom ((LinearMap.id : (Fin (T n).generators → R) →ₗ[R] _).prod 0))
    (n + 1) (by simp) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ((resolutionComplex C T).d n (n + 1)).hom (x, 0) = 0
      rw [resolutionComplex_differential, map_zero]
      rfl)

/-- A generator is a model cycle with zero relation-source coordinate. -/
def generatorCycle (n : ℤ) (x : Fin (T n).generators → R) :
    (resolutionComplex C T).cycles n := (generatorCycleMap C T n).hom x

/-- The generator-cycle inclusion has the displayed coordinates. -/
theorem generatorCycle_coordinates (n : ℤ) (x : Fin (T n).generators → R) :
    ((resolutionComplex C T).iCycles n).hom (generatorCycle C T n x) = (x, 0) := by
  exact congrArg (fun f => f.hom x) ((resolutionComplex C T).liftCycles_i
    (ModuleCat.ofHom ((LinearMap.id : (Fin (T n).generators → R) →ₗ[R] _).prod 0))
    (n + 1) (by simp) _)

/-- On the class of a model cycle, the comparison is precisely its chosen cohomology projection. -/
theorem resolutionComparison_class (n : ℤ) (z : (resolutionComplex C T).cycles n) :
    (HomologicalComplex.homologyMap (resolutionComparison C T) n).hom
      (((resolutionComplex C T).homologyπ n).hom z) =
        (T n).projection ((((resolutionComplex C T).iCycles n).hom z).1) := by
  let P := resolutionComplex C T
  have hnat := congrArg (fun f => f.hom z)
    (HomologicalComplex.homologyπ_naturality (resolutionComparison C T) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat]
  have hc : (HomologicalComplex.cyclesMap (resolutionComparison C T) n).hom z =
      generatorLift C T n (((P.iCycles n).hom z).1) := by
    apply (ModuleCat.mono_iff_injective (C.iCycles n)).1 inferInstance
    have h := congrArg (fun f => f.hom z)
      (HomologicalComplex.cyclesMap_i (resolutionComparison C T) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h]
    change (C.iCycles n).hom (generatorLift C T n (((P.iCycles n).hom z).1)) +
      relationLift C T n (((P.iCycles n).hom z).2) = _
    rw [resolutionCycle_second_zero, map_zero, add_zero]
  rw [hc]
  exact LinearMap.congr_fun (generatorLift_projection C T n) _

/-- The actual resolution comparison induces an isomorphism in every degree. -/
theorem resolutionComparison_quasiIso : QuasiIso (resolutionComparison C T) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let P := resolutionComplex C T
  have hb : Function.Bijective (HomologicalComplex.homologyMap (resolutionComparison C T) n).hom := by
    constructor
    · apply (injective_iff_map_eq_zero _).2
      intro y hy
      obtain ⟨z, rfl⟩ := homologyProjection_surjective P n y
      rw [resolutionComparison_class] at hy
      obtain ⟨r, hr⟩ := (T n).exact _ |>.1 hy
      obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
      have hbd : (P.toCycles m (m + 1)).hom (0, r) = z := by
        apply (ModuleCat.mono_iff_injective (P.iCycles (m + 1))).1 inferInstance
        have hd := congrArg (fun f => f.hom (0, r)) (P.toCycles_i m (m + 1))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hd
        rw [hd, resolutionComplex_differential]
        exact Prod.ext hr (resolutionCycle_second_zero C T (m + 1) z).symm
      exact (P.moduleCat_homologyπ_eq_zero_iff
        (n := m + 1) (m := m) (by simp) z).2 ⟨(0, r), hbd⟩
    · intro y
      obtain ⟨x, hx⟩ := (T n).surjective y
      refine ⟨(P.homologyπ n).hom (generatorCycle C T n x), ?_⟩
      rw [resolutionComparison_class, generatorCycle_coordinates]
      exact hx
  exact (LinearEquiv.ofBijective _ hb).toModuleIso.isIso_hom

/-- The replacement is degreewise finite free. -/
theorem resolutionComplex_finite_free (n : ℤ) :
    Module.Free R ((resolutionComplex C T).X n) ∧
      Module.Finite R ((resolutionComplex C T).X n) := by
  change Module.Free R ((Fin (T n).generators → R) × (Fin (T (n + 1)).relations → R)) ∧
    Module.Finite R ((Fin (T n).generators → R) × (Fin (T (n + 1)).relations → R))
  exact ⟨inferInstance, inferInstance⟩

end ResolutionComplex

section FiniteReplacement

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  (C : CochainComplex (ModuleCat.{0} R) ℤ)
  (hfinite : ∀ n : ℤ, Module.Finite R (C.homology n))

/-- The finite free replacement selected from finite integral cohomology. -/
def finiteReplacement : CochainComplex (ModuleCat.{0} R) ℤ :=
  resolutionComplex C (fun n => chosenFreeResolution (hfinite n))

/-- Its actual comparison to the original cochain complex. -/
def finiteReplacementMap : finiteReplacement C hfinite ⟶ C :=
  resolutionComparison C (fun n => chosenFreeResolution (hfinite n))

/-- Finite integral cohomology constructs a degreewise finite free quasi-isomorphic model. -/
theorem finiteReplacementMap_quasiIso : QuasiIso (finiteReplacementMap C hfinite) :=
  resolutionComparison_quasiIso C _

/-- Every term of the constructed replacement is finite free. -/
theorem finiteReplacement_finite_free (n : ℤ) :
    Module.Free R ((finiteReplacement C hfinite).X n) ∧
      Module.Finite R ((finiteReplacement C hfinite).X n) :=
  resolutionComplex_finite_free C _ n

/-- If the original cohomology vanishes outside [lo,hi], the replacement vanishes outside
[lo-1,hi]. This does not require boundedness of the original cochain modules. -/
theorem finiteReplacement_bounded (lo hi : ℤ)
    (hbounded : ∀ n : ℤ, n < lo ∨ hi < n → Subsingleton (C.homology n))
    (n : ℤ) (hn : n < lo - 1 ∨ hi < n) :
    Subsingleton ((finiteReplacement C hfinite).X n) := by
  have hn0 : n < lo ∨ hi < n := by omega
  have hn1 : n + 1 < lo ∨ hi < n + 1 := by omega
  have h0 := chosenFreeResolution_zero (hfinite n) (hbounded n hn0)
  have h1 := chosenFreeResolution_zero (hfinite (n + 1)) (hbounded (n + 1) hn1)
  change Subsingleton ((Fin (chosenFreeResolution (hfinite n)).generators → R) ×
    (Fin (chosenFreeResolution (hfinite (n + 1))).relations → R))
  rw [h0.1, h1.2]
  infer_instance

end FiniteReplacement

section DiagonalPresentations

variable {R : Type} [CommRing R]

/-- Coordinates of a basis vector are the corresponding standard vector. -/
theorem basisEquivFun_basis {ι M : Type} [Fintype ι] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (i : ι) : b.equivFun (b i) = Pi.basisFun R ι i := by
  classical
  funext j
  simp [Pi.basisFun_apply, Pi.single, Function.update_apply, eq_comm]

/-- A finite free resolution in which every relation is a nonzero scalar times one distinct
generator. The other generator coordinates are the free core. -/
structure DiagonalResolution (H : Type) [AddCommGroup H] [Module R H]
    extends FreeResolution (R := R) H where
  embedding : Fin relations ↪ Fin generators
  coefficient : Fin relations → R
  coefficient_ne_zero : ∀ j, coefficient j ≠ 0
  differential_basis : ∀ j, differential (Pi.basisFun R (Fin relations) j) =
    coefficient j • Pi.basisFun R (Fin generators) (embedding j)

variable {H : Type} [AddCommGroup H] [Module R H]

/-- The diagonal zero presentation for a zero module. -/
def zeroDiagonalResolution (hH : Subsingleton H) : DiagonalResolution (R := R) H where
  toFreeResolution := zeroFreeResolution hH
  embedding := Function.Embedding.refl _
  coefficient := Fin.elim0
  coefficient_ne_zero := by intro j; exact j.elim0
  differential_basis := by intro j; exact j.elim0

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Smith normal form constructs a finite diagonal resolution from finite integral cohomology.
No torsion lengths are specified in advance. -/
def smithDiagonalResolution (hH : Module.Finite R H) : DiagonalResolution (R := R) H := by
  let := hH
  let a := Classical.choose (Module.Finite.exists_fin' R H)
  let q := Classical.choose (Classical.choose_spec (Module.Finite.exists_fin' R H))
  have hq := Classical.choose_spec (Classical.choose_spec (Module.Finite.exists_fin' R H))
  let B := (LinearMap.ker q).smithNormalForm (Pi.basisFun R (Fin a))
  let d : (Fin B.1 → R) →ₗ[R] (Fin a → R) := B.2.bM.equivFun.toLinearMap.comp
    ((LinearMap.ker q).subtype.comp B.2.bN.equivFun.symm.toLinearMap)
  let p : (Fin a → R) →ₗ[R] H := q.comp B.2.bM.equivFun.symm.toLinearMap
  refine
    { generators := a
      relations := B.1
      differential := d
      injective := B.2.bM.equivFun.injective.comp
        (Subtype.val_injective.comp B.2.bN.equivFun.symm.injective)
      projection := p
      surjective := hq.comp B.2.bM.equivFun.symm.surjective
      exact := ?_
      embedding := B.2.f
      coefficient := B.2.a
      coefficient_ne_zero := ?_
      differential_basis := ?_ }
  · intro x
    constructor
    · intro hx
      let z : LinearMap.ker q := ⟨B.2.bM.equivFun.symm x, hx⟩
      refine ⟨B.2.bN.equivFun z, ?_⟩
      change B.2.bM.equivFun ((B.2.bN.equivFun.symm (B.2.bN.equivFun z) :
        LinearMap.ker q) : (Fin a → R)) = x
      rw [B.2.bN.equivFun.symm_apply_apply]
      exact B.2.bM.equivFun.apply_symm_apply x
    · rintro ⟨y, rfl⟩
      change q (B.2.bM.equivFun.symm (B.2.bM.equivFun
        ((B.2.bN.equivFun.symm y : LinearMap.ker q) : (Fin a → R)))) = 0
      rw [B.2.bM.equivFun.symm_apply_apply]
      exact (B.2.bN.equivFun.symm y).2
  · intro j hj
    have hz := B.2.snf j
    rw [hj, zero_smul] at hz
    exact B.2.bN.ne_zero j (Subtype.ext hz)
  · intro j
    have hN : B.2.bN.equivFun.symm (Pi.basisFun R (Fin B.1) j) = B.2.bN j := by
      apply B.2.bN.equivFun.injective
      rw [B.2.bN.equivFun.apply_symm_apply, basisEquivFun_basis]
    change B.2.bM.equivFun ((B.2.bN.equivFun.symm (Pi.basisFun R (Fin B.1) j) :
      LinearMap.ker q) : (Fin a → R)) = B.2.a j • Pi.basisFun R (Fin a) (B.2.f j)
    rw [hN, B.2.snf j, map_smul, basisEquivFun_basis]

/-- Choose the Smith presentation with no terms for a zero module. -/
def chosenDiagonalResolution (hH : Module.Finite R H) : DiagonalResolution (R := R) H := by
  classical
  exact if h0 : Subsingleton H then zeroDiagonalResolution h0 else smithDiagonalResolution hH

/-- The chosen Smith presentation vanishes for a zero module. -/
theorem chosenDiagonalResolution_zero (hH : Module.Finite R H) (h0 : Subsingleton H) :
    (chosenDiagonalResolution hH).generators = 0 ∧
      (chosenDiagonalResolution hH).relations = 0 := by
  simp [chosenDiagonalResolution, h0, zeroDiagonalResolution, zeroFreeResolution]

end DiagonalPresentations

section DiagonalNormalForm

variable {R : Type} [CommRing R] {H : Type} [AddCommGroup H] [Module R H]

/-- The coordinates not used as targets of relations. -/
def DiagonalResolution.Core (T : DiagonalResolution (R := R) H) : Type :=
  {i : Fin T.generators // ¬ ∃ j, T.embedding j = i}

noncomputable instance DiagonalResolution.coreFintype (T : DiagonalResolution (R := R) H) :
    Fintype T.Core := by
  classical
  unfold DiagonalResolution.Core
  infer_instance

/-- The number of free core generators. -/
def DiagonalResolution.coreRank (T : DiagonalResolution (R := R) H) : ℕ :=
  Fintype.card T.Core

/-- Separate the free core coordinates from the disk-target coordinates. -/
def DiagonalResolution.coordinates (T : DiagonalResolution (R := R) H) :
    (Fin T.generators → R) ≃ₗ[R] ((T.Core → R) × (Fin T.relations → R)) := by
  classical
  exact
    { toFun x := (fun i => x i.1, fun j => x (T.embedding j))
      invFun x i := if hi : ∃ j, T.embedding j = i then x.2 hi.choose else x.1 ⟨i, hi⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv x := by
        funext i
        dsimp only
        split_ifs with hi
        · exact congrArg x hi.choose_spec
        · rfl
      right_inv x := by
        apply Prod.ext
        · funext i
          simp only [dite_eq_right i.2]
          exact congrArg x.1 (Subtype.ext rfl)
        · funext j
          have hj : ∃ k, T.embedding k = T.embedding j := ⟨j, rfl⟩
          have hk : hj.choose = j := T.embedding.injective hj.choose_spec
          simp only [dite_eq_left hj, hk] }

/-- The diagonal differential of all elementary disks in one degree. -/
def DiagonalResolution.diskMap (T : DiagonalResolution (R := R) H) :
    (Fin T.relations → R) →ₗ[R] (Fin T.relations → R) where
  toFun x j := T.coefficient j * x j
  map_add' x y := by funext j; exact mul_add _ _ _
  map_smul' a x := by funext j; change _ * (a * _) = a * (_ * _); ring

/-- In the separated coordinates, every differential has a zero core block and a diagonal disk
block with its nonzero Smith coefficients. -/
theorem DiagonalResolution.coordinates_differential (T : DiagonalResolution (R := R) H)
    (y : Fin T.relations → R) :
    T.coordinates (T.differential y) = (0, T.diskMap y) := by
  classical
  have heq : T.coordinates.toLinearMap.comp T.differential =
      (0 : (Fin T.relations → R) →ₗ[R] (T.Core → R)).prod T.diskMap := by
    apply (Pi.basisFun R (Fin T.relations)).ext
    intro j
    rw [LinearMap.comp_apply, T.differential_basis, map_smul]
    apply Prod.ext
    · funext i
      have hji : T.embedding j ≠ i.1 := fun h => i.2 ⟨j, h⟩
      change T.coefficient j * Pi.basisFun R (Fin T.generators) (T.embedding j) i.1 = 0
      simp [Pi.basisFun_apply, hji]
    · funext k
      change T.coefficient j * Pi.basisFun R (Fin T.generators) (T.embedding j) (T.embedding k) =
        T.coefficient k * Pi.basisFun R (Fin T.relations) j k
      by_cases hjk : j = k
      · subst k
        simp [Pi.basisFun_apply]
      · have hslot : T.embedding j ≠ T.embedding k := fun h => hjk (T.embedding.injective h)
        simp [Pi.basisFun_apply, hjk, hslot]
  exact LinearMap.congr_fun heq y

/-- All elementary-disk maps are injective over the principal ideal domain. -/
theorem DiagonalResolution.diskMap_injective [IsDomain R] (T : DiagonalResolution (R := R) H) :
    Function.Injective T.diskMap := by
  intro x y hxy
  funext j
  exact mul_left_cancel₀ (T.coefficient_ne_zero j) (congrFun hxy j)

/-- Standard finite coordinates on the free core. -/
def DiagonalResolution.coreCoordinates (T : DiagonalResolution (R := R) H) :
    (T.Core → R) ≃ₗ[R] (Fin T.coreRank → R) :=
  LinearEquiv.funCongrLeft R R (Fintype.equivFin T.Core).symm

/-- The torsion part presented by the nonzero elementary disks. -/
abbrev DiagonalResolution.DiskCokernel (T : DiagonalResolution (R := R) H) : Type :=
  (Fin T.relations → R) ⧸ LinearMap.range T.diskMap

/-- The free and torsion class coordinates on the generator module. -/
def DiagonalResolution.classMap (T : DiagonalResolution (R := R) H) :
    (Fin T.generators → R) →ₗ[R] ((T.Core → R) × T.DiskCokernel) :=
  ((LinearMap.id : (T.Core → R) →ₗ[R] _).prodMap
    (LinearMap.range T.diskMap).mkQ).comp T.coordinates.toLinearMap

/-- Every free and torsion class coordinate is represented by a generator. -/
theorem DiagonalResolution.classMap_surjective (T : DiagonalResolution (R := R) H) :
    Function.Surjective T.classMap := by
  rintro ⟨x, z⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range T.diskMap) z
  refine ⟨T.coordinates.symm (x, y), ?_⟩
  change ((T.coordinates (T.coordinates.symm (x, y))).1,
    Submodule.Quotient.mk (T.coordinates (T.coordinates.symm (x, y))).2) = _
  rw [T.coordinates.apply_symm_apply]

/-- The free and torsion coordinates have exactly the relation kernel of the presentation. -/
theorem DiagonalResolution.classMap_kernel (T : DiagonalResolution (R := R) H) :
    LinearMap.ker T.classMap = LinearMap.ker T.projection := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hx
    have hx0 : (T.coordinates x).1 = 0 := congrArg Prod.fst hx
    have hxq : (Submodule.Quotient.mk (T.coordinates x).2 : T.DiskCokernel) = 0 :=
      congrArg Prod.snd hx
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero (LinearMap.range T.diskMap)).1 hxq
    apply (T.exact x).2
    refine ⟨y, T.coordinates.injective ?_⟩
    rw [T.coordinates_differential]
    exact Prod.ext hx0.symm hy
  · intro hx
    obtain ⟨y, rfl⟩ := (T.exact x).1 hx
    change ((T.coordinates (T.differential y)).1,
      (Submodule.Quotient.mk (T.coordinates (T.differential y)).2 : T.DiskCokernel)) = (0, 0)
    rw [T.coordinates_differential]
    exact Prod.ext rfl ((Submodule.Quotient.mk_eq_zero _).2 ⟨y, rfl⟩)

/-- The module itself is its free core plus the cokernel of its elementary disks. -/
def DiagonalResolution.moduleEquiv (T : DiagonalResolution (R := R) H) :
    H ≃ₗ[R] ((T.Core → R) × T.DiskCokernel) :=
  (T.projection.quotKerEquivOfSurjective T.surjective).symm.trans
    ((Submodule.Quotient.equiv (LinearMap.ker T.projection) (LinearMap.ker T.classMap)
      (LinearEquiv.refl R _) (by
        change Submodule.map LinearMap.id (LinearMap.ker T.projection) = LinearMap.ker T.classMap
        rw [Submodule.map_id]
        exact T.classMap_kernel.symm)).trans
      (T.classMap.quotKerEquivOfSurjective T.classMap_surjective))

/-- The determinant of the elementary-disk block. -/
def DiagonalResolution.diskDeterminant (T : DiagonalResolution (R := R) H) : R :=
  ∏ j, T.coefficient j

/-- Every constructed disk determinant is nonzero, including the empty determinant. -/
theorem DiagonalResolution.diskDeterminant_ne_zero [IsDomain R] (T : DiagonalResolution (R := R) H) :
    T.diskDeterminant ≠ 0 :=
  Finset.prod_ne_zero_iff.2 (fun j _ => T.coefficient_ne_zero j)

/-- The disk cokernel is a torsion module: the product of the Smith coefficients annihilates it. -/
theorem DiagonalResolution.diskCokernel_torsion [IsDomain R] (T : DiagonalResolution (R := R) H) :
    Module.IsTorsion R T.DiskCokernel := by
  intro z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range T.diskMap) z
  refine ⟨⟨T.diskDeterminant, mem_nonZeroDivisors_of_ne_zero T.diskDeterminant_ne_zero⟩, ?_⟩
  change (Submodule.Quotient.mk (T.diskDeterminant • x) : T.DiskCokernel) = 0
  apply (Submodule.Quotient.mk_eq_zero _).2
  refine ⟨fun j => (∏ k ∈ Finset.univ.erase j, T.coefficient k) * x j, ?_⟩
  funext j
  change T.coefficient j * ((∏ k ∈ Finset.univ.erase j, T.coefficient k) * x j) =
    T.diskDeterminant * x j
  rw [← mul_assoc, Finset.mul_prod_erase Finset.univ T.coefficient (Finset.mem_univ j)]
  rfl

/-- The constructed core rank is exactly the integral rank of the cohomology module. -/
theorem DiagonalResolution.coreRank_eq_finrank [IsDomain R] (T : DiagonalResolution (R := R) H) :
    T.coreRank = Module.finrank R H := by
  let M := (T.Core → R) × T.DiskCokernel
  let p : M →ₗ[R] (T.Core → R) := LinearMap.fst R _ _
  have hp : Function.Surjective p := fun x => ⟨(x, 0), rfl⟩
  have ht : LinearMap.ker p ≤ Submodule.torsion R M := by
    intro x hx
    obtain ⟨a, ha⟩ := T.diskCokernel_torsion (x := x.2)
    refine ⟨a, Prod.ext ?_ ha⟩
    change (a : R) • x.1 = 0
    change x.1 = 0 at hx
    rw [hx, smul_zero]
  calc T.coreRank = Module.finrank R (T.Core → R) := (Module.finrank_pi R).symm
    _ = Module.finrank R (M ⧸ LinearMap.ker p) :=
      (p.quotKerEquivOfSurjective hp).finrank_eq.symm
    _ = Module.finrank R M := finrank_quotient_eq_of_le_torsion ht
    _ = Module.finrank R H := T.moduleEquiv.finrank_eq.symm

/-- The elementary-disk matrix represents the diagonal map in its integral bases. -/
theorem DiagonalResolution.diskMatrix (T : DiagonalResolution (R := R) H) :
    (Matrix.diagonal T.coefficient).mulVecLin = T.diskMap := by
  classical
  apply LinearMap.ext
  intro x
  funext j
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal,
    DiagonalResolution.diskMap]

/-- The disk matrix has nonzero determinant. -/
theorem DiagonalResolution.diskMatrix_det_ne_zero [IsDomain R] (T : DiagonalResolution (R := R) H) :
    (Matrix.diagonal T.coefficient).det ≠ 0 := by
  rw [Matrix.det_diagonal]
  exact T.diskDeterminant_ne_zero

end DiagonalNormalForm

section ElementaryModel

variable {R : Type} [CommRing R]
  (C : CochainComplex (ModuleCat.{0} R) ℤ)
  (T : ∀ n : ℤ, DiagonalResolution (R := R) (C.homology n))

/-- A free core, disk targets, and the next degree's disk sources. -/
def elementaryTerm (n : ℤ) : ModuleCat.{0} R :=
  ModuleCat.of R ((Fin (T n).coreRank → R) × (Fin (T n).relations → R) ×
    (Fin (T (n + 1)).relations → R))

/-- The integral core-and-elementary-disks normal form, in all degrees. -/
def elementaryGCx : GCx R where
  X := elementaryTerm C T
  d i j hij := by
    subst j
    exact (0 : (elementaryTerm C T i) →ₗ[R] (Fin (T (i + 1)).coreRank → R)).prod
      (((T (i + 1)).diskMap.comp
        ((LinearMap.snd R _ _).comp (LinearMap.snd R _ _))).prod 0)
  d_d i j k hij hjk x := by
    subst j
    subst k
    change (0, (T (i + 1 + 1)).diskMap 0, 0) = 0
    simp

/-- The cochain-complex version of the elementary normal form. -/
def elementaryComplex : CochainComplex (ModuleCat.{0} R) ℤ := (elementaryGCx C T).toCC

/-- Its differential has zero core block and the diagonal elementary-disk block. -/
theorem elementaryComplex_differential (n : ℤ) (x : (elementaryComplex C T).X n) :
    ((elementaryComplex C T).d n (n + 1)).hom x = (0, (T (n + 1)).diskMap x.2.2, 0) :=
  GCx.toCC_d_hom (elementaryGCx C T) n (n + 1) rfl x

/-- Integral coordinates on the retained finite free resolution separate the free core and
elementary disks. -/
def elementaryCoordinates (n : ℤ) :
    (resolutionComplex C (fun n => (T n).toFreeResolution)).X n ≃ₗ[R]
      (elementaryComplex C T).X n :=
  (((T n).coordinates.prodCongr (LinearEquiv.refl R (Fin (T (n + 1)).relations → R))).trans
    (LinearEquiv.prodAssoc R ((T n).Core → R) (Fin (T n).relations → R)
      (Fin (T (n + 1)).relations → R))).trans
    ((T n).coreCoordinates.prodCongr (LinearEquiv.refl R _))

/-- The retained-basis change carries every differential to the elementary normal form. -/
theorem elementaryCoordinates_differential (n : ℤ)
    (x : (resolutionComplex C (fun n => (T n).toFreeResolution)).X n) :
    elementaryCoordinates C T (n + 1)
      (((resolutionComplex C (fun n => (T n).toFreeResolution)).d n (n + 1)).hom x) =
        (0, (T (n + 1)).diskMap x.2, 0) := by
  rw [resolutionComplex_differential]
  change ((T (n + 1)).coreCoordinates
      ((T (n + 1)).coordinates ((T (n + 1)).differential x.2)).1,
    ((T (n + 1)).coordinates ((T (n + 1)).differential x.2)).2, 0) = _
  rw [(T (n + 1)).coordinates_differential, map_zero]

/-- The elementary normal form is an actual integral isomorphism of complexes, not just a
rational comparison. -/
def elementaryIso : resolutionComplex C (fun n => (T n).toFreeResolution) ≅ elementaryComplex C T :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (elementaryCoordinates C T n).toModuleIso) (by
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((elementaryComplex C T).d i (i + 1)).hom (elementaryCoordinates C T i x) =
      elementaryCoordinates C T (i + 1)
        (((resolutionComplex C (fun n => (T n).toFreeResolution)).d i (i + 1)).hom x)
    rw [elementaryComplex_differential, elementaryCoordinates_differential]
    rfl)

/-- The comparison from the integral elementary normal form to the original complex. -/
def elementaryComparison : elementaryComplex C T ⟶ C :=
  (elementaryIso C T).inv ≫ resolutionComparison C (fun n => (T n).toFreeResolution)

/-- The constructed core-and-disks comparison is a quasi-isomorphism. -/
theorem elementaryComparison_quasiIso : QuasiIso (elementaryComparison C T) := by
  have := resolutionComparison_quasiIso C (fun n => (T n).toFreeResolution)
  dsimp only [elementaryComparison]
  infer_instance

/-- Every elementary normal-form term is finite free over the integral coefficient ring. -/
theorem elementaryComplex_finite_free (n : ℤ) :
    Module.Free R ((elementaryComplex C T).X n) ∧
      Module.Finite R ((elementaryComplex C T).X n) := by
  change Module.Free R ((Fin (T n).coreRank → R) × (Fin (T n).relations → R) ×
    (Fin (T (n + 1)).relations → R)) ∧
    Module.Finite R ((Fin (T n).coreRank → R) × (Fin (T n).relations → R) ×
      (Fin (T (n + 1)).relations → R))
  exact ⟨inferInstance, inferInstance⟩

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Finite generation chooses the integral elementary presentations in every degree. -/
def chosenPresentations (hfinite : ∀ n : ℤ, Module.Finite R (C.homology n)) :
    ∀ n : ℤ, DiagonalResolution (R := R) (C.homology n) :=
  fun n => chosenDiagonalResolution (hfinite n)

/-- The constructed free core has exactly the original integral cohomology ranks. -/
theorem chosenPresentations_coreRank (hfinite : ∀ n : ℤ, Module.Finite R (C.homology n)) (n : ℤ) :
    (chosenPresentations C hfinite n).coreRank = Module.finrank R (C.homology n) :=
  (chosenPresentations C hfinite n).coreRank_eq_finrank

end ElementaryModel

section CalibrationNormalForm

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- The arithmetic cohomology shape required by the central calibration: rank one in degrees
one and two, torsion in degree three, and no cohomology elsewhere. No finite-level orders occur. -/
structure CalibrationCohomologyShape (C : CochainComplex (ModuleCat.{0} R) ℤ) : Prop where
  outside : ∀ n : ℤ, n < 1 ∨ 3 < n → Subsingleton (C.homology n)
  rank_one : Module.finrank R (C.homology 1) = 1
  rank_two : Module.finrank R (C.homology 2) = 1
  rank_three : Module.finrank R (C.homology 3) = 0

omit [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] in
/-- Finite coordinates of rank zero form a zero module. -/
theorem finiteCoordinates_zero (r : ℕ) (hr : r = 0) : Subsingleton (Fin r → R) := by
  subst r
  infer_instance

/-- Identify rank-one coordinates with an integral line. -/
def finiteLineEquiv (r : ℕ) (hr : r = 1) : (Fin r → R) ≃ₗ[R] R := by
  subst r
  exact (lineCoordinates R).symm

/-- Remove two zero factors from a direct product. -/
def dropTwoZeroFactors {L M N : Type} [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Subsingleton L] [Subsingleton M] : (L × M × N) ≃ₗ[R] N where
  toFun x := x.2.2
  invFun x := (0, 0, x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _x := Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv _ := rfl

/-- Remove the two zero edge factors from a direct product. -/
def dropZeroEdgeFactors {L M N : Type} [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Subsingleton L] [Subsingleton N] : (L × M × N) ≃ₗ[R] M where
  toFun x := x.2.1
  invFun x := (0, x, 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _x := Prod.ext (Subsingleton.elim _ _) (Prod.ext rfl (Subsingleton.elim _ _))
  right_inv _ := rfl

/-- A zero module has its unique coordinates in the zero term. -/
def trivialModuleEquiv {M : Type} [AddCommGroup M] [Module R M] [Subsingleton M] : M ≃ₗ[R] PUnit where
  toFun _ := PUnit.unit
  invFun _ := 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := rfl

variable (C : CochainComplex (ModuleCat.{0} R) ℤ)
  (hfinite : ∀ n : ℤ, Module.Finite R (C.homology n)) (H : CalibrationCohomologyShape C)

include H

/-- Outside the cohomological support, the chosen disk block is empty. -/
theorem calibrationPresentation_relations_zero (n : ℤ) (hn : n < 1 ∨ 3 < n) :
    (chosenPresentations C hfinite n).relations = 0 :=
  (chosenDiagonalResolution_zero (hfinite n) (H.outside n hn)).2

/-- Outside the cohomological support, the constructed free core is empty. -/
theorem calibrationPresentation_core_zero (n : ℤ) (hn : n < 1 ∨ 3 < n) :
    (chosenPresentations C hfinite n).coreRank = 0 := by
  rw [chosenPresentations_coreRank]
  let := H.outside n hn
  exact Module.finrank_zero_of_subsingleton

/-- The elementary complex is bounded in exactly the four central degrees. -/
theorem calibrationElementary_zero (n : ℤ) (hn : n < 0 ∨ 3 < n) :
    Subsingleton ((elementaryComplex C (chosenPresentations C hfinite)).X n) := by
  let T := chosenPresentations C hfinite
  have hc : (T n).coreRank = 0 := calibrationPresentation_core_zero C hfinite H n (by omega)
  have hd : (T n).relations = 0 := calibrationPresentation_relations_zero C hfinite H n (by omega)
  have hd' : (T (n + 1)).relations = 0 :=
    calibrationPresentation_relations_zero C hfinite H (n + 1) (by omega)
  let := finiteCoordinates_zero (R := R) _ hc
  let := finiteCoordinates_zero (R := R) _ hd
  let := finiteCoordinates_zero (R := R) _ hd'
  change Subsingleton ((Fin (T n).coreRank → R) × (Fin (T n).relations → R) ×
    (Fin (T (n + 1)).relations → R))
  infer_instance

/-- The three integral diagonal disk matrices constructed from the cohomology presentations. -/
def calibrationDiskMatrix (j : ℤ) : Matrix (Fin (chosenPresentations C hfinite j).relations)
    (Fin (chosenPresentations C hfinite j).relations) R :=
  Matrix.diagonal (chosenPresentations C hfinite j).coefficient

/-- The normal-form term coordinates are integral and remove only zero summands. -/
def calibrationDegreeCoordinates : (n : ℤ) →
    (elementaryComplex C (chosenPresentations C hfinite)).X n ≃ₗ[R]
      (blockComplex (calibrationDiskMatrix C hfinite 1) (calibrationDiskMatrix C hfinite 2)
        (calibrationDiskMatrix C hfinite 3)).X n
  | .ofNat 0 => by
      let := finiteCoordinates_zero (R := R) _
        (calibrationPresentation_core_zero C hfinite H 0 (by omega))
      let := finiteCoordinates_zero (R := R) _
        (calibrationPresentation_relations_zero C hfinite H 0 (by omega))
      exact dropTwoZeroFactors
  | .ofNat 1 =>
      (finiteLineEquiv (R := R) _ ((chosenPresentations_coreRank C hfinite 1).trans H.rank_one)).prodCongr
        (LinearEquiv.refl R _)
  | .ofNat 2 =>
      (finiteLineEquiv (R := R) _ ((chosenPresentations_coreRank C hfinite 2).trans H.rank_two)).prodCongr
        (LinearEquiv.refl R _)
  | .ofNat 3 => by
      let := finiteCoordinates_zero (R := R) _
        ((chosenPresentations_coreRank C hfinite 3).trans H.rank_three)
      let := finiteCoordinates_zero (R := R) _
        (calibrationPresentation_relations_zero C hfinite H (Int.ofNat 3 + 1) (by norm_num))
      exact dropZeroEdgeFactors
  | .ofNat (n + 4) => by
      let := calibrationElementary_zero C hfinite H (.ofNat (n + 4))
        (by simp only [Int.ofNat_eq_natCast]; omega)
      exact trivialModuleEquiv
  | .negSucc n => by
      let := calibrationElementary_zero C hfinite H (.negSucc n) (by omega)
      exact trivialModuleEquiv

/-- The general core-and-disks form is the required four-degree central matrix model when the
arithmetic cohomology shape holds. This is an integral chain isomorphism. -/
def calibrationBlockIso : elementaryComplex C (chosenPresentations C hfinite) ≅
    blockComplex (calibrationDiskMatrix C hfinite 1) (calibrationDiskMatrix C hfinite 2)
      (calibrationDiskMatrix C hfinite 3) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (calibrationDegreeCoordinates C hfinite H n).toModuleIso) (by
      intro i j hij
      have hj : i + 1 = j := hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      cases i with
      | negSucc n =>
        let := calibrationElementary_zero C hfinite H (.negSucc n) (by omega)
        have hx : x = 0 := Subsingleton.elim _ _
        simp only [ModuleCat.hom_comp, hx, map_zero]
      | ofNat n =>
        rcases n with _ | _ | _ | n
        · change ((blockComplex _ _ _).d 0 1).hom (calibrationDegreeCoordinates C hfinite H 0 x) =
            calibrationDegreeCoordinates C hfinite H 1
              (((elementaryComplex C (chosenPresentations C hfinite)).d 0 1).hom x)
          erw [elementaryComplex_differential C (chosenPresentations C hfinite) 0 x, blockComplex_d0]
          change (0, (calibrationDiskMatrix C hfinite 1).mulVecLin x.2.2, 0) =
            (finiteLineEquiv (R := R) _ _ 0, (chosenPresentations C hfinite 1).diskMap x.2.2, 0)
          erw [(chosenPresentations C hfinite 1).diskMatrix, map_zero]
        · change ((blockComplex _ _ _).d 1 2).hom (calibrationDegreeCoordinates C hfinite H 1 x) =
            calibrationDegreeCoordinates C hfinite H 2
              (((elementaryComplex C (chosenPresentations C hfinite)).d 1 2).hom x)
          erw [elementaryComplex_differential C (chosenPresentations C hfinite) 1 x, blockComplex_d1]
          change (0, (calibrationDiskMatrix C hfinite 2).mulVecLin x.2.2, 0) =
            (finiteLineEquiv (R := R) _ _ 0, (chosenPresentations C hfinite 2).diskMap x.2.2, 0)
          erw [(chosenPresentations C hfinite 2).diskMatrix, map_zero]
        · change ((blockComplex _ _ _).d 2 3).hom (calibrationDegreeCoordinates C hfinite H 2 x) =
            calibrationDegreeCoordinates C hfinite H 3
              (((elementaryComplex C (chosenPresentations C hfinite)).d 2 3).hom x)
          erw [elementaryComplex_differential C (chosenPresentations C hfinite) 2 x, blockComplex_d2]
          change (calibrationDiskMatrix C hfinite 3).mulVecLin x.2.2 =
            (chosenPresentations C hfinite 3).diskMap x.2.2
          exact LinearMap.congr_fun (chosenPresentations C hfinite 3).diskMatrix x.2.2
        · let : Subsingleton ((blockComplex (calibrationDiskMatrix C hfinite 1)
              (calibrationDiskMatrix C hfinite 2) (calibrationDiskMatrix C hfinite 3)).X
                (Int.ofNat (n + 1 + 1 + 1) + 1)) := by
            have hidx : Int.ofNat (n + 1 + 1 + 1) + 1 = Int.ofNat (n + 4) := by
              simp only [Int.ofNat_eq_natCast]
              omega
            rw [hidx]
            exact inferInstanceAs (Subsingleton PUnit)
          exact Subsingleton.elim _ _)

end CalibrationNormalForm

section ScalarExtension

variable {R A : Type} [CommRing R] [CommRing A]
  {C D : CochainComplex (ModuleCat.{0} R) ℤ}

/-- Extension of coefficients is an additive functor. -/
instance scalarExtensionAdditive (φ : R →+* A) :
    (ModuleCat.extendScalars.{0, 0, 0} φ).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    let oneA : (ModuleCat.restrictScalars φ).obj (ModuleCat.of A A) := (1 : A)
    change oneA ⊗ₜ[R] (f.hom x + g.hom x) = _
    exact TensorProduct.tmul_add _ _ _

/-- Extension of coefficients preserves an actual homotopy equivalence. -/
def scalarHomotopyEquiv (φ : R →+* A) (e : HomotopyEquiv C D) :
    HomotopyEquiv (scalarChangedComplex φ C) (scalarChangedComplex φ D) :=
  (ModuleCat.extendScalars φ).mapHomotopyEquiv e

/-- The extended forward comparison is a quasi-isomorphism, even for a nonflat coefficient ring. -/
theorem scalarHomotopyEquiv_quasiIso (φ : R →+* A) (e : HomotopyEquiv C D) :
    QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom) :=
  (scalarHomotopyEquiv φ e).quasiIso_hom

/-- The extended inverse comparison is also a quasi-isomorphism. -/
theorem scalarHomotopyEquiv_inverse_quasiIso (φ : R →+* A) (e : HomotopyEquiv C D) :
    QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map e.inv) :=
  (scalarHomotopyEquiv φ e).quasiIso_inv

end ScalarExtension

section FlatReduction

variable {R : Type} [CommRing R]

set_option backward.isDefEq.respectTransparency true in
/-- The kernel inclusion of a surjection onto a flat module remains injective after tensoring
with any module. -/
theorem tensor_kernel_injective {M N : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R N]
    (A : Type) [AddCommGroup A] [Module R A] (g : M →ₗ[R] N)
    (hg : Function.Surjective g) :
    Function.Injective ((LinearMap.ker g).subtype.lTensor A) := by
  let q : (A →₀ R) →ₗ[R] A := Finsupp.linearCombination R id
  have hq : Function.Surjective q := Finsupp.linearCombination_surjective _ Function.surjective_id
  have hfirst : Function.Injective ((LinearMap.ker q).subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := N)
      (LinearMap.ker q).subtype Subtype.val_injective
  have hsecond : Function.Injective ((LinearMap.ker g).subtype.lTensor (A →₀ R)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := A →₀ R)
      (LinearMap.ker g).subtype Subtype.val_injective
  exact @lTensor_injective_of_exact_of_exact_of_rTensor_injective R inferInstance
    (LinearMap.ker q) (A →₀ R) A (LinearMap.ker g) M N
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (LinearMap.ker q).subtype q (LinearMap.ker g).subtype g
    (LinearMap.exact_subtype_ker_map q) hq (LinearMap.exact_subtype_ker_map g) hg hfirst hsecond

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Two consecutive exact pairs with a flat last term remain exact at their first middle
term after arbitrary coefficient extension over a principal ideal domain. -/
theorem baseChange_exact_of_two_exact_pairs {M N P Q A : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [Module.Flat R Q]
    [CommRing A] [Algebra R A] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : P →ₗ[R] Q)
    (hfg : Function.Exact f g) (hgh : Function.Exact g h) :
    Function.Exact (f.baseChange A) (g.baseChange A) := by
  let K := LinearMap.ker h.rangeRestrict
  let g' : N →ₗ[R] K := g.codRestrict K (fun x =>
    Subtype.ext ((hgh (g x)).2 ⟨x, rfl⟩))
  have hg' : Function.Surjective g' := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (hgh x).1 (congrArg Subtype.val hx)
    exact ⟨y, Subtype.ext hy⟩
  have hfg' : Function.Exact f g' := by
    intro x
    change g' x = 0 ↔ ∃ y, f y = x
    rw [Subtype.ext_iff]
    exact hfg x
  have hh : Function.Surjective h.rangeRestrict := by
    rintro ⟨x, y, rfl⟩
    exact ⟨y, rfl⟩
  let : Module.Flat R (LinearMap.range h) := inferInstance
  have hinj : Function.Injective (K.subtype.lTensor A) :=
    tensor_kernel_injective A h.rangeRestrict hh
  have hfactor : g = K.subtype.comp g' := rfl
  rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor,
    hfactor, LinearMap.lTensor_comp]
  intro x
  change (K.subtype.lTensor A) ((g'.lTensor A) x) = 0 ↔ ∃ y, (f.lTensor A) y = x
  refine Iff.trans ?_ ((lTensor_exact A hfg' hg') x)
  constructor
  · intro hx
    exact hinj (hx.trans (map_zero _).symm)
  · intro hx
    rw [hx, map_zero]

/-- An acyclic complex of flat modules over a principal ideal domain remains acyclic after
arbitrary coefficient extension. -/
theorem scalarChanged_acyclic {A : Type} [CommRing A] (φ : R →+* A)
    (C : CochainComplex (ModuleCat.{0} R) ℤ)
    (hflat : ∀ n : ℤ, Module.Flat R (C.X n)) (hacyclic : C.Acyclic) :
    (scalarChangedComplex φ C).Acyclic := by
  let : Algebra R A := φ.toAlgebra
  intro n
  apply ((scalarChangedComplex φ C).exactAt_iff' (n - 1) n (n + 1)
    (by simp) (by simp)).2
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
  have hfg : Function.Exact (C.d (n - 1) n).hom (C.d n (n + 1)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((C.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).1 (hacyclic n))
  have hgh : Function.Exact (C.d n (n + 1)).hom (C.d (n + 1) (n + 2)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      ((C.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp [add_assoc])).1 (hacyclic (n + 1)))
  let := hflat (n + 2)
  change Function.Exact ((C.d (n - 1) n).hom.baseChange A) ((C.d n (n + 1)).hom.baseChange A)
  exact baseChange_exact_of_two_exact_pairs _ _ _ hfg hgh

omit [IsDomain R] [IsPrincipalIdealRing R] in
/-- A comparison is a quasi-isomorphism precisely when its mapping cone is acyclic. -/
theorem quasiIso_iff_mappingCone_acyclic {C D : CochainComplex (ModuleCat.{0} R) ℤ}
    (f : C ⟶ D) : QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff f,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff f,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic (ModuleCat.{0} R)).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

/-- The mapping cone of a comparison of degreewise flat complexes is degreewise flat. -/
theorem mappingCone_flat {C D : CochainComplex (ModuleCat.{0} R) ℤ} (f : C ⟶ D)
    (hC : ∀ n : ℤ, Module.Flat R (C.X n)) (hD : ∀ n : ℤ, Module.Flat R (D.X n)) (n : ℤ) :
    Module.Flat R ((CochainComplex.mappingCone f).X n) := by
  let := hC (n + 1)
  let := hD n
  exact Module.Flat.of_linearEquiv
    ((HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl) ≪≫
      ModuleCat.biprodIsoProd (C.X (n + 1)) (D.X n)).toLinearEquiv

/-- A quasi-isomorphism between complexes of flat modules over a principal ideal domain
remains a quasi-isomorphism after tensoring with any coefficient ring. -/
theorem scalarChanged_quasiIso {A : Type} [CommRing A] (φ : R →+* A)
    {C D : CochainComplex (ModuleCat.{0} R) ℤ} (f : C ⟶ D)
    (hC : ∀ n : ℤ, Module.Flat R (C.X n)) (hD : ∀ n : ℤ, Module.Flat R (D.X n))
    (hf : QuasiIso f) :
    QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have hc := scalarChanged_acyclic φ (CochainComplex.mappingCone f)
    (mappingCone_flat f hC hD) ((quasiIso_iff_mappingCone_acyclic f).1 hf)
  let e := HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f
    (ModuleCat.extendScalars φ)
  have : QuasiIso e.hom := inferInstance
  apply (quasiIso_iff_mappingCone_acyclic _).2
  intro n
  exact (exactAt_iff_of_quasiIsoAt e.hom n).1 (hc n)

end FlatReduction

section CompactKummer

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.CoefModules
attribute [local instance] levTop

variable {K : Type} [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) (W : WeierstrassCurve K) [W.IsElliptic]
  (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))

/-- Continuous cochains with torsion-free coefficients are torsion-free. -/
theorem contCochain_torsionFree {R G M : Type} [CommRing R] [Group G]
    [AddCommGroup M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M]
    [TopologicalSpace G] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul R M] [Module.IsTorsionFree R M] (n : ℕ) :
    Module.IsTorsionFree R (contCochain R G M n) := by
  let : Module.IsTorsionFree R ((groupCohomology.inhomogeneousCochains (rep R G M)).X n) :=
    inferInstanceAs (Module.IsTorsionFree R ((Fin n → G) → M))
  infer_instance

/-- Extension by zero preserves degreewise torsion-freeness. -/
theorem natCx_torsionFree {R : Type} [CommRing R]
    (A : CochainComplex (ModuleCat.{0} R) ℕ)
    (hA : ∀ n : ℕ, Module.IsTorsionFree R (A.X n)) (n : ℤ) :
    Module.IsTorsionFree R ((natCx A).X n) := by
  cases n with
  | ofNat n => exact hA n
  | negSucc n => exact inferInstanceAs (Module.IsTorsionFree R PUnit)

/-- Restricting a group action does not change torsion-freeness of the coefficient module. -/
theorem resMod_torsionFree {R G H M : Type} [CommRing R] [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] (φ : H →ₜ* G) :
    Module.IsTorsionFree R (ResMod φ M) :=
  Function.Injective.moduleIsTorsionFree (fun x : ResMod φ M => (show M from x))
    (fun _ _ h => h) (fun _ _ => rfl)

/-- The genuine compact Kummer complex is degreewise flat over the two-adic integers. -/
theorem compactKummerComplex_flat (n : ℤ) :
    Module.Flat ℤ_[2] ((compactKummerComplex S W hFull).X n) := by
  classical
  let : HasFullTwoTorsion K S W := ⟨hFull⟩
  have hG : Module.IsTorsionFree ℤ_[2] ((tateKummerSelData S W hFull).G.X n) := by
    exact natCx_torsionFree _ (fun m => contCochain_torsionFree m) n
  have hL : ∀ (v : Places K S) (m : ℤ),
      Module.IsTorsionFree ℤ_[2] ((locAt K S ℤ_[2] (TateS K S W) v).X m) := by
    intro v m
    let : Module.IsTorsionFree ℤ_[2] (ResMod (locMap K S v.1) (TateS K S W)) :=
      resMod_torsionFree (locMap K S v.1)
    exact natCx_torsionFree _ (fun a => contCochain_torsionFree a) m
  have hU : ∀ (v : Places K S),
      Module.IsTorsionFree ℤ_[2] ((tateKummerCondition W hFull v.1).X n) := by
    intro v
    let := hL v n
    exact Function.Injective.moduleIsTorsionFree
      ((tateKummerConditionι W hFull v.1).f n n rfl)
      (tateKummerLocalConditions_injective S W hFull v n)
      (fun _ _ => LinearMap.map_smul _ _ _)
  let := hG
  let : ∀ v : Places K S, Module.IsTorsionFree ℤ_[2]
      ((tateKummerCondition W hFull v.1).X n) := hU
  let : ∀ v : Places K S, Module.IsTorsionFree ℤ_[2]
      ((locAt K S ℤ_[2] (TateS K S W) v).X (n - 1)) := fun v => hL v (n - 1)
  let : Module.IsTorsionFree ℤ_[2] ((tateKummerSelData S W hFull).U.X n) := by
    change Module.IsTorsionFree ℤ_[2] (∀ v : Places K S, (tateKummerCondition W hFull v.1).X n)
    infer_instance
  let : Module.IsTorsionFree ℤ_[2] ((tateKummerSelData S W hFull).L.X (n - 1)) := by
    change Module.IsTorsionFree ℤ_[2] (∀ v : Places K S,
      (locAt K S ℤ_[2] (TateS K S W) v).X (n - 1))
    infer_instance
  change Module.Flat ℤ_[2] (selT (tateKummerSelData S W hFull) n)
  have : Module.IsTorsionFree ℤ_[2] (selT (tateKummerSelData S W hFull) n) := by
    change Module.IsTorsionFree ℤ_[2] ((tateKummerSelData S W hFull).G.X n ×
      (tateKummerSelData S W hFull).U.X n × (tateKummerSelData S W hFull).L.X (n - 1))
    infer_instance
  infer_instance

/-- Finite integral Kummer cohomology supplies the actual finite free comparison. -/
theorem compactKummer_finiteReplacement
    (hfinite : ∀ n, Module.Finite ℤ_[2] ((compactKummerComplex S W hFull).homology n)) :
    QuasiIso (finiteReplacementMap (compactKummerComplex S W hFull) hfinite) ∧
      ∀ n : ℤ, Module.Free ℤ_[2]
        ((finiteReplacement (compactKummerComplex S W hFull) hfinite).X n) ∧
        Module.Finite ℤ_[2] ((finiteReplacement (compactKummerComplex S W hFull) hfinite).X n) :=
  ⟨finiteReplacementMap_quasiIso _ _, finiteReplacement_finite_free _ _⟩

/-- The constructed finite free comparison remains a quasi-isomorphism under every coefficient
extension; no flatness of the new coefficient ring is required. -/
theorem compactKummer_finiteReplacement_baseChange {A : Type} [CommRing A]
    (φ : ℤ_[2] →+* A)
    (hfinite : ∀ n, Module.Finite ℤ_[2] ((compactKummerComplex S W hFull).homology n)) :
    QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (finiteReplacementMap (compactKummerComplex S W hFull) hfinite)) := by
  apply scalarChanged_quasiIso φ _ _ (compactKummerComplex_flat S W hFull)
    (finiteReplacementMap_quasiIso _ _)
  intro n
  have := (finiteReplacement_finite_free (compactKummerComplex S W hFull) hfinite n).1
  infer_instance

/-- The finite free replacement is supported in degrees zero through three once the
integral cohomology is supported in degrees one through three. -/
theorem compactKummer_finiteReplacement_bounded
    (hfinite : ∀ n, Module.Finite ℤ_[2] ((compactKummerComplex S W hFull).homology n))
    (hbounded : ∀ n : ℤ, n < 1 ∨ 3 < n →
      Subsingleton ((compactKummerComplex S W hFull).homology n)) (n : ℤ)
    (hn : n < 0 ∨ 3 < n) :
    Subsingleton ((finiteReplacement (compactKummerComplex S W hFull) hfinite).X n) :=
  finiteReplacement_bounded _ _ 1 3 hbounded n (by omega)

end CompactKummer

section CentralAssembly

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData K E₀ hZ)
  (hfinite : ∀ n, Module.Finite ℤ_[2]
    ((compactKummerComplex G.S (centralCurve G) (centralFullTorsion G)).homology n))

/-- The retained finite free central complex, chosen in integral Smith bases. -/
def retainedCentralComplex : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ :=
  resolutionComplex (compactCentralComplex G)
    (fun n => (chosenPresentations (compactCentralComplex G) hfinite n).toFreeResolution)

/-- The actual comparison of the retained central complex with the compact Kummer complex. -/
def retainedCentralComparison : retainedCentralComplex G hfinite ⟶ compactCentralComplex G :=
  resolutionComparison (compactCentralComplex G)
    (fun n => (chosenPresentations (compactCentralComplex G) hfinite n).toFreeResolution)

/-- Finite generation constructs the integral quasi-isomorphism of the retained central model. -/
theorem retainedCentralComparison_quasiIso : QuasiIso (retainedCentralComparison G hfinite) :=
  resolutionComparison_quasiIso _ _

/-- The retained central complex is degreewise finite free. -/
theorem retainedCentralComplex_finite_free (n : ℤ) :
    Module.Free ℤ_[2] ((retainedCentralComplex G hfinite).X n) ∧
      Module.Finite ℤ_[2] ((retainedCentralComplex G hfinite).X n) :=
  resolutionComplex_finite_free _ _ n

/-- Every coefficient extension of the retained central comparison is a quasi-isomorphism.
In particular this applies both to the integer residue rings and to the finite coefficient rings
used by calibration. -/
theorem retainedCentralComparison_baseChange {A : Type} [CommRing A] (φ : ℤ_[2] →+* A) :
    QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (retainedCentralComparison G hfinite)) := by
  apply scalarChanged_quasiIso φ _ _ _ (retainedCentralComparison_quasiIso G hfinite)
  · intro n
    have := (retainedCentralComplex_finite_free G hfinite n).1
    infer_instance
  · intro n
    rw [compactCentralComplex_eq]
    exact compactKummerComplex_flat G.S (centralCurve G) (centralFullTorsion G) n

/-- The finite-fibre condition on the constructed retained model is exactly the derived condition
on the canonical compact-to-finite Kummer reduction map. It is not inferred from cocycle reduction. -/
theorem retainedCentral_fibre_quasiIso_iff (i : ℕ) :
    QuasiIso (((ModuleCat.extendScalars (constRed i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (retainedCentralComparison G hfinite) ≫ canonicalCentralReductionMap G i) ↔
        QuasiIso (canonicalCentralReductionMap G i) := by
  have := retainedCentralComparison_baseChange G hfinite (constRed i)
  exact quasiIso_iff_comp_left _ _

/-- The three diagonal disk matrices are constructed, rather than assigned torsion lengths. -/
def centralDiskMatrix (j : ℤ) :
    Matrix (Fin (chosenPresentations (compactCentralComplex G) hfinite j).relations)
      (Fin (chosenPresentations (compactCentralComplex G) hfinite j).relations) ℤ_[2] :=
  calibrationDiskMatrix (compactCentralComplex G) hfinite j

/-- Every central disk determinant is nonzero. -/
theorem centralDiskMatrix_det_ne_zero (j : ℤ) : (centralDiskMatrix G hfinite j).det ≠ 0 :=
  (chosenPresentations (compactCentralComplex G) hfinite j).diskMatrix_det_ne_zero

variable (H : CalibrationCohomologyShape (compactCentralComplex G))

include H

/-- The integral normalization of the retained complex has one free line in each of degrees one
and two and the three constructed diagonal disk blocks in degrees zero through three. -/
def retainedCentralNormalization :
    blockComplex (centralDiskMatrix G hfinite 1) (centralDiskMatrix G hfinite 2)
      (centralDiskMatrix G hfinite 3) ≅ retainedCentralComplex G hfinite :=
  (calibrationBlockIso (compactCentralComplex G) hfinite H).symm ≪≫
    (elementaryIso (compactCentralComplex G) (chosenPresentations (compactCentralComplex G) hfinite)).symm

/-- Retain the integral basis produced by the normalization, in the central block indices. -/
def retainedCentralCoordinates (n : ℤ) :
    (retainedCentralComplex G hfinite).X n ≃ₗ[ℤ_[2]]
      (blockIndex (chosenPresentations (compactCentralComplex G) hfinite 1).relations
        (chosenPresentations (compactCentralComplex G) hfinite 2).relations
        (chosenPresentations (compactCentralComplex G) hfinite 3).relations n → ℤ_[2]) :=
  ((HomologicalComplex.Hom.isoApp (retainedCentralNormalization G hfinite H) n).toLinearEquiv.symm).trans
    (blockCoordinates (centralDiskMatrix G hfinite 1) (centralDiskMatrix G hfinite 2)
      (centralDiskMatrix G hfinite 3) n)

/-- The integral central model is assembled from finite integral cohomology, its arithmetic
amplitude and ranks, and the derived quasi-isomorphism of the canonical Kummer reduction.
The retained complex, bases, normalization, disk matrices, and integral comparison are constructed.
No disk-order equality is an input. -/
def integralBlockCentralModel
    (hreduce : ∀ i : ℕ, i ≠ 0 → QuasiIso (canonicalCentralReductionMap G i)) :
    IntegralBlockCentralModel G (centralDiskMatrix G hfinite 1) (centralDiskMatrix G hfinite 2)
      (centralDiskMatrix G hfinite 3) where
  P := retainedCentralComplex G hfinite
  coordinates := retainedCentralCoordinates G hfinite H
  normalization := retainedCentralNormalization G hfinite H
  comparison := retainedCentralComparison G hfinite
  quasi_iso := retainedCentralComparison_quasiIso G hfinite
  fibre_quasi_iso i hi := (retainedCentral_fibre_quasiIso_iff G hfinite i).2 (hreduce i hi)
  disk1_det_ne_zero := centralDiskMatrix_det_ne_zero G hfinite 1
  disk2_det_ne_zero := centralDiskMatrix_det_ne_zero G hfinite 2
  disk3_det_ne_zero := centralDiskMatrix_det_ne_zero G hfinite 3

/-- The constructed retained-basis normalization is integral and unimodular in every degree. -/
theorem integralBlockCentralModel_basis_unimodular
    (hreduce : ∀ i : ℕ, i ≠ 0 → QuasiIso (canonicalCentralReductionMap G i)) (n : ℤ) :
    IsUnit ((integralBlockCentralModel G hfinite H hreduce).basisMatrix n).det :=
  (integralBlockCentralModel G hfinite H hreduce).basisMatrix_isUnit_det n

/-- The inverse determinant-line basis factor has central valuation zero; no rational
normalization or arithmetic order is needed for this integral statement. -/
theorem integralBlockCentralModel_inverseDeterminant_valuation
    (hreduce : ∀ i : ℕ, i ≠ 0 → QuasiIso (canonicalCentralReductionMap G i)) :
    ((integralBlockCentralModel G hfinite H hreduce).inverseDeterminantBasisFactor : ℤ_[2]).valuation = 0 :=
  (integralBlockCentralModel G hfinite H hreduce).inverseDeterminantBasisFactor_valuation

/-- The calibration disk tie is now a consequence of the constructed matrices and model,
subject only to the stated cohomology and canonical derived-reduction hypotheses. -/
theorem diskTie_of_finite_cohomology
    (hreduce : ∀ i : ℕ, i ≠ 0 → QuasiIso (canonicalCentralReductionMap G i)) :
    DiskTie G (centralDiskMatrix G hfinite 1).det (centralDiskMatrix G hfinite 2).det
      (centralDiskMatrix G hfinite 3).det :=
  (integralBlockCentralModel G hfinite H hreduce).diskTie

end CentralAssembly

end ZInQ.Contrib.RC53Assist.CalibrationModel
