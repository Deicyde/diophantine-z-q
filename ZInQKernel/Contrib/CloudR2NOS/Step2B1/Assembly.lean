/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step2-b/src/ZInQKernel/Contrib/CloudR2NOS/Step2B1/Assembly.lean (sha256 4b764b14718bcfd0b27ab298db045087962ffed29faa55230539a9ed17d51996).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 2, B1 `FiniteSupportStabilizer`: ASSEMBLY, PROVED from the KEY multiplicity step
(B1.c, Plan.lean 205980f8) and two small topological obligations. 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED. Universe u.

Small obligations (TRUE, elementary):
* `SupportComponentsFinite`: the maximal irreducible subsets of the closed `supp D` are finite in
  number. `A` is Noetherian; this is Mathlib `NoetherianSpace.finite_irreducibleComponents` on
  the subspace, transported to subsets.
* `TranslationPermutesComponents`: if `t_x⁻¹(supp D) = supp D`, then `t_x⁻¹` maps maximal
  irreducible subsets of `supp D` to maximal irreducible subsets. `t_x` is a homeomorphism (an
  isomorphism of schemes), and preimages under homeomorphisms preserve irreducibility and
  inclusion.

PROVED here, modulo compile:
* `supportStabilizer_inv`: the support stabilizer is closed under inverses.
* `finiteSupportStabilizer`: the finite-index argument (B1.d).
  - `x ↦ (C ↦ t_x⁻¹C)` sends `S` into a finite function space.
  - Equal images give `y·x⁻¹`, which fixes every component and so lies in the finite `H(D)` by
    the KEY step.
  - Hence each fibre lies in the finite coset `H(D)·x`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.Plan
import ZInQKernel.Contrib.CloudR2NOS.Step1.TwistSelection

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step2B1

local notation "tr" => H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation

/-- (TRUE) Finitely many maximal irreducible subsets of the support. -/
def SupportComponentsFinite : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData),
    {C : Set A.X.left | Maximal
      (fun Z : Set A.X.left => Z ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Z) C}.Finite

/-- (TRUE) Support-preserving translations permute the maximal irreducible subsets. -/
def TranslationPermutesComponents : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData) (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X),
    (tr A x) ⁻¹' (D.support : Set A.X.left) = (D.support : Set A.X.left) →
    ∀ C : Set A.X.left,
      Maximal (fun Z : Set A.X.left => Z ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Z) C →
      Maximal (fun Z : Set A.X.left => Z ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Z)
        ((tr A x) ⁻¹' C)

section Lemmas

variable {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K))))

theorem tr_mul (x y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    tr A (x * y) = tr A x ≫ tr A y :=
  (ZInQ.Contrib.CloudR2NOS.Step1.transl_mul A x y).symm

theorem tr_one : tr A (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) = 𝟙 _ :=
  ZInQ.Contrib.CloudR2NOS.Step1.transl_one A

theorem preimage_tr_mul (x y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) (Z : Set A.X.left) :
    (tr A (x * y)) ⁻¹' Z = (tr A x) ⁻¹' ((tr A y) ⁻¹' Z) := by
  rw [tr_mul]
  rfl

theorem preimage_tr_one (Z : Set A.X.left) :
    (tr A (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X)) ⁻¹' Z = Z := by
  rw [tr_one]
  rfl

/-- `t_x⁻¹ Z = Z` implies `t_{x⁻¹}⁻¹ Z = Z`. -/
theorem preimage_tr_inv {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X} {Z : Set A.X.left}
    (h : (tr A x) ⁻¹' Z = Z) : (tr A x⁻¹) ⁻¹' Z = Z := by
  have h1 : (tr A x⁻¹) ⁻¹' ((tr A x) ⁻¹' Z) = Z := by
    rw [← preimage_tr_mul, inv_mul_cancel, preimage_tr_one]
  rwa [h] at h1

end Lemmas

/-- The support stabilizer is closed under inverses (support of `comap` is the preimage). -/
theorem supportStabilizer_inv {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K))))
    (D : A.X.left.IdealSheafData) {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X}
    (hx : (tr A x) ⁻¹' (D.support : Set A.X.left) = (D.support : Set A.X.left)) :
    (tr A x⁻¹) ⁻¹' (D.support : Set A.X.left) = (D.support : Set A.X.left) :=
  preimage_tr_inv A hx

/-- B1, PROVED from the KEY step and the two small obligations. -/
theorem finiteSupportStabilizer (hKey : ComponentFixingPreservesDivisor.{u})
    (hFin : SupportComponentsFinite.{u}) (hPerm : TranslationPermutesComponents.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSupportStabilizer.{u} := by
  intro K _ _ A _ D hD hH
  classical
  let Z₀ : Set A.X.left := (D.support : Set A.X.left)
  let Comp : Set (Set A.X.left) := {C | Maximal
    (fun Z : Set A.X.left => Z ⊆ (D.support : Set A.X.left) ∧ IsIrreducible Z) C}
  have hComp : Comp.Finite := hFin A D
  let S : Set (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :=
    {x | (D.comap (tr A x)).support = D.support}
  -- membership in `S` is preimage invariance of the support
  have hSmem : ∀ x, x ∈ S ↔ (tr A x) ⁻¹' Z₀ = Z₀ := by
    intro x
    change (D.comap (tr A x)).support = D.support ↔ _
    rw [Scheme.IdealSheafData.support_comap]
    exact ⟨fun h => congrArg (fun T : Closeds A.X.left => (T : Set A.X.left)) h,
      fun h => Closeds.ext h⟩
  -- the component map, restricted to the finite set of components
  haveI : Fintype Comp := hComp.fintype
  let Ψ : (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) → (Comp → Set A.X.left) :=
    fun x C => (tr A x) ⁻¹' C.1
  have himg : (Ψ '' S).Finite := by
    refine (Set.finite_range (fun φ : Comp → Comp => fun C => (φ C).1)).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨fun C => ⟨(tr A x) ⁻¹' C.1, hPerm A D x ((hSmem x).mp hx) C.1 C.2⟩, rfl⟩
  -- each fibre lies in the finite coset `H(D)·x`
  have hfib : ∀ x ∈ S, {y | y ∈ S ∧ Ψ y = Ψ x} ⊆
      (fun h => h * x) '' H5OriginalDVR.Lane2.NativeDivisorKernel.divisorStabilizer A D := by
    intro x hx y ⟨hy, hΨ⟩
    refine ⟨y * x⁻¹, ?_, by simp⟩
    apply hKey A D hD (y * x⁻¹)
    intro C _ hCmax
    have hxinv := supportStabilizer_inv A D ((hSmem x).mp hx)
    -- `C' := t_{x⁻¹}⁻¹ C` is a component, with `t_x⁻¹ C' = C`
    have hC' := hPerm A D x⁻¹ hxinv C hCmax
    have h1 : (tr A x) ⁻¹' ((tr A x⁻¹) ⁻¹' C) = C := by
      rw [← preimage_tr_mul, mul_inv_cancel, preimage_tr_one]
    have h2 := congrFun hΨ ⟨(tr A x⁻¹) ⁻¹' C, hC'⟩
    change (tr A y) ⁻¹' ((tr A x⁻¹) ⁻¹' C) = (tr A x) ⁻¹' ((tr A x⁻¹) ⁻¹' C) at h2
    rw [preimage_tr_mul, h2, h1]
  -- `S` is a finite union of finite fibres
  have hcover : S ⊆ ⋃ φ ∈ Ψ '' S, {y | y ∈ S ∧ Ψ y = φ} := by
    intro y hy
    exact Set.mem_biUnion ⟨y, hy, rfl⟩ ⟨hy, rfl⟩
  refine (himg.biUnion fun φ hφ => ?_).subset hcover
  obtain ⟨x, hx, rfl⟩ := hφ
  exact ((hH.image _).subset (hfib x hx))

end ZInQ.Contrib.CloudR2NOS.Step2B1
