import ZInQKernel.Contrib.CloudR2Poincare.L5.D1BaseChange
import ZInQKernel.Contrib.CloudR2Poincare.L5.D1HigherProjection
import ZInQKernel.Contrib.CloudR2Poincare.L5.B1FiniteCoefficients
import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedGlobalSeesaw

/-!
# D1: actual finite-free higher-direct-image coefficient objects

The base-change isomorphism carries the actual vector space N.H j; its finite
basis supplies an actual free-sheaf isomorphism. Projection then supplies the
actual N tensor free coefficient, and the lower-zero consequences are objects,
not chosen rank equations. Every intrinsic finiteH/H0/multiplicativity input
is proved or imported as an actual proof; no caller supplies one in these
AbVar-level comparisons.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules BigOperators

namespace ZInQ.Contrib.CloudR2Poincare.L5

/-- The actual finite-dimensional cohomology vector space gives the product's
higher direct image as an actual free sheaf, not merely a matching rank. -/
def nativeProductHigherDirectImageFreeIso
    {k : Type} [Field k] (B : PkgI3.AbVar k) (N : B.X.left.Modules) [N.IsInvertible] (j : ℕ) :
    letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
    (Scheme.Modules.higherDirectImage (fst B.X B.X).left j).obj
        ((Scheme.Modules.pullback (snd B.X B.X).left).obj N) ≅
      SheafOfModules.free (R := B.X.left.ringCatSheaf) (Fin (N.finrankH k j)) := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  haveI : Module.Finite k (N.H j) := native_finiteH_invertible_abVar B N j
  let V := ModuleCat.of k (N.H j)
  let coordinates : V ≅ ModuleCat.of k (Fin (N.finrankH k j) →₀ k) :=
    (Module.finBasis k (N.H j)).repr.toModuleIso
  let coefficientIso : (tilde.functor (.of k)).obj V ≅
      SheafOfModules.free (R := (Spec (.of k)).ringCatSheaf) (Fin (N.finrankH k j)) :=
    (tilde.functor (.of k)).mapIso coordinates ≪≫ tildeFinsupp (Fin (N.finrankH k j))
  exact nativeProductHigherDirectImageIso B N j ≪≫
    (Scheme.Modules.pullback B.X.hom).mapIso coefficientIso ≪≫
      Scheme.Modules.pullbackFreeIso B.X.hom _

/-- The actual degree-j direct image for F1, obtained from higher projection
and the actual base-change free coefficient. -/
def nativeTensorProductHigherDirectImageFreeIso
    {k : Type} [Field k] (B : PkgI3.AbVar k) (N : B.X.left.Modules) [N.IsInvertible] (j : ℕ) :
    letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
    (Scheme.Modules.higherDirectImage (fst B.X B.X).left j).obj
        ((Scheme.Modules.pullback (fst B.X B.X).left).obj N ⊗
          (Scheme.Modules.pullback (snd B.X B.X).left).obj N) ≅
      N ⊗ SheafOfModules.free (R := B.X.left.ringCatSheaf) (Fin (N.finrankH k j)) :=
  nativeHigherProjectionIso (fst B.X B.X).left N
    ((Scheme.Modules.pullback (snd B.X B.X).left).obj N) j ≪≫
      (tensorLeft N).mapIso (nativeProductHigherDirectImageFreeIso B N j)

/-- Finite constant coefficients have actual finite native cohomology,
transported through the actual coproduct isomorphism and native finite-H sigma
lemma. The base-field action is unchanged throughout. -/
theorem native_finiteH_tensor_free
    {k : Type} [Field k] {X : Scheme} [X.Over (Spec (.of k))]
    (N : X.Modules) [N.IsInvertible] (r q : ℕ) [Module.Finite k (N.H q)] :
    Module.Finite k ((N ⊗ SheafOfModules.free (R := X.ringCatSheaf) (Fin r)).H q) := by
  letI : HasBiproduct (fun _ : Fin r => N) := finiteModulesBiproduct _
  let e : N ⊗ SheafOfModules.free (R := X.ringCatSheaf) (Fin r) ≅ ∐ fun _ : Fin r => N :=
    tensorFiniteFreeIso N (Fin r) ≪≫ biproduct.isoCoproduct (fun _ : Fin r => N)
  exact Scheme.Modules.finite_H_of_iso (p := X ↘ Spec (.of k)) e.symm q
    (Scheme.Modules.finite_H_sigma (p := X ↘ Spec (.of k)) (fun _ : Fin r => N) q
      (fun _ => inferInstance))

/-- The actual coefficient N tensor O^r has zero H0 when N does. -/
theorem native_subsingleton_H_zero_tensor_free
    {k : Type} [Field k] (B : PkgI3.AbVar k) (N : B.X.left.Modules) [N.IsInvertible]
    (r : ℕ) (zero : Subsingleton (N.H 0)) :
    Subsingleton ((N ⊗ SheafOfModules.free (R := B.X.left.ringCatSheaf) (Fin r)).H 0) := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  letI := zero
  haveI : Module.Finite k (N.H 0) := native_finiteH_invertible_abVar B N 0
  haveI : Module.Finite k
      ((N ⊗ SheafOfModules.free (R := B.X.left.ringCatSheaf) (Fin r)).H 0) :=
    native_finiteH_tensor_free N r 0
  suffices zeroRank : Module.finrank k
      ((N ⊗ SheafOfModules.free (R := B.X.left.ringCatSheaf) (Fin r)).H 0) = 0 by
    exact Module.finrank_zero_iff.mp zeroRank
  have rank := native_finrankH_tensor_finiteFree (k := k) N (Fin r) 0
  simpa only [Fintype.card_fin, Scheme.Modules.finrankH,
    Module.finrank_zero_of_subsingleton, mul_zero] using rank

/-- H0 of the actual free coefficient on B has its literal free rank,
using the already-proved native original-field H0(O)=1. -/
theorem native_finrankH_free_zero
    {k : Type} [Field k] (B : PkgI3.AbVar k) (r : ℕ) :
    letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
    Scheme.Modules.finrankH (X := B.X.left) k
      (SheafOfModules.free (R := B.X.left.ringCatSheaf) (Fin r)) 0 = r := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  let O : B.X.left.Modules := SheafOfModules.unit B.X.left.ringCatSheaf
  let F : B.X.left.Modules := SheafOfModules.free (R := B.X.left.ringCatSheaf) (Fin r)
  haveI : Module.Finite k (O.H 0) := native_finiteH_invertible_abVar B O 0
  calc
    F.finrankH k 0 = (O ⊗ F).finrankH k 0 :=
      (Scheme.Modules.finrankH_congr k (λ_ F) 0).symm
    _ = Fintype.card (Fin r) * O.finrankH k 0 := native_finrankH_tensor_finiteFree O (Fin r) 0
    _ = r := by rw [Fintype.card_fin, native_abVar_unit_finrankH_zero B, mul_one]

/-- The old actual shear comparison specialized with the PROVED seesaw,
and the actual left-unit coefficient iso, gives F1/F2 equal native ranks. -/
theorem native_product_tensor_finrankH_eq_secondPullback
    {k : Type} [Field k] [IsAlgClosed k] (B : PkgI3.AbVar k)
    (N : B.X.left.Modules) [N.IsInvertible]
    (invariant : L3.TranslationInvariant B (Scheme.Pic.mk N)) (q : ℕ) :
    letI : (B.X ⊗ B.X).left.Over (Spec (.of k)) := ⟨(B.X ⊗ B.X).hom⟩
    ((Scheme.Modules.pullback (fst B.X B.X).left).obj N ⊗
      (Scheme.Modules.pullback (snd B.X B.X).left).obj N).finrankH k q =
        ((Scheme.Modules.pullback (snd B.X B.X).left).obj N).finrankH k q := by
  letI : (B.X ⊗ B.X).left.Over (Spec (.of k)) := ⟨(B.X ⊗ B.X).hom⟩
  let F := (Scheme.Modules.pullback (snd B.X B.X).left).obj N
  let unitIso : (Scheme.Modules.pullback (fst B.X B.X).left).obj
      (SheafOfModules.unit B.X.left.ringCatSheaf) ⊗ F ≅ F :=
    (tensorRight F).mapIso (Scheme.Modules.pullbackObjUnitIso (fst B.X B.X).left) ≪≫ λ_ F
  exact (native_product_rank_eq_of_multiplicative_pullback B N
    (mul_pullback_of_translationInvariant L1.ReducedGlobalNormalizedSeesaw_proof B N invariant) q).trans
      (Scheme.Modules.finrankH_congr k unitIso q)

end ZInQ.Contrib.CloudR2Poincare.L5
