import ZInQKernel.Contrib.CloudR2Poincare.L2.TildeConeComparison
import ZInQKernel.Contrib.CloudR2Poincare.L6.ConeSemicontinuity
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# True raw finite-free modules give actual finite-free tilde-cone terms

Free and finite are literal module properties of the ORIGINAL P.X n and
D.X n. Their actual finite bases yield native tilde/free-sheaf isomorphisms;
L6's proved cone-term and semicontinuity suppliers then apply unchanged.
No rank/model geometry, residue-flatness or cone nonnegativity is supplied.
This contains no semantic Cech face square or native-H face comparison.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry HomologicalComplex

namespace ZInQ.Contrib.CloudR2Poincare.L2

/-- An ORIGINAL free finite raw module has a genuine finite-free native tilde
sheaf. The finite basis is taken from true freeness, not from fibre ranks. -/
theorem nativeTilde_freeFinite (S : Type u) [CommRing S]
    (M : ModuleCat.{u} S) [Module.Free S M] [Module.Finite S M] :
    ∃ r : ℕ, Nonempty ((tilde.functor (.of S)).obj M ≅
      SheafOfModules.free (R := (Spec (.of S)).ringCatSheaf) (ULift.{u} (Fin r))) := by
  classical
  let I := Module.Free.ChooseBasisIndex S M
  let r := Fintype.card I
  let e : I ≃ ULift.{u} (Fin r) := (Fintype.equivFin I).trans Equiv.ulift.symm
  let b := (Module.Free.chooseBasis S M).reindex e
  let em : M ≅ ModuleCat.of S (ULift.{u} (Fin r) →₀ S) := b.repr.toModuleIso
  exact ⟨r, ⟨(tilde.functor (.of S)).mapIso em ≪≫ tildeFinsupp (ULift.{u} (Fin r))⟩⟩

/-- Actual termwise Free+Finite on the raw complex supplies the literal
finite-free SHEAF terms required by L6's semicontinuity API. -/
theorem nativeTildeCochain_freeFiniteTerms (S : Type u) [CommRing S]
    (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (hP : ∀ n, Module.Free S (P.X n) ∧ Module.Finite S (P.X n)) :
    ∀ n, ∃ r : ℕ, Nonempty (((nativeTildeCochainFunctor (.of S)).obj P).X n ≅
      SheafOfModules.free (R := (Spec (.of S)).ringCatSheaf) (ULift.{u} (Fin r))) := by
  intro n
  letI : Module.Free S (P.X n) := (hP n).1
  letI : Module.Finite S (P.X n) := (hP n).2
  exact nativeTilde_freeFinite S (P.X n)

/-- The ACTUAL cone of tilde Phi has finite-free sheaf terms, including degree
-1. L6's cone-biproduct supplier is reused, not duplicated or assumed. -/
theorem nativeTildeCone_freeFiniteTerms (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D)
    (hP : ∀ n, Module.Free S (P.X n) ∧ Module.Finite S (P.X n))
    (hD : ∀ n, Module.Free S (D.X n) ∧ Module.Finite S (D.X n)) :
    ∀ n, ∃ r : ℕ, Nonempty ((CochainComplex.mappingCone ((nativeTildeCochainFunctor (.of S)).map Φ)).X n ≅
      SheafOfModules.free (R := (Spec (.of S)).ringCatSheaf) (ULift.{u} (Fin r))) :=
  L6.finiteFree_mappingCone_terms
    ((nativeTildeCochainFunctor (.of S)).obj P) ((nativeTildeCochainFunctor (.of S)).obj D)
    ((nativeTildeCochainFunctor (.of S)).map Φ)
    (nativeTildeCochain_freeFiniteTerms S P hP) (nativeTildeCochain_freeFiniteTerms S D hD)

/-- ORIGINAL scalar-cone fibre homology is finite from genuine free finite
raw terms. The exact canonical field-homology comparison is used. -/
theorem nativeTildeCone_finite_fibreHomology (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D)
    (hP : ∀ n, Module.Free S (P.X n) ∧ Module.Finite S (P.X n))
    (hD : ∀ n, Module.Free S (D.X n) ∧ Module.Finite S (D.X n))
    (s : Spec (.of S)) (q : ℤ) :
    Module.Finite ((Spec (.of S)).residueField s)
      ((CochainComplex.mappingCone ((nativeResidueCochainFunctor S s).map Φ)).homology q) := by
  letI : Module.Finite ((Spec (.of S)).residueField s)
      ((moduleSpecΓFunctor (R := (Spec (.of S)).residueField s)).obj
        ((((Scheme.Modules.pullback ((Spec (.of S)).fromSpecResidueField s)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mappingCone ((nativeTildeCochainFunctor (.of S)).map Φ))).homology q)) :=
    Scheme.Modules.finite_moduleSpecΓFunctor_obj_homology_pullback
      (nativeTildeCone_freeFiniteTerms S P D Φ hP hD)
      (Field.toIsField ((Spec (.of S)).residueField s))
      ((Spec (.of S)).fromSpecResidueField s) q
  exact Module.Finite.equiv (nativeTildeCone_fibreHomologyIso S P D Φ s q).toLinearEquiv.symm

/-- Exact application of L6's CERTIFIED sheaf-cone neighborhood bound to
ORIGINAL raw scalar-cone ranks, with the actual beta_s at every point. -/
theorem nativeTildeCone_exists_open_finrankHZero_le (S : Type u) [CommRing S]
    (P D : CochainComplex (ModuleCat.{u} S) ℤ) (Φ : P ⟶ D)
    (hP : ∀ n, Module.Free S (P.X n) ∧ Module.Finite S (P.X n))
    (hD : ∀ n, Module.Free S (D.X n) ∧ Module.Finite S (D.X n))
    (s : Spec (.of S)) :
    ∃ V : (Spec (.of S)).Opens, s ∈ V ∧ ∀ t : Spec (.of S), t ∈ V →
      Module.finrank ((Spec (.of S)).residueField t)
          ((CochainComplex.mappingCone ((nativeResidueCochainFunctor S t).map Φ)).homology 0) ≤
        Module.finrank ((Spec (.of S)).residueField s)
          ((CochainComplex.mappingCone ((nativeResidueCochainFunctor S s).map Φ)).homology 0) := by
  obtain ⟨V, hs, hV⟩ := L6.exists_open_derivedFiberDimension_cone_le
    ((nativeTildeCochainFunctor (.of S)).obj P) ((nativeTildeCochainFunctor (.of S)).obj D)
    ((nativeTildeCochainFunctor (.of S)).map Φ)
    (nativeTildeCochain_freeFiniteTerms S P hP) (nativeTildeCochain_freeFiniteTerms S D hD) s
  refine ⟨V, hs, fun t ht => ?_⟩
  rw [nativeTildeCone_finrankHZero_eq_derivedFiberDimension,
    nativeTildeCone_finrankHZero_eq_derivedFiberDimension]
  exact hV t ht

end ZInQ.Contrib.CloudR2Poincare.L2
