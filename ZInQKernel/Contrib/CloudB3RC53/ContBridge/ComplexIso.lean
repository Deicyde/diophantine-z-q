import ZInQKernel.Contrib.CloudB3RC53.ContBridge.DiffCompat
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Cochains

/-!
# Homogeneous and inhomogeneous continuous cochains: the iso of complexes, all degrees (A5)

For a locally compact topological group `G` and `X : TopRep k G` whose action `G × X → X` is
jointly continuous (`hcont`):

* `contSub X hcont`: the continuous inhomogeneous cochains `C(Gⁿ, X)`, as a subcomplex (RC26's
  `SubCx`) of Mathlib's `groupCohomology.inhomogeneousCochains (repOf X)`; stability under the
  differential is deduced from (A4);
* `degEquiv X hcont n : (homogeneousCochains X).X n ≃ₗ[k] (contSub X hcont).P n`, the inverse of
  lane L2's `Inv.cochainEquiv` followed by the tautological identification; on elements it is the
  forward map `toInhom` (`degEquiv_coe`);
* `cxIso X hcont`: the isomorphism of cochain complexes of `k`-modules between Mathlib's
  homogeneous complex (topologies forgotten) and `(contSub X hcont).toCx`;
* `homologyIso X hcont n`: `continuousCohomology n X ≅ Hⁿ((contSub X hcont).toCx)` in
  `ModuleCat k` (after forgetting the topology of the left side), for **every** `n`, and its
  `k`-linear form `homologyLinearEquiv`.

All PROVED. The forgetful functor `TopModuleCat k ⥤ ModuleCat k` preserves homology (it is both a
left and a right adjoint), which is what `ShortComplex.mapHomologyIso` uses.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ContBridge

open CategoryTheory ContRepresentation
open ZInQ.Manuscript.RC.SelmerComplex (SubCx)

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace k]
  [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  (X : TopRep.{u} k G) (hcont : Continuous fun p : G × X.V => X.ρ p.1 p.2)

/-- **The continuous inhomogeneous cochains** of `X`, a subcomplex of Mathlib's inhomogeneous
cochains of the underlying representation. -/
def contSub : SubCx (groupCohomology.inhomogeneousCochains (repOf X)) where
  P n :=
    { carrier := {f | Continuous (show (Fin n → G) → X.V from f)}
      add_mem' hf hg := hf.add hg
      zero_mem' := continuous_const
      smul_mem' c _ hf := hf.const_smul c }
  d_mem n f hf := by
    have key := cochainEquiv_symm_d X hcont n (Inv.cochainEquiv hcont n ⟨f, hf⟩)
    rw [LinearEquiv.symm_apply_apply] at key
    change Continuous (show (Fin (n + 1) → G) → X.V from
      ((groupCohomology.inhomogeneousCochains (repOf X)).d n (n + 1)).hom f)
    rw [groupCohomology.inhomogeneousCochains.d_def]
    change Continuous ((inhomogeneousCochains.d (repOf X) n).hom
      ((⟨f, hf⟩ : C(Fin n → G, X.V)) : (Fin n → G) → X.V))
    rw [← key]
    exact ContinuousMap.continuous _

theorem mem_contSub {n : ℕ} (f : (groupCohomology.inhomogeneousCochains (repOf X)).X n) :
    f ∈ (contSub X hcont).P n ↔ Continuous (show (Fin n → G) → X.V from f) :=
  Iff.rfl

/-- Continuous maps `Gⁿ → X` are the degree-`n` terms of `contSub`. -/
def toP (n : ℕ) : C(Fin n → G, X.V) ≃ₗ[k] (contSub X hcont).P n where
  toFun c := ⟨(c : (Fin n → G) → X.V), c.continuous⟩
  invFun f := ⟨f.1, f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The degreewise identification** of homogeneous and continuous inhomogeneous cochains. -/
def degEquiv (n : ℕ) : (TopRep.homogeneousCochains X).X n ≃ₗ[k] (contSub X hcont).P n :=
  (Inv.cochainEquiv hcont n).symm.trans (toP X hcont n)

/-- On elements, `degEquiv` is the forward map `toInhom`. -/
theorem degEquiv_coe (n : ℕ) (F : (TopRep.homogeneousCochains X).X n) :
    (show (Fin n → G) → X.V from ((degEquiv X hcont n F : (contSub X hcont).P n) :
      (groupCohomology.inhomogeneousCochains (repOf X)).X n)) = toInhom X n F :=
  fwdMap_eq_toInhom X n F

/-- **(A5) The isomorphism of cochain complexes**, all degrees. -/
def cxIso : ((forget₂ (TopModuleCat k) (ModuleCat k)).mapHomologicalComplex _).obj
    (TopRep.homogeneousCochains X) ≅ (contSub X hcont).toCx :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (degEquiv X hcont n).toModuleIso) (by
    rintro i j (rfl : i + 1 = j)
    ext F
    change ((contSub X hcont).toCx.d i (i + 1)).hom (degEquiv X hcont i F) =
      degEquiv X hcont (i + 1) (((TopRep.homogeneousCochains X).d i (i + 1)).hom F)
    apply Subtype.ext
    refine ((contSub X hcont).toCx_d_apply i _).trans ?_
    rw [groupCohomology.inhomogeneousCochains.d_def]
    change (inhomogeneousCochains.d (repOf X) i).hom
      (show (Fin i → G) → X.V from ((degEquiv X hcont i F : (contSub X hcont).P i) :
        (groupCohomology.inhomogeneousCochains (repOf X)).X i)) =
      (show (Fin (i + 1) → G) → X.V from
        ((degEquiv X hcont (i + 1) (((TopRep.homogeneousCochains X).d i (i + 1)).hom F) :
          (contSub X hcont).P (i + 1)) : (groupCohomology.inhomogeneousCochains (repOf X)).X
            (i + 1)))
    rw [degEquiv_coe, degEquiv_coe, toInhom_d])

/-- **(A5) Continuous cohomology in every degree** is the cohomology of the continuous
inhomogeneous cochains (in `ModuleCat k`, after forgetting the topology of the left side). -/
def homologyIso (n : ℕ) :
    (forget₂ (TopModuleCat k) (ModuleCat k)).obj (continuousCohomology n X) ≅
      (contSub X hcont).toCx.homology n :=
  (((TopRep.homogeneousCochains X).sc n).mapHomologyIso
      (forget₂ (TopModuleCat k) (ModuleCat k))).symm ≪≫
    HomologicalComplex.homologyMapIso (cxIso X hcont) n

/-- The same, as a `k`-linear equivalence. -/
def homologyLinearEquiv (n : ℕ) :
    continuousCohomology n X ≃ₗ[k] (contSub X hcont).toCx.homology n :=
  (homologyIso X hcont n).toLinearEquiv

end ZInQ.Contrib.CloudB3RC53.ContBridge
