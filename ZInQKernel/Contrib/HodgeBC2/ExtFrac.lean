import Mathlib

/-! # Exterior powers commute with passage to the fraction field (Mathlib-only)

Task hodge-bc2 (used by `HodgeBCInjective`, scratch/hodge-bc2/; same text as
scratch/hodge-bc2/ExtFrac.lean).

For a domain `R` with fraction field `K` and an `R`-module `M` that is a `K`-vector space
(compatibly), `K ⊗_R ⋀^n_R M ≅ ⋀^n_K M` (`extFracEquiv`), `1 ⊗ ιMulti_R v ↔ ιMulti_K v`.
Hence a `K`-basis `b` of `M` gives the `K`-basis `1 ⊗ ιMulti_family R n b` of `K ⊗_R ⋀^n_R M`
(`extFracBasis`). -/

namespace ZInQ.HodgeBC2

open TensorProduct

variable {R K M : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower R K M] (n : ℕ)

/-- `v ↦ 1 ⊗ ιMulti_R v`, `R`-multilinear. -/
noncomputable def extFracAltR : M [⋀^Fin n]→ₗ[R] K ⊗[R] ⋀[R]^n M :=
  (TensorProduct.mk R K (⋀[R]^n M) 1).compAlternatingMap (exteriorPower.ιMulti R n)

omit [IsDomain R] [IsFractionRing R K] [Module K M] [IsScalarTower R K M] in
theorem extFracAltR_apply (v : Fin n → M) :
    extFracAltR (K := K) n v = (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n v := rfl

include R in
/-- `K`-homogeneity of an `R`-linear map into a `K`-module, from that of its restriction to `R`. -/
theorem smul_eq_of_frac {N P : Type*} [AddCommGroup N] [Module R N] [Module K N]
    [IsScalarTower R K N] [AddCommGroup P] [Module R P] [Module K P] [IsScalarTower R K P]
    (F : N → P) (hF : ∀ (r : R) x, F (r • x) = r • F x) (c : K) (x : N) :
    F (c • x) = c • F x := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
  have hs : (algebraMap R K (s : R)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have key : (s : R) • F (IsLocalization.mk' K a s • x) = (a : R) • F x := by
    rw [← hF, ← algebraMap_smul K, smul_smul, IsLocalization.mk'_spec', algebraMap_smul, hF]
  have key' : algebraMap R K (s : R) • F (IsLocalization.mk' K a s • x) =
      algebraMap R K (s : R) • (IsLocalization.mk' K a s • F x) := by
    rw [algebraMap_smul, key, smul_smul, IsLocalization.mk'_spec', algebraMap_smul]
  exact smul_right_injective P hs key'

/-- `v ↦ 1 ⊗ ιMulti_R v` is `K`-multilinear. -/
noncomputable def extFracAlt : M [⋀^Fin n]→ₗ[K] K ⊗[R] ⋀[R]^n M where
  toFun v := (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n v
  map_update_add' v i x y := (extFracAltR (K := K) n).map_update_add v i x y
  map_update_smul' v i c x := by
    classical
    have := smul_eq_of_frac (R := R) (K := K)
      (fun y : M => (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n (Function.update v i y))
      (fun r y => (extFracAltR (K := K) n).map_update_smul v i r y) c x
    convert this using 2
  map_eq_zero_of_eq' v i j h hij := (extFracAltR (K := K) n).map_eq_zero_of_eq v h hij

/-- `⋀^n_K M → K ⊗_R ⋀^n_R M`. -/
noncomputable def extFracTo : ⋀[K]^n M →ₗ[K] K ⊗[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv (extFracAlt (R := R) n)

theorem extFracTo_ιMulti (v : Fin n → M) :
    extFracTo (R := R) (K := K) n (exteriorPower.ιMulti K n v) =
      (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-- `⋀^n_R M → ⋀^n_K M`, induced by `ιMulti_K`. -/
noncomputable def extFracJ : ⋀[R]^n M →ₗ[R] ⋀[K]^n M :=
  exteriorPower.alternatingMapLinearEquiv
    { ((exteriorPower.ιMulti K n (M := M)).toMultilinearMap.restrictScalars R) with
      map_eq_zero_of_eq' := fun v _ _ h hij => (exteriorPower.ιMulti K n).map_eq_zero_of_eq v h hij }

/-- `K ⊗_R ⋀^n_R M → ⋀^n_K M`. -/
noncomputable def extFracFrom : K ⊗[R] ⋀[R]^n M →ₗ[K] ⋀[K]^n M :=
  (extFracJ (R := R) (K := K) n).liftBaseChange K

theorem extFracFrom_tmul (c : K) (v : Fin n → M) :
    extFracFrom (R := R) (K := K) n (c ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      c • exteriorPower.ιMulti K n v := by
  rw [extFracFrom, LinearMap.liftBaseChange_tmul]
  congr 1
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ v

/-- **`K ⊗_R ⋀^n_R M ≅ ⋀^n_K M`.** -/
noncomputable def extFracEquiv : ⋀[K]^n M ≃ₗ[K] K ⊗[R] ⋀[R]^n M :=
  LinearEquiv.ofLinearMap (extFracTo (R := R) n) (extFracFrom (R := R) n)
    (by
      apply TensorProduct.AlgebraTensorModule.curry_injective
      apply LinearMap.ext_ring
      apply exteriorPower.linearMap_ext
      ext v
      simp only [AlternatingMap.compLinearMap_apply, LinearMap.compAlternatingMap_apply,
        TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.restrictScalars_apply, LinearMap.id_apply,
        TensorProduct.curry_apply]
      rw [extFracFrom_tmul, one_smul, extFracTo_ιMulti])
    (by
      apply exteriorPower.linearMap_ext
      ext v
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.id_apply]
      rw [extFracTo_ιMulti, extFracFrom_tmul, one_smul])

theorem extFracEquiv_ιMulti (v : Fin n → M) :
    extFracEquiv (R := R) (K := K) n (exteriorPower.ιMulti K n v) =
      (1 : K) ⊗ₜ[R] exteriorPower.ιMulti R n v :=
  extFracTo_ιMulti n v

/-- **The basis `1 ⊗ ιMulti_family R n b` of `K ⊗_R ⋀^n_R M`** for a `K`-basis `b` of `M`. -/
noncomputable def extFracBasis {I : Type*} [LinearOrder I] (b : Module.Basis I K M) :
    Module.Basis (Set.powersetCard I n) K (K ⊗[R] ⋀[R]^n M) :=
  (b.exteriorPower n).map (extFracEquiv (R := R) n)

theorem extFracBasis_apply {I : Type*} [LinearOrder I] (b : Module.Basis I K M)
    (s : Set.powersetCard I n) :
    extFracBasis (R := R) n b s = (1 : K) ⊗ₜ[R] exteriorPower.ιMulti_family R n b s := by
  rw [extFracBasis, Module.Basis.map_apply, exteriorPower.basis_apply]
  exact extFracEquiv_ιMulti n _

end ZInQ.HodgeBC2
