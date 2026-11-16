/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (Lean closes these implicitly at EOF in the original; no-op).
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
r2nos_namespace_dual

set_option autoImplicit false

open Polynomial
r2nos_open_dual "Polynomial"

namespace P2mGenericNoether
r2nos_namespace_dual

universe u v

section Denominators

variable {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [Algebra R C]
  {L : Type*} [Field L] [Algebra C L] [Algebra R L] [IsScalarTower R C L]
  [Algebra (FractionRing R) L] [IsScalarTower R (FractionRing R) L]

lemma exists_mul_eq_of_mem_adjoin (S : Set C) {w : L}
    (hw : w ∈ Algebra.adjoin (FractionRing R) ((algebraMap C L) '' S)) :
    ∃ r : R, r ≠ 0 ∧ ∃ c ∈ Algebra.adjoin R S, algebraMap R L r * w = algebraMap C L c := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨1, one_ne_zero, c, Algebra.subset_adjoin hc, by simp⟩
  | algebraMap κ =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) κ
    refine ⟨b, nonZeroDivisors.ne_zero hb, algebraMap R C a, Subalgebra.algebraMap_mem _ a, ?_⟩
    have hb' : algebraMap R L b ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply R (FractionRing R) L]
      exact (_root_.map_ne_zero _).mpr
        ((_root_.map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr
          (nonZeroDivisors.ne_zero hb))
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, mul_div_cancel₀ _ hb']
  | add x y _ _ ihx ihy =>
    obtain ⟨r, hr, c, hc, e⟩ := ihx
    obtain ⟨r', hr', c', hc', e'⟩ := ihy
    refine ⟨r * r', mul_ne_zero hr hr', r' • c + r • c',
      add_mem (Subalgebra.smul_mem _ hc _) (Subalgebra.smul_mem _ hc' _), ?_⟩
    simp only [map_add, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply R C L]
    rw [← e, ← e']
    ring
  | mul x y _ _ ihx ihy =>
    obtain ⟨r, hr, c, hc, e⟩ := ihx
    obtain ⟨r', hr', c', hc', e'⟩ := ihy
    refine ⟨r * r', mul_ne_zero hr hr', c * c', mul_mem hc hc', ?_⟩
    rw [map_mul, map_mul, ← e, ← e']
    ring

end Denominators

section Scaling

variable {K : Type*} [Field K] {d : ℕ}

noncomputable def scale (u : Fin d → K) : MvPolynomial (Fin d) K →ₐ[K] MvPolynomial (Fin d) K :=
  MvPolynomial.aeval fun i => MvPolynomial.C (u i) * MvPolynomial.X i

lemma scale_comp_scale_inv (u : Fin d → K) (hu : ∀ i, u i ≠ 0) :
    (scale u).comp (scale fun i => (u i)⁻¹) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [scale, AlgHom.coe_comp, Function.comp_apply, MvPolynomial.aeval_X, map_mul,
    MvPolynomial.aeval_C, AlgHom.coe_id, id_eq, MvPolynomial.algebraMap_eq]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hu i), map_one, one_mul]

lemma scale_injective (u : Fin d → K) (hu : ∀ i, u i ≠ 0) : Function.Injective (scale u) := by
  have hu' : ∀ i, (u i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hu i)
  have h := scale_comp_scale_inv (fun i => (u i)⁻¹) hu'
  simp only [inv_inv] at h
  intro a b hab
  have := congrArg (scale fun i => (u i)⁻¹) hab
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, h] at this
  simpa using this

end Scaling

section Main

variable {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
  [Algebra R C] [FaithfulSMul R C] [Algebra.FiniteType R C]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in

theorem main :
    ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C), AlgebraicIndependent R z ∧
      ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c) := by
  classical

  let K := FractionRing R
  let L := FractionRing C
  letI : Algebra K L := FractionRing.liftAlgebra R L
  haveI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  have hCL : Function.Injective (algebraMap C L) := IsFractionRing.injective C L
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := C)
  let CK : Subalgebra K L := Algebra.adjoin K ((algebraMap C L) '' (s : Set C))
  haveI : Algebra.FiniteType K CK := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact ⟨(s.image (algebraMap C L)), by simp [CK]⟩

  have hmemCK : ∀ c : C, algebraMap C L c ∈ CK := by
    intro c
    have hc : c ∈ Algebra.adjoin R (s : Set C) := by rw [hs]; exact Algebra.mem_top
    have : (Algebra.adjoin R (s : Set C)).map (IsScalarTower.toAlgHom R C L) ≤
        CK.restrictScalars R := by
      rw [AlgHom.map_adjoin]
      exact Algebra.adjoin_le (fun x hx => Algebra.subset_adjoin hx)
    exact this ⟨c, hc, rfl⟩

  obtain ⟨d, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg K CK

  have hw : ∀ i : Fin d, ∃ r : R, r ≠ 0 ∧ ∃ c ∈ Algebra.adjoin R (s : Set C),
      algebraMap R L r * (g (MvPolynomial.X i) : L) = algebraMap C L c :=
    fun i => exists_mul_eq_of_mem_adjoin (R := R) _ (g (MvPolynomial.X i)).2
  choose ρ hρ0 z _hzmem hz using hw

  have hg_aeval : ∀ p : MvPolynomial (Fin d) K,
      (g p : L) = MvPolynomial.aeval (fun i => (g (MvPolynomial.X i) : L)) p := by
    intro p
    have : (CK.val.comp g) = MvPolynomial.aeval (fun i => (g (MvPolynomial.X i) : L)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp
    exact congrArg (fun φ : MvPolynomial (Fin d) K →ₐ[K] L => φ p) this
  have hzaeval : ∀ p : MvPolynomial (Fin d) K,
      MvPolynomial.aeval (fun i => algebraMap C L (z i)) p =
        (g (scale (fun i => algebraMap R K (ρ i)) p) : L) := by
    intro p
    rw [hg_aeval]
    have : (MvPolynomial.aeval (fun i => algebraMap C L (z i)) : MvPolynomial (Fin d) K →ₐ[K] L)
        = (MvPolynomial.aeval (fun i => (g (MvPolynomial.X i) : L))).comp
          (scale fun i => algebraMap R K (ρ i)) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [MvPolynomial.aeval_X, AlgHom.coe_comp, Function.comp_apply, scale, map_mul,
        MvPolynomial.aeval_C]
      rw [← hz i, IsScalarTower.algebraMap_apply R K L]
    exact congrArg (fun φ : MvPolynomial (Fin d) K →ₐ[K] L => φ p) this
  have hρK : ∀ i, algebraMap R K (ρ i) ≠ 0 := fun i => (map_ne_zero_iff _ hRK).mpr (hρ0 i)

  have hzind : AlgebraicIndependent R z := by
    rw [AlgebraicIndependent]
    intro p q hpq
    have h1 : MvPolynomial.aeval (fun i => algebraMap C L (z i)) (MvPolynomial.map (algebraMap R K) p)
        = MvPolynomial.aeval (fun i => algebraMap C L (z i)) (MvPolynomial.map (algebraMap R K) q) := by
      rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_map_algebraMap]
      have e : ∀ t : MvPolynomial (Fin d) R, MvPolynomial.aeval (fun i => algebraMap C L (z i)) t =
          algebraMap C L (MvPolynomial.aeval z t) := by
        intro t
        rw [← MvPolynomial.aeval_algebraMap_apply]
        rfl
      rw [e, e]
      exact congrArg _ hpq
    rw [hzaeval, hzaeval] at h1
    have h2 := hginj (Subtype.ext h1)
    have h3 := scale_injective _ hρK h2
    exact MvPolynomial.map_injective _ hRK h3

  set A : Subalgebra R C := Algebra.adjoin R (Set.range z) with hA

  have hrange : ∀ p : MvPolynomial (Fin d) K,
      (g p : L) ∈ Algebra.adjoin K ((algebraMap C L) '' Set.range z) := by
    intro p
    rw [hg_aeval]
    induction p using MvPolynomial.induction_on with
    | C κ => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ κ
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      refine mul_mem hp ?_
      have : (g (MvPolynomial.X i) : L) =
          algebraMap K L (algebraMap R K (ρ i))⁻¹ * algebraMap C L (z i) := by
        rw [← hz i, IsScalarTower.algebraMap_apply R K L, ← mul_assoc, ← map_mul,
          inv_mul_cancel₀ (hρK i), map_one, one_mul]
      rw [this]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin ⟨z i, ⟨i, rfl⟩, rfl⟩)

  have hint : ∀ c : C, ∃ τ : R, τ ≠ 0 ∧ IsIntegral A (τ • c) := by
    intro c
    have hgint : g.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hgfin
    obtain ⟨P, hPm, hP⟩ := hgint ⟨algebraMap C L c, hmemCK c⟩

    let P₂ : L[X] := (P.map g.toRingHom).map (CK.val : CK →+* L)
    have hP₂m : P₂.Monic := (hPm.map _).map _
    have hP₂ : P₂.eval (algebraMap C L c) = 0 := by
      have h2 : (CK.val : CK →+* L) (P.eval₂ g.toRingHom ⟨_, hmemCK c⟩) = 0 := by
        rw [hP, map_zero]
      rw [Polynomial.hom_eval₂] at h2
      simp only [P₂, Polynomial.map_map, Polynomial.eval_map]
      exact h2

    have hcoef : ∀ j : ℕ, ∃ r : R, r ≠ 0 ∧ ∃ a ∈ A, algebraMap R L r * P₂.coeff j =
        algebraMap C L a := by
      intro j
      have hj : P₂.coeff j ∈ Algebra.adjoin K ((algebraMap C L) '' Set.range z) := by
        simp only [P₂, Polynomial.coeff_map]
        exact hrange _
      exact exists_mul_eq_of_mem_adjoin (R := R) _ hj
    choose r hr0 a haA ha using hcoef
    let τ : R := ∏ j ∈ Finset.range P₂.natDegree, r j
    have hτ0 : τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hr0 j
    refine ⟨τ, hτ0, ?_⟩

    let P₃ : L[X] := P₂.scaleRoots (algebraMap R L τ)
    have hP₃m : P₃.Monic := (Polynomial.monic_scaleRoots_iff _).mpr hP₂m
    have hP₃ : P₃.eval₂ (RingHom.id L) (algebraMap R L τ * algebraMap C L c) = 0 := by
      have h := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id L) (r := algebraMap C L c)
        (s := algebraMap R L τ) (by rw [Polynomial.eval₂_id]; exact hP₂)
      simpa using h

    have hlift : P₃ ∈ Polynomial.lifts (algebraMap A L) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro j
      simp only [P₃, Polynomial.coeff_scaleRoots]
      by_cases hj : j < P₂.natDegree
      · obtain ⟨k, hk⟩ : ∃ k, P₂.natDegree - j = k + 1 := ⟨P₂.natDegree - j - 1, by omega⟩
        have hdvd : r j ∣ τ := Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj)
        obtain ⟨τ', hτ'⟩ := hdvd
        refine ⟨⟨algebraMap R C (τ' * τ ^ k) * a j,
          mul_mem (Subalgebra.algebraMap_mem _ _) (haA j)⟩, ?_⟩
        change algebraMap C L (algebraMap R C (τ' * τ ^ k) * a j) =
          P₂.coeff j * algebraMap R L τ ^ (P₂.natDegree - j)
        rw [hk, map_mul, ← IsScalarTower.algebraMap_apply, ← ha j, pow_succ, hτ', map_mul,
          map_mul, map_pow, map_mul]
        ring
      · by_cases hj' : j = P₂.natDegree
        · subst hj'
          refine ⟨1, ?_⟩
          rw [hP₂m.coeff_natDegree, Nat.sub_self, pow_zero, one_mul, map_one]
        · refine ⟨0, ?_⟩
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, map_zero]
    obtain ⟨Q, hQmap, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hP₃m
    have hτc : IsIntegral A (algebraMap C L (τ • c)) := by
      refine ⟨Q, hQm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map, hQmap, Polynomial.eval, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply]
      exact hP₃
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A C L) hCL).mp hτc

  choose τ hτ0 hτint using hint
  let r : R := ∏ c ∈ s, τ c
  have hr0 : r ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hτ0 c
  refine ⟨r, hr0, d, z, hzind, ?_⟩
  have hAint : ∀ x : R, IsIntegral A (algebraMap R C x) := fun x =>
    (isIntegral_algebraMap (R := A) (A := C) (x := ⟨algebraMap R C x, Subalgebra.algebraMap_mem _ x⟩))

  let T : Subalgebra R C :=
    { carrier := {c | ∃ n : ℕ, IsIntegral A (r ^ n • c)}
      mul_mem' := by
        rintro a b ⟨n, ha⟩ ⟨m, hb⟩
        refine ⟨n + m, ?_⟩
        have : r ^ (n + m) • (a * b) = (r ^ n • a) * (r ^ m • b) := by
          rw [pow_add, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
        rw [this]
        exact ha.mul hb
      add_mem' := by
        rintro a b ⟨n, ha⟩ ⟨m, hb⟩
        refine ⟨n + m, ?_⟩
        have : r ^ (n + m) • (a + b) =
            algebraMap R C (r ^ m) * (r ^ n • a) + algebraMap R C (r ^ n) * (r ^ m • b) := by
          rw [pow_add, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]; ring
        rw [this]
        exact ((hAint _).mul ha).add ((hAint _).mul hb)
      algebraMap_mem' := by
        intro x
        refine ⟨0, ?_⟩
        rw [pow_zero, one_smul]
        exact hAint x }
  have hsT : (s : Set C) ⊆ T := by
    intro c hc
    refine ⟨1, ?_⟩
    obtain ⟨r', hr'⟩ : τ c ∣ r := Finset.dvd_prod_of_mem _ hc
    have : r ^ 1 • c = algebraMap R C r' * (τ c • c) := by
      rw [pow_one, hr', Algebra.smul_def, Algebra.smul_def, map_mul]; ring
    rw [this]
    exact (hAint r').mul (hτint c)
  have hT : Algebra.adjoin R (s : Set C) ≤ T := Algebra.adjoin_le hsT
  intro c
  have hc : c ∈ T := hT (by rw [hs]; exact Algebra.mem_top)
  exact hc

end Main

end P2mGenericNoether

universe u v

theorem solution
    {R : Type u} {C : Type v} [CommRing R] [IsDomain R] [CommRing C] [IsDomain C]
    [Algebra R C] [FaithfulSMul R C] [Algebra.FiniteType R C] :
    ∃ r : R, r ≠ 0 ∧ ∃ (d : ℕ) (z : Fin d → C), AlgebraicIndependent R z ∧
      ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin R (Set.range z)) (r ^ n • c) :=
  P2mGenericNoether.main

end S_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
