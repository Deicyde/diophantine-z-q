/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.lean
  Source sha256  : e91195ee9c7f5732474e52fd2c993bf3bb7b945e176ae536bd5ced02c96ee6e7
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale
r2nos_namespace_dual

set_option autoImplicit false

universe u

open TensorProduct
r2nos_open_dual "TensorProduct"

namespace EtaleH1GC7
r2nos_namespace_dual

open Polynomial RingTheory.Sequence
r2nos_open_dual "Polynomial RingTheory.Sequence"

theorem isWeaklyRegular_pair {B : Type*} [CommRing B] (f g : B) (hf : f ∈ nonZeroDivisors B) :
    IsWeaklyRegular B[X] [C g * X - 1, C f] := by
  classical
  refine IsWeaklyRegular.cons ?_ ((isWeaklyRegular_singleton_iff _ _).mpr ?_)
  ·
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro h hh
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at hh
    have key : ∀ n, h.coeff n = 0 := by
      intro n
      induction n with
      | zero => rw [← hh, mul_assoc, coeff_C_mul, coeff_X_mul_zero, mul_zero]
      | succ n ih => rw [← hh, mul_assoc, coeff_C_mul, coeff_X_mul, ih, mul_zero]
    ext n
    rw [key, coeff_zero]
  ·
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro x hx
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    rw [smul_eq_mul, smul_eq_mul] at hy
    haveI := IsLocalization.adjoin_inv g
    have hfA : algebraMap B (AdjoinRoot (C g * X - 1)) f ∈ nonZeroDivisors (AdjoinRoot (C g * X - 1)) :=
      IsLocalization.map_nonZeroDivisors_le (Submonoid.powers g) (AdjoinRoot (C g * X - 1)) ⟨f, hf, rfl⟩
    have h0 : AdjoinRoot.mk (C g * X - 1) (C f * x) = 0 := by
      rw [← hy, AdjoinRoot.mk_eq_zero]
      exact dvd_mul_right _ y
    rw [map_mul, AdjoinRoot.mk_C] at h0
    rw [AdjoinRoot.algebraMap_eq] at hfA
    have hx0 : AdjoinRoot.mk (C g * X - 1) x = 0 := (mem_nonZeroDivisors_iff_left.mp hfA) _ h0
    obtain ⟨z, rfl⟩ := AdjoinRoot.mk_eq_zero.mp hx0
    exact Submodule.smul_mem_pointwise_smul z (C g * X - 1) ⊤ trivial

theorem isWeaklyRegular_pair_mv {D : Type*} [CommRing D] (f g : D[X]) (hf : f.Monic) :
    IsWeaklyRegular (MvPolynomial (Fin 2) D)
      [Bivariate.equivMvPolynomial D (C g * X - 1), Bivariate.equivMvPolynomial D (C f)] := by
  have h := isWeaklyRegular_pair f g hf.mem_nonZeroDivisors
  refine ((Bivariate.equivMvPolynomial D).toRingEquiv.toAddEquiv.isWeaklyRegular_congr ?_).mp h
  refine List.Forall₂.cons (fun x => ?_) (List.Forall₂.cons (fun x => ?_) List.Forall₂.nil)
  · change Bivariate.equivMvPolynomial D ((C g * X - 1) * x) = _ * Bivariate.equivMvPolynomial D x
    rw [map_mul]
  · change Bivariate.equivMvPolynomial D (C f * x) = _ * Bivariate.equivMvPolynomial D x
    rw [map_mul]

end EtaleH1GC7

open EtaleH1GC7 in
r2nos_open_dual "EtaleH1GC7" in
theorem solution (R D T : Type u)
    [CommRing R] [CommRing D] [CommRing T] [Algebra R D] [Algebra D T] [Algebra R T] [IsScalarTower R D T]
    [Algebra.Etale D T] :
    Function.Injective ((Algebra.H1Cotangent.map R R D T).liftBaseChange T) := by
  classical

  let s : Set T := {t | Algebra.IsStandardEtale D (Localization.Away t)}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hm.isPrime
    obtain ⟨t, htm, ht⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := D) m
    exact htm (hle (Ideal.subset_span ht))
  refine Algebra.injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular
    s hs ?_
  intro t ht
  haveI : Algebra.IsStandardEtale D (Localization.Away t) := ht
  obtain ⟨Pr⟩ := (Algebra.IsStandardEtale.nonempty_standardEtalePresentation :
    Nonempty (StandardEtalePresentation D (Localization.Away t)))
  let Q := Pr.toPresentation
  let F : List (MvPolynomial (Fin 2) D) :=
    [Polynomial.Bivariate.equivMvPolynomial D (Polynomial.C Pr.g * Polynomial.X - 1),
      Polynomial.Bivariate.equivMvPolynomial D (Polynomial.C Pr.f)]
  have hF : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin 2) D) F := isWeaklyRegular_pair_mv Pr.f Pr.g Pr.monic_f
  refine ⟨Fin 2, Q.val, F, ?_, ?_, ?_⟩
  ·
    intro y
    obtain ⟨x, hx⟩ := Q.algebraMap_surjective y
    exact ⟨x, by rw [← Q.algebraMap_apply]; exact hx⟩
  ·
    rw [← Q.ker_eq_ker_aeval_val, ← Q.span_range_relation_eq_ker]
    have hrel : Q.relation = ![Polynomial.Bivariate.equivMvPolynomial D (Polynomial.C Pr.f),
        Polynomial.Bivariate.equivMvPolynomial D (Polynomial.X * Polynomial.C Pr.g - 1)] := rfl
    rw [hrel, Ideal.ofList, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, mul_comm (Polynomial.X) (Polynomial.C Pr.g)]
    congr 1
    ext p
    simp only [F, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, List.mem_cons,
      List.not_mem_nil, or_false]
    tauto
  ·
    intro m _ hm
    haveI : Module.Flat (MvPolynomial (Fin 2) D) (Localization.AtPrime m) :=
      IsLocalization.flat (Localization.AtPrime m) m.primeCompl
    have h2 := hF.isWeaklyRegular_lTensor (M₂ := Localization.AtPrime m)
    have h3 := ((TensorProduct.rid (MvPolynomial (Fin 2) D) (Localization.AtPrime m)).isWeaklyRegular_congr
      F).mp h2
    exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (Localization.AtPrime m)
      (Localization.AtPrime m) F).mpr h3
end S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
