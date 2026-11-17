/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField/NormedField.lean
Original SHA-256: 1ac15fca1c71992dd49e4ab8a64d7eb0898669209aefb97837bc7291d0755ba9
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/NumberTheory/LocalField/NormedField.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.Analysis.Normed.Group.Ultra
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.NormalizedValuation
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open ValuativeRel Topology

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (K) in
/- The normed-field structure on a nonarchimedean local field `K` whose norm is the normalized
absolute value `‖x‖_K = q ^ (-v_K(x))`, where `q` is the cardinality of the residue field. -/
@[expose, implicit_reducible]
def normalizedNormedField : NormedField K :=
  AbsoluteValue.toNormedField
    { toFun x := normalizedAbsoluteValue K x
      map_mul' x y := by simp
      nonneg' x := by positivity
      eq_zero' x := by simp
      add_le' x y := by exact_mod_cast (normalizedAbsoluteValue K).add_le x y }

/- The norm of `normalizedNormedField K` is the normalized absolute value. -/
theorem normalizedNormedField_norm_def (x : K) :
    letI := normalizedNormedField K
    ‖x‖ = normalizedAbsoluteValue K x := (rfl)

variable (K) in
/- The topology on `K` induced by the norm of `normalizedNormedField K`. It is kept as a separate
definition because it agrees with the given topology of `K` only propositionally, by
`normalizedNormedField_topology_eq`. -/
@[expose, implicit_reducible]
def normalizedNormedFieldTopology : TopologicalSpace K :=
  (normalizedNormedField K).toUniformSpace.toTopologicalSpace

variable (K) in
/- The topology induced by the normalized absolute value is the given topology of a
nonarchimedean local field. -/
theorem normalizedNormedField_topology_eq :
    normalizedNormedFieldTopology K = ‹TopologicalSpace K› := by
  let _ := normalizedNormedField K
  refine IsTopologicalAddGroup.ext (t := normalizedNormedFieldTopology K)
    IsUniformAddGroup.isTopologicalAddGroup inferInstance ?_
  -- Compare the metric balls around `0` with the valuation balls around `0`.
  refine (Metric.nhds_basis_ball (x := (0 : K))).ext
    (IsValuativeTopology.hasBasis_nhds_zero' K) (fun ε hε => ?_) (fun γ hγ => ?_)
  · obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    have hy : ‖y‖ < 1 := by
      rw [normalizedNormedField_norm_def]
      exact_mod_cast (normalizedAbsoluteValue_lt_one_iff y).2 hy1
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hy
    refine ⟨valuation K (y ^ n), by simp [hy0], fun x hx => ?_⟩
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right] at hx ⊢
    refine lt_trans ?_ hn
    rw [← norm_pow, normalizedNormedField_norm_def, normalizedNormedField_norm_def]
    exact_mod_cast (normalizedAbsoluteValue_lt_normalizedAbsoluteValue_iff x (y ^ n)).2 hx
  · obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective γ
    refine ⟨‖y‖, by simpa using hγ, fun x hx => ?_⟩
    simp only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right,
      normalizedNormedField_norm_def] at hx ⊢
    exact (normalizedAbsoluteValue_lt_normalizedAbsoluteValue_iff x y).1 (mod_cast hx)

variable (K) in
/- The normalized absolute value is ultrametric. -/
theorem normalizedNormedField_isUltrametricDist :
    letI := normalizedNormedField K
    IsUltrametricDist K := by
  let _ := normalizedNormedField K
  refine IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => ?_
  simp only [normalizedNormedField_norm_def]
  exact_mod_cast isNonarchimedean_normalizedAbsoluteValue x y

variable (K) in
/- A nonarchimedean local field is complete for its normalized absolute value. -/
theorem normalizedNormedField_completeSpace :
    letI := normalizedNormedField K
    CompleteSpace K := by
  let _ := normalizedNormedField K
  have h : @IsNonarchimedeanLocalField K _ _ (normalizedNormedFieldTopology K) := by
    rw [normalizedNormedField_topology_eq]
    infer_instance
  infer_instance

variable (K) in
/- The normalized absolute value of a nonarchimedean local field `K`, as a nontrivially normed
field structure on `K`. Its underlying normed field is `normalizedNormedField K`. -/
@[expose, implicit_reducible]
def normalizedNontriviallyNormedField : NontriviallyNormedField K where
  __ := normalizedNormedField K
  non_trivial := by
    let _ := normalizedNormedField K
    obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    refine ⟨y⁻¹, ?_⟩
    rw [norm_inv, one_lt_inv₀ (norm_pos_iff.2 hy0), normalizedNormedField_norm_def]
    exact_mod_cast (normalizedAbsoluteValue_lt_one_iff y).2 hy1

end TauCeti
