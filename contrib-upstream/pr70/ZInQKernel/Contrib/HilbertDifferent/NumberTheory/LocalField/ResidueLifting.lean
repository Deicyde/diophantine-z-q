/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField/ResidueLifting.lean
Original SHA-256: 9bc51187ed159b1dc5bb9c528e49c7140da09e656a9bf97a8a82fae3a3cf5d7c
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.FiniteExtension.Basic
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.InertiaDegree
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.PrimitiveElement
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DiscreteValuationRing.Monogenic

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
The native Henselian adapter retains the construction in
TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/NumberTheory/LocalField/Henselian.lean, TauCeti/RingTheory/Henselian/Basic.lean,
and TauCeti/NumberTheory/LocalField/FiniteExtension/Basic.lean.
Full license: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/
/- Modified: the residue lift and adjoin construction are adapted to the native
ValuativeRel local-field and residue-algebra interfaces. Source: NYLL
fe40c03df1b2b195053fdd63305571d97c73ce48,
Nyll/ValuedFieldTheory/LocalField/Unramified/ResidueLifting.lean.
Full license and entire attribution chain: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace the adapted declarations by direct use when this project's pinned Mathlib
supplies equivalent declarations. -/

noncomputable section
open ValuativeRel IsLocalRing IsLocalRing.ResidueField Polynomial

namespace TauCeti

section FiniteExtensionStructures

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (M : Type*) [Field M] [Algebra K M] [Module.Finite K M]

/-- The topology on a finite extension `M` of a nonarchimedean local field `K` induced by the
norm of `finiteExtensionNormedField K M`. -/
@[expose, implicit_reducible]
def finiteExtensionNormedFieldTopology : TopologicalSpace M :=
  (finiteExtensionNormedField K M).toUniformSpace.toTopologicalSpace

/-- The norm of `finiteExtensionNormedField K M` is the spectral norm of `M/K`. -/
theorem finiteExtensionNormedField_norm_def (x : M) :
    letI := finiteExtensionNormedField K M
    letI := normalizedNontriviallyNormedField K
    ‖x‖ = spectralNorm K M x := (rfl)

variable {K M} in
/-- The norm of `finiteExtensionNormedField K M` extends the normalized absolute value of `K`. -/
@[simp]
theorem finiteExtensionNormedField_norm_algebraMap (x : K) :
    letI := finiteExtensionNormedField K M
    ‖algebraMap K M x‖ = normalizedAbsoluteValue K x := by
  let _ := normalizedNontriviallyNormedField K
  rw [finiteExtensionNormedField_norm_def, spectralNorm_extends]
  exact normalizedNormedField_norm_def x

/-- The norm of `finiteExtensionNormedField K M` is ultrametric. -/
theorem finiteExtensionNormedField_isUltrametricDist :
    letI := finiteExtensionNormedField K M
    IsUltrametricDist M := by
  let _ := finiteExtensionNormedField K M
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_isUltrametricDist K
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm

/-- The valuative relation on a finite extension `M` of a nonarchimedean local field `K` defined
by the norm of `finiteExtensionNormedField K M`: `x ≤ᵥ y` exactly when `‖x‖ ≤ ‖y‖`. -/
@[expose, implicit_reducible]
def finiteExtensionValuativeRel : ValuativeRel M :=
  letI := finiteExtensionNormedField K M
  haveI := finiteExtensionNormedField_isUltrametricDist K M
  ValuativeRel.ofValuation (NormedField.valuation (K := M))

variable {K M} in
/-- The relation `finiteExtensionValuativeRel K M` compares norms. -/
@[simp]
theorem finiteExtensionValuativeRel_vle_iff (x y : M) :
    letI := finiteExtensionValuativeRel K M
    letI := finiteExtensionNormedField K M
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ :=
  -- `ValuativeRel.ofValuation` defines `x ≤ᵥ y` as `‖x‖₊ ≤ ‖y‖₊` for `NormedField.valuation`.
  NNReal.coe_le_coe

/-- The valuative relation `finiteExtensionValuativeRel K M` extends the valuative relation
of `K`. -/
theorem finiteExtension_valuativeExtension :
    letI := finiteExtensionValuativeRel K M
    ValuativeExtension K M := by
  let _ := finiteExtensionValuativeRel K M
  refine ⟨fun a b => ?_⟩
  rw [finiteExtensionValuativeRel_vle_iff, finiteExtensionNormedField_norm_algebraMap,
    finiteExtensionNormedField_norm_algebraMap, NNRat.cast_le,
    normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff, (valuation K).vle_iff_le]

/-- The norm topology `finiteExtensionNormedFieldTopology K M` is the valuative topology of
`finiteExtensionValuativeRel K M`. -/
theorem finiteExtension_isValuativeTopology :
    @IsValuativeTopology M _ (finiteExtensionValuativeRel K M)
      (finiteExtensionNormedFieldTopology K M) := by
  let _ := finiteExtensionNormedField K M
  let _ := finiteExtensionValuativeRel K M
  have := finiteExtensionNormedField_isUltrametricDist K M
  have := Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle NormedField.valuation
    fun {s} => NormedField.toValued.is_topological_valuation s

/-- A finite extension `M` of a nonarchimedean local field `K`, with the topology and valuative
relation of the spectral norm, is a nonarchimedean local field. -/
theorem finiteExtension_isNonarchimedeanLocalField :
    @IsNonarchimedeanLocalField M _ (finiteExtensionValuativeRel K M)
      (finiteExtensionNormedFieldTopology K M) := by
  let _ := finiteExtensionNormedField K M
  let _ := finiteExtensionValuativeRel K M
  let _ := normalizedNontriviallyNormedField K
  have := normalizedNormedField_isUltrametricDist K
  have := normalizedNormedField_completeSpace K
  have := finiteExtensionNormedField_isUltrametricDist K M
  have := finiteExtension_isValuativeTopology K M
  -- Local compactness: `K` is locally compact for its norm, so the finite-dimensional normed
  -- `K`-space `M` is proper.
  have : @LocallyCompactSpace K (normalizedNormedFieldTopology K) := by
    rw [normalizedNormedField_topology_eq]
    infer_instance
  let _ := spectralNorm.normedSpace K M
  have : ProperSpace M := FiniteDimensional.proper K M
  -- Nontriviality: an element of `K` of valuation strictly between `0` and `1` keeps its
  -- absolute value in `M`.
  have : ValuativeRel.IsNontrivial M := by
    have := Valuation.Compatible.ofValuation (NormedField.valuation (K := M))
    refine (isNontrivial_iff_isNontrivial NormedField.valuation).2 ?_
    obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    refine ⟨⟨algebraMap K M y, by simpa using hy0, fun h => ?_⟩⟩
    have h' : ‖algebraMap K M y‖ = 1 := by simpa using congrArg NNReal.toReal h
    rw [finiteExtensionNormedField_norm_algebraMap] at h'
    exact ((normalizedAbsoluteValue_lt_one_iff y).2 hy1).ne (mod_cast h')
  exact { }


variable {K M}

/-- **Uniqueness of the extended valuation.** Any two valuations on a finite extension `M` of a
nonarchimedean local field `K` which restrict to the valuation class of `K` are equivalent. -/
theorem finiteExtensionValuation_isEquiv {Γ₁ Γ₂ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    [LinearOrderedCommGroupWithZero Γ₂] {w₁ : Valuation M Γ₁} {w₂ : Valuation M Γ₂}
    (h₁ : (w₁.comap (algebraMap K M)).IsEquiv (valuation K))
    (h₂ : (w₂.comap (algebraMap K M)).IsEquiv (valuation K)) :
    w₁.IsEquiv w₂ := fun x y =>
  (finiteExtensionNormedField_norm_le_norm_iff h₁ x y).symm.trans
    (finiteExtensionNormedField_norm_le_norm_iff h₂ x y)


/-- **Embeddings respect the extended valuations.** A `K`-algebra map `ι : M →ₐ[K] N` from a
finite extension `M` of a nonarchimedean local field `K` to a field `N`, for valuative relations
on `M` and on `N` both extending that of `K`, makes `N` a valuative extension of `M` through
`ι.toAlgebra`. -/
theorem _root_.AlgHom.valuativeExtension {N : Type*} [Field N] [ValuativeRel N] [Algebra K N]
    [ValuativeExtension K N] [ValuativeRel M] [ValuativeExtension K M] (ι : M →ₐ[K] N) :
    letI := ι.toAlgebra
    ValuativeExtension M N := by
  let _ := ι.toAlgebra
  -- The valuation of `N` pulled back along `ι` extends the valuation class of `K`, so by
  -- uniqueness it is the valuation of `M`.
  have hN := ValuativeRel.isEquiv ((valuation N).comap (algebraMap K N)) (valuation K)
  rw [← ι.comp_algebraMap, Valuation.comap_comp] at hN
  have h := finiteExtensionValuation_isEquiv hN
    (ValuativeRel.isEquiv ((valuation M).comap (algebraMap K M)) (valuation K))
  exact ⟨fun a b ↦ (valuation N).vle_iff_le.trans ((h a b).trans (valuation M).vle_iff_le.symm)⟩


end FiniteExtensionStructures

private theorem integer_henselian (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : HenselianLocalRing 𝒪[K] := by
  let _ := IsTopologicalAddGroup.rightUniformSpace K
  let _ := isUniformAddGroup_of_addCommGroup (G := K)
  exact {
    is_henselian := fun f hf a ha hu =>
      HenselianRing.is_henselian (I := 𝓂[K]) f hf a ha (hu.map _) }

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

private theorem lift_separable_residue (α : 𝓀[L]) (hα : IsSeparable 𝓀[K] α) :
    ∃ F : 𝒪[K][X], F.Monic ∧
      F.map (residue 𝒪[K]) = minpoly 𝓀[K] α ∧
      F.natDegree = (minpoly 𝓀[K] α).natDegree ∧
      ∃ β : 𝒪[L], aeval β F = 0 ∧ residue 𝒪[L] β = α := by
  classical
  letI := integer_henselian L
  have hlifts : minpoly 𝓀[K] α ∈ Polynomial.lifts (residue 𝒪[K]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact residue_surjective _
  obtain ⟨F, hFmap, hFdeg, hFmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts (minpoly.monic hα.isIntegral)
  let FL := F.map (algebraMap 𝒪[K] 𝒪[L])
  have hFL : FL.map (residue 𝒪[L]) =
      (minpoly 𝓀[K] α).map (algebraMap 𝓀[K] 𝓀[L]) := by
    calc
      FL.map (residue 𝒪[L]) =
          (F.map (residue 𝒪[K])).map (algebraMap 𝓀[K] 𝓀[L]) := by
        simp only [FL, Polynomial.map_map]
        congr 1
      _ = _ := by rw [hFmap]
  have hbarRoot : ((minpoly 𝓀[K] α).map (algebraMap 𝓀[K] 𝓀[L])).eval α = 0 := by
    simpa only [aeval_def, eval₂_eq_eval_map] using (minpoly.aeval 𝓀[K] α)
  have hroot : aeval α FL = 0 := by
    simpa only [aeval_def, eval₂_eq_eval_map, ResidueField.algebraMap_eq, hFL] using hbarRoot
  have hderiv : aeval α FL.derivative ≠ 0 := by
    rw [aeval_def, eval₂_eq_eval_map, ← derivative_map, ResidueField.algebraMap_eq, hFL]
    have hsep : ((minpoly 𝓀[K] α).map (algebraMap 𝓀[K] 𝓀[L])).Separable :=
      Polynomial.Separable.map hα
    exact hsep.eval₂_derivative_ne_zero (RingHom.id 𝓀[L]) (by
      simpa only [eval₂_id] using hbarRoot)
  have hlift : ∀ f : 𝒪[L][X], f.Monic → ∀ a : 𝓀[L],
      aeval a f = 0 → aeval a f.derivative ≠ 0 →
        ∃ b : 𝒪[L], f.IsRoot b ∧ residue 𝒪[L] b = a :=
    ((HenselianLocalRing.TFAE 𝒪[L]).out 1 2).mp (integer_henselian L)
  obtain ⟨β, hβ, hβres⟩ :=
    hlift FL (hFmonic.map _) α hroot hderiv
  refine ⟨F, hFmonic, hFmap, hFdeg, β, ?_, hβres⟩
  simpa only [FL, IsRoot, eval_map_algebraMap] using hβ

theorem uniformizer_presentation (hres : Function.Bijective (algebraMap 𝓀[K] 𝓀[L]))
    (π : 𝒪[L]) (hπ : Irreducible π) :
    Algebra.adjoin 𝒪[K] {π} = ⊤ ∧
      (minpoly 𝒪[K] π).natDegree = ramificationIndex K L := by
  letI : Module.Finite 𝒪[K] 𝒪[L] := integerRingModuleFinite K L
  have hgen : Algebra.adjoin 𝒪[K] {π} = ⊤ := by
    apply TauCeti.IsLocalRing.adjoin_eq_top_of_span_eval_eq_maximalIdeal (g := X)
    · rw [eq_top_iff]
      rintro x -
      obtain ⟨y, rfl⟩ := hres.2 x
      exact Subalgebra.algebraMap_mem _ y
    · simpa using hπ.maximalIdeal_eq.symm
  have hint : IsIntegral 𝒪[K] π := Algebra.IsIntegral.isIntegral π
  let pb := PowerBasis.ofAdjoinEqTop' hint hgen
  have hf : inertiaDegree K L = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr hres
  refine ⟨hgen, ?_⟩
  calc
    (minpoly 𝒪[K] π).natDegree = pb.dim := rfl
    _ = Module.finrank 𝒪[K] 𝒪[L] := pb.finrank.symm
    _ = Module.finrank K L := finrank_integerRing K L
    _ = ramificationIndex K L := by
      simpa only [hf, mul_one] using (ramificationIndex_mul_inertiaDegree K L).symm

/-- A finite extension contains a finite intermediate local field with ramification index one
and a bijective canonical map to the ambient residue field. -/
theorem exists_unramified_residue_subextension [Module.Finite K L] :
    ∃ M : IntermediateField K L,
      letI := finiteExtensionValuativeRel K M
      letI := finiteExtensionNormedFieldTopology K M
      letI := finiteExtension_isNonarchimedeanLocalField K M
      letI := finiteExtension_valuativeExtension K M
      letI : ValuativeExtension M L := M.val.valuativeExtension
      ramificationIndex K M = 1 ∧
        Function.Bijective (algebraMap 𝓀[M] 𝓀[L]) ∧
        ∀ π : 𝒪[L], Irreducible π →
          Algebra.adjoin 𝒪[M] {π} = ⊤ ∧
            (minpoly 𝒪[M] π).natDegree = ramificationIndex M L := by
  classical
  obtain ⟨α, hαgen⟩ := Field.exists_primitive_element_of_finite_top 𝓀[K] 𝓀[L]
  obtain ⟨F, hFmonic, hFmap, hFdeg, β, hβroot, hβres⟩ :=
    lift_separable_residue K L α (Algebra.IsSeparable.isSeparable 𝓀[K] α)
  let M : IntermediateField K L := IntermediateField.adjoin K {(β : L)}
  refine ⟨M, ?_⟩
  letI := finiteExtensionValuativeRel K M
  letI := finiteExtensionNormedFieldTopology K M
  letI := finiteExtension_isNonarchimedeanLocalField K M
  letI := finiteExtension_valuativeExtension K M
  letI : ValuativeExtension M L := M.val.valuativeExtension
  letI : IsScalarTower 𝒪[K] 𝒪[M] 𝒪[L] :=
    IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
      simp only [coe_algebraMap_integerRing]
      exact IsScalarTower.algebraMap_apply K M L (x : K))
  let βM : M := ⟨(β : L), IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
  have hβL : aeval (β : L) F = 0 := by
    change aeval (algebraMap 𝒪[L] L β) F = 0
    rw [aeval_algebraMap_apply, hβroot, map_zero]
  have hrootM : aeval βM F = 0 := by
    apply (algebraMap M L).injective
    rw [← aeval_algebraMap_apply, map_zero]
    exact hβL
  have hβint : IsIntegral 𝒪[K] βM := ⟨F, hFmonic, hrootM⟩
  let βO : 𝒪[M] := ⟨βM,
    ((Valuation.integer.integers (valuation K)).isIntegral_iff_valuation_le_one βM).mp hβint⟩
  have hβO : algebraMap 𝒪[M] 𝒪[L] βO = β := by
    apply Subtype.ext
    rw [coe_algebraMap_integerRing]
    rfl
  letI : Module 𝓀[K] 𝓀[M] := (inferInstance : Algebra 𝓀[K] 𝓀[M]).toModule
  let j : 𝓀[M] →ₐ[𝓀[K]] 𝓀[L] := IsScalarTower.toAlgHom _ _ _
  have himage : α ∈ j.fieldRange := by
    refine ⟨residue 𝒪[M] βO, ?_⟩
    change algebraMap 𝓀[M] 𝓀[L] (residue 𝒪[M] βO) = α
    rw [algebraMap_residue, hβO, hβres]
  have hjtop : j.fieldRange = ⊤ := by
    apply top_unique
    rw [← hαgen]
    exact IntermediateField.adjoin_simple_le_iff.mpr himage
  have hjbij : Function.Bijective j := ⟨j.injective, AlgHom.fieldRange_eq_top.mp hjtop⟩
  have hresdegree : Module.finrank 𝓀[K] 𝓀[M] = Module.finrank 𝓀[K] 𝓀[L] :=
    (AlgEquiv.ofBijective j hjbij).toLinearEquiv.finrank_eq
  have hann : aeval (β : L) (F.map (algebraMap 𝒪[K] K)) = 0 := by
    rw [aeval_map_algebraMap]
    exact hβL
  have hmin : (minpoly K (β : L)).natDegree ≤ F.natDegree := by
    calc
      _ ≤ (F.map (algebraMap 𝒪[K] K)).natDegree :=
        natDegree_le_natDegree (minpoly.min K (β : L) (hFmonic.map _) hann)
      _ = _ := hFmonic.natDegree_map _
  have hdegree : Module.finrank K M ≤ inertiaDegree K M := by
    calc
      _ = (minpoly K (β : L)).natDegree :=
        IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _)
      _ ≤ F.natDegree := hmin
      _ = (minpoly 𝓀[K] α).natDegree := hFdeg
      _ = Module.finrank 𝓀[K] 𝓀[L] :=
        (Field.primitive_element_iff_minpoly_natDegree_eq 𝓀[K] α).mp hαgen
      _ = inertiaDegree K M := hresdegree.symm
  have he : ramificationIndex K M = 1 := by
    have hfund := ramificationIndex_mul_inertiaDegree K M
    have hfpos : 0 < inertiaDegree K M := Module.finrank_pos
    have hepos := ramificationIndex_pos (K := K) (L := M)
    nlinarith
  exact ⟨he, hjbij, uniformizer_presentation M L hjbij⟩

end TauCeti
