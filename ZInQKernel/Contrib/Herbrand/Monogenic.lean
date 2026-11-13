/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream file LICENSE.
Authors: The Tau Ceti contributors, Bianca Viray, Bryan Boehnke, Grant Yang, George Peykanu,
Tianshuo Wang

CHANGED / PORTED FILE: This is a focused, AI-assisted port with Metamate to Lean 4.35.0
and Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. Namespaces, imports, and the
Nakayama API were adapted; only the general monogenicity proof and its necessary
principal-ideal helper are retained. The perfect-residue-field DVR wrapper is new.

Upstream: TauCetiProject/TauCeti, revision a6027b1d24fcb935c53bd5b50d11b40991cda418
  TauCeti/RingTheory/LocalRing/Monogenic.lean, lines 63-191
    SHA256 f9b301a678c8614f345018152f96dbbb562aa9b4fcb07ef14b2c175759300a99
  TauCeti/RingTheory/DiscreteValuationRing/Monogenic.lean, lines 70-73
    SHA256 aa078f8a606b8c73b7f7aca434b2a829a21b7640aea14da523beded02ac0d6d4
  TauCeti/RingTheory/Ideal/Operations.lean, lines 517-536
    SHA256 ecba32e3decc94eb2083d8696ea1f8cbb79983ba75c13d17232b13d3d7139634
The entire three source files were read, including the omitted results.
Upstream license: https://raw.githubusercontent.com/TauCetiProject/TauCeti/
  a6027b1d24fcb935c53bd5b50d11b40991cda418/LICENSE (Apache-2.0).
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.Tactic.Ring

/-!
# Monogenicity of finite extensions of discrete valuation rings

This module ports the general local-ring argument from Tau Ceti, rather than
specializing an unramified or finite-residue-field result. A primitive residue
field element is lifted, and one Newton step chooses either that lift or the
lift plus a generator of the upstairs maximal ideal. A polynomial value at the
chosen element generates that ideal. Generation modulo the maximal ideal then
propagates through every power, and nilpotence modulo the downstairs maximal
ideal together with Nakayama proves algebra generation.

The exported DVR theorem assumes only a finite torsion-free algebra extension
of DVRs and a perfect downstairs residue field. Neither completeness nor
finiteness of the residue field is assumed. The separable-residue-field and
principal-maximal-ideal local-ring versions are also exposed.

This is one reusable foundation for T22, not the assembled Herbrand statement,
a proof of H, or an independent protocol/Astra acceptance. No existing project
target, registry, manuscript, or protected record is modified.

Reference: J.-P. Serre, *Corps locaux*, Chapter III, §6, Proposition 12.
-/

namespace ZInQ.Contrib.Herbrand

open IsLocalRing Polynomial

namespace Monogenic

section PrincipalIdeal

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- If a subalgebra contains a generator of a principal ideal and spans modulo
that ideal, it spans modulo every power of the ideal.

Port of Tau Ceti's `Subalgebra.toSubmodule_sup_pow_restrictScalars_eq_top`;
no other result from its ideal-operations supplier is needed. -/
theorem toSubmodule_sup_pow_restrictScalars_eq_top {T : Subalgebra R S} {I : Ideal S} {π : S}
    (hπ : Ideal.span {π} = I) (hπT : π ∈ T)
    (h : T.toSubmodule ⊔ I.restrictScalars R = ⊤) (n : ℕ) :
    T.toSubmodule ⊔ (I ^ n).restrictScalars R = ⊤ := by
  subst I
  induction n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨t, ht, m, hm, rfl⟩ := Submodule.mem_sup.mp (h.ge Submodule.mem_top : s ∈ _)
    obtain ⟨u, rfl⟩ : ∃ u, u * π = m := by
      rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hm
      exact hm
    obtain ⟨t', ht', m', hm', rfl⟩ := Submodule.mem_sup.mp (ih.ge Submodule.mem_top : u ∈ _)
    refine Submodule.mem_sup.mpr ⟨t + t' * π, ?_, m' * π, ?_, by
      simp only [add_mul, add_assoc]⟩
    · rw [Subalgebra.mem_toSubmodule] at ht ht' ⊢
      exact add_mem ht (mul_mem ht' hπT)
    · rw [Submodule.restrictScalars_mem, Submodule.pow_succ]
      exact Ideal.mul_mem_mul hm' (Ideal.mem_span_singleton_self _)

end PrincipalIdeal

section Newton

variable {S : Type*} [CommRing S] [IsLocalRing S]

/-- One Newton step at a principal maximal ideal: either `a` or `a + π`
is congruent to `a` and has polynomial value generating the maximal ideal. -/
theorem exists_span_eval_eq_maximalIdeal {f : S[X]} {a π : S}
    (hπ : Ideal.span {π} = maximalIdeal S) (ha : f.eval a ∈ maximalIdeal S)
    (ha' : IsUnit ((derivative f).eval a)) :
    ∃ b : S, b - a ∈ maximalIdeal S ∧ Ideal.span {f.eval b} = maximalIdeal S := by
  have hπmem : π ∈ maximalIdeal S := hπ ▸ Ideal.mem_span_singleton_self π
  by_cases h : Ideal.span {f.eval a} = maximalIdeal S
  · exact ⟨a, by simp, h⟩
  refine ⟨a + π, by simpa using hπmem, ?_⟩
  -- Failure at `a` forces its polynomial value into the square of the maximal ideal.
  obtain ⟨u, hu⟩ : ∃ u, f.eval a = π * u :=
    Ideal.mem_span_singleton.mp (hπ ▸ ha)
  have hu' : u ∈ maximalIdeal S := by
    by_contra hu'
    exact h (by rw [hu, Ideal.span_singleton_mul_right_unit (notMem_maximalIdeal.mp hu'), hπ])
  obtain ⟨d, hd⟩ : ∃ d, u = π * d := Ideal.mem_span_singleton.mp (hπ ▸ hu')
  obtain ⟨k, hk⟩ := binomExpansion f a π
  have hfac : f.eval (a + π) = π * ((derivative f).eval a + π * (d + k)) := by
    rw [hk, hu, hd]
    ring
  have hunit : IsUnit ((derivative f).eval a + π * (d + k)) := by
    refine notMem_maximalIdeal.mp fun hmem => notMem_maximalIdeal.mpr ha' ?_
    simpa using sub_mem hmem (Ideal.mul_mem_right (d + k) _ hπmem)
  rw [hfac, Ideal.span_singleton_mul_right_unit hunit, hπ]

end Newton

section LocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- The actual residue-field algebra structure commutes with reduction of scalars. -/
theorem residue_comp_algebraMap :
    (algebraMap (ResidueField R) (ResidueField S)).comp (residue R) =
      (residue S).comp (algebraMap R S) :=
  RingHom.ext fun x => ResidueField.algebraMap_residue x

/-- A lift of a residue-field algebra generator spans the upstairs ring modulo
its maximal ideal, as a module over the downstairs ring. -/
theorem adjoin_toSubmodule_sup_maximalIdeal_eq_top_of_adjoin_residue_eq_top {β : S}
    (hβ : Algebra.adjoin (ResidueField R) {residue S β} = ⊤) :
    (Algebra.adjoin R {β}).toSubmodule ⊔ (maximalIdeal S).restrictScalars R = ⊤ := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top] at hβ
  refine eq_top_iff.mpr fun s _ => ?_
  obtain ⟨p, hp⟩ := hβ (residue S s)
  obtain ⟨q, rfl⟩ := Polynomial.map_surjective _ residue_surjective p
  rw [← map_aeval_eq_aeval_map residue_comp_algebraMap] at hp
  refine Submodule.mem_sup.mpr ⟨aeval β q, ?_, s - aeval β q, ?_, by ring⟩
  · rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, rfl⟩
  · rw [Submodule.restrictScalars_mem, ← Ideal.Quotient.eq]
    exact hp.symm

variable [Module.Finite R S]

omit [IsLocalHom (algebraMap R S)] in
/-- The upstairs maximal ideal is nilpotent modulo the ideal generated by the
downstairs maximal ideal. No bound or finiteness of either residue field is used. -/
theorem exists_maximalIdeal_pow_le_map :
    ∃ n : ℕ, maximalIdeal S ^ n ≤ (maximalIdeal R).map (algebraMap R S) := by
  have : Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R _).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (R ⧸ maximalIdeal R) :=
    letI := Ideal.Quotient.field (maximalIdeal R)
    inferInstance
  have : IsArtinianRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  exact IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient _

/-- Generation of the residue extension plus a polynomial value generating the
upstairs maximal ideal implies generation of the whole algebra, by Nakayama. -/
theorem adjoin_eq_top_of_span_eval_eq_maximalIdeal {β : S} {g : R[X]}
    (hres : Algebra.adjoin (ResidueField R) {residue S β} = ⊤)
    (hgen : Ideal.span {aeval β g} = maximalIdeal S) :
    Algebra.adjoin R {β} = ⊤ := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_map (R := R) (S := S)
  have hmem : aeval β g ∈ Algebra.adjoin R {β} := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨g, rfl⟩
  have hsup := toSubmodule_sup_pow_restrictScalars_eq_top hgen hmem
    (adjoin_toSubmodule_sup_maximalIdeal_eq_top_of_adjoin_residue_eq_top hres) n
  rw [← Algebra.toSubmodule_eq_top]
  refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_)
  rw [Ideal.smul_top_eq_map]
  exact hsup.ge.trans (sup_le_sup_left (Submodule.restrictScalars_mono R hn) _)

/-- General local-ring monogenicity: a finite local algebra with principal
upstairs maximal ideal and separable residue-field extension is monogenic. -/
theorem exists_adjoin_eq_top_of_span_eq_maximalIdeal
    [Algebra.IsSeparable (ResidueField R) (ResidueField S)] {π : S}
    (hπ : Ideal.span {π} = maximalIdeal S) : ∃ β : S, Algebra.adjoin R {β} = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField R) (ResidueField S)
  obtain ⟨a, rfl⟩ := residue_surjective (R := S) α
  -- Lift the minimal polynomial of the primitive residue element through reduction.
  obtain ⟨g, hg⟩ := (mem_lifts _).mp
    (mem_lifts_of_surjective residue_surjective (minpoly (ResidueField R) (residue S a)))
  have hbridge : ∀ x : S, residue S (aeval x g) =
      aeval (residue S x) (minpoly (ResidueField R) (residue S a)) := fun x => by
    rw [map_aeval_eq_aeval_map residue_comp_algebraMap, hg]
  have hbridge' : ∀ x : S, residue S (aeval x (derivative g)) =
      aeval (residue S x) (derivative (minpoly (ResidueField R) (residue S a))) := fun x => by
    rw [map_aeval_eq_aeval_map residue_comp_algebraMap, ← derivative_map, hg]
  have hval : (g.map (algebraMap R S)).eval a ∈ maximalIdeal S := by
    rw [eval_map, ← aeval_def, ← residue_eq_zero_iff]
    exact (hbridge a).trans (minpoly.aeval _ _)
  have hder : IsUnit ((derivative (g.map (algebraMap R S))).eval a) := by
    rw [derivative_map, eval_map, ← aeval_def, ← residue_ne_zero_iff_isUnit, hbridge' a]
    exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨β, hβa, hβ⟩ := exists_span_eval_eq_maximalIdeal hπ hval hder
  have hres : residue S β = residue S a := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hβa
  refine ⟨β, adjoin_eq_top_of_span_eval_eq_maximalIdeal (g := g) ?_ ?_⟩
  · exact hres ▸ Algebra.adjoin_eq_top_of_primitive_element (IsAlgebraic.of_finite _ _) hα
  · rwa [aeval_def, ← eval_map]

end LocalRing

end Monogenic

section DVR

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]

/-- A finite torsion-free extension of DVRs with separable residue extension is
monogenic. Completeness is unnecessary once the upstairs ring is itself a DVR. -/
theorem exists_dvr_adjoin_eq_top_of_isSeparable
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    ∃ β : B, Algebra.adjoin A {β} = ⊤ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  exact Monogenic.exists_adjoin_eq_top_of_span_eq_maximalIdeal hπ.maximalIdeal_eq.symm

/-- A finite torsion-free extension of DVRs is monogenic when the downstairs
residue field is perfect. This statement has no completeness, finite-residue,
or nonarchimedean-local-field hypothesis. -/
theorem exists_dvr_adjoin_eq_top [PerfectField (ResidueField A)] :
    ∃ β : B, Algebra.adjoin A {β} = ⊤ :=
  exists_dvr_adjoin_eq_top_of_isSeparable

end DVR

end ZInQ.Contrib.Herbrand

#print axioms ZInQ.Contrib.Herbrand.Monogenic.toSubmodule_sup_pow_restrictScalars_eq_top
#print axioms ZInQ.Contrib.Herbrand.Monogenic.exists_span_eval_eq_maximalIdeal
#print axioms ZInQ.Contrib.Herbrand.Monogenic.residue_comp_algebraMap
#print axioms ZInQ.Contrib.Herbrand.Monogenic.adjoin_toSubmodule_sup_maximalIdeal_eq_top_of_adjoin_residue_eq_top
#print axioms ZInQ.Contrib.Herbrand.Monogenic.exists_maximalIdeal_pow_le_map
#print axioms ZInQ.Contrib.Herbrand.Monogenic.adjoin_eq_top_of_span_eval_eq_maximalIdeal
#print axioms ZInQ.Contrib.Herbrand.Monogenic.exists_adjoin_eq_top_of_span_eq_maximalIdeal
#print axioms ZInQ.Contrib.Herbrand.exists_dvr_adjoin_eq_top_of_isSeparable
#print axioms ZInQ.Contrib.Herbrand.exists_dvr_adjoin_eq_top
