/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; a copy is in docs/research/t13-skolem-noether.md.
Authors: The Tau Ceti contributors

Adapted for Lean/Mathlib 4.35.0 by Metamate (2026-11-13): isolated namespace;
assume the finite-dimensionality of the acting algebra, which T13 constructs
explicitly, rather than port the separate faithful-action finiteness theorem.
Source: TauCetiProject/TauCeti, revision 61090fff281d0c6cece0176aa8436ab748b53048,
TauCeti/RingTheory/Semisimple/SimpleArtinian.lean.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.Finiteness.Basic

namespace ZInQ.Contrib.SkolemNoether

open Module

variable {R : Type*} [Ring R] [IsSimpleRing R]

/-- Simple modules over a simple Artinian ring all have the same isomorphism type,
even when they occur in different ambient modules. -/
theorem isIsotypicOfType_of_isSimpleRing [IsArtinianRing R] (S : Type*) [AddCommGroup S]
    [Module R S] [IsSimpleModule R S] (M : Type*) [AddCommGroup M] [Module R M] :
    IsIsotypicOfType R M S := by
  intro m _
  obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m
  obtain ⟨J, ⟨eS⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R S
  have : IsSimpleModule R I := IsSimpleModule.congr e.symm
  have : IsSimpleModule R J := IsSimpleModule.congr eS.symm
  exact ⟨(e.trans (IsSimpleRing.isIsotypic R R I J).some.symm).trans eS.symm⟩

variable (K : Type*) [Field K] [Algebra K R] [FiniteDimensional K R]
  {M : Type*} [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]
  [FiniteDimensional K M]
  {N : Type*} [AddCommGroup N] [Module K N] [Module R N] [IsScalarTower K R N]
  [FiniteDimensional K N]

/-- Equal ground-field dimension classifies finite modules over a finite-dimensional
simple algebra: both are powers of one fixed minimal left ideal. -/
theorem nonempty_linearEquiv_of_finrank_eq (h : finrank K M = finrank K N) :
    Nonempty (M ≃ₗ[R] N) := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · have : Subsingleton N := by
      rw [← Module.finrank_zero_iff (R := K), ← h]
      exact Module.finrank_zero_of_subsingleton
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  obtain ⟨S, _⟩ := IsSemisimpleModule.exists_simple_submodule R R
  have : Module.Finite R M := Module.Finite.of_restrictScalars_finite K R M
  have : Module.Finite R N := Module.Finite.of_restrictScalars_finite K R N
  obtain ⟨n, ⟨eM⟩⟩ :=
    (isIsotypicOfType_of_isSimpleRing (R := R) ↥S M).linearEquiv_fun
  obtain ⟨m, ⟨eN⟩⟩ :=
    (isIsotypicOfType_of_isSimpleRing (R := R) ↥S N).linearEquiv_fun
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  obtain rfl : n = m := by
    simpa [(eM.restrictScalars K).finrank_eq, (eN.restrictScalars K).finrank_eq,
      Module.finrank_pi_fintype, Module.finrank_pos.ne'] using h
  exact ⟨eM.trans eN.symm⟩

end ZInQ.Contrib.SkolemNoether
