/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_Patching_SystemTypes.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical only; no statement, hypothesis, definition or proof term was
altered, weakened or omitted:
  * one `w03_open "IsLocalRing"` inserted after the port namespace: this file `open`s `IsLocalRing`, which the port also declares as nested namespace(s), so a
    plain `open` would resolve to the nested one and hide Mathlib's. The dual root+prefix
    shim keeps the Mathlib root namespace(s) visible, exactly as in the original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Data.ENat.Lattice
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

w03_open "IsLocalRing"

set_option autoImplicit false

open IsLocalRing

namespace IsLocalRing

class IsAdicTopology (R : Type*) [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : Prop where
  isAdic : IsAdic (maximalIdeal R)

end IsLocalRing

class Algebra.TopologicallyFG (R S : Type*) [CommRing R] [Ring S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S] : Prop where
  out : ∃ s : Finset S, Dense (Algebra.adjoin R (s : Set S) : Set S)

instance (priority := 100) {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S] [Algebra.FiniteType R S] :
    Algebra.TopologicallyFG R S where
  out := have ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S); ⟨s, by simp [hs]⟩

open RingTheory in

noncomputable def Module.depth (R M : Type*) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] : ℕ∞ :=
  sSup { List.length s | (s : List R)
    (_ : Sequence.IsWeaklyRegular M s)
    (_ : ∀ r ∈ s, r ∈ maximalIdeal R) }

section PatchingPredicates

attribute [local instance] Module.quotientAnnihilator

variable {ι : Type*}

class Algebra.UniformlyBoundedRank (R : ι → Type*) [∀ i, CommRing (R i)]
    [∀ i, IsLocalRing (R i)] : Prop where
  cond : ∀ k, ∃ n : ℕ, ∀ i, Nat.card (R i ⧸ maximalIdeal (R i) ^ k) < n

class Module.UniformlyBoundedRank (R : Type*) (M : ι → Type*) [CommRing R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] : Prop where
  cond : ∃ n : ℕ, ∀ i, Module.rank (R ⧸ Module.annihilator R (M i)) (M i) < n

class IsPatchingSystem (R : Type*) (M : ι → Type*) [CommRing R] [TopologicalSpace R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (F : Filter ι) : Prop where
  cond : ∀ α : Ideal R, IsOpen (X := R) α → ∀ᶠ i in F, Module.annihilator R (M i) ≤ α

end PatchingPredicates

end ZInQ.Contrib.CloudW03NeronSurj.FLT
