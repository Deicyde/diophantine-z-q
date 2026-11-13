import ZInQKernel.Contrib.Herbrand.Monogenic

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described at
https://www.apache.org/licenses/LICENSE-2.0 .
Authors: The Tau Ceti contributors, Bianca Viray, Bryan Boehnke, Grant Yang,
George Peykanu, Tianshuo Wang

CHANGED / PORTED FILE: the residue-surjective generation criterion from
TauCeti/RingTheory/LocalRing/Monogenic.lean at
 a6027b1d24fcb935c53bd5b50d11b40991cda418
is exposed on the receiving Mathlib 4.35 ring objects. The complete source is
recorded in `docs/research/t22-herbrand.md`; the DVR wrapper is new.
-/

namespace ZInQ.Contrib.Herbrand

open IsLocalRing Polynomial

section LocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]

/-- If the residue extension is trivial, every generator of the upstairs
maximal ideal generates the actual upstairs ring as an algebra. No residue
finiteness, separability, topology, or completeness hypothesis is required. -/
theorem adjoin_eq_top_of_residue_surjective_of_span_eq_maximalIdeal
    (hsurj : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    {π : S} (hπ : Ideal.span {π} = maximalIdeal S) : Algebra.adjoin R {π} = ⊤ := by
  refine Monogenic.adjoin_eq_top_of_span_eval_eq_maximalIdeal (g := X) ?_
    (by simpa using hπ)
  rw [eq_top_iff]
  rintro x _
  obtain ⟨y, rfl⟩ := hsurj x
  exact Subalgebra.algebraMap_mem _ y

end LocalRing

section DVR

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]

/-- In a finite torsion-free DVR extension with surjective residue map, every
actual uniformizer is an algebra generator. -/
theorem dvr_adjoin_eq_top_of_residue_surjective
    (hsurj : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)))
    {π : B} (hπ : Irreducible π) : Algebra.adjoin A {π} = ⊤ :=
  adjoin_eq_top_of_residue_surjective_of_span_eq_maximalIdeal hsurj hπ.maximalIdeal_eq.symm

end DVR

end ZInQ.Contrib.Herbrand

#print axioms ZInQ.Contrib.Herbrand.adjoin_eq_top_of_residue_surjective_of_span_eq_maximalIdeal
#print axioms ZInQ.Contrib.Herbrand.dvr_adjoin_eq_top_of_residue_surjective
