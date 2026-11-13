/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.Cyclotomic.FixingSubgroup), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.Cyclotomic.FixingSubgroup`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.Cyclotomic.FixingSubgroup
public import Mathlib.FieldTheory.KrullTopology
public import ZInQKernel.Contrib.TauCeti.NumberTheory.Cyclotomic.Adjoin
public import ZInQKernel.Contrib.TauCeti.RingTheory.RootsOfUnity.Action
public import ZInQKernel.Contrib.TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots

public section

section
open IntermediateField

/-- **The kernel of the cyclotomic character is open** in the Krull topology: it fixes the finite
extension `K(μ_m) = K(ζ)`. -/
theorem IsPrimitiveRoot.isOpen_ker_autToPow {K M : Type*} [Field K] [Field M] [Algebra K M]
    {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) :
    IsOpen ((hζ.autToPow K).ker : Set Gal(M/K)) := by
  have : FiniteDimensional K K⟮ζ⟯ :=
    adjoin.finiteDimensional ((hζ.isIntegral (NeZero.pos m)).tower_top (A := K))
  rw [← hζ.fixingSubgroup_adjoin_nth_roots_eq_ker_autToPow,
    ← hζ.adjoin_singleton_eq_adjoin_nth_roots]
  exact K⟮ζ⟯.fixingSubgroup_isOpen

end

section
open IntermediateField

/-- **A character of `(ℤ / m)ˣ` read on the cyclotomic character has open kernel**: its kernel
contains the open kernel of the cyclotomic character (`IsPrimitiveRoot.isOpen_ker_autToPow`). Use
it to feed such a character to constructions that require a continuous character of `Gal(M/K)`. -/
theorem IsPrimitiveRoot.isOpen_ker_comp_autToPow {K M A : Type*} [Field K] [Field M]
    [Algebra K M] [AddZeroClass A] {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m)
    (ψ : Additive (ZMod m)ˣ →+ A) :
    IsOpen ((ψ.comp (hζ.autToPow K).toAdditive).ker : Set (Additive Gal(M/K))) := by
  refine AddSubgroup.isOpen_mono (H₁ := Subgroup.toAddSubgroup (hζ.autToPow K).ker)
    (fun g hg ↦ ?_) (hζ.isOpen_ker_autToPow.preimage continuous_toMul)
  have hu : hζ.autToPow K g.toMul = 1 := hg
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, hu,
    ofMul_one, map_zero]

end

end
