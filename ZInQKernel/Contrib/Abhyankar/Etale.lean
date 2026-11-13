/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The Tau Ceti contributors

Modified for this contribution: forward-only minimal port to Mathlib v4.35.0,
with project-local names, from TauCeti/RingTheory/Etale/AdjoinRoot.lean,
revision 30f41378f0cb1d569f51d8a4d0cb74aea8a80e44.
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.FieldTheory.Separable

/-!
# Etaleness of the unit-root step in the tame DVR model

Only the forward monic/separable presentation is ported. There is no import
of Tau Ceti's function-field or perfect-residue theory.
-/

namespace ZInQ.Contrib.Abhyankar

open Polynomial

private noncomputable def standardEtalePairOfSeparable
    {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) (hs : f.Separable) :
    StandardEtalePair R where
  f := f
  monic_f := hf
  g := 1
  cond := by
    obtain ⟨a, b, hab⟩ := (separable_def' f).mp hs
    exact ⟨b, a, 0, by rw [pow_zero, ← hab]; ring⟩

/-- A monic separable polynomial gives an actual standard-etale adjoin-root algebra. -/
theorem standardEtale_adjoinRoot_of_monic_separable
    {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) (hs : f.Separable) :
    Algebra.IsStandardEtale R (AdjoinRoot f) := by
  let P := standardEtalePairOfSeparable hf hs
  have hroot : P.HasMap (AdjoinRoot.root f) :=
    ⟨AdjoinRoot.aeval_eq f ▸ AdjoinRoot.mk_self, by simp [P, standardEtalePairOfSeparable]⟩
  have hX : f.eval₂ (Algebra.ofId R P.Ring : R →+* P.Ring) P.X = 0 := P.hasMap_X.1
  let φ : P.Ring →ₐ[R] AdjoinRoot f := P.lift _ hroot
  let ψ : AdjoinRoot f →ₐ[R] P.Ring := AdjoinRoot.liftAlgHom f (Algebra.ofId R _) P.X hX
  have hψ : ψ (AdjoinRoot.root f) = P.X := AdjoinRoot.liftAlgHom_root f _ _ hX
  have hφψ : φ.comp ψ = AlgHom.id R _ :=
    AdjoinRoot.algHom_ext (by rw [AlgHom.comp_apply, hψ]; exact P.lift_X _ hroot)
  have hψφ : ψ.comp φ = AlgHom.id R _ :=
    P.hom_ext (by rw [AlgHom.comp_apply, P.lift_X, hψ, AlgHom.id_apply])
  have : Algebra.IsStandardEtale R P.Ring := inferInstance
  exact this.of_equiv (AlgEquiv.ofAlgHom φ ψ hφψ hψφ)

/-- Extracting a root of a unit with an invertible exponent is etale over the actual ring. -/
theorem etale_unitRoot
    {R : Type*} [CommRing R] {u : R} (hu : IsUnit u) {e : ℕ}
    (he : 0 < e) (hunit : IsUnit (e : R)) :
    Algebra.Etale R (AdjoinRoot (X ^ e - C u)) := by
  have := standardEtale_adjoinRoot_of_monic_separable (monic_X_pow_sub_C u he.ne')
    (separable_X_pow_sub_C_unit hu.unit hunit)
  infer_instance

end ZInQ.Contrib.Abhyankar
