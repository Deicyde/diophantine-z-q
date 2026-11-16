/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AlgebraicGeometry_AdicThickening
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)

abbrev adicThickeningBase (n : ℕ) : Spec (.of (R ⧸ I ^ (n + 1))) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))

def adicThickening (n : ℕ) : Scheme.{u} := pullback f (adicThickeningBase I n)

def adicThickeningι (n : ℕ) : adicThickening f I n ⟶ X := pullback.fst f (adicThickeningBase I n)

def adicThickeningToBase (n : ℕ) : adicThickening f I n ⟶ Spec (.of (R ⧸ I ^ (n + 1))) :=
  pullback.snd f (adicThickeningBase I n)

theorem adicThickeningι_comp (n : ℕ) :
    adicThickeningι f I n ≫ f = adicThickeningToBase f I n ≫ adicThickeningBase I n :=
  pullback.condition

theorem adicThickeningBase_succ_comp (n : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) ≫
      adicThickeningBase I (n + 1) = adicThickeningBase I n := by
  rw [adicThickeningBase, adicThickeningBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]

def adicThickeningTransition (n : ℕ) : adicThickening f I n ⟶ adicThickening f I (n + 1) :=
  pullback.lift (adicThickeningι f I n)
    (adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))))
    (by rw [adicThickeningι_comp, Category.assoc, adicThickeningBase_succ_comp])

@[simp] theorem adicThickeningTransition_ι (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningι f I (n + 1) = adicThickeningι f I n := by
  rw [adicThickeningTransition]; exact pullback.lift_fst _ _ _

theorem adicThickeningTransition_toBase (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningToBase f I (n + 1) =
      adicThickeningToBase f I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1)))) := by
  rw [adicThickeningTransition]; exact pullback.lift_snd _ _ _

instance isClosedImmersion_adicThickeningι (n : ℕ) : IsClosedImmersion (adicThickeningι f I n) := by
  have : IsClosedImmersion (adicThickeningBase I n) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact MorphismProperty.pullback_fst _ _ this

theorem adicThickening_def (n : ℕ) : adicThickening f I n = pullback f (adicThickeningBase I n) := rfl
theorem adicThickeningι_def (n : ℕ) : adicThickeningι f I n = pullback.fst f (adicThickeningBase I n) := rfl
theorem adicThickeningToBase_def (n : ℕ) :
    adicThickeningToBase f I n = pullback.snd f (adicThickeningBase I n) := rfl

end AlgebraicGeometry

end
