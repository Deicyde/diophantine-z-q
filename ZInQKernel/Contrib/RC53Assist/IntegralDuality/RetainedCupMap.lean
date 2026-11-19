import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Duality

/-!
# Pulling a traced cup adjoint back to the specified cochain models

The comparison maps are the given maps of cochain complexes. Pullback of a
traced pairing produces a map into the dual of the model, with an explicit
evaluation formula. The construction does not assert that dualizing an
arbitrary comparison preserves quasi-isomorphisms.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

variable {R : Type u} [CommRing R]

/-- A cochain map between the existing relation-indexed complexes, without changing it. -/
def relationHomOfCochainHom {A B : GCx R} (f : A.toCC ⟶ B.toCC) : GHom A B where
  f i j h := h ▸ (f.f i).hom
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj
    have hf := congrArg (fun k => k.hom x) (f.comm i i₁)
    change (B.toCC.d i i₁).hom ((f.f i).hom x) =
      (f.f i₁).hom ((A.toCC.d i i₁).hom x) at hf
    erw [GCx.toCC_d_hom B i i₁ h₁, GCx.toCC_d_hom A i i₁ h₁] at hf
    exact hf.symm

/-- Going back to a cochain map recovers exactly the given comparison. -/
theorem relationHomOfCochainHom_toCC {A B : GCx R} (f : A.toCC ⟶ B.toCC) :
    GHom.toCC (relationHomOfCochainHom f) = f := by
  ext n x
  rfl

/-- The traced cup adjoint pulled back through the two specified model comparisons. -/
def pullbackCupAdjoint {A B T P Q : GCx R} (cup : GPair A B T)
    (c : P.toCC ⟶ A.toCC) (c' : Q.toCC ⟶ B.toCC)
    (m : ℤ) (tr : T.X m →ₗ[R] R)
    (htr : ∀ z, tr (T.d (m - 1) m (by omega) z) = 0) : GHom P (dualCx Q m) :=
  ghomComp (ghomComp (relationHomOfCochainHom c) (adjHom cup m tr htr))
    (dualHom (relationHomOfCochainHom c') m)

/-- Evaluation uses the original cup, trace and comparison maps, not a new pairing. -/
theorem pullbackCupAdjoint_apply {A B T P Q : GCx R} (cup : GPair A B T)
    (c : P.toCC ⟶ A.toCC) (c' : Q.toCC ⟶ B.toCC)
    (m : ℤ) (tr : T.X m →ₗ[R] R)
    (htr : ∀ z, tr (T.d (m - 1) m (by omega) z) = 0)
    (n : ℤ) (x : P.X n) (y : Q.X (m - n)) :
    asDual ((pullbackCupAdjoint cup c c' m tr htr).f n n rfl x) y =
      tr (cup.P n (m - n) m (by omega) ((c.f n).hom x) ((c'.f (m - n)).hom y)) :=
  rfl

end ZInQ.Contrib.RC53Assist.IntegralDuality
