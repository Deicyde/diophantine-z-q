import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.RingHom.Smooth

/-!
# smooth-fibre: the statement `SmoothFibreReduced`

Verbatim copy of `VertWitness.SmoothFibreReduced` (scratch/vert-witness/VertWitness.lean, line 1840,
task vert-witness), placed in namespace `ZInQ.SmoothFibre` so that it does not clash with the
vert-witness file when that file is moved under `ZInQKernel/Contrib/`. The two definitions have the
same body, so they are definitionally equal and either can be used for the other.
-/

namespace ZInQ.SmoothFibre

/-- **Textbook (commutative algebra): the fibres of a smooth ring map over closed
points are reduced.** For a smooth ring map `φ : R → A` (Mathlib's `RingHom.Smooth`: formally
smooth and of finite presentation) and a maximal ideal `m ⊂ R`, the ideal `m A` is radical, i.e.
`A/mA` is reduced. (`A/mA = A ⊗_R R/m` is smooth over the field `R/m`, hence regular, hence
reduced: Stacks, *Smooth ring maps* (base change) and *smooth over a field ⇒ regular*;
Matsumura, *Commutative Ring Theory*, Thm 28.7 (UNVERIFIED numbers). Mathlib 4.35 has neither
"smooth over a field ⇒ reduced" nor "⇒ regular".) -/
def SmoothFibreReduced : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A), φ.Smooth →
    ∀ m : Ideal R, m.IsMaximal → (m.map φ).IsRadical

end ZInQ.SmoothFibre
